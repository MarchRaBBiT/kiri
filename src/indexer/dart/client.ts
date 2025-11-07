/**
 * DartAnalysisClient: Dart Analysis Server との JSON-RPC 通信クライアント
 */

import { spawn, type ChildProcess } from "node:child_process";
import { createInterface, type Interface } from "node:readline";
import { detectDartSdk, MissingToolError } from "./sdk.js";
import type {
  RpcRequest,
  RpcResponse,
  RpcNotification,
  UpdateContentParams,
  GetOutlineResult,
  GetLibraryDependenciesResult,
  DartAnalysisPayload,
  ServerConnectedParams,
  ServerErrorParams,
} from "./types.js";

export interface DartAnalysisClientOptions {
  workspaceRoots: string[];
  logPath?: string;
}

/**
 * DAPProtocolError: Analysis Server プロトコルエラー
 */
export class DAPProtocolError extends Error {
  constructor(
    message: string,
    public code?: number,
    public data?: unknown
  ) {
    super(message);
    this.name = "DAPProtocolError";
  }
}

/**
 * DartAnalysisClient: Dart Analysis Server プロセス管理と JSON-RPC 通信
 */
export class DartAnalysisClient {
  private process: ChildProcess | null = null;
  private readline: Interface | null = null;
  private requestId = 0;
  private pendingRequests = new Map<
    string,
    {
      resolve: (result: unknown) => void;
      reject: (error: Error) => void;
      timeout: NodeJS.Timeout;
    }
  >();
  private serverVersion: string | null = null;
  private initialized = false;
  private initializePromise: Promise<void> | null = null;

  constructor(private options: DartAnalysisClientOptions) {}

  /**
   * Analysis Server プロセスを起動し初期化する
   *
   * 並行呼び出しを安全に処理: 既に初期化中の場合は同じPromiseを返す
   *
   * @throws MissingToolError - Dart SDK が見つからない場合
   * @throws DAPProtocolError - サーバー起動失敗時
   */
  async initialize(): Promise<void> {
    if (this.initialized) {
      return;
    }

    // 既に初期化中なら、そのPromiseを返す（並行初期化の競合を防ぐ）
    if (this.initializePromise) {
      return this.initializePromise;
    }

    this.initializePromise = (async () => {
      try {
        // Dart SDK 検出
        const sdkInfo = detectDartSdk();
        console.log(
          `[DartAnalysisClient] Detected Dart SDK ${sdkInfo.version} at ${sdkInfo.sdkPath}`
        );

        // Analysis Server プロセス起動
        // Windows対応: dartExecutable の絶対パスを使用
        const args = [
          "--disable-dart-dev",
          sdkInfo.analysisServerPath,
          "--protocol=instrumentation",
        ];

        if (this.options.logPath) {
          args.push(`--instrumentation-log-file=${this.options.logPath}`);
        }

        this.process = spawn(sdkInfo.dartExecutable, args, {
          stdio: ["pipe", "pipe", "pipe"],
        });

        if (!this.process.stdout || !this.process.stdin) {
          throw new DAPProtocolError("Failed to spawn Analysis Server: stdio not available");
        }

        // readline で行単位で JSON を読み取る
        this.readline = createInterface({
          input: this.process.stdout,
          crlfDelay: Infinity,
        });

        this.readline.on("line", (line) => {
          this.handleMessage(line);
        });

        this.process.stderr?.on("data", (data) => {
          console.error(`[DartAnalysisClient] stderr: ${data}`);
        });

        this.process.on("error", (error) => {
          console.error(`[DartAnalysisClient] process error:`, error);
          this.rejectAllPending(
            new DAPProtocolError(`Analysis Server process error: ${error.message}`)
          );
        });

        this.process.on("exit", (code, signal) => {
          console.log(`[DartAnalysisClient] process exited: code=${code}, signal=${signal}`);
          this.rejectAllPending(
            new DAPProtocolError(`Analysis Server exited unexpectedly: code=${code}`)
          );
        });

        // server.setSubscriptions で接続通知を受け取る
        await this.sendRequest("server.setSubscriptions", {
          subscriptions: ["STATUS"],
        });

        // analysis.setAnalysisRoots でワークスペースルートを設定
        await this.sendRequest("analysis.setAnalysisRoots", {
          included: this.options.workspaceRoots,
          excluded: [],
        });

        this.initialized = true;
        console.log(`[DartAnalysisClient] Initialized with roots:`, this.options.workspaceRoots);
      } finally {
        // 初期化完了（成功/失敗問わず）後はPromiseをリセット
        this.initializePromise = null;
      }
    })();

    await this.initializePromise;
  }

  /**
   * ファイルを解析してシンボル情報を取得（MVP版）
   *
   * @param filePath - 解析対象ファイルの絶対パス
   * @param content - ファイル内容
   * @returns DartAnalysisPayload
   */
  async analyzeFile(filePath: string, content: string): Promise<DartAnalysisPayload> {
    if (!this.initialized) {
      await this.initialize();
    }

    // analysis.updateContent でファイル内容を送信
    const updateParams: UpdateContentParams = {
      files: {
        [filePath]: {
          type: "add",
          content,
        },
      },
    };

    await this.sendRequest("analysis.updateContent", updateParams);

    try {
      // analysis.getOutline でシンボル階層を取得
      const outlineResult = await this.sendRequest<GetOutlineResult>("analysis.getOutline", {
        file: filePath,
      });

      return {
        outline: outlineResult.outline,
      };
    } finally {
      // メモリリーク防止: オーバーレイを必ず削除
      await this.sendRequest("analysis.updateContent", {
        files: {
          [filePath]: {
            type: "remove",
          },
        },
      }).catch((error) => {
        console.warn(`[analyzeFile] Failed to remove overlay for ${filePath}:`, error);
      });
    }
  }

  /**
   * ライブラリの依存関係を取得（Phase 3）
   *
   * @param filePath - 解析対象ファイルの絶対パス
   * @returns GetLibraryDependenciesResult
   */
  async getLibraryDependencies(filePath: string): Promise<GetLibraryDependenciesResult> {
    if (!this.initialized) {
      await this.initialize();
    }

    const result = await this.sendRequest<GetLibraryDependenciesResult>(
      "analysis.getLibraryDependencies",
      {}
    );

    return result;
  }

  /**
   * Analysis Server プロセスを終了
   */
  async dispose(): Promise<void> {
    if (!this.process) {
      return;
    }

    try {
      // server.shutdown リクエスト
      await this.sendRequest("server.shutdown", {});

      // プロセス終了を待つ
      await new Promise<void>((resolve) => {
        if (!this.process) {
          resolve();
          return;
        }
        this.process.once("exit", () => resolve());
        // タイムアウト後は強制終了
        setTimeout(() => {
          this.process?.kill("SIGTERM");
          resolve();
        }, 5000);
      });
    } catch (error) {
      console.error(`[DartAnalysisClient] dispose error:`, error);
    } finally {
      this.readline?.close();
      this.process?.kill("SIGTERM");
      this.process = null;
      this.readline = null;
      this.initialized = false;
    }
  }

  /**
   * JSON-RPC リクエスト送信
   */
  private async sendRequest<TResult = unknown>(method: string, params: unknown): Promise<TResult> {
    if (!this.process?.stdin) {
      throw new DAPProtocolError("Analysis Server process not running");
    }

    const id = `${++this.requestId}`;
    const request: RpcRequest = { id, method, params };

    return new Promise<TResult>((resolve, reject) => {
      // タイムアウト設定（30秒）
      const timeout = setTimeout(() => {
        this.pendingRequests.delete(id);
        reject(new DAPProtocolError(`Request timeout: ${method}`, -32000, { method, params }));
      }, 30000);

      this.pendingRequests.set(id, {
        resolve: resolve as (result: unknown) => void,
        reject,
        timeout,
      });

      // JSON-RPC メッセージ送信（改行区切り）
      const message = JSON.stringify(request) + "\n";
      this.process!.stdin!.write(message);
    });
  }

  /**
   * サーバーからのメッセージを処理
   */
  private handleMessage(line: string): void {
    if (!line.trim()) {
      return;
    }

    try {
      const message = JSON.parse(line);

      // レスポンス処理
      if ("id" in message && message.id) {
        this.handleResponse(message as RpcResponse);
      }
      // 通知処理
      else if ("event" in message) {
        this.handleNotification(message as RpcNotification);
      }
    } catch (error) {
      console.error(`[DartAnalysisClient] Failed to parse message:`, line, error);
    }
  }

  /**
   * レスポンス処理
   */
  private handleResponse(response: RpcResponse): void {
    const pending = this.pendingRequests.get(response.id);
    if (!pending) {
      console.warn(`[DartAnalysisClient] Received response for unknown request: ${response.id}`);
      return;
    }

    this.pendingRequests.delete(response.id);
    clearTimeout(pending.timeout);

    if (response.error) {
      pending.reject(
        new DAPProtocolError(response.error.message, response.error.code, response.error.data)
      );
    } else {
      pending.resolve(response.result);
    }
  }

  /**
   * 通知処理
   */
  private handleNotification(notification: RpcNotification): void {
    switch (notification.event) {
      case "server.connected": {
        const params = notification.params as ServerConnectedParams;
        this.serverVersion = params.version;
        console.log(
          `[DartAnalysisClient] Server connected: version=${params.version}, pid=${params.pid}`
        );
        break;
      }
      case "server.error": {
        const params = notification.params as ServerErrorParams;
        console.error(
          `[DartAnalysisClient] Server error (fatal=${params.isFatal}):`,
          params.message
        );
        if (params.isFatal) {
          this.rejectAllPending(new DAPProtocolError(`Fatal server error: ${params.message}`));
        }
        break;
      }
      case "analysis.errors":
        // MVP では無視（後のフェーズで処理）
        break;
      default:
        // その他の通知は無視
        break;
    }
  }

  /**
   * 全ての pending リクエストを reject
   */
  private rejectAllPending(error: Error): void {
    for (const [id, pending] of this.pendingRequests) {
      clearTimeout(pending.timeout);
      pending.reject(error);
    }
    this.pendingRequests.clear();
  }
}
