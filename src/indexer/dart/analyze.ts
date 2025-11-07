/**
 * Dart Analysis Server を使った Dart ファイル解析のエントリポイント
 */

import path from "node:path";
import type { SymbolRecord, SnippetRecord, DependencyRecord } from "../codeintel.js";
import { DartAnalysisClient } from "./client.js";
import { outlineToSymbols } from "./transform.js";
import { isDartSdkAvailable } from "./sdk.js";
import { extractDependencies } from "./dependencies.js";
import { normalizeWorkspaceKey } from "./pathKey.js";
import { createCapacityLimiter, type CapacityLimiter } from "./poolGate.js";

// ワークスペース毎のクライアント管理（参照カウント + アイドルTTL方式）
interface ClientEntry {
  client: DartAnalysisClient;
  refs: number;
  initPromise: Promise<DartAnalysisClient> | null;
  idleTimer: NodeJS.Timeout | null; // Fix #2: アイドルタイマー
  lastUsed: number; // Fix #2: 最終使用時刻
}

const clients = new Map<string, ClientEntry>();

// Fix #2: アイドルTTL (デフォルト: 60秒、環境変数で調整可能)
// Fix #6: ?? 演算子を使用して IDLE_TTL_MS=0 でTTLを無効化可能にする
const IDLE_TTL_MS = Number(process.env.DART_ANALYSIS_IDLE_MS ?? "60000");

// Fix #4: 最大クライアント数制限（デフォルト: 8、環境変数で調整可能）
// 大規模モノレポでメモリ枯渇を防ぐため、LRU evictionを実施
const MAX_CLIENTS = parseInt(process.env.DART_ANALYSIS_MAX_CLIENTS ?? "8", 10);

// Fix #1: Client wait timeout (default: 10000ms = 10 seconds)
const DART_ANALYSIS_CLIENT_WAIT_MS = parseInt(
  process.env.DART_ANALYSIS_CLIENT_WAIT_MS ?? "10000",
  10
);

// Fix #1 & #2: Pool capacity limiter to enforce MAX_CLIENTS
const poolLimiter: CapacityLimiter = createCapacityLimiter(MAX_CLIENTS);

/**
 * Dart Analysis Client の取得（参照カウント方式）
 *
 * 進行中のリクエストがあるクライアントは dispose されず、
 * 全ての参照が解放されるまで維持される
 *
 * @param workspaceRoot - ワークスペースルート（リポジトリパス）
 * @returns DartAnalysisClient インスタンス
 */
async function acquireClient(workspaceRoot: string): Promise<DartAnalysisClient> {
  // Fix #3: Normalize workspace path for Windows case-insensitivity
  const workspaceKey = normalizeWorkspaceKey(workspaceRoot);
  let entry = clients.get(workspaceKey);

  if (!entry) {
    // Fix #1 & #2: Acquire pool permit before creating new client
    // This enforces MAX_CLIENTS limit and provides waiting queue with timeout
    await poolLimiter.acquire({ timeoutMs: DART_ANALYSIS_CLIENT_WAIT_MS });

    // Re-check after await (another request might have created the same client)
    entry = clients.get(workspaceKey);
    if (entry) {
      // Client was created by concurrent request - release permit and use existing
      poolLimiter.release();
    } else {
      // Fix #2: Try LRU eviction if pool is full (atomic with permit acquisition)
      if (clients.size >= MAX_CLIENTS) {
        // Find least recently used idle client
        let lruWorkspace: string | null = null;
        let oldestTime = Infinity;

        for (const [ws, ent] of clients.entries()) {
          if (ent.refs === 0 && ent.lastUsed < oldestTime) {
            oldestTime = ent.lastUsed;
            lruWorkspace = ws;
          }
        }

        // Evict LRU client atomically
        if (lruWorkspace) {
          const lruEntry = clients.get(lruWorkspace)!;
          if (lruEntry.idleTimer) {
            clearTimeout(lruEntry.idleTimer);
          }
          clients.delete(lruWorkspace);
          console.log(
            `[acquireClient] Evicting LRU client for ${lruWorkspace} (pool size: ${MAX_CLIENTS})`
          );

          // Dispose in background (don't await to avoid blocking)
          lruEntry.client
            .dispose({ timeoutMs: 2000 })
            .catch((error) => {
              console.error(
                `[acquireClient] Failed to dispose LRU client for ${lruWorkspace}:`,
                error
              );
            })
            .finally(() => {
              // Fix #2: Release permit after disposal completes
              poolLimiter.release();
            });
        } else {
          // Fix #7 (Critical Review): No idle client to evict - cannot exceed MAX_CLIENTS
          // All clients are actively processing files. Release permit and throw error.
          poolLimiter.release();
          throw new Error(
            `[acquireClient] Dart Analysis Server pool is full with ${MAX_CLIENTS} active clients. ` +
              `Cannot create new client for workspace ${workspaceRoot}. ` +
              `Consider increasing DART_ANALYSIS_MAX_CLIENTS or reducing concurrent indexing.`
          );
        }
      }
    }

    // Create new client only if we still don't have one
    if (!entry) {
      // 新しいクライアントエントリを作成
      const client = new DartAnalysisClient({
        workspaceRoots: [workspaceRoot],
      });

      entry = {
        client,
        refs: 0,
        initPromise: client.initialize().then(() => client),
        idleTimer: null, // Fix #2: アイドルタイマー初期化
        lastUsed: Date.now(), // Fix #2: 最終使用時刻初期化
      };

      clients.set(workspaceKey, entry);
    }
  }

  // Fix #2: アイドルタイマーをクリア（再利用時）
  if (entry.idleTimer) {
    clearTimeout(entry.idleTimer);
    entry.idleTimer = null;
  }

  // Fix #3: 初期化を待つ（失敗時はエントリを削除してリトライ可能にする）
  if (entry.initPromise) {
    try {
      await entry.initPromise;
      entry.initPromise = null;
    } catch (error) {
      // 初期化失敗: エントリを削除して次回リトライ可能にする
      clients.delete(workspaceKey);
      // Fix #3: skipShutdown で即時強制終了（二重タイムアウト回避）
      await entry.client.dispose({ skipShutdown: true }).catch(() => {});
      // Fix #1: Release permit on initialization failure
      poolLimiter.release();
      throw error;
    }
  }

  // 参照カウントを増やす
  entry.refs += 1;
  entry.lastUsed = Date.now(); // Fix #2: 最終使用時刻更新

  return entry.client;
}

/**
 * Dart Analysis Client の解放（参照カウント + アイドルTTL方式）
 *
 * Fix #2: 参照カウントが 0 になったら即座に dispose せず、アイドルTTL後に dispose
 * これによりファイル毎のサーバー再起動を回避し、性能を大幅に改善
 *
 * @param workspaceRoot - ワークスペースルート（リポジトリパス）
 */
function releaseClient(workspaceRoot: string): void {
  // Fix #3: Normalize workspace path for Windows case-insensitivity
  const workspaceKey = normalizeWorkspaceKey(workspaceRoot);
  const entry = clients.get(workspaceKey);
  if (!entry) {
    return;
  }

  entry.refs -= 1;

  // Fix #2: refs が 0 になったらアイドルタイマーを起動（即座に dispose しない）
  if (entry.refs === 0) {
    entry.idleTimer = setTimeout(() => {
      // タイムアウト時に再度 refs をチェック（タイマー中に再取得された可能性）
      if (entry.refs === 0) {
        console.log(`[releaseClient] Disposing idle client for ${workspaceRoot}`);
        clients.delete(workspaceKey);
        entry.client
          .dispose({ timeoutMs: 2000 })
          .catch((error) => {
            console.error(`[releaseClient] Failed to dispose client for ${workspaceRoot}:`, error);
          })
          .finally(() => {
            // Fix #1: Release pool permit after disposal
            poolLimiter.release();
          });
      }
    }, IDLE_TTL_MS);

    // Fix #1: Node.jsがタイマー待ちでハングしないように unref() を呼ぶ
    // これによりCLIプロセスがアイドルタイマーを待たずに終了できる
    entry.idleTimer.unref();
  }
}

/**
 * Dart ファイルを解析してシンボル・スニペット・依存関係を抽出
 *
 * Fix #5: status フィールドを追加してエラーをリトライ可能にする
 *
 * @param filePath - ファイルパス（相対パスの場合は workspaceRoot からの相対パス）
 * @param content - ファイル内容
 * @param workspaceRoot - ワークスペースルート（絶対パス）
 * @returns { symbols, snippets, dependencies, status, error? }
 */
export async function analyzeDartSource(
  filePath: string,
  content: string,
  workspaceRoot: string
): Promise<{
  symbols: SymbolRecord[];
  snippets: SnippetRecord[];
  dependencies: DependencyRecord[];
  status: "success" | "error" | "sdk_unavailable";
  error?: string;
}> {
  // Dart SDK が利用できない場合は空の結果を返す
  if (!isDartSdkAvailable()) {
    console.warn(`[analyzeDartSource] Dart SDK not available, skipping analysis for ${filePath}`);
    return { symbols: [], snippets: [], dependencies: [], status: "sdk_unavailable" };
  }

  // Analysis Server は絶対パスを要求するため、相対パスの場合は絶対パスに変換
  const absoluteFilePath = path.isAbsolute(filePath)
    ? filePath
    : path.resolve(workspaceRoot, filePath);

  // クライアントを取得（参照カウント増加）
  const client = await acquireClient(workspaceRoot);

  try {
    const payload = await client.analyzeFile(absoluteFilePath, content);

    const { symbols, snippets } = outlineToSymbols(payload.outline, content);

    // Phase 3 (disabled): 依存関係を取得
    // TODO: analysis.getLibraryDependencies は workspace 全体の依存関係を返すため、
    // ファイル単位の依存関係を正しく取得できない。
    // Phase 4 で analysis.getOutline から import/export ディレクティブを抽出するか、
    // analysis.getNavigation を使用した実装に切り替える必要がある。
    // 現在は誤ったデータを返さないために空配列を返す。
    const dependencies: DependencyRecord[] = [];

    return { symbols, snippets, dependencies, status: "success" };
  } catch (error) {
    console.error(`[analyzeDartSource] Failed to analyze ${absoluteFilePath}:`, error);
    // Fix #5: エラー時はstatusとerrorフィールドを返して呼び出し元がリトライ可能にする
    return {
      symbols: [],
      snippets: [],
      dependencies: [],
      status: "error",
      error: error instanceof Error ? error.message : String(error),
    };
  } finally {
    // クライアントを解放（参照カウント減少）
    releaseClient(workspaceRoot);
  }
}

/**
 * 全クライアントのクリーンアップ
 *
 * プロセス終了時やインデクサー終了時に呼ぶ
 * 全てのワークスペースのクライアントを強制的に dispose する
 */
export async function cleanup(): Promise<void> {
  const disposePromises: Promise<void>[] = [];

  for (const [workspaceRoot, entry] of clients.entries()) {
    // Fix #2: アイドルタイマーをクリア
    if (entry.idleTimer) {
      clearTimeout(entry.idleTimer);
      entry.idleTimer = null;
    }

    // 初期化中なら待つ
    if (entry.initPromise) {
      disposePromises.push(
        entry.initPromise
          .then((client) => client.dispose({ timeoutMs: 2000 }))
          .catch((error) => {
            console.error(`[cleanup] Failed to dispose client for ${workspaceRoot}:`, error);
          })
      );
    } else {
      disposePromises.push(
        entry.client.dispose({ timeoutMs: 2000 }).catch((error) => {
          console.error(`[cleanup] Failed to dispose client for ${workspaceRoot}:`, error);
        })
      );
    }
  }

  await Promise.allSettled(disposePromises);
  clients.clear();
}

/**
 * Fix #1: プロセスライフサイクルフックの登録
 *
 * beforeExit/シグナルハンドラで非同期 cleanup を実行し、
 * exit フォールバックでは同期的な強制終了のみ行う
 */
function registerDartLifecycleHooks(): void {
  let cleanupInProgress = false;

  const gracefulShutdown = async (signal: string) => {
    if (cleanupInProgress) {
      return; // 二重実行防止
    }
    cleanupInProgress = true;

    console.log(`[DartLifecycle] Received ${signal}, cleaning up Analysis Server processes...`);
    try {
      await cleanup();
      console.log(`[DartLifecycle] Cleanup completed successfully`);
    } catch (error) {
      console.error(`[DartLifecycle] Cleanup failed:`, error);
    } finally {
      // SIGINT/SIGTERM の場合はプロセス終了
      if (signal !== "beforeExit") {
        process.exit(signal === "SIGTERM" ? 0 : 1);
      }
    }
  };

  // Fix #1: beforeExit で非同期 cleanup
  process.once("beforeExit", () => gracefulShutdown("beforeExit"));

  // Fix #1: シグナルハンドラ
  process.once("SIGINT", () => gracefulShutdown("SIGINT"));
  process.once("SIGTERM", () => gracefulShutdown("SIGTERM"));
  process.once("SIGQUIT", () => gracefulShutdown("SIGQUIT"));

  // Fix #1: 未捕捉例外時のクリーンアップ
  process.once("uncaughtException", async (error) => {
    console.error(`[DartLifecycle] Uncaught exception:`, error);
    await gracefulShutdown("uncaughtException");
    process.exit(1);
  });

  // Fix #1: exit フォールバック - 同期的な強制終了のみ
  process.once("exit", () => {
    // 非同期処理は実行されないため、同期的にプロセスを強制終了
    for (const [, entry] of clients.entries()) {
      try {
        entry.client.forceKill();
      } catch {
        // exit時なのでエラーは無視
      }
    }
    clients.clear();
  });
}

// Fix #1: ライフサイクルフックを登録
registerDartLifecycleHooks();
