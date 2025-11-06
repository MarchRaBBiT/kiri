/**
 * Dart Analysis Server を使った Dart ファイル解析のエントリポイント
 */

import path from "node:path";
import type { SymbolRecord, SnippetRecord, DependencyRecord } from "../codeintel.js";
import { DartAnalysisClient } from "./client.js";
import { outlineToSymbols } from "./transform.js";
import { isDartSdkAvailable } from "./sdk.js";
import { extractDependencies } from "./dependencies.js";

// グローバルな Analysis Client インスタンス（リポジトリ単位で共有）
let globalClient: DartAnalysisClient | null = null;
let clientWorkspaceRoot: string | null = null;
let clientPromise: Promise<DartAnalysisClient> | null = null;

/**
 * Dart Analysis Client の取得（遅延初期化）
 *
 * 並行呼び出しを安全に処理: 既に切り替え処理中の場合は待機する
 *
 * @param workspaceRoot - ワークスペースルート（リポジトリパス）
 * @returns DartAnalysisClient インスタンス
 */
async function ensureDartClient(workspaceRoot: string): Promise<DartAnalysisClient> {
  // 既存クライアントがあり、同じワークスペースなら再利用
  if (globalClient && clientWorkspaceRoot === workspaceRoot) {
    return globalClient;
  }

  // 既にワークスペース切り替え処理中なら待つ
  if (clientPromise) {
    await clientPromise;
    // 待機後、目的のワークスペースになっていればそれを返す
    if (clientWorkspaceRoot === workspaceRoot) {
      return globalClient!;
    }
  }

  // 新しいクライアントを作成（並行処理をロック）
  clientPromise = (async () => {
    // 異なるワークスペースの場合は古いクライアントを破棄
    if (globalClient) {
      await globalClient.dispose();
    }

    const client = new DartAnalysisClient({
      workspaceRoots: [workspaceRoot],
    });

    await client.initialize();
    globalClient = client;
    clientWorkspaceRoot = workspaceRoot;

    return client;
  })();

  try {
    const client = await clientPromise;
    return client;
  } finally {
    // 処理完了後はPromiseをリセット
    clientPromise = null;
  }
}

/**
 * Dart ファイルを解析してシンボル・スニペット・依存関係を抽出
 *
 * @param filePath - ファイルパス（相対パスの場合は workspaceRoot からの相対パス）
 * @param content - ファイル内容
 * @param workspaceRoot - ワークスペースルート（絶対パス）
 * @returns { symbols, snippets, dependencies }
 */
export async function analyzeDartSource(
  filePath: string,
  content: string,
  workspaceRoot: string
): Promise<{
  symbols: SymbolRecord[];
  snippets: SnippetRecord[];
  dependencies: DependencyRecord[];
}> {
  // Dart SDK が利用できない場合は空の結果を返す
  if (!isDartSdkAvailable()) {
    console.warn(`[analyzeDartSource] Dart SDK not available, skipping analysis for ${filePath}`);
    return { symbols: [], snippets: [], dependencies: [] };
  }

  // Analysis Server は絶対パスを要求するため、相対パスの場合は絶対パスに変換
  const absoluteFilePath = path.isAbsolute(filePath)
    ? filePath
    : path.resolve(workspaceRoot, filePath);

  try {
    const client = await ensureDartClient(workspaceRoot);
    const payload = await client.analyzeFile(absoluteFilePath, content);

    const { symbols, snippets } = outlineToSymbols(payload.outline, content);

    // Phase 3: 依存関係を取得
    let dependencies: DependencyRecord[] = [];
    try {
      const dependenciesResult = await client.getLibraryDependencies(absoluteFilePath);
      dependencies = extractDependencies(absoluteFilePath, dependenciesResult, workspaceRoot);
    } catch (depError) {
      // 依存関係の取得に失敗しても、シンボル情報は返す
      console.warn(
        `[analyzeDartSource] Failed to get dependencies for ${absoluteFilePath}:`,
        depError
      );
    }

    return { symbols, snippets, dependencies };
  } catch (error) {
    console.error(`[analyzeDartSource] Failed to analyze ${absoluteFilePath}:`, error);
    // エラー時は空の結果を返す（Swift/PHP と同様）
    return { symbols: [], snippets: [], dependencies: [] };
  }
}

/**
 * グローバルクライアントのクリーンアップ
 *
 * プロセス終了時やインデクサー終了時に呼ぶ
 */
export async function cleanup(): Promise<void> {
  // 進行中の初期化があれば待つ
  if (clientPromise) {
    await clientPromise;
  }

  if (globalClient) {
    await globalClient.dispose();
    globalClient = null;
    clientWorkspaceRoot = null;
    clientPromise = null;
  }
}
