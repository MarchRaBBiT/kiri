/**
 * Dart Analysis Server を使った Dart ファイル解析のエントリポイント
 */

import type { SymbolRecord, SnippetRecord, DependencyRecord } from "../codeintel.js";
import { DartAnalysisClient } from "./client.js";
import { outlineToSymbols } from "./transform.js";
import { isDartSdkAvailable } from "./sdk.js";
import { extractDependencies } from "./dependencies.js";

// グローバルな Analysis Client インスタンス（リポジトリ単位で共有）
let globalClient: DartAnalysisClient | null = null;
let clientWorkspaceRoot: string | null = null;

/**
 * Dart Analysis Client の取得（遅延初期化）
 *
 * @param workspaceRoot - ワークスペースルート（リポジトリパス）
 * @returns DartAnalysisClient インスタンス
 */
async function ensureDartClient(workspaceRoot: string): Promise<DartAnalysisClient> {
  // 既存クライアントがあり、同じワークスペースなら再利用
  if (globalClient && clientWorkspaceRoot === workspaceRoot) {
    return globalClient;
  }

  // 異なるワークスペースの場合は古いクライアントを破棄
  if (globalClient) {
    await globalClient.dispose();
  }

  // 新しいクライアントを作成
  globalClient = new DartAnalysisClient({
    workspaceRoots: [workspaceRoot],
  });

  await globalClient.initialize();
  clientWorkspaceRoot = workspaceRoot;

  return globalClient;
}

/**
 * Dart ファイルを解析してシンボル・スニペット・依存関係を抽出
 *
 * @param filePath - ファイルパス（絶対パス推奨）
 * @param content - ファイル内容
 * @param workspaceRoot - ワークスペースルート
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

  try {
    const client = await ensureDartClient(workspaceRoot);
    const payload = await client.analyzeFile(filePath, content);

    const { symbols, snippets } = outlineToSymbols(payload.outline, content);

    // Phase 3: 依存関係を取得
    let dependencies: DependencyRecord[] = [];
    try {
      const dependenciesResult = await client.getLibraryDependencies(filePath);
      dependencies = extractDependencies(filePath, dependenciesResult, workspaceRoot);
    } catch (depError) {
      // 依存関係の取得に失敗しても、シンボル情報は返す
      console.warn(`[analyzeDartSource] Failed to get dependencies for ${filePath}:`, depError);
    }

    return { symbols, snippets, dependencies };
  } catch (error) {
    console.error(`[analyzeDartSource] Failed to analyze ${filePath}:`, error);
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
  if (globalClient) {
    await globalClient.dispose();
    globalClient = null;
    clientWorkspaceRoot = null;
  }
}
