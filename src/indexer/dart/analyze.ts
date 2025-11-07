/**
 * Dart Analysis Server を使った Dart ファイル解析のエントリポイント
 */

import path from "node:path";
import type { SymbolRecord, SnippetRecord, DependencyRecord } from "../codeintel.js";
import { DartAnalysisClient } from "./client.js";
import { outlineToSymbols } from "./transform.js";
import { isDartSdkAvailable } from "./sdk.js";
import { extractDependencies } from "./dependencies.js";

// ワークスペース毎のクライアント管理（参照カウント方式）
interface ClientEntry {
  client: DartAnalysisClient;
  refs: number;
  initPromise: Promise<DartAnalysisClient> | null;
}

const clients = new Map<string, ClientEntry>();

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
  let entry = clients.get(workspaceRoot);

  if (!entry) {
    // 新しいクライアントエントリを作成
    const client = new DartAnalysisClient({
      workspaceRoots: [workspaceRoot],
    });

    entry = {
      client,
      refs: 0,
      initPromise: client.initialize().then(() => client),
    };

    clients.set(workspaceRoot, entry);
  }

  // 初期化を待つ
  if (entry.initPromise) {
    await entry.initPromise;
    entry.initPromise = null;
  }

  // 参照カウントを増やす
  entry.refs += 1;

  return entry.client;
}

/**
 * Dart Analysis Client の解放（参照カウント方式）
 *
 * 参照カウントを減少させるが、即座に dispose はしない。
 * クライアントは cleanup() が呼ばれるまで再利用のために保持される。
 *
 * @param workspaceRoot - ワークスペースルート（リポジトリパス）
 */
function releaseClient(workspaceRoot: string): void {
  const entry = clients.get(workspaceRoot);
  if (!entry) {
    return;
  }

  entry.refs -= 1;

  // Note: refs が 0 になっても即座に dispose せず、再利用のために保持する
  // dispose は cleanup() でまとめて実行される
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

    return { symbols, snippets, dependencies };
  } catch (error) {
    console.error(`[analyzeDartSource] Failed to analyze ${absoluteFilePath}:`, error);
    // エラー時は空の結果を返す（Swift/PHP と同様）
    return { symbols: [], snippets: [], dependencies: [] };
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
    // 初期化中なら待つ
    if (entry.initPromise) {
      disposePromises.push(
        entry.initPromise
          .then((client) => client.dispose())
          .catch((error) => {
            console.error(`[cleanup] Failed to dispose client for ${workspaceRoot}:`, error);
          })
      );
    } else {
      disposePromises.push(
        entry.client.dispose().catch((error) => {
          console.error(`[cleanup] Failed to dispose client for ${workspaceRoot}:`, error);
        })
      );
    }
  }

  await Promise.all(disposePromises);
  clients.clear();
}
