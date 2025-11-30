/**
 * Language analyzer core types
 *
 * このファイルは言語アナライザーシステムの中核となる型定義を提供します。
 * Alloyで検証済みのPlan A (Central Registry) 設計に基づいています。
 */

/**
 * シンボル情報を表すレコード
 * クラス、関数、メソッドなどのコード要素を表現します
 */
export interface SymbolRecord {
  /** 1から始まる連番ID */
  symbolId: number;
  /** シンボル名 */
  name: string;
  /** シンボルの種類 (function, class, method, interface, enum等) */
  kind: string;
  /** 開始行番号 (1-based) */
  rangeStartLine: number;
  /** 終了行番号 (1-based) */
  rangeEndLine: number;
  /** シグネチャ (最大200文字) */
  signature: string | null;
  /** ドキュメントコメント */
  doc: string | null;
}

/**
 * スニペット情報を表すレコード
 * コードの行範囲を表現します
 */
export interface SnippetRecord {
  /** 開始行番号 (1-based) */
  startLine: number;
  /** 終了行番号 (1-based) */
  endLine: number;
  /** 関連するシンボルID (nullの場合はファイル全体) */
  symbolId: number | null;
}

/**
 * 依存関係を表すレコード
 * import/requireなどの依存関係を表現します
 */
export interface DependencyRecord {
  /** 依存先の種類 */
  dstKind: "path" | "package";
  /** 依存先のパスまたはパッケージ名 */
  dst: string;
  /** 関係の種類 (import, require等) */
  rel: string;
}

/**
 * 解析コンテキスト
 * アナライザーに渡される入力情報
 */
export interface AnalysisContext {
  /** リポジトリルートからの相対パス */
  pathInRepo: string;
  /** ファイルの内容 */
  content: string;
  /** インデックス済みファイルのセット (相対パス解決用) */
  fileSet: Set<string>;
  /** ワークスペースルート (LSPベースのアナライザー用、絶対パス) */
  workspaceRoot?: string;
}

/**
 * 解析結果
 * アナライザーが返す出力情報
 */
export interface AnalysisResult {
  /** 抽出されたシンボル一覧 */
  symbols: SymbolRecord[];
  /** 生成されたスニペット一覧 */
  snippets: SnippetRecord[];
  /** 検出された依存関係一覧 */
  dependencies: DependencyRecord[];
  /** 解析ステータス (エラー時に設定) */
  status?: "success" | "error" | "sdk_unavailable";
  /** エラーメッセージ (エラー時に設定) */
  error?: string;
}

/**
 * 言語アナライザーインターフェース
 *
 * 実装要件:
 * 1. ステートレスまたは内部で状態を管理 (スレッドセーフ)
 * 2. パースエラー時は空の結果を返す (例外をスローしない)
 * 3. 並行解析リクエストをサポート
 *
 * Alloyモデルの `Analyzer` atomに対応:
 * - language: 言語識別子
 * - analyze: 解析メソッド
 * - dispose: リソース解放メソッド (オプション)
 */
export interface LanguageAnalyzer {
  /** 言語識別子 (例: "TypeScript", "Swift") */
  readonly language: string;

  /**
   * ソースコードを解析してシンボル、スニペット、依存関係を抽出
   *
   * @param context - 解析コンテキスト
   * @returns 解析結果 (エラー時も例外をスローせず空の結果を返す)
   */
  analyze(context: AnalysisContext): Promise<AnalysisResult>;

  /**
   * アナライザーが保持するリソースを解放
   * レジストリからの削除時に呼び出される
   */
  dispose?(): Promise<void>;
}

/**
 * 空の解析結果を生成するヘルパー
 */
export function emptyResult(): AnalysisResult {
  return { symbols: [], snippets: [], dependencies: [] };
}
