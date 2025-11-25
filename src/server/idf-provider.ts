/**
 * IDF Provider
 *
 * IDF（逆文書頻度）を計算するプロバイダー。
 * 高頻度語の重みを自動的に減衰させ、検索精度を向上させる。
 *
 * @see Issue #48: Improve context_bundle stop word coverage and configurability
 * @see Phase 2: IDF-based keyword weighting
 */

import type { DuckDBClient } from "../shared/duckdb.js";

import { type IdfProvider, StopWordsService } from "./stop-words.js";

// ============================================================
// 定数
// ============================================================

/**
 * IDFキャッシュの最大サイズ
 * メモリ消費を抑えつつ、典型的なセッションでのキャッシュヒット率を確保
 */
const MAX_CACHE_SIZE = 10000;

/**
 * BM25 IDF計算のスムージングパラメータ
 * df = 0 の場合のゼロ除算を防ぎ、高頻度語へのペナルティを安定させる
 */
const SMOOTHING_FACTOR = 0.5;

// ============================================================
// DuckDbIdfProvider クラス
// ============================================================

/**
 * DuckDB ベースの IDF プロバイダー
 *
 * 遅延計算とLRUキャッシュを使用し、クエリ時のパフォーマンスを最適化。
 * BM25スタイルのIDF計算式を使用:
 *   idf = log((N - df + 0.5) / (df + 0.5) + 1)
 *
 * 正規化された重み(0.0-1.0)を返し、StopWordsService との統合を容易にする。
 */
export class DuckDbIdfProvider implements IdfProvider {
  private readonly cache = new Map<string, number>();
  private totalDocs: number | null = null;
  private maxIdf: number | null = null;

  /**
   * @param db - DuckDBクライアント
   * @param repoId - リポジトリID
   */
  constructor(
    private readonly db: DuckDBClient,
    private readonly repoId: number
  ) {}

  /**
   * 総ドキュメント数を取得（キャッシュ付き）
   *
   * @returns 総ドキュメント数（最小1）
   */
  async getDocumentCount(): Promise<number> {
    if (this.totalDocs !== null) {
      return this.totalDocs;
    }

    const result = await this.db.all<{ count: number }>(
      `SELECT COUNT(*) as count FROM file WHERE repo_id = ?`,
      [this.repoId]
    );

    // 最小1を保証（ゼロ除算防止）
    this.totalDocs = Math.max(1, result[0]?.count ?? 1);

    // maxIdf も同時に計算（N が確定したため）
    this.maxIdf = this.calculateMaxIdf(this.totalDocs);

    return this.totalDocs;
  }

  /**
   * 特定の語の文書頻度（DF）を取得
   *
   * @param term - 検索語（正規化済み）
   * @returns 語を含むドキュメント数
   */
  async getDocumentFrequency(term: string): Promise<number> {
    const result = await this.db.all<{ count: number }>(
      `SELECT COUNT(DISTINCT f.path) as count
       FROM file f
       JOIN blob b ON b.hash = f.blob_hash
       WHERE f.repo_id = ? AND b.content ILIKE '%' || ? || '%'`,
      [this.repoId, term]
    );

    return result[0]?.count ?? 0;
  }

  /**
   * 同期的にIDF重みを取得（キャッシュヒット時のみ有効値）
   *
   * キャッシュミス時は1.0（ニュートラル重み）を返す。
   * 正確なIDF値が必要な場合は computeIdf() を使用すること。
   *
   * @param word - 対象単語
   * @returns 正規化された重み（0.0-1.0）
   */
  getIdf(word: string): number {
    const normalized = StopWordsService.normalizeToken(word);
    if (!normalized) {
      return 0;
    }

    const cached = this.cache.get(normalized);
    if (cached !== undefined) {
      return cached;
    }

    // キャッシュミス時はニュートラル重みを返す
    // 正確な値は computeIdf() で非同期計算
    return 1.0;
  }

  /**
   * 非同期でIDF重みを計算（DB問い合わせを含む）
   *
   * BM25スタイルのIDF計算式を使用:
   *   idf = log((N - df + 0.5) / (df + 0.5) + 1)
   *
   * @param word - 対象単語
   * @returns 正規化された重み（0.0-1.0）
   */
  async computeIdf(word: string): Promise<number> {
    const normalized = StopWordsService.normalizeToken(word);
    if (!normalized) {
      return 0;
    }

    // キャッシュチェック
    const cached = this.cache.get(normalized);
    if (cached !== undefined) {
      return cached;
    }

    // 総ドキュメント数を取得
    const N = await this.getDocumentCount();

    // 文書頻度を取得
    const df = await this.getDocumentFrequency(normalized);

    // BM25スタイルIDF計算
    const idf = Math.log((N - df + SMOOTHING_FACTOR) / (df + SMOOTHING_FACTOR) + 1);

    // 0-1 に正規化
    const maxIdf = this.maxIdf ?? this.calculateMaxIdf(N);
    const weight = Math.min(1, Math.max(0, idf / maxIdf));

    // キャッシュに保存（LRU eviction）
    this.addToCache(normalized, weight);

    return weight;
  }

  /**
   * 複数の単語のIDF重みをバッチ計算
   *
   * 複数の単語を一度に計算することで、DB問い合わせのオーバーヘッドを削減。
   *
   * @param words - 対象単語の配列
   * @returns 単語→重みのマップ
   */
  async computeIdfBatch(words: string[]): Promise<Map<string, number>> {
    const result = new Map<string, number>();

    // 正規化と重複除去
    const uniqueTerms = new Set<string>();
    for (const word of words) {
      const normalized = StopWordsService.normalizeToken(word);
      if (normalized) {
        uniqueTerms.add(normalized);
      }
    }

    // キャッシュ済みの語を先に処理
    const uncachedTerms: string[] = [];
    for (const term of uniqueTerms) {
      const cached = this.cache.get(term);
      if (cached !== undefined) {
        result.set(term, cached);
      } else {
        uncachedTerms.push(term);
      }
    }

    // 未キャッシュの語を個別計算
    // TODO: 将来的にはバッチクエリで最適化可能
    for (const term of uncachedTerms) {
      const weight = await this.computeIdf(term);
      result.set(term, weight);
    }

    return result;
  }

  /**
   * キャッシュをクリア
   */
  clearCache(): void {
    this.cache.clear();
    this.totalDocs = null;
    this.maxIdf = null;
  }

  /**
   * キャッシュサイズを取得（デバッグ用）
   */
  get cacheSize(): number {
    return this.cache.size;
  }

  // ============================================================
  // プライベートメソッド
  // ============================================================

  /**
   * 理論上の最大IDF値を計算
   *
   * df = 0 の場合（未出現語）のIDF値を計算。
   * この値で正規化することで、すべての重みが0-1の範囲に収まる。
   *
   * @param N - 総ドキュメント数
   * @returns 最大IDF値
   */
  private calculateMaxIdf(N: number): number {
    // df = 0 の場合: log((N + 0.5) / 0.5 + 1)
    return Math.log((N + SMOOTHING_FACTOR) / SMOOTHING_FACTOR + 1);
  }

  /**
   * キャッシュに追加（簡易LRU）
   *
   * キャッシュサイズが上限を超えた場合、最も古いエントリを削除。
   *
   * @param term - 正規化された語
   * @param weight - IDF重み
   */
  private addToCache(term: string, weight: number): void {
    // 簡易LRU: Map の挿入順序を利用
    if (this.cache.size >= MAX_CACHE_SIZE) {
      // 最初のエントリを削除
      const firstKey = this.cache.keys().next().value;
      if (firstKey !== undefined) {
        this.cache.delete(firstKey);
      }
    }

    this.cache.set(term, weight);
  }
}

// ============================================================
// ファクトリー関数
// ============================================================

/**
 * IdfProvider を作成
 *
 * @param db - DuckDBクライアント
 * @param repoId - リポジトリID
 * @returns IdfProvider インスタンス
 */
export function createIdfProvider(db: DuckDBClient, repoId: number): DuckDbIdfProvider {
  return new DuckDbIdfProvider(db, repoId);
}
