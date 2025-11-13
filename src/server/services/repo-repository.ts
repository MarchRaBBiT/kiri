import { DuckDBClient } from "../../shared/duckdb.js";

/**
 * RepoRecord
 *
 * リポジトリレコードのデータ構造
 */
export interface RepoRecord {
  id: number;
  root: string;
}

/**
 * RepoRepository
 *
 * リポジトリテーブルへのデータアクセスを担当するクラス。
 * DB I/O のみを行い、ビジネスロジックは持たない。
 */
export class RepoRepository {
  constructor(private db: DuckDBClient) {}

  /**
   * 指定されたパス候補のいずれかに一致するリポジトリを検索する。
   *
   * @param candidates - 検索するパス候補の配列
   * @returns 最初に見つかったリポジトリレコード、見つからない場合はnull
   */
  async findByPaths(candidates: string[]): Promise<RepoRecord | null> {
    if (candidates.length === 0) {
      return null;
    }

    const placeholders = candidates.map(() => "?").join(", ");
    const rows = await this.db.all<RepoRecord>(
      `SELECT id, root FROM repo WHERE root IN (${placeholders}) LIMIT 1`,
      candidates
    );
    return rows[0] || null;
  }

  /**
   * 正規化されたパスに一致するリポジトリを検索する（フォールバック、遅い）。
   * NOTE: この処理は O(n) である。normalized_root カラム + インデックスの追加を検討すべき。
   *
   * @param normalized - 正規化されたパス
   * @param normalizeFn - パスを正規化する関数
   * @returns 見つかったリポジトリレコード、見つからない場合はnull
   */
  async findByNormalizedPath(
    normalized: string,
    normalizeFn: (path: string) => string
  ): Promise<RepoRecord | null> {
    const allRepos = await this.db.all<RepoRecord>("SELECT id, root FROM repo");
    return allRepos.find((repo) => normalizeFn(repo.root) === normalized) || null;
  }

  /**
   * リポジトリのrootパスを更新する。
   *
   * @param id - リポジトリID
   * @param newRoot - 新しいrootパス
   */
  async updateRoot(id: number, newRoot: string): Promise<void> {
    await this.db.run("UPDATE repo SET root = ? WHERE id = ?", [newRoot, id]);
  }

  /**
   * repoテーブルが存在するかチェックする。
   *
   * @returns テーブルが存在する場合はtrue
   */
  async tableExists(): Promise<boolean> {
    try {
      await this.db.all("SELECT 1 FROM repo LIMIT 1");
      return true;
    } catch (error) {
      if (error instanceof Error && error.message.includes("Table with name repo")) {
        return false;
      }
      throw error;
    }
  }
}
