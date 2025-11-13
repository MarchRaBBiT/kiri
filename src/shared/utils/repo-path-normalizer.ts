import { realpathSync } from "node:fs";
import { resolve } from "node:path";

/**
 * RepoPathNormalizer
 *
 * リポジトリパスの正規化を担当する純粋なユーティリティクラス。
 * 副作用を持たず、パス変換のみを行う。
 */
export class RepoPathNormalizer {
  /**
   * リポジトリパスを正規化して返す。
   * realpath に失敗した場合は resolve 結果を使用する。
   *
   * @param input - 正規化するリポジトリパス
   * @returns 正規化されたパス
   */
  normalize(input: string): string {
    const abs = resolve(input);
    try {
      return realpathSync.native(abs);
    } catch {
      return abs;
    }
  }

  /**
   * 旧バージョンのパス表現（resolve ベース）との互換性を保つための候補一覧を返す。
   * 配列の先頭は正規化済みパス。
   *
   * @param input - リポジトリパス
   * @returns パス候補の配列（先頭が正規化済みパス）
   */
  getCandidates(input: string): string[] {
    const normalized = this.normalize(input);
    const legacy = resolve(input);
    const candidates = [normalized];
    if (legacy !== normalized) {
      candidates.push(legacy);
    }
    return candidates;
  }
}
