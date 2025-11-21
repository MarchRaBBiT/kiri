# Issue 106 Formal Reference

## Modules

| Module                    | Purpose                                                               |
| ------------------------- | --------------------------------------------------------------------- |
| `PathPenaltyMerge.tla`    | Models YAML/ENV/Profile path penalty merging, invariants、liveness。  |
| `PathPenaltyEncoding.tla` | 別モジュール化したプレフィックスの encode / decode / 正規化ロジック。 |

## 仕様→実装対応

| 仕様要素                       | 実装参照                                              | 説明                                                                                     |
| ------------------------------ | ----------------------------------------------------- | ---------------------------------------------------------------------------------------- |
| `EntryPool` / `Merge`          | `src/server/config-loader.ts`（予定）                 | YAML・環境変数を読み、pathMultipliers 配列を構築するフェーズ。                           |
| `WinningMultiplier`            | `src/server/handlers.ts#getPathMultiplier`            | 最長一致+優先度選択。条件が合わない場合は 1.0 になり `applyFileTypeMultipliers` に反映。 |
| `BuildSortedList`              | `config-loader` 内 `sortByPrefixLength`（実装タスク） | prefix 長で降順にソートし、`PrefixOrder` のような構造を生成。                            |
| `Encode/Decode` (別モジュール) | env 変数パーサ (`process.env.KIRI_PATH_PENALTY_*`)    | `/ ↔ __` 変換や Windows 正規化の契約を定義。                                            |

## TLC プロファイルと戦略

- `PathPenaltyMerge.cfg` … `(MaxSeqLenYaml, MaxSeqLenEnv, MaxSeqLenProfile) = (2,2,2)` の高速検証。CI はこちらを使用。
- `PathPenaltyMerge-max3.cfg` … YAML を 3 まで広げた再検証。状態数が増えるためローカル/ナイトリー専用。
- さらに探索を広げる場合は:
  - **bounded exploration**: `.cfg` に別途 `MaxSeqLen*` を追加し、1段階ずつ増やす。
  - **symmetry reduction**: prefix が実装上同型な場合は `Symmetry` 宣言で削減。
  - **random sampling**: `EntryPool` をサブセットに差し替えた派生 `.cfg` を複数用意し、seed を変えて走らせる。

## Windows / 相対パス

`PathPenaltyEncoding.tla` の `OSNormalize` は「実装が `\` や `.` / `..` を resolve 済みである」ことを前提とする演算子。実装では `path.posix` + 追加ルールを適用し、仕様側は `ASSUME PrefixesAreNormalized` で整合を取る。

## 今後の TODO

- `config-loader` 実装が固まったら `EntryPool` や `PrefixOrder` を自動生成するテストコードを追加。
- env エンコードの完全性は Alloy で検証する予定（構造整合性に向いた題材）。
- 活性・公平性など、より非自明な性質も随時追加する。
