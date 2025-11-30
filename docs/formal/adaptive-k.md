# Adaptive K (Issue 78) 形式仕様と検証

## 1. 形式化候補一覧

- 適応Kマッピング関数 `getAdaptiveK` / High / TLA+ / カテゴリ→K決定の安全性と境界値保証。
- 未知カテゴリフォールバック / Medium / TLA+ / デフォルト挙動を明示し漏れを防ぐ。
- K値の外部上書き（環境変数・設定）/ Low / Alloy（未着手）/ 設定組合せで既定セットを壊すリスク検知。

## 2. 選定対象と不変条件

- 対象: 適応Kマッピング + 未知カテゴリフォールバック + 許容集合/範囲チェック
  - InvAllowedSet: k ∈ ALLOWED_SET
  - InvRange: K_MIN ≤ k ≤ K_MAX
  - InvBugfixPrecision: bugfix → K_BUGFIX
  - InvIntegrationPrecision: integration → K_INTEGRATION
  - InvTestfailRecall: testfail → K_TESTFAIL
  - InvPerformanceRecall: performance → K_PERFORMANCE
  - InvGenericBalance: その他 → K_DEFAULT（未知カテゴリ含む）

## 3. 形式仕様（TLA+）

- 本体: `docs/formal/AdaptiveK.tla`
- CFG: 本番 `docs/formal/AdaptiveK-prod.cfg`（既定セット {5,10,20}）、実験例 `docs/formal/AdaptiveK-exp.cfg`（既定セット {5,10,15,20} かつデフォルト15）。
- 抜粋:

```tla
CONSTANTS CATEGORIES, ALLOWED_SET, K_MIN, K_MAX,
          K_BUGFIX, K_INTEGRATION, K_TESTFAIL, K_PERFORMANCE, K_DEFAULT
AdaptiveK(cat) ==
  IF cat = "bugfix" THEN K_BUGFIX
  ELSE IF cat = "integration" THEN K_INTEGRATION
  ELSE IF cat = "testfail" THEN K_TESTFAIL
  ELSE IF cat = "performance" THEN K_PERFORMANCE
  ELSE K_DEFAULT
```

- 不変条件: `InvAllowedSet`, `InvRange`, 各カテゴリのK固定、汎用フォールバックを `Spec == Init /\ [][Next]_<<queryCat, k>>` 上で証明。

### 設定・フラグ（実装方針メモ）

- フラグ: `KIRI_ADAPTIVE_K_ENABLED`（env）、falseで常に `kWhenDisabled` を返す。
- 許容集合: `KIRI_ADAPTIVE_K_ALLOWED_SET`（カンマ区切り）。
- 範囲: `KIRI_ADAPTIVE_K_MIN` / `KIRI_ADAPTIVE_K_MAX`。
- カテゴリ別K: `KIRI_ADAPTIVE_K_BUGFIX` / `KIRI_ADAPTIVE_K_INTEGRATION` / `KIRI_ADAPTIVE_K_TESTFAIL` / `KIRI_ADAPTIVE_K_PERFORMANCE`。
- デフォルト: `KIRI_ADAPTIVE_K_DEFAULT`、フラグOFF固定値 `KIRI_ADAPTIVE_K_DISABLED_VALUE`。

## 4. 検証結果

- 本番プロファイル: `java -cp /tmp/tla2tools.jar tlc2.TLC -deadlock -config docs/formal/AdaptiveK-prod.cfg docs/formal/AdaptiveK.tla`
  - 42 states / 6 distinct / 深さ1、デッドロックなし、全不変成立。
- 実験プロファイル: `java -cp /tmp/tla2tools.jar tlc2.TLC -deadlock -config docs/formal/AdaptiveK-exp.cfg docs/formal/AdaptiveK.tla`
  - 42 states / 6 distinct / 深さ1、デッドロックなし、全不変成立。
- CI 推奨: `pnpm run check:adaptive-k`（設定読み込み＋バリデーションを実行）。

## 5. 仕様 → 実装対応表

| 仕様要素                          | 実装箇所（想定）                          | 説明                                              |
| --------------------------------- | ----------------------------------------- | ------------------------------------------------- |
| `AdaptiveK(cat)`                  | `src/shared/adaptive-k.ts:getAdaptiveK`   | カテゴリ→Kの決定ロジック。                        |
| `CATEGORIES`                      | `src/types/query.ts` のカテゴリ型ユニオン | クエリメタデータ定義と同期必須。                  |
| `ALLOWED_SET` / `K_MIN` / `K_MAX` | 設定読み込み＋バリデーション層            | 許容K集合と範囲を起動時チェック。                 |
| `K_*` 定数                        | 設定または定数マップ                      | 各カテゴリの既定K値。未知カテゴリは `K_DEFAULT`。 |
| `kWhenDisabled` (実装)            | 設定読み込み層                            | フラグOFF時に返す固定K。                          |
| `InvAllowedSet` / `InvRange`      | バリデーション＋テレメトリ                | 実行時に集合・範囲を外れたら即検知。              |
| `Init/Next`                       | リクエストごとに K を再計算する検索前処理 | 毎回最新カテゴリで決定。                          |

## 6. 残課題・リスク

- カテゴリ分類器の誤分類は未形式化。誤分類時の影響を評価・監視する必要あり。
- 設定や環境変数で ALLOWED*SET / K*\* を変える場合の整合性（設定優先度・衝突）は未検証。Alloy/TLA+で別途モデル化予定。
- カテゴリ追加時に `CATEGORIES` と型ユニオン・設定がズレるリスク。単一ソース生成かCIチェックを推奨。

## 7. 仮定と不明点

- 仮定: 未知カテゴリは常に `K_DEFAULT`（本番デフォルト10）へフォールバックする。
- 仮定: ALLOWED_SET は起動時に設定で確定し、実行時に動的変更しない。
- 不明点: ALLOWED_SET の上限・下限を決める運用上の根拠（レイテンシ・UI枠）が未記載。決定後に K_MIN/K_MAX を更新し再検証が必要。
