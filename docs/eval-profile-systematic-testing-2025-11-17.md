# ブーストプロファイル系統的テスト評価結果

**日付**: 2025-11-17  
**担当**: Issue #77 実装  
**関連Issue**: [#77](https://github.com/CAPHTECH/kiri/issues/77)  
**ベースライン**: `default` プロファイル  
**テスト対象**: 7つの新規プロファイル  
**データセット**: `datasets/kiri-ab.yaml` (24クエリ)

## エグゼクティブサマリー

全7つのブーストプロファイル（feature, bugfix, debug, api, editor, testfail, typeerror）を系統的にテストしました。結果、**いずれのプロファイルもbaselineである`default`プロファイルよりF1スコアが低下**しました（-0.09～-0.10）。

### 主要な発見

1. **Recall改善 vs Precision低下のトレードオフ**
   - 全プロファイルでRecallが+8.3%～+12.5%改善
   - 一方、Precisionが-8.3%～-9.2%低下
   - 結果として F1スコアは悪化

2. **統計的有意差なし**
   - 全プロファイルで統計的に有意な差は検出されず
   - サンプルサイズ（24クエリ）が小さいことが一因

3. **最良プロファイル**
   - `testfail`と`typeerror`が F1=0.222 で最良
   - `default` (F1=0.310) には及ばず

## 性能マトリクス

| Profile                | P@5            | R@5            | F1@5           | Latency (ms) | vs default | 統計的有意性 |
| ---------------------- | -------------- | -------------- | -------------- | ------------ | ---------- | ------------ |
| **default** (baseline) | 0.217          | 0.542          | 0.310          | 523.1        | -          | -            |
| testfail               | 0.133 (-0.083) | 0.667 (+0.125) | 0.222 (-0.087) | 544.0        | Δ          | ~            |
| typeerror              | 0.133 (-0.083) | 0.667 (+0.125) | 0.222 (-0.087) | 533.8        | Δ          | ~            |
| bugfix                 | 0.129 (-0.088) | 0.646 (+0.104) | 0.215 (-0.094) | 539.8        | Δ          | ~            |
| debug                  | 0.129 (-0.088) | 0.646 (+0.104) | 0.215 (-0.094) | 560.9        | Δ          | ~            |
| api                    | 0.129 (-0.088) | 0.646 (+0.104) | 0.215 (-0.094) | 554.2        | Δ          | ~            |
| editor                 | 0.129 (-0.088) | 0.646 (+0.104) | 0.215 (-0.094) | 538.9        | Δ          | ~            |
| feature                | 0.125 (-0.092) | 0.625 (+0.083) | 0.208 (-0.101) | 561.6        | Δ          | ~            |

## 詳細分析

### 1. Precision低下の原因

新規プロファイルは以下の設定を使用：

- `impl` boost: 1.3～1.5 (defaultは1.3)
- `doc` penalty: 0.5 (defaultと同じ)
- `config` penalty: 0.05 (defaultと同じ)

**仮説**:

- `impl` boostが強すぎる（1.4～1.5）ことで、関連性の低い実装ファイルも上位にランクされている
- `limit=10` (defaultは5) により、より多くの結果が返されるが、関連性の低いものが混入

### 2. Recall改善の要因

`limit=10`により、より多くのファイルが返されるため、正解ファイルが含まれる確率が上昇しました。

### 3. プロファイル間の差異

- `testfail` / `typeerror`: `tests/` や `types/` へのpath multiplierが功を奏した可能性
- `feature` / `bugfix` / `debug` / `api` / `editor`: ほぼ同じ性能（設定が類似しているため）

### 4. レイテンシ

全プロファイルで約540msと、`default` (523ms) とほぼ同等。`limit=10`の影響は軽微。

## 推奨事項

### 即時アクション

1. **プロファイル設定の見直し**
   - `impl` boostを 1.2～1.3 に引き下げ
   - または`doc` penaltyを 0.6～0.7 に緩和
   - 再テストして F1 改善を確認

2. **limitパラメータの最適化**
   - `limit=5` vs `limit=10` vs `limit=7` で A/B テスト
   - Precision/Recall のバランスを調整

### 中期アクション

1. **クエリカテゴリ別の分析**
   - 24クエリを「bugfix」「feature」「testfail」などのカテゴリに分類
   - カテゴリごとに最適プロファイルを特定

2. **統計的検出力の向上**
   - データセットを50～100クエリに拡張
   - より多様なクエリタイプを追加

3. **ハイブリッドアプローチ**
   - クエリの意図を自動分類し、適切なプロファイルを動的に選択
   - 例: "test failed" → `testfail` プロファイル

### 長期アクション

1. **機械学習ベースのブースト**
   - クエリとファイルの関連性を学習
   - 手動設定からデータ駆動の最適化へ移行

2. **ユーザーフィードバックの収集**
   - 実際の使用状況でどのプロファイルが好まれるか
   - Implicit feedback (クリック率など) の活用

## 結論

**現時点では`default`プロファイルが最良**です。新規プロファイルは Recall 改善を示しましたが、Precision の大幅な低下により F1スコアは悪化しました。

今後は：

1. プロファイル設定の微調整（impl boost削減）
2. limitパラメータの最適化
3. より大規模なデータセットでの再評価

を行うことで、`default`を上回るプロファイルの開発を目指します。

## 実行環境

- **KIRI バージョン**: 0.10.0
- **データセット**: kiri-ab (v2025-11-14), 24クエリ
- **リポジトリ**: kiri (409ファイル)
- **統計手法**: Mann-Whitney U test (α=0.05, Holm補正)
- **実行時間**: 約6分（7プロファイル × 24クエリ × 2回実行）

## 参考資料

- マトリクスレポート: `var/assay/profile-matrix-2025-11-17.md`
- 生データ: `var/assay/comparison-default-vs-*.json`
- 関連Issue: [#77](https://github.com/CAPHTECH/kiri/issues/77)
- プロファイル定義: `src/server/boost-profiles.ts`
- Variant定義: `scripts/assay/kiri-variants.ts`

## 付録: 実装詳細

### 新規追加ファイル

- `scripts/assay/run-profile-matrix.ts`: バッチ実行スクリプト
- `scripts/assay/report-matrix.ts`: マトリクスレポート生成

### 変更ファイル

- `scripts/assay/kiri-variants.ts`: 7プロファイル追加
- `src/server/boost-profiles.ts`: `BoostProfileName`型と`BOOST_PROFILES`に7プロファイル追加
- `src/server/rpc.ts`: エラーメッセージを動的生成に変更
- `package.json`: `assay:profile-matrix`, `assay:report-matrix` コマンド追加

### package.jsonコマンド

```bash
# 全プロファイルのマトリクステスト
pnpm run assay:profile-matrix

# 特定プロファイルをスキップ
pnpm run assay:profile-matrix -- --skip balanced,docs

# マトリクスレポート生成
pnpm run assay:report-matrix var/assay/profile-matrix-YYYY-MM-DD.json
```
