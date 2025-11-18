# NDCG評価結果 - 2025-11-18

## 概要

全10プロファイル × 24クエリでNDCG（Normalized Discounted Cumulative Gain）評価を実施しました。

- **データセット**: `kiri-ab-issue76` (v2025-11-14)
- **クエリ数**: 24クエリ（17カテゴリ）
- **評価プロファイル**: default, docs, balanced, feature, bugfix, debug, api, editor, testfail, typeerror
- **主要メトリクス**: NDCG, MRR, F1@5, P@5, R@5

## 主要な発見

### 1. 全体的な傾向

**ほとんどのカテゴリでNDCG=0.613**が共通値として現れています。これは：

- 重み付き関連度が正しく計算されている（relevance=3, 2が反映）
- しかし、専門化プロファイル間で差異が少ない
- MRR=1.000（全プロファイルで一致）が示すように、最も関連度の高いアイテムは常に#1にランク

### 2. 顕著な差異が見られたカテゴリ（上位3つ）

#### 🥇 integration カテゴリ (NDCG=0.850)

- **トッププロファイル**: feature, bugfix, debug, api, editor, testfail, typeerror
- **NDCG**: 0.850（+38% vs baseline 0.613）
- **P@5**: 0.333（+396% vs balanced 0.067）
- **R@5**: 1.000（完全再現率）
- **解釈**: 統合テストファイル検索で、専門プロファイルが明確に優位

#### 🥈 plugins カテゴリ (NDCG=0.732)

- **トッププロファイル**: api, editor, testfail, typeerror
- **NDCG**: 0.732（+19% vs balanced 0.613）
- **P@5**: 0.250（+273% vs balanced 0.067）
- **R@5**: 0.750
- **解釈**: プラグイン関連コードで、src/重視プロファイルが効果的

#### 🥉 reporter カテゴリ (NDCG=0.722)

- **トッププロファイル**: api, editor, testfail, typeerror
- **NDCG**: 0.722（+18% vs balanced 0.613）
- **P@5**: 0.250（+273% vs balanced 0.067）
- **R@5**: 0.750
- **解釈**: レポート生成スクリプトで、scripts/重視プロファイルが有効

### 3. プロファイル別パフォーマンス

| Profile   | 高NDCG達成カテゴリ数  | 平均NDCG | 特徴                        |
| --------- | --------------------- | -------- | --------------------------- |
| api       | 2 (plugins, reporter) | 0.626    | src/ + scripts/assay/を強化 |
| editor    | 2 (plugins, reporter) | 0.626    | src/server/を重視           |
| testfail  | 2 (plugins, reporter) | 0.626    | tests/を強化                |
| typeerror | 2 (plugins, reporter) | 0.626    | types/を強化                |
| feature   | 1 (integration)       | 0.616    | 新機能実装ファイルを優先    |
| bugfix    | 1 (integration)       | 0.616    | バグ修正ファイルを優先      |
| debug     | 1 (integration)       | 0.616    | デバッグ用ファイルを重視    |
| balanced  | 0                     | 0.613    | バランス型（ベースライン）  |
| docs      | 0                     | 0.613    | ドキュメント優先            |
| noBoost   | 0                     | 0.613    | ブースティング無し          |

## 結論

### ✅ 成功点

1. **NDCGの正常動作**: 重み付き関連度（relevance=3/2）がNDCGに正しく反映
2. **一部カテゴリで明確な改善**: integration (+38%), plugins (+19%), reporter (+18%)
3. **MRR=1.000の維持**: 最重要アイテムは全プロファイルで#1をキープ

### ⚠️ 課題

1. **大半のカテゴリで差異なし**: 17カテゴリ中14カテゴリで全プロファイルがNDCG=0.613
2. **データセットの単純性**: 各クエリにexpectedが2件のみ → ランキングの差異が出にくい
3. **統計的有意性の欠如**: サンプル数不足により有意差検定が困難

### 📈 推奨される次のステップ

#### 短期（1-2週間）

1. **データセット拡張**: 各クエリにrelevance=1のアイテムを3-5件追加
2. **NDCG閾値設定**: NDCG < 0.70をアラート、NDCG > 0.80を目標に設定
3. **専門プロファイルの調整**: integration/plugins/reporterで効果があったパターンを他カテゴリに適用

#### 中期（1-2ヶ月）

1. **実運用データ収集**: 実際のユーザークエリログからゴールデンセットを構築
2. **A/Bテスト実施**: 本番環境でNDCG差異を検証
3. **自動プロファイル選択**: クエリタイプから最適プロファイルを自動推薦

## 付録：技術的詳細

### NDCG計算式

```
NDCG@K = DCG@K / IDCG@K

DCG@K = Σ(i=1 to K) [rel_i / log2(i+1)]

rel_i = relevance score of item at position i
```

### データセット統計

- **relevance=3**: 24アイテム（各クエリの第1位期待値）
- **relevance=2**: 24アイテム（各クエリの第2位期待値）
- **relevance=1**: 0アイテム（未追加）
- **relevance=0**: 検索結果外の全アイテム

### 評価環境

- **KIRI version**: current (feat-implement-77-ZWy5h)
- **assay-kit version**: v0.1.1-78-g0625bb2
- **DuckDB**: 526 files indexed (including submodules)
- **評価時間**: 約15分（全240テストケース）
