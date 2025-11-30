# オプションA実装後の調査結果 - 2025-11-18

## 背景

q-featureクエリの expected を修正し、plugins実装ファイルを中心に配置しました：

```yaml
# 修正前（runner/types中心）
expected:
  - runner/types.ts (relevance=3)
  - cli/commands/evaluate.ts (relevance=2)
  - plugins/registry.ts (relevance=1)
  - plugins/types.ts (relevance=1)
  - plugins/logger.ts (relevance=1)

# 修正後（plugins実装中心）
expected:
  - plugins/registry.ts (relevance=3)  ← 最重要
  - plugins/types.ts (relevance=2)
  - plugins/logger.ts (relevance=1)
  - plugins/dependencies.ts (relevance=1)
  - cli/commands/evaluate.ts (relevance=1)
```

## 📊 評価結果

### NDCG変化

| 修正   | NDCG      | 変化       | 評価              |
| ------ | --------- | ---------- | ----------------- |
| 修正前 | 0.294     | -          | ❌ 不良           |
| 修正後 | **0.098** | **-66.7%** | ❌❌ **更に悪化** |

### 検索結果の実態

実際の検索順位（Top 5）:

1. `plugins/index.ts` → relevance=0 （expected外）
2. `plugins/types.ts` → relevance=2 ✅
3. `plugins/registry.ts` → relevance=3 ✅
4. `plugins/dependencies.ts` → relevance=1 ✅
5. `dart/analyze.ts` → relevance=0 （無関係）

## 🔍 NDCG計算の検証

### 手動計算（理論値）

**DCG計算**:

```
DCG = 0/log2(2) + 2/log2(3) + 3/log2(4) + 1/log2(5) + 0/log2(6)
    = 0 + 1.262 + 1.500 + 0.431 + 0
    = 3.193
```

**IDCG計算** (理想順序: [3,2,1,1,1]):

```
IDCG = 3/log2(2) + 2/log2(3) + 1/log2(4) + 1/log2(5) + 1/log2(6)
     = 3.000 + 1.262 + 0.500 + 0.431 + 0.387
     = 5.580
```

**NDCG**:

```
NDCG = DCG / IDCG = 3.193 / 5.580 = 0.572 (57.2%)
```

### 実測値との比較

| 項目 | 理論値    | 実測値    | 差分       |
| ---- | --------- | --------- | ---------- |
| DCG  | 3.193     | ?         | -          |
| IDCG | 5.580     | ?         | -          |
| NDCG | **0.572** | **0.098** | **-0.474** |

## 🚨 **重大な不一致**

理論値（0.572）と実測値（0.098）の差は **0.474**（83%の誤差）です。

## 📝 考えられる原因

### 1. IDCGの計算方法の違い

**assay-kit の実装**:

```typescript
// relevanceMap全体から上位k個のgradeを取得
const allGrades = Array.from(relevanceMap.values()).sort((a, b) => b - a);
const idealGrades = allGrades.slice(0, kInt);
const idcgValue = dcg(idealGrades, kInt);
```

**我々の仮定**:

- relevanceMapには5個のアイテム（3,2,1,1,1）が含まれる
- IDCGは[3,2,1,1,1]で計算される

**実際の可能性**:

- もしrelevanceMapに**更に多くのアイテム**が含まれている場合、IDCGが大きくなる
- 例：relevanceMapに10個のアイテムがあり、上位5個が[3,2,1,1,1]なら、IDCGは同じ
- しかし、もし他のクエリのrelevanceが混入していたら？

### 2. limit設定の不一致

**確認済み**:

- kiri-variants.ts: `limit: 5` (default variant)
- kiri-adapter.ts: `const k = this.config.limit` ✅

**可能性**:

- context_bundleが実際には5個より多くの結果を返している？
- evaluateRetrieval()に渡す `items` 配列が5個を超えている？

### 3. relevance gradesのマッピング失敗

**確認済み**:

- kiri-adapter.ts は正しく relevanceGrades Map を構築している ✅
- query.metadata.expected からpathとrelevanceを正しく抽出 ✅

**未確認**:

- 実際の実行時に relevanceGrades.size がいくつか？
- evaluateRetrieval() に渡される relevanceGrades の内容は？

## 🔬 次の調査ステップ

### 優先度1: デバッグログ追加

kiri-adapter.tsに一時的なデバッグログを追加：

```typescript
// After building relevanceGrades
if (query.id === "q-feature") {
  console.error("=== DEBUG: q-feature ===");
  console.error("relevanceGrades.size:", relevanceGrades.size);
  console.error("relevanceGrades:", Array.from(relevanceGrades.entries()));
  console.error("retrievedPaths.length:", retrievedPaths.length);
  console.error("retrievedPaths:", retrievedPaths.slice(0, 5));
  console.error("k:", k);
}
```

### 優先度2: assay-kit NDCGの単体テスト

直接ndcg()関数をテスト：

```typescript
import { ndcg } from "assay-kit";

const retrievedIds = [
  "external/assay-kit/packages/assay-kit/src/plugins/index.ts",
  "external/assay-kit/packages/assay-kit/src/plugins/types.ts",
  "external/assay-kit/packages/assay-kit/src/plugins/registry.ts",
  "external/assay-kit/packages/assay-kit/src/plugins/dependencies.ts",
  "src/indexer/dart/analyze.ts",
];

const relevanceMap = new Map([
  ["external/assay-kit/packages/assay-kit/src/plugins/registry.ts", 3],
  ["external/assay-kit/packages/assay-kit/src/plugins/types.ts", 2],
  ["external/assay-kit/packages/assay-kit/src/plugins/logger.ts", 1],
  ["external/assay-kit/packages/assay-kit/src/plugins/dependencies.ts", 1],
  ["external/assay-kit/packages/assay-kit/src/cli/commands/evaluate.ts", 1],
]);

const result = ndcg(retrievedIds, relevanceMap, 5);
console.log("NDCG:", result); // 期待値: 0.572
```

### 優先度3: 実行ログ確認

実際の評価実行時のJSON出力を詳細確認：

```bash
cat var/assay/comparison-default-vs-feature-*.json | \
  jq '.left.queries[] | select(.queryId == "q-feature")'
```

## 💡 暫定結論

### データセット修正の評価

**技術的には正しい**:

- plugins実装ファイルを中心にしたexpectedは、クエリ意図と一致
- relevance=3（registry.ts）、relevance=2（types.ts）の配置は妥当

**しかし結果は悪化**:

- NDCG: 0.294 → 0.098 （-66.7%）
- 理論値（0.572）と実測値（0.098）の乖離が大きすぎる

### 次のアクション選択肢

#### A. デバッグ継続（推奨）

- 一時的なデバッグログを追加
- 実行時の relevanceGrades とretrievedPaths を確認
- assay-kit の ndcg() を単独でテスト
- **時間**: 30分-1時間
- **リスク**: 低（調査のみ）

#### B. データセットをロールバック

- q-featureを以前の状態（runner/types中心）に戻す
- NDCG 0.294 を許容する
- **時間**: 5分
- **リスク**: 中（根本原因不明のまま）

#### C. q-featureクエリを完全に再設計

- クエリテキストとexpectedを両方変更
- 新しいカテゴリとして扱う
- **時間**: 2-3時間（再評価含む）
- **リスク**: 高（他クエリとの一貫性）

## 📌 ステータス

- ✅ オプションA実装完了
- ✅ 再評価実行完了
- ✅ 理論値計算完了
- ❌ 実測値との乖離調査**継続中**
- ⏳ ユーザー判断待ち

## 📂 関連ファイル

- データセット: `datasets/kiri-ab.yaml` (q-feature: 行36-58)
- アダプター: `scripts/assay/kiri-adapter.ts` (relevance処理: 行187-227)
- 評価結果: `var/assay/profile-matrix-2025-11-18.json`
- デバッグスクリプト: `scripts/test-ndcg-debug.ts`
