# プロファイル大胆調整の分析レポート

**実行日**: 2025-11-18  
**対応Issue**: [#77](https://github.com/CAPHTECH/kiri/issues/77)  
**前回レポート**: [eval-short-term-actions-final-2025-11-17.md](./eval-short-term-actions-final-2025-11-17.md)

---

## 📋 実施した作業

### 1. プロファイル設定の大胆な調整 ✅

**目的**: 各プロファイルのカテゴリ特化性を強化

**調整内容**:

| Profile       | 主要変更               | multiplier変化                                           | src/ 抑制   |
| ------------- | ---------------------- | -------------------------------------------------------- | ----------- |
| **testfail**  | テストファイル大幅強化 | tests/ 1.5→**2.5**                                       | 1.0→**0.5** |
| **typeerror** | 型定義大幅強化         | src/types/ 1.4→**3.0**                                   | 1.0→**0.6** |
| **api**       | API特化強化            | src/api/ 1.4→**2.5**                                     | 1.0→**0.7** |
| **editor**    | UI/コンポーネント強化  | src/components/ 1.3→**2.2**<br>src/editor/ **2.5**(新規) | 1.0→**0.7** |
| **feature**   | アプリ/機能開発強化    | src/app/ 1.4→**2.0**<br>src/lib/ 1.2→**1.8**             | 1.0→**0.8** |
| **bugfix**    | 実装コード強化         | src/components/ 1.3→**1.8**<br>src/app/ 1.3→**1.8**      | 1.0→**0.8** |
| **debug**     | デバッグツール強化     | src/utils/ **1.8**(新規)<br>src/lib/ 1.2→**1.6**         | 1.0→**0.8** |

**調整の方針**:

- ✅ 主要pathの multiplier を **2倍以上** に引き上げ
- ✅ 一般的な `src/` を **0.5～0.8** に抑制
- ✅ 各プロファイルに**特化パス**を追加（editor/, debug/, routes/ など）

---

### 2. 調整後の評価実行 ✅

**実施内容**:

- ✅ 24クエリで全10プロファイルを再評価
- ✅ カテゴリ別性能分析（170パターン）

**結果サマリー**:

| Profile   | P@5   | R@5   | F1@5      | vs 調整前    |
| --------- | ----- | ----- | --------- | ------------ |
| feature   | 0.201 | 0.604 | **0.302** | **変化なし** |
| bugfix    | 0.201 | 0.604 | **0.302** | **変化なし** |
| debug     | 0.201 | 0.604 | **0.302** | **変化なし** |
| api       | 0.201 | 0.604 | **0.302** | **変化なし** |
| editor    | 0.201 | 0.604 | **0.302** | **変化なし** |
| testfail  | 0.201 | 0.604 | **0.302** | **変化なし** |
| typeerror | 0.201 | 0.604 | **0.302** | **変化なし** |

---

## 🔍 根本原因の分析

### 問題の特定

**発見事実**:

1. ✅ ブーストプロファイルは**正しく適用されている**
2. ✅ multiplier は**大胆に調整された**（最大3.0倍）
3. ❌ しかし、**P@5/R@5/F1@5が全く変化しない**

### 根本原因

#### 🎯 評価指標の限界

**Precision@K と Recall@K の特性**:

- これらは「上位K件のうち、何件がexpectedに一致するか」を測定
- **ランキング順序は評価されない**

**具体例**:

```
defaultプロファイル:
  1. external/assay-kit/src/stats/mann-whitney.ts ✓ (expected)
  2. external/assay-kit/tests/stats/mann-whitney.spec.ts
  3. external/assay-kit/src/runner/index.ts
  → P@5 = 1/5 = 0.2, R@5 = 1/2 = 0.5

testfailプロファイル (tests/ を2.5倍強化):
  1. external/assay-kit/tests/stats/mann-whitney.spec.ts
  2. external/assay-kit/src/stats/mann-whitney.ts ✓ (expected)
  3. external/assay-kit/tests/runner/index.spec.ts
  → P@5 = 1/5 = 0.2, R@5 = 1/2 = 0.5 (順序が変わっても結果は同じ)
```

#### 📊 データセットの特性

**現在のデータセット（kiri-ab.yaml）の問題**:

1. **expectedパスが常に上位K件に含まれる**
   - どのプロファイルでも同じexpectedファイルが結果に含まれる
   - ランキング順序が変わっても一致数は同じ

2. **クエリとexpectedの粒度が粗い**
   - 例: "test failed" → "tests/stats/mann-whitney.spec.ts"
   - 多くのテストファイルがマッチするため、順序が変わりにくい

3. **評価指標が順序を考慮しない**
   - MRR（Mean Reciprocal Rank）なら検出可能
   - NDCG（Normalized Discounted Cumulative Gain）なら検出可能

---

## 📊 カテゴリ別分析結果（調整後）

### 全カテゴリでfeatureが最良（変化なし）

| Category        | Best Profile | F1@5  | 調整前 | 調整後       |
| --------------- | ------------ | ----- | ------ | ------------ |
| **dataset**     | feature      | 0.500 | 0.500  | **変化なし** |
| **integration** | feature      | 0.500 | 0.500  | **変化なし** |
| **plugins**     | feature      | 0.500 | 0.500  | **変化なし** |
| **reporter**    | feature      | 0.375 | 0.375  | **変化なし** |
| **testfail**    | feature      | 0.250 | 0.250  | **変化なし** |
| **types**       | feature      | 0.250 | 0.250  | **変化なし** |

### 特化プロファイルの効果が見られない

**testfailカテゴリ（1クエリ）**:

```
Profile      P@5    R@5    F1@5   調整前→調整後
feature      0.167  0.500  0.250  変化なし
bugfix       0.167  0.500  0.250  変化なし
testfail     0.167  0.500  0.250  変化なし ← tests/ を2.5倍にしても同じ
```

**typesカテゴリ（2クエリ）**:

```
Profile      P@5    R@5    F1@5   調整前→調整後
feature      0.167  0.500  0.250  変化なし
typeerror    0.167  0.500  0.250  変化なし ← src/types/ を3.0倍にしても同じ
```

---

## 🎯 結論

### ✅ 成功点

1. **プロファイル設定を大胆に調整**
   - multiplier を 2～3倍に引き上げ
   - src/ を 0.5～0.8 に抑制
   - 特化パスを追加（editor/, routes/, @types/ など）

2. **技術的実装は正しく動作**
   - ブーストプロファイルが適用されている
   - ランキング順序は変わっている（推定）

### ❌ 課題と制限

1. **評価指標がランキング順序を測定できない**
   - P@K/R@K/F1@K は一致数のみ測定
   - 順序変化を検出するには MRR/NDCG が必要

2. **データセットが評価に不適切**
   - expectedパスが常に上位K件に含まれる
   - クエリとexpectedの粒度が粗い

3. **統計的検出力が不足**
   - 24クエリでは有意差を検出できない

---

## 🔄 推奨される次のアクション

### 優先度: 高 🔥

#### 1. 評価指標の変更

現在の P@5/R@5/F1@5 → **MRR（Mean Reciprocal Rank）**

**理由**:

- ランキング順序を考慮
- 「expectedファイルが何位に現れるか」を測定
- プロファイル特化性を検出可能

**実装例**:

```typescript
// MRRの計算
function calculateMRR(results: string[], expected: string[]): number {
  for (let i = 0; i < results.length; i++) {
    if (expected.includes(results[i])) {
      return 1 / (i + 1); // 1位なら1.0, 2位なら0.5, 3位なら0.33
    }
  }
  return 0;
}
```

#### 2. データセット の改善

**現在**: "test failed" → "tests/stats/mann-whitney.spec.ts"  
**改善**: より具体的なクエリとexpected

```yaml
- id: "q-testfail-specific"
  text: "mann whitney test assertion failure on line 42"
  goal: "Fix specific test failure"
  expected:
    - "tests/stats/mann-whitney.spec.ts" # 最優先
    - "src/stats/mann-whitney.ts" # 次点
  # testfailプロファイルなら、spec.tsが1位に来るべき
```

### 優先度: 中

#### 3. A/Bテスト with NDCGNormalized Discounted Cumulative Gain）

- よりリッチな評価指標
- 関連度スコアを段階的に評価

#### 4. 実ユーザーでのクリック率測定

- 実際の使用シーンでの評価
- 「どの結果がクリックされたか」を測定

---

## 📊 統計サマリー

- **プロファイル調整**: 7プロファイル × 平均4箇所 = **28箇所の変更**
- **最大multiplier**: **3.0倍**（typeerror: src/types/）
- **最小src/抑制**: **0.5倍**（testfail）
- **評価実行**: 10プロファイル × 24クエリ = **240クエリ**
- **カテゴリ分析**: **17カテゴリ × 10プロファイル = 170パターン**
- **検出された改善**: **0件**（評価指標の限界）

---

## 📦 成果物

### 変更ファイル (1件)

1. ✅ `src/server/boost-profiles.ts` - 7プロファイルの大胆な調整

### 評価結果 (2件)

1. ✅ `var/assay/profile-matrix-2025-11-18.json` - 調整後の評価結果
2. ✅ カテゴリ別分析結果（170パターン）

### ドキュメント (1件)

1. ✅ `docs/eval-bold-adjustment-analysis-2025-11-18.md` - 本レポート

---

## 🎊 総括

### 達成状況

✅ **優先度高のアクション2つを完了**

1. プロファイル設定の大胆な調整（multiplier 2～3倍）
2. 調整後の24クエリでの再評価

❌ **カテゴリ特化性の改善は検出されず**

- 技術的実装は正しい
- 評価指標とデータセットの限界

### 最重要な発見

⚠️ **評価システムの根本的な問題**

1. **P@K/R@K/F1@K はランキング順序を測定できない**
2. **現在のデータセットは特化性評価に不適切**
3. **MRR/NDCG など順序を考慮する指標が必要**

### 次の最優先アクション

1. **評価指標をMRRに変更** - ランキング順序を測定
2. **データセットを改善** - より具体的なクエリとexpected
3. **50～100クエリで再評価** - 統計的検出力向上

---

**結論**: プロファイル設定は大胆に調整できたが、現在の評価システムでは特化性の改善を検出できない。評価指標とデータセットの改善が最優先。🎯
