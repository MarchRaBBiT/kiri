# NDCG Implementation for KIRI Profile Evaluation

**Date**: 2025-11-18  
**Status**: Implementation Complete  
**Related**: Issue #77

## Executive Summary

assay-kitの新しいNDCG（Normalized Discounted Cumulative Gain）機能を活用し、ブーストプロファイルの順位改善効果を段階的関連度で評価できるようになりました。これにより、P@K/R@K/F1@KやMRRでは検出できなかった微細な順位差を定量化できます。

## Implementation Overview

### 1. Weighted Relevance Scores

全24クエリのdatasetに重み付き関連度スコア（0-3）を追加：

```yaml
expected:
  - path: "external/assay-kit/src/stats/mann-whitney.ts"
    relevance: 3 # Most relevant
  - path: "external/assay-kit/src/stats/rank-biserial.ts"
    relevance: 2 # Relevant
  - path: "external/assay-kit/src/stats/utils.ts"
    relevance: 1 # Somewhat relevant
```

**Scoring Criteria:**

- **relevance: 3**: クエリで直接言及されているファイル、または主要な実装ファイル
- **relevance: 2**: relevance=3のファイルから直接呼び出される依存ファイル
- **relevance: 1**: 間接的に関連するファイル（同じディレクトリ内の関連モジュール）

### 2. KIRI Adapter Update

`scripts/assay/kiri-adapter.ts` に以下を追加：

```typescript
interface ExpectedItem {
  path: string;
  relevance: number;
}

interface KiriQueryMetadata extends Record<string, unknown> {
  hints?: string[];
  expected?: (string | ExpectedItem)[]; // Backward compatible
}
```

`execute()` メソッドで relevanceGrades マップを構築：

```typescript
const relevanceGrades = new Map<string, number>();
for (const item of query.metadata.expected) {
  if (typeof item === "object" && "path" in item && "relevance" in item) {
    relevanceGrades.set(item.path as string, item.relevance as number);
  } else if (typeof item === "string") {
    // Backward compatibility: treat as relevance=1
    relevanceGrades.set(item, 1);
  }
}

const retrievalMetrics = evaluateRetrieval({
  items: retrievedPaths.map((path, i) => ({
    id: path,
    timestampMs: startTime + i * 10,
  })),
  relevant: relevantPaths,
  k,
  startTimestampMs: startTime,
  relevanceGrades, // Enable NDCG calculation
});
```

### 3. Analysis Script Update

`scripts/assay/analyze-by-category.ts` にNDCG列を追加：

```typescript
interface CategoryMetrics {
  avgNDCG: number; // Added
  avgMRR: number;
  avgF1: number;
  // ...
}

// Sort by NDCG (primary metric for ranking quality)
categoryMetrics.sort((a, b) => {
  if (a.category !== b.category) {
    return a.category.localeCompare(b.category);
  }
  return b.avgNDCG - a.avgNDCG;
});
```

Output format:

```
Category        Profile      NDCG    MRR     F1@5    P@5     R@5     Latency    Queries
```

### 4. Validation

`scripts/datasets/validate-relevance.ts` を作成：

```bash
pnpm exec tsx scripts/datasets/validate-relevance.ts datasets/kiri-ab.yaml
```

Validates:

- relevance is within 0-3 range
- Each query has at least one relevance > 0
- path is a string
- expected is an array

## Key Features

### Backward Compatibility

Old format (string array) is still supported:

```yaml
expected:
  - "path/to/file.ts" # Treated as relevance: 1
```

New format (object array with relevance):

```yaml
expected:
  - path: "path/to/file.ts"
    relevance: 3
```

Both formats can coexist and will be handled correctly by the adapter.

### NDCG vs MRR

| Metric       | Ranking-aware | Graded Relevance | Simple Dataset Support |
| ------------ | ------------- | ---------------- | ---------------------- |
| P@K/R@K/F1@K | ❌            | ❌               | ✅ (binary)            |
| MRR          | ✅            | ❌               | ✅ (binary)            |
| NDCG         | ✅            | ✅               | ⚠️ (requires weighted) |

**NDCG Advantages:**

1. ✅ Accurately evaluates ranking order
2. ✅ Distinguishes between "highly relevant" and "somewhat relevant"
3. ✅ Quantifies boost profile specialization effects
4. ✅ Detects subtle ranking differences that MRR cannot

## Usage

### Step 1: Run Profile Matrix Evaluation

```bash
# Stop any existing KIRI servers
ps aux | grep 'src/server/main.ts' | grep -v grep | awk '{print $2}' | xargs kill

# Run full profile matrix evaluation
pnpm run assay:profile-matrix
```

This will generate:

- `var/assay/profile-matrix-YYYY-MM-DD.json` - Raw comparison results
- Individual comparison results in `var/assay/comparison-*.json`

### Step 2: Analyze by Category with NDCG

```bash
pnpm exec tsx scripts/assay/analyze-by-category.ts var/assay/profile-matrix-2025-11-18.json
```

Output includes:

- Category performance sorted by NDCG
- Best profile per category (by NDCG)
- NDCG, MRR, F1@5, P@5, R@5, Latency for each profile

### Step 3: Generate Report

```bash
pnpm run assay:report-matrix
```

This generates a markdown report:

- `var/assay/profile-matrix-YYYY-MM-DD.md`

## Expected Outcomes

### Before NDCG (with MRR only)

- All profiles showed MRR=1.000 for simple datasets
- Could not distinguish profile specialization
- Ranking order changes were not detected
- Same relevant items in top-K → same metrics

### After NDCG (with weighted relevance)

- NDCG can differentiate profiles even when MRR=1.000
- Detects when high-relevance items are ranked lower
- Quantifies boost profile effectiveness
- Reveals specialization by category

Example scenario:

- Profile A: ranks relevance=3 item at #1 → NDCG=1.000
- Profile B: ranks relevance=2 item at #1, relevance=3 at #2 → NDCG=0.850
- MRR for both: 1.000 (no differentiation)
- NDCG shows clear quality difference

## Technical Notes

### NDCG Calculation

assay-kit uses standard NDCG@k formula:

```
DCG@k = Σ (2^rel[i] - 1) / log2(i + 2)
IDCG@k = DCG of ideal ranking
NDCG@k = DCG@k / IDCG@k
```

Where:

- `rel[i]` is the relevance grade at position i
- Position i is 0-indexed (first item is i=0)
- `log2(i + 2)` provides position discount

### TypeScript Type Safety

All changes maintain strict TypeScript compliance:

- Optional `relevanceGrades` parameter properly typed
- Backward-compatible union types `(string | ExpectedItem)[]`
- Explicit type assertions where needed

### Performance Considerations

NDCG calculation adds minimal overhead:

- O(k) complexity for DCG
- O(n log n) for IDCG sorting (n = number of relevant items)
- Negligible impact on evaluation latency

## Files Modified

### Core Implementation

- `scripts/assay/kiri-adapter.ts` - Added relevanceGrades support
- `scripts/assay/analyze-by-category.ts` - Added NDCG display
- `datasets/kiri-ab.yaml` - Added weighted relevance to 24 queries

### New Files

- `scripts/datasets/validate-relevance.ts` - Dataset validation tool
- `docs/eval-ndcg-implementation-2025-11-18.md` - This document

### Import Path Updates

- `scripts/assay/kiri-adapter.ts`
- `scripts/eval/export-baseline.ts`
- `scripts/assay/run-evaluation.ts`
- `scripts/assay/run-comparison.ts`
- `scripts/assay/baseline.ts`

Updated to use new monorepo structure:

```typescript
// Old
import { ... } from "../../external/assay-kit/src/index.ts";

// New
import { ... } from "../../external/assay-kit/packages/assay-kit/src/index.ts";
```

## Next Steps

### Immediate Actions

1. **Run Full Evaluation**

   ```bash
   pnpm run assay:profile-matrix
   pnpm exec tsx scripts/assay/analyze-by-category.ts var/assay/profile-matrix-*.json
   ```

2. **Analyze Results**
   - Compare NDCG across profiles
   - Identify best profile per category
   - Document findings in separate analysis document

3. **Refine Relevance Scores** (if needed)
   - Review NDCG results
   - Adjust relevance scores based on actual retrieval
   - Re-run validation and evaluation

### Future Enhancements

1. **More Complex Relevance Schemes**
   - Add relevance=0 for explicitly non-relevant items
   - Support negative relevance for harmful results

2. **Additional Queries**
   - Expand dataset to 50-100 queries
   - Cover more edge cases and categories

3. **Statistical Significance Testing**
   - Compare NDCG distributions between profiles
   - Use Wilcoxon signed-rank test for paired comparisons

4. **Profile Optimization**
   - Use NDCG as optimization target
   - Auto-tune boost multipliers for maximum NDCG

## References

- [assay-kit NDCG Implementation](../../external/assay-kit/packages/assay-kit/src/metrics/ranking.ts)
- [Järvelin & Kekäläinen (2002)](https://dl.acm.org/doi/10.1145/582415.582418) - Original NDCG paper
- [Microsoft LambdaMART](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/MSR-TR-2010-82.pdf) - Learning to Rank using NDCG

## Validation Checklist

- ✅ Dataset validation passes
- ✅ TypeScript builds without errors
- ✅ NDCG calculation unit test passes
- ✅ Backward compatibility maintained
- ✅ Import paths updated for monorepo
- ✅ All 24 queries have weighted relevance
- ✅ Analysis script displays NDCG
- ⏳ Full profile matrix evaluation (to be run)
- ⏳ NDCG-based specialization analysis (pending results)

## Conclusion

NDCG実装により、ブーストプロファイルの順位改善効果を正確に評価できるようになりました。重み付き関連度スコアにより、重要なファイルが上位にランクされているかを定量化でき、各プロファイルの特化度を明確に区別できます。

MRRやP@K/R@K/F1@Kでは検出できなかった微細な順位差をNDCGで捕捉でき、より洗練されたプロファイル選定が可能になります。
