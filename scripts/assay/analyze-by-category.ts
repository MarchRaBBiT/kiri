#!/usr/bin/env tsx
/**
 * Analyze profile performance by query category
 */

import { readFileSync } from "node:fs";
import { join } from "node:path";

interface QueryMetrics {
  queryId: string;
  status: string;
  metrics: {
    precision: number;
    recall: number;
    latencyMs: number;
    extras?: {
      mrr?: number;
      map?: number;
      hitsAtK?: number;
      f1?: number;
      ndcg?: number; // Add NDCG
    };
  };
}

interface ComparisonResult {
  comparisonId: string;
  metadata: {
    variantA: { name: string };
    variantB: { name: string };
  };
  left: {
    queries: QueryMetrics[];
  };
  right: {
    queries: QueryMetrics[];
  };
}

interface CategoryMetrics {
  category: string;
  profile: string;
  avgPrecision: number;
  avgRecall: number;
  avgF1: number;
  avgMRR: number;
  avgMAP: number;
  avgNDCG: number; // Add NDCG
  avgLatency: number;
  queryCount: number;
}

function calculateF1(precision: number, recall: number): number {
  if (precision === 0 && recall === 0) return 0;
  return (2 * precision * recall) / (precision + recall);
}

async function main(): Promise<void> {
  const repoRoot = process.cwd();
  const resultsDir = join(repoRoot, "var/assay");

  // Load dataset to get category mappings
  const datasetPath = join(repoRoot, "datasets/kiri-ab.yaml");
  console.log(`📖 Loading dataset: ${datasetPath}`);

  // Simple YAML parsing for category extraction
  const datasetContent = readFileSync(datasetPath, "utf-8");
  const categoryMap: Record<string, string> = {};

  const idMatches = datasetContent.matchAll(/id: ["']([^"']+)["']/g);
  const categoryMatches = datasetContent.matchAll(/category: ["']([^"']+)["']/g);

  const ids = Array.from(idMatches).map((m) => m[1]);
  const categories = Array.from(categoryMatches).map((m) => m[1]);

  for (let i = 0; i < Math.min(ids.length, categories.length); i++) {
    categoryMap[ids[i]] = categories[i];
  }

  console.log(`✅ Loaded ${Object.keys(categoryMap).length} query categories`);

  // Find all comparison result files - use latest by default
  const matrixPath = process.argv[2] || join(resultsDir, "profile-matrix-2025-11-18.json");
  const matrixContent = readFileSync(matrixPath, "utf-8");
  const matrixData = JSON.parse(matrixContent);
  const matrixResults: Array<{ resultPath: string; variant: string }> =
    matrixData.comparisons || [];

  console.log(`📊 Analyzing ${matrixResults.length} comparisons from ${matrixPath}...`);

  // Collect metrics by category and profile
  const categoryMetrics: CategoryMetrics[] = [];

  for (const { resultPath, variant } of matrixResults) {
    if (!resultPath) continue;

    const comparisonContent = readFileSync(resultPath, "utf-8");
    const comparison: ComparisonResult = JSON.parse(comparisonContent);

    // Group queries by category
    const categoryGroups: Record<string, QueryMetrics[]> = {};

    for (const query of comparison.right.queries) {
      const category = categoryMap[query.queryId] || "unknown";
      if (!categoryGroups[category]) {
        categoryGroups[category] = [];
      }
      categoryGroups[category].push(query);
    }

    // Calculate metrics for each category
    for (const [category, queries] of Object.entries(categoryGroups)) {
      const precisions = queries.map((q) => q.metrics.precision);
      const recalls = queries.map((q) => q.metrics.recall);
      const latencies = queries.map((q) => q.metrics.latencyMs);
      const mrrs = queries.map((q) => q.metrics.extras?.mrr ?? 0);
      const maps = queries.map((q) => q.metrics.extras?.map ?? 0);

      const ndcgs = queries.map((q) => q.metrics.extras?.ndcg ?? 0);

      const avgPrecision = precisions.reduce((sum, v) => sum + v, 0) / precisions.length;
      const avgRecall = recalls.reduce((sum, v) => sum + v, 0) / recalls.length;
      const avgF1 = calculateF1(avgPrecision, avgRecall);
      const avgMRR = mrrs.reduce((sum, v) => sum + v, 0) / mrrs.length;
      const avgMAP = maps.reduce((sum, v) => sum + v, 0) / maps.length;
      const avgNDCG = ndcgs.reduce((sum, v) => sum + v, 0) / ndcgs.length;
      const avgLatency = latencies.reduce((sum, v) => sum + v, 0) / latencies.length;

      categoryMetrics.push({
        category,
        profile: variant,
        avgPrecision,
        avgRecall,
        avgF1,
        avgMRR,
        avgMAP,
        avgNDCG,
        avgLatency,
        queryCount: queries.length,
      });
    }
  }

  console.log(`\n📈 Category Performance Analysis\n`);
  console.log(
    `${"Category".padEnd(15)} ${"Profile".padEnd(12)} ${"NDCG".padEnd(8)} ${"MRR".padEnd(8)} ${"F1@5".padEnd(8)} ${"P@5".padEnd(8)} ${"R@5".padEnd(8)} ${"Latency".padEnd(10)} ${"Queries"}`
  );
  console.log("─".repeat(105));

  // Sort by category, then by NDCG (primary ranking metric for graded relevance)
  categoryMetrics.sort((a, b) => {
    if (a.category !== b.category) {
      return a.category.localeCompare(b.category);
    }
    return b.avgNDCG - a.avgNDCG;
  });

  let currentCategory = "";
  for (const metric of categoryMetrics) {
    if (metric.category !== currentCategory) {
      if (currentCategory !== "") console.log("");
      currentCategory = metric.category;
    }

    const ndcg = metric.avgNDCG.toFixed(3);
    const mrr = metric.avgMRR.toFixed(3);
    const f1 = metric.avgF1.toFixed(3);
    const p = metric.avgPrecision.toFixed(3);
    const r = metric.avgRecall.toFixed(3);
    const lat = metric.avgLatency.toFixed(1);

    console.log(
      `${metric.category.padEnd(15)} ${metric.profile.padEnd(12)} ${ndcg.padEnd(8)} ${mrr.padEnd(8)} ${f1.padEnd(8)} ${p.padEnd(8)} ${r.padEnd(8)} ${lat.padEnd(10)} ${metric.queryCount}`
    );
  }

  // Find best profile for each category (by NDCG)
  console.log(`\n\n📌 Best Profile per Category (by NDCG)\n`);
  const bestByCategory: Record<string, CategoryMetrics> = {};

  for (const metric of categoryMetrics) {
    if (
      !bestByCategory[metric.category] ||
      metric.avgNDCG > bestByCategory[metric.category].avgNDCG
    ) {
      bestByCategory[metric.category] = metric;
    }
  }

  console.log(
    `${"Category".padEnd(15)} ${"Best Profile".padEnd(12)} ${"NDCG".padEnd(8)} ${"MRR".padEnd(8)} ${"F1@5".padEnd(8)} ${"P@5".padEnd(8)} ${"R@5"}`
  );
  console.log("─".repeat(80));

  for (const [category, metric] of Object.entries(bestByCategory).sort()) {
    const ndcg = metric.avgNDCG.toFixed(3);
    const mrr = metric.avgMRR.toFixed(3);
    const f1 = metric.avgF1.toFixed(3);
    const p = metric.avgPrecision.toFixed(3);
    const r = metric.avgRecall.toFixed(3);

    console.log(
      `${category.padEnd(15)} ${metric.profile.padEnd(12)} ${ndcg.padEnd(8)} ${mrr.padEnd(8)} ${f1.padEnd(8)} ${p.padEnd(8)} ${r}`
    );
  }
}

main().catch((error) => {
  console.error("❌ Error:", error);
  process.exit(1);
});
