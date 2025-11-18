#!/usr/bin/env tsx
import { readFileSync, writeFileSync } from "node:fs";
import { join, basename } from "node:path";

interface ComparisonResult {
  comparisonId: string;
  metadata: {
    variantA: { name: string; description: string };
    variantB: { name: string; description: string };
  };
  left: {
    overall: {
      avgLatencyMs: number;
    };
    queries: Array<{
      metrics: {
        precision: number;
        recall: number;
        latencyMs: number;
      };
    }>;
  };
  right: {
    overall: {
      avgLatencyMs: number;
    };
    queries: Array<{
      metrics: {
        precision: number;
        recall: number;
        latencyMs: number;
      };
    }>;
  };
  statisticalAnalysis?: {
    tests: StatisticalTest[];
  };
  summary?: {
    degraded: boolean;
  };
}

interface StatisticalTest {
  metric: string;
  significant: boolean;
  pValue: number;
  effectSize?: number;
}

interface ProfileMetrics {
  variant: string;
  precision: number;
  recall: number;
  f1: number;
  latency: number;
  significant: boolean;
  degraded: boolean;
  pValue?: number;
  effectSize?: number;
}

interface MatrixReportOptions {
  matrixJsonPath: string;
  outputMdPath?: string;
}

function parseArgs(): MatrixReportOptions {
  const args = process.argv.slice(2);

  if (args.length === 0 || args.includes("--help")) {
    printHelp();
    process.exit(args.includes("--help") ? 0 : 1);
  }

  const options: MatrixReportOptions = {
    matrixJsonPath: args[0],
  };

  for (let i = 1; i < args.length; i++) {
    const flag = args[i];
    const value = args[i + 1];
    if (flag === "--output" && typeof value === "string") {
      options.outputMdPath = value;
      i += 1;
    }
  }

  return options;
}

function printHelp(): void {
  console.log(
    `\n📊 Matrix Report Generator (KIRI)\n\nUsage:\n  tsx scripts/assay/report-matrix.ts <matrix-json-path> [--output <md-path>]\n\nArguments:\n  <matrix-json-path>    Path to profile-matrix-*.json\n  --output <md-path>    Output markdown path (default: same dir as JSON with .md extension)\n`
  );
}

function loadComparisonResult(path: string): ComparisonResult {
  const content = readFileSync(path, "utf-8");
  return JSON.parse(content) as ComparisonResult;
}

function calculateF1(precision: number, recall: number): number {
  if (precision + recall === 0) {
    return 0;
  }
  return (2 * precision * recall) / (precision + recall);
}

function extractProfileMetrics(
  baselineVariant: string,
  comparisonResult: ComparisonResult
): ProfileMetrics {
  const { right, statisticalAnalysis, summary, metadata } = comparisonResult;

  // Calculate average precision and recall from queries
  const precisionValues = right.queries.map((q) => q.metrics.precision);
  const recallValues = right.queries.map((q) => q.metrics.recall);

  const precision = precisionValues.reduce((sum, v) => sum + v, 0) / precisionValues.length;
  const recall = recallValues.reduce((sum, v) => sum + v, 0) / recallValues.length;
  const f1 = calculateF1(precision, recall);
  const latency = right.overall.avgLatencyMs;

  let significant = false;
  let pValue: number | undefined;
  let effectSize: number | undefined;

  if (statisticalAnalysis?.tests) {
    const precisionTest = statisticalAnalysis.tests.find((t) => t.metric === "precision");
    const recallTest = statisticalAnalysis.tests.find((t) => t.metric === "recall");

    if (precisionTest?.significant || recallTest?.significant) {
      significant = true;
      pValue = Math.min(precisionTest?.pValue ?? 1, recallTest?.pValue ?? 1);
      effectSize = precisionTest?.effectSize ?? recallTest?.effectSize;
    }
  }

  const degraded = summary?.degraded ?? false;

  return {
    variant: metadata.variantB.name,
    precision,
    recall,
    f1,
    latency,
    significant,
    degraded,
    pValue,
    effectSize,
  };
}

function generateMarkdownTable(
  baselineVariant: string,
  baselineMetrics: { precision: number; recall: number; f1: number; latency: number },
  profileMetrics: ProfileMetrics[]
): string {
  const lines: string[] = [];

  lines.push("## プロファイル性能マトリクス\n");
  lines.push(
    `| Profile | P@5 | R@5 | F1@5 | Latency (ms) | vs ${baselineVariant} | 統計的有意性 | 劣化 |`
  );
  lines.push(
    "|---------|-----|-----|------|--------------|----------------------|--------------|------|"
  );

  // Baseline row
  lines.push(
    `| **${baselineVariant}** (baseline) | ${baselineMetrics.precision.toFixed(3)} | ${baselineMetrics.recall.toFixed(3)} | ${baselineMetrics.f1.toFixed(3)} | ${baselineMetrics.latency.toFixed(1)} | - | - | - |`
  );

  // Sort by F1 score descending
  const sorted = [...profileMetrics].sort((a, b) => b.f1 - a.f1);

  for (const pm of sorted) {
    const precisionDelta = pm.precision - baselineMetrics.precision;
    const recallDelta = pm.recall - baselineMetrics.recall;
    const f1Delta = pm.f1 - baselineMetrics.f1;

    const precisionStr = `${pm.precision.toFixed(3)} (${precisionDelta >= 0 ? "+" : ""}${precisionDelta.toFixed(3)})`;
    const recallStr = `${pm.recall.toFixed(3)} (${recallDelta >= 0 ? "+" : ""}${recallDelta.toFixed(3)})`;
    const f1Str = `${pm.f1.toFixed(3)} (${f1Delta >= 0 ? "+" : ""}${f1Delta.toFixed(3)})`;

    const significantStr = pm.significant ? `✓ (p=${pm.pValue?.toFixed(4) ?? "N/A"})` : "~";
    const degradedStr = pm.degraded ? "✗" : "-";

    lines.push(
      `| ${pm.variant} | ${precisionStr} | ${recallStr} | ${f1Str} | ${pm.latency.toFixed(1)} | Δ | ${significantStr} | ${degradedStr} |`
    );
  }

  return lines.join("\n");
}

function generateCategoryAnalysis(profileMetrics: ProfileMetrics[]): string {
  const lines: string[] = [];

  lines.push("\n## カテゴリ別推奨プロファイル\n");

  // Best overall F1
  const bestF1 = [...profileMetrics].sort((a, b) => b.f1 - a.f1)[0];
  lines.push(`### 総合最適 (F1スコア)`);
  lines.push(
    `- **${bestF1.variant}**: F1=${bestF1.f1.toFixed(3)}, P@5=${bestF1.precision.toFixed(3)}, R@5=${bestF1.recall.toFixed(3)}\n`
  );

  // Best precision
  const bestPrecision = [...profileMetrics].sort((a, b) => b.precision - a.precision)[0];
  lines.push(`### Precision重視`);
  lines.push(
    `- **${bestPrecision.variant}**: P@5=${bestPrecision.precision.toFixed(3)}, R@5=${bestPrecision.recall.toFixed(3)}\n`
  );

  // Best recall
  const bestRecall = [...profileMetrics].sort((a, b) => b.recall - a.recall)[0];
  lines.push(`### Recall重視`);
  lines.push(
    `- **${bestRecall.variant}**: R@5=${bestRecall.recall.toFixed(3)}, P@5=${bestRecall.precision.toFixed(3)}\n`
  );

  // Fastest latency
  const fastest = [...profileMetrics].sort((a, b) => a.latency - b.latency)[0];
  lines.push(`### レイテンシ最小`);
  lines.push(`- **${fastest.variant}**: ${fastest.latency.toFixed(1)}ms\n`);

  return lines.join("\n");
}

function generateSummary(
  baselineVariant: string,
  baselineMetrics: { precision: number; recall: number; f1: number; latency: number },
  profileMetrics: ProfileMetrics[]
): string {
  const lines: string[] = [];

  lines.push("\n## サマリー\n");

  const improved = profileMetrics.filter((pm) => pm.f1 > baselineMetrics.f1 && pm.significant);
  const degradedList = profileMetrics.filter((pm) => pm.degraded);

  lines.push(`- テスト対象プロファイル数: ${profileMetrics.length}`);
  lines.push(`- Baseline (${baselineVariant}): F1=${baselineMetrics.f1.toFixed(3)}`);
  lines.push(`- 統計的に有意な改善: ${improved.length}件`);
  lines.push(`- 劣化検出: ${degradedList.length}件\n`);

  if (improved.length > 0) {
    lines.push("### 有意に改善したプロファイル\n");
    for (const pm of improved) {
      const delta = pm.f1 - baselineMetrics.f1;
      lines.push(
        `- **${pm.variant}**: F1=${pm.f1.toFixed(3)} (+${delta.toFixed(3)}), p=${pm.pValue?.toFixed(4) ?? "N/A"}`
      );
    }
    lines.push("");
  }

  if (degradedList.length > 0) {
    lines.push("### 劣化が検出されたプロファイル\n");
    for (const pm of degradedList) {
      const delta = pm.f1 - baselineMetrics.f1;
      lines.push(`- **${pm.variant}**: F1=${pm.f1.toFixed(3)} (${delta.toFixed(3)})`);
    }
    lines.push("");
  }

  return lines.join("\n");
}

async function main(): Promise<void> {
  const options = parseArgs();
  const matrixJsonPath = options.matrixJsonPath;

  if (!matrixJsonPath.endsWith(".json")) {
    throw new Error("Matrix JSON path must end with .json");
  }

  const matrixData = JSON.parse(readFileSync(matrixJsonPath, "utf-8")) as {
    baseline: string;
    comparisons: Array<{ resultPath: string; success: boolean; variant: string }>;
  };

  const baselineVariant = matrixData.baseline;
  const successfulComparisons = matrixData.comparisons.filter((c) => c.success);

  if (successfulComparisons.length === 0) {
    throw new Error("No successful comparisons found in matrix result");
  }

  console.log(`📊 Generating matrix report for ${successfulComparisons.length} comparisons...`);

  const profileMetrics: ProfileMetrics[] = [];

  // Load baseline metrics from first comparison
  const firstComparison = loadComparisonResult(successfulComparisons[0].resultPath);
  const baselineLeft = firstComparison.left;

  // Calculate average precision and recall from baseline queries
  const baselinePrecisionValues = baselineLeft.queries.map((q) => q.metrics.precision);
  const baselineRecallValues = baselineLeft.queries.map((q) => q.metrics.recall);

  const baselinePrecision =
    baselinePrecisionValues.reduce((sum, v) => sum + v, 0) / baselinePrecisionValues.length;
  const baselineRecall =
    baselineRecallValues.reduce((sum, v) => sum + v, 0) / baselineRecallValues.length;

  const baselineMetrics = {
    precision: baselinePrecision,
    recall: baselineRecall,
    f1: calculateF1(baselinePrecision, baselineRecall),
    latency: baselineLeft.overall.avgLatencyMs,
  };

  // Extract metrics from each comparison
  for (const comparison of successfulComparisons) {
    const comparisonResult = loadComparisonResult(comparison.resultPath);
    const metrics = extractProfileMetrics(baselineVariant, comparisonResult);
    profileMetrics.push(metrics);
  }

  // Generate markdown report
  const reportLines: string[] = [];
  reportLines.push(`# ブーストプロファイル系統的テスト結果\n`);
  reportLines.push(`**実行日**: ${new Date().toISOString().split("T")[0]}`);
  reportLines.push(`**Baseline**: ${baselineVariant}`);
  reportLines.push(`**比較プロファイル数**: ${profileMetrics.length}\n`);

  reportLines.push(generateMarkdownTable(baselineVariant, baselineMetrics, profileMetrics));
  reportLines.push(generateSummary(baselineVariant, baselineMetrics, profileMetrics));
  reportLines.push(generateCategoryAnalysis(profileMetrics));

  const markdown = reportLines.join("\n");

  // Determine output path
  const outputMdPath = options.outputMdPath ?? matrixJsonPath.replace(/\.json$/, ".md");

  writeFileSync(outputMdPath, markdown, "utf-8");

  console.log(`✅ Matrix report saved to ${outputMdPath}`);
  console.log(`\n${markdown}\n`);

  process.exit(0);
}

main().catch((error) => {
  console.error(
    `\n❌ Matrix report generation failed: ${error instanceof Error ? error.message : String(error)}`
  );
  process.exit(1);
});
