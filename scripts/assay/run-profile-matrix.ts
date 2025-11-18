#!/usr/bin/env tsx
import { spawnSync, execSync } from "node:child_process";
import { existsSync, mkdirSync, writeFileSync, unlinkSync } from "node:fs";
import { join } from "node:path";

import { getAvailableVariants } from "./kiri-variants.js";

interface ProfileMatrixOptions {
  dataset: string;
  baseline: string;
  concurrency: number;
  degradationThreshold: number;
  statsMethod: "auto" | "paired-t" | "independent-t" | "mann-whitney-u";
  statsAlpha: number;
  correction: "none" | "bonferroni" | "holm";
  dbPath?: string;
  skipVariants?: string[];
}

interface ComparisonSummary {
  variant: string;
  baselineVariant: string;
  timestamp: string;
  resultPath: string;
  success: boolean;
  error?: string;
}

interface MatrixResult {
  matrixId: string;
  executionDate: string;
  baseline: string;
  dataset: string;
  comparisons: ComparisonSummary[];
  summary: {
    totalVariants: number;
    successfulComparisons: number;
    failedComparisons: number;
  };
}

function parseArgs(): ProfileMatrixOptions {
  const args = process.argv.slice(2);
  const options: ProfileMatrixOptions = {
    dataset: "datasets/kiri-ab.yaml",
    baseline: "default",
    concurrency: 2,
    degradationThreshold: 0.3,
    statsMethod: "mann-whitney-u",
    statsAlpha: 0.05,
    correction: "holm",
    skipVariants: [],
  };

  for (let i = 0; i < args.length; i++) {
    const flag = args[i];
    if (flag === "--") {
      continue;
    }
    const value = args[i + 1];
    switch (flag) {
      case "--dataset":
        if (typeof value === "string" && value.length > 0) {
          options.dataset = value;
        }
        i += 1;
        break;
      case "--baseline":
        if (typeof value === "string" && value.length > 0) {
          options.baseline = value;
        }
        i += 1;
        break;
      case "--concurrency":
        options.concurrency = parseInt(value ?? String(options.concurrency), 10);
        i += 1;
        break;
      case "--degradation":
        options.degradationThreshold = parseFloat(value ?? String(options.degradationThreshold));
        i += 1;
        break;
      case "--stats":
        if (typeof value === "string" && value.length > 0) {
          options.statsMethod = value as ProfileMatrixOptions["statsMethod"];
        }
        i += 1;
        break;
      case "--alpha":
        options.statsAlpha = parseFloat(value ?? String(options.statsAlpha));
        i += 1;
        break;
      case "--correction":
        if (typeof value === "string" && value.length > 0) {
          options.correction = value as ProfileMatrixOptions["correction"];
        }
        i += 1;
        break;
      case "--db":
        if (typeof value === "string" && value.length > 0) {
          options.dbPath = value;
        }
        i += 1;
        break;
      case "--skip":
        if (typeof value === "string" && value.length > 0) {
          options.skipVariants = value.split(",").map((v) => v.trim());
        }
        i += 1;
        break;
      case "--help":
        printHelp();
        process.exit(0);
        break;
      default:
        if (!flag.startsWith("-")) {
          continue;
        }
        console.warn(`Unknown option: ${flag}`);
    }
  }

  return options;
}

function printHelp(): void {
  const availableVariants = getAvailableVariants();
  console.log(
    `\n🔬 Profile Matrix Runner (KIRI)\n\nUsage:\n  pnpm run assay:profile-matrix -- [options]\n\nOptions:\n  --dataset <path>          Dataset path (default: datasets/kiri-ab.yaml)\n  --baseline <name>         Baseline variant (default: default)\n  --concurrency <n>         Runner concurrency (default: 2)\n  --degradation <ratio>     Degradation threshold (default: 0.3)\n  --stats <method>          Statistical test (auto|paired-t|independent-t|mann-whitney-u)\n  --alpha <value>           Significance level (default: 0.05)\n  --correction <method>     Multiple comparison correction (none|bonferroni|holm, default: holm)\n  --db <path>               DuckDB path (default: var/index.duckdb)\n  --skip <variants>         Comma-separated variants to skip (e.g., balanced,docs)\n  --help                    Show this message\n\nAvailable variants: ${availableVariants.join(", ")}\n`
  );
}

function killRemainingServers(): void {
  try {
    // Kill any remaining KIRI MCP server processes
    execSync("pkill -f 'src/server/main.ts' || true", { stdio: "ignore" });
  } catch {
    // Ignore errors if no processes found
  }
}

function cleanupDbCopy(repoRoot: string, variant: string): void {
  try {
    const dbPath = join(repoRoot, "var", `index-${variant}.duckdb`);
    const walPath = `${dbPath}.wal`;
    if (existsSync(dbPath)) {
      unlinkSync(dbPath);
    }
    if (existsSync(walPath)) {
      unlinkSync(walPath);
    }
  } catch (error) {
    console.warn(`⚠️  Failed to cleanup DB copy for ${variant}: ${error}`);
  }
}

function runComparison(
  variantA: string,
  variantB: string,
  options: ProfileMatrixOptions,
  repoRoot: string
): ComparisonSummary {
  const timestamp = new Date().toISOString().split("T")[0];
  const resultsDir = join(repoRoot, "var/assay");

  console.log(`\n📊 Running: ${variantA} vs ${variantB}`);

  // Ensure no server processes are running before starting
  killRemainingServers();

  // Wait 1 second to ensure processes are fully terminated
  execSync("sleep 1", { stdio: "ignore" });

  const args = [
    "scripts/assay/run-comparison.ts",
    "--dataset",
    options.dataset,
    "--variant-a",
    variantA,
    "--variant-b",
    variantB,
    "--concurrency",
    String(options.concurrency),
    "--degradation",
    String(options.degradationThreshold),
    "--stats",
    options.statsMethod,
    "--alpha",
    String(options.statsAlpha),
    "--correction",
    options.correction,
  ];

  if (options.dbPath) {
    args.push("--db-left", options.dbPath);
  }

  const result = spawnSync("tsx", args, {
    cwd: repoRoot,
    stdio: "inherit",
    env: { ...process.env },
  });

  // Kill any remaining server processes after comparison
  killRemainingServers();

  // Cleanup DB copy created by run-comparison.ts
  if (variantB !== variantA) {
    cleanupDbCopy(repoRoot, variantB);
  }

  const expectedResultPath = join(
    resultsDir,
    `comparison-${variantA}-vs-${variantB}-${timestamp}.json`
  );

  return {
    variant: variantB,
    baselineVariant: variantA,
    timestamp,
    resultPath: expectedResultPath,
    success: result.status === 0 && existsSync(expectedResultPath),
    error: result.status !== 0 ? `Exit code: ${result.status}` : undefined,
  };
}

async function main(): Promise<void> {
  const options = parseArgs();
  const repoRoot = process.cwd();
  const defaultDbPath = join(repoRoot, "var/index.duckdb");
  const datasetPath = join(repoRoot, options.dataset);
  const resultsDir = join(repoRoot, "var/assay");

  if (!existsSync(options.dbPath ?? defaultDbPath)) {
    throw new Error(
      `DuckDB not found at ${options.dbPath ?? defaultDbPath}. Run kiri index first.`
    );
  }
  if (!existsSync(datasetPath)) {
    throw new Error(`Dataset not found at ${datasetPath}.`);
  }
  if (!existsSync(resultsDir)) {
    mkdirSync(resultsDir, { recursive: true });
  }

  const allVariants = getAvailableVariants();
  const targetVariants = allVariants.filter(
    (v) => v !== options.baseline && !options.skipVariants?.includes(v)
  );

  console.log("🔬 KIRI Profile Matrix Runner");
  console.log(`  Dataset: ${datasetPath}`);
  console.log(`  Baseline: ${options.baseline}`);
  console.log(`  Target Variants: ${targetVariants.join(", ")}`);
  console.log(`  Stats Method: ${options.statsMethod} (α=${options.statsAlpha})`);
  console.log(`  Correction: ${options.correction}`);
  console.log(`  Degradation Threshold: ${(options.degradationThreshold * 100).toFixed(0)}%\n`);

  const matrixResult: MatrixResult = {
    matrixId: `profile-matrix-${options.baseline}`,
    executionDate: new Date().toISOString(),
    baseline: options.baseline,
    dataset: options.dataset,
    comparisons: [],
    summary: {
      totalVariants: targetVariants.length,
      successfulComparisons: 0,
      failedComparisons: 0,
    },
  };

  for (const variant of targetVariants) {
    const comparisonResult = runComparison(options.baseline, variant, options, repoRoot);
    matrixResult.comparisons.push(comparisonResult);

    if (comparisonResult.success) {
      matrixResult.summary.successfulComparisons += 1;
      console.log(`✅ ${variant}: Success`);
    } else {
      matrixResult.summary.failedComparisons += 1;
      console.log(`❌ ${variant}: Failed - ${comparisonResult.error ?? "Unknown error"}`);
    }
  }

  const timestamp = new Date().toISOString().split("T")[0];
  const matrixJsonPath = join(resultsDir, `profile-matrix-${timestamp}.json`);

  writeFileSync(matrixJsonPath, JSON.stringify(matrixResult, null, 2), "utf-8");

  console.log(`\n📄 Matrix result saved to ${matrixJsonPath}`);
  console.log(`\n📊 Summary:`);
  console.log(`  Total Variants: ${matrixResult.summary.totalVariants}`);
  console.log(`  Successful: ${matrixResult.summary.successfulComparisons}`);
  console.log(`  Failed: ${matrixResult.summary.failedComparisons}`);

  if (matrixResult.summary.failedComparisons > 0) {
    console.log(`\n⚠️  Some comparisons failed. Check logs above for details.`);
    process.exit(1);
  }

  process.exit(0);
}

main().catch((error) => {
  console.error(
    `\n❌ Profile matrix execution failed: ${error instanceof Error ? error.message : String(error)}`
  );
  process.exit(1);
});
