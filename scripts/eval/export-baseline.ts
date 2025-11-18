#!/usr/bin/env tsx
import { readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import type { Metrics } from "../../external/assay-kit/packages/assay-kit/src/types/metrics.ts";

interface GoldenEvalResult {
  timestamp?: string;
  datasetVersion?: string;
  k?: number;
  overall?: {
    precisionAtK?: number;
    avgTTFU?: number;
    avgTokensEstimate?: number;
    avgBaselineTokens?: number;
    avgTokenSavingsRatio?: number;
    avgHintCoverage?: number;
  };
  queries?: Array<{
    durationMs?: number;
  }>;
}

function average(values: number[]): number | undefined {
  if (values.length === 0) {
    return undefined;
  }
  const total = values.reduce((sum, value) => sum + value, 0);
  return total / values.length;
}

function format(value: number | undefined): number | undefined {
  if (value === undefined || Number.isNaN(value)) {
    return undefined;
  }
  return Number(value.toFixed(6));
}

function main(): void {
  const [, , inputPathArg, outputPathArg] = process.argv;
  const cwd = process.cwd();
  const inputPath = resolve(cwd, inputPathArg ?? "var/eval/latest.json");
  const outputPath = resolve(cwd, outputPathArg ?? "var/eval/latest.metrics.json");

  const raw = readFileSync(inputPath, "utf8");
  const parsed = JSON.parse(raw) as GoldenEvalResult;

  const durations = (parsed.queries ?? [])
    .map((query) => (typeof query.durationMs === "number" ? query.durationMs : undefined))
    .filter((value): value is number => value !== undefined && Number.isFinite(value));

  if (!durations.length) {
    throw new Error(`No durationMs entries found in ${inputPath}`);
  }

  const metrics: Metrics = {
    latencyMs: format(average(durations)) ?? 0,
  };

  if (typeof parsed.overall?.precisionAtK === "number") {
    const precision = format(parsed.overall.precisionAtK);
    if (precision !== undefined) {
      metrics.precision = precision;
    }
  }
  if (typeof parsed.overall?.avgTTFU === "number") {
    const ttfu = format(parsed.overall.avgTTFU);
    if (ttfu !== undefined) {
      metrics.timeToFirstUseful = ttfu;
    }
  }

  const extras: Record<string, number> = {};
  if (typeof parsed.overall?.avgTokenSavingsRatio === "number") {
    const value = format(parsed.overall.avgTokenSavingsRatio);
    extras.tokenSavingsRatio = value ?? parsed.overall.avgTokenSavingsRatio;
  }
  if (typeof parsed.overall?.avgHintCoverage === "number") {
    const value = format(parsed.overall.avgHintCoverage);
    extras.hintCoverage = value ?? parsed.overall.avgHintCoverage;
  }
  if (typeof parsed.overall?.avgTokensEstimate === "number") {
    const value = format(parsed.overall.avgTokensEstimate);
    extras.avgTokensEstimate = value ?? parsed.overall.avgTokensEstimate;
  }
  if (typeof parsed.overall?.avgBaselineTokens === "number") {
    const value = format(parsed.overall.avgBaselineTokens);
    extras.avgBaselineTokens = value ?? parsed.overall.avgBaselineTokens;
  }
  if (Object.keys(extras).length > 0) {
    metrics.extras = extras;
  }

  const metadata = {
    source: inputPath,
    datasetVersion: parsed.datasetVersion,
    generatedAt: new Date().toISOString(),
  };

  writeFileSync(outputPath, JSON.stringify({ metrics, metadata }, null, 2));
  console.log(`✅ Exported metrics to ${outputPath}`);
}

main();
