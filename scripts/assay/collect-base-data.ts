#!/usr/bin/env tsx
/* global fetch */
import { spawn, type ChildProcess } from "node:child_process";
import { randomUUID } from "node:crypto";
import { existsSync, mkdirSync, readFileSync, writeFileSync, copyFileSync } from "node:fs";
import { join, dirname } from "node:path";
import { performance } from "node:perf_hooks";

import { parse as parseYAML } from "yaml";

import { resolveSafePath } from "../../src/shared/fs/safePath.ts";
import { matchesGlob } from "../../src/shared/utils/glob.ts";
import { withRetry } from "../../src/shared/utils/retry.ts";

interface DatasetQuery {
  id: string;
  text: string;
  metadata?: {
    category?: string;
    intent?: string;
    tool?: string;
    boostProfile?: string;
    tags?: string[];
    expected?: string[];
    [key: string]: unknown;
  };
  boostProfile?: string;
  tool?: string;
}

interface DatasetReferenceEntry {
  id: string;
  reference?: {
    paths?: string[];
    patterns?: string[];
  };
}

interface DatasetFile {
  schemaVersion?: string;
  version?: string;
  name?: string;
  description?: string;
  defaultParams?: {
    k?: number;
    timeoutMs?: number;
    tool?: string;
  };
  queries: DatasetQuery[];
  expected?: DatasetReferenceEntry[];
}

interface ReferenceData {
  paths: string[];
  patterns: string[];
}

interface QueryResultSnapshot {
  id: string;
  tool: string;
  status: "success" | "error";
  retrieved: string[];
  precisionAtK: number | null;
  recallAtK: number | null;
  latencyMs: number;
  error?: string;
}

const RELEASE_VERSION = process.env.KIRI_BASE_RELEASE ?? "0.10.0";
const SERVER_PORT = Number(process.env.KIRI_BASE_PORT ?? "22899");
const ALLOW_EXTERNAL_PATHS = process.env.KIRI_ALLOW_UNSAFE_PATHS === "1";
const DATASET_PATH = resolveSafePath(
  process.env.KIRI_DATASET_PATH ??
    "external/assay-kit/examples/kiri-integration/datasets/kiri-golden.yaml",
  { allowOutsideBase: ALLOW_EXTERNAL_PATHS }
);
const ASSAY_OUTPUT_DIR = join(process.cwd(), "var/assay/base");
const REPO_ROOT = process.cwd();
const DB_SOURCE = join(process.cwd(), "var/index.duckdb");
const DB_COPY = join(process.cwd(), `var/index-base-${RELEASE_VERSION}.duckdb`);

type CleanupEvent = NodeJS.Signals | "exit";

function registerCleanup(server: ChildProcess): Array<[CleanupEvent, () => void]> {
  const cleanupHandlers: Array<[CleanupEvent, () => void]> = [];
  const cleanup = () => stopServer(server);
  const events: CleanupEvent[] = ["SIGINT", "SIGTERM", "SIGQUIT", "exit"];
  for (const event of events) {
    const handler = () => cleanup();
    cleanupHandlers.push([event, handler]);
    process.on(event, handler);
  }
  return cleanupHandlers;
}

function removeCleanup(handlers: Array<[CleanupEvent, () => void]>): void {
  for (const [event, handler] of handlers) {
    process.off(event, handler);
  }
}

function stopServer(server: ChildProcess | null, signal: NodeJS.Signals = "SIGTERM"): void {
  if (!server || server.killed) {
    return;
  }
  server.kill(signal);
  setTimeout(() => {
    if (!server.killed) {
      server.kill("SIGKILL");
    }
  }, 5000);
}

function ensureDirectories(): void {
  mkdirSync(dirname(DB_COPY), { recursive: true });
  mkdirSync(ASSAY_OUTPUT_DIR, { recursive: true });
}

function copyDatabase(): void {
  if (!existsSync(DB_SOURCE)) {
    throw new Error(`Source DB not found at ${DB_SOURCE}. Run pnpm exec kiri index first.`);
  }
  copyFileSync(DB_SOURCE, DB_COPY);
  const walSource = `${DB_SOURCE}.wal`;
  if (existsSync(walSource)) {
    copyFileSync(walSource, `${DB_COPY}.wal`);
  }
}

async function waitForServer(port: number, timeoutMs = 20000): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    try {
      const response = await fetch(`http://localhost:${port}`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ jsonrpc: "2.0", id: "ping", method: "ping", params: {} }),
      });
      if (response.ok) {
        return;
      }
    } catch {
      // Retry
    }
    await new Promise((resolve) => setTimeout(resolve, 500));
  }
  throw new Error(`KIRI server on port ${port} did not respond within ${timeoutMs}ms`);
}

async function callKiri(
  port: number,
  method: string,
  params: Record<string, unknown>,
  timeoutMs: number
): Promise<unknown> {
  return await withRetry(
    async () => {
      const controller = new AbortController();
      const timer = setTimeout(() => controller.abort(), timeoutMs);
      try {
        const response = await fetch(`http://localhost:${port}`, {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ jsonrpc: "2.0", id: randomUUID(), method, params }),
          signal: controller.signal,
        });
        const payload = (await response.json()) as {
          result?: unknown;
          error?: { message: string };
        };
        if (payload.error) {
          throw new Error(payload.error.message);
        }
        return payload.result;
      } finally {
        clearTimeout(timer);
      }
    },
    {
      maxAttempts: 3,
      delayMs: 1000,
      jitterMs: 500,
      isRetriable: (error) => {
        if (!(error instanceof Error)) {
          return false;
        }
        if (error.name === "AbortError") {
          return true;
        }
        return /ECONNREFUSED|ECONNRESET|fetch failed/i.test(error.message);
      },
    }
  );
}

function computeMetrics(
  retrieved: string[],
  reference: ReferenceData,
  k: number
): { precision: number | null; recall: number | null } {
  if (retrieved.length === 0 || k <= 0) {
    return { precision: 0, recall: null };
  }
  const relevant = new Set(reference.paths.map((p) => p.replace(/^\.\//, "")));
  for (const entry of retrieved) {
    if (reference.patterns.some((pattern) => matchesGlob(entry, pattern))) {
      relevant.add(entry);
    }
  }
  if (relevant.size === 0) {
    return { precision: 0, recall: 0 };
  }
  const hits = retrieved.filter((path) => relevant.has(path)).length;
  const precision = hits / k;
  const recall = hits / relevant.size;
  return { precision, recall };
}

function extractPaths(result: unknown, tool: string): string[] {
  if (tool === "files_search" && Array.isArray(result)) {
    return result
      .map((item) =>
        typeof item === "object" && item !== null ? (item as { path?: string }).path : null
      )
      .filter((p): p is string => typeof p === "string");
  }
  if (
    result &&
    typeof result === "object" &&
    Array.isArray((result as { context?: unknown }).context)
  ) {
    const context = (result as { context?: Array<{ path?: string }> }).context ?? [];
    return context.map((item) => item?.path).filter((p): p is string => typeof p === "string");
  }
  return [];
}

async function main(): Promise<void> {
  ensureDirectories();
  copyDatabase();

  console.log(`📦 Collecting base data using npx kiri-server@${RELEASE_VERSION}`);

  const dataset = parseYAML(readFileSync(DATASET_PATH, "utf8")) as DatasetFile;
  const expectedMap = new Map<string, ReferenceData>();
  for (const entry of dataset.expected ?? []) {
    if (!entry?.id) continue;
    expectedMap.set(entry.id, {
      paths: entry.reference?.paths ?? [],
      patterns: entry.reference?.patterns ?? [],
    });
  }

  const server = spawn(
    "npx",
    [
      "--yes",
      "--package",
      `kiri-mcp-server@${RELEASE_VERSION}`,
      "kiri-server",
      "--port",
      String(SERVER_PORT),
      "--repo",
      REPO_ROOT,
      "--db",
      DB_COPY,
    ],
    { cwd: REPO_ROOT, stdio: "pipe" }
  );

  server.stdout?.on("data", (data) => process.stdout.write(`[server] ${data}`));
  server.stderr?.on("data", (data) => process.stderr.write(`[server] ${data}`));
  const cleanupHandlers = registerCleanup(server);

  try {
    await waitForServer(SERVER_PORT);
    console.log("✅ Release server ready\n");

    const timeoutMs = dataset.defaultParams?.timeoutMs ?? 30000;
    const limit = dataset.defaultParams?.k ?? 10;
    const results: QueryResultSnapshot[] = [];

    for (const query of dataset.queries) {
      const tool =
        query.tool || query.metadata?.tool || dataset.defaultParams?.tool || "context_bundle";
      const params: Record<string, unknown> = { limit };
      if (tool === "context_bundle") {
        params.goal = query.text;
        params.compact = true;
        if (query.boostProfile || query.metadata?.boostProfile) {
          params.boost_profile = query.boostProfile ?? query.metadata?.boostProfile;
        }
      } else if (tool === "files_search") {
        params.query = query.text;
      } else {
        console.warn(`⚠️ Unsupported tool ${tool}, skipping query ${query.id}`);
        continue;
      }

      console.log(`→ ${query.id} (${tool})`);
      const start = performance.now();
      try {
        const rpcResult = await callKiri(SERVER_PORT, tool, params, timeoutMs);
        const latencyMs = performance.now() - start;
        const retrieved = extractPaths(rpcResult, tool);
        const reference = expectedMap.get(query.id) ?? { paths: [], patterns: [] };
        const metrics = computeMetrics(retrieved, reference, limit);
        results.push({
          id: query.id,
          tool,
          status: "success",
          retrieved,
          precisionAtK: metrics.precision,
          recallAtK: metrics.recall,
          latencyMs,
        });
        console.log(
          `   ✓ retrieved=${retrieved.length} P@${limit}=${(metrics.precision ?? 0).toFixed(3)}`
        );
      } catch (error) {
        const latencyMs = performance.now() - start;
        console.error(`   ✗ ${query.id} failed: ${error}`);
        results.push({
          id: query.id,
          tool,
          status: "error",
          retrieved: [],
          precisionAtK: null,
          recallAtK: null,
          latencyMs,
          error: error instanceof Error ? error.message : String(error),
        });
      }
    }

    const success = results.filter((r) => r.status === "success");
    const overallPrecision = success.length
      ? success.reduce((sum, r) => sum + (r.precisionAtK ?? 0), 0) / success.length
      : 0;
    const overallRecall = success.length
      ? success.reduce((sum, r) => sum + (r.recallAtK ?? 0), 0) / success.length
      : 0;

    const snapshot = {
      release: `kiri-server@${RELEASE_VERSION}`,
      datasetVersion: dataset.version,
      timestamp: new Date().toISOString(),
      repo: REPO_ROOT,
      db: DB_COPY,
      port: SERVER_PORT,
      overall: {
        queries: results.length,
        success: success.length,
        errors: results.length - success.length,
        precisionAtK: overallPrecision,
        recallAtK: overallRecall,
      },
      results,
    };

    const stamp = new Date().toISOString().split("T")[0];
    const jsonPath = join(ASSAY_OUTPUT_DIR, `kiri-${RELEASE_VERSION}-base-${stamp}.json`);
    writeFileSync(jsonPath, JSON.stringify(snapshot, null, 2));

    const mdLines = [
      `# KIRI ${RELEASE_VERSION} Baseline`,
      "",
      `- Dataset: ${dataset.name ?? "kiri-golden"} (${dataset.version ?? "unknown"})`,
      `- Release: kiri-server@${RELEASE_VERSION}`,
      `- Date: ${stamp}`,
      `- Queries: ${results.length} (success: ${success.length}, errors: ${results.length - success.length})`,
      `- Avg P@${limit}: ${(overallPrecision * 100).toFixed(2)}%`,
      `- Avg R@${limit}: ${(overallRecall * 100).toFixed(2)}%`,
      "",
      "| Query | Tool | Status | P@K | Latency (ms) |",
      "|-------|------|--------|-----|--------------|",
      ...results.map((r) => {
        const precision = r.precisionAtK !== null ? (r.precisionAtK * 100).toFixed(1) + "%" : "-";
        return `| ${r.id} | ${r.tool} | ${r.status} | ${precision} | ${r.latencyMs.toFixed(0)} |`;
      }),
    ];
    const mdPath = join(ASSAY_OUTPUT_DIR, `kiri-${RELEASE_VERSION}-base-${stamp}.md`);
    writeFileSync(mdPath, mdLines.join("\n"));

    console.log(`\n📄 Saved JSON: ${jsonPath}`);
    console.log(`📄 Saved Markdown: ${mdPath}`);
  } finally {
    console.log("\n🛑 Stopping release server...");
    stopServer(server);
    removeCleanup(cleanupHandlers);
  }
}

main().catch((error) => {
  console.error("\n❌ Failed to collect base data:", error);
  process.exit(1);
});
