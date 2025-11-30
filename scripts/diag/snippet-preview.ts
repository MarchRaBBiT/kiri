import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import process from "node:process";

import yaml from "yaml";

import { DuckDBClient } from "../../src/shared/duckdb.js";

interface CliOptions {
  datasetPath: string;
  repoRoot: string;
  dbPath: string;
  maxLines: number;
}

interface DatasetFile {
  queries?: Array<{
    id?: string;
    metadata?: {
      expected?: unknown;
    };
  }>;
  expected?: Array<{
    id?: string;
    reference?: {
      paths?: unknown;
    };
  }>;
}

interface PathUsage {
  queryIds: Set<string>;
}

interface SnippetRow {
  path: string;
  start_line: number;
  end_line: number;
  content: string | null;
}

function parseCliArgs(argv: string[]): CliOptions {
  const options: CliOptions = {
    datasetPath: "datasets/kiri-ab.yaml",
    repoRoot: ".",
    dbPath: "var/index.duckdb",
    maxLines: 8,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (!arg) break;
    switch (arg) {
      case "--dataset": {
        const value = argv[i + 1];
        if (!value) throw new Error("--dataset requires a path");
        options.datasetPath = value;
        i += 1;
        break;
      }
      case "--repo": {
        const value = argv[i + 1];
        if (!value) throw new Error("--repo requires a path");
        options.repoRoot = value;
        i += 1;
        break;
      }
      case "--db": {
        const value = argv[i + 1];
        if (!value) throw new Error("--db requires a path");
        options.dbPath = value;
        i += 1;
        break;
      }
      case "--max-lines": {
        const value = argv[i + 1];
        if (!value) throw new Error("--max-lines requires a numeric value");
        const parsed = Number.parseInt(value, 10);
        if (!Number.isFinite(parsed) || parsed <= 0) {
          throw new Error("--max-lines must be a positive integer");
        }
        options.maxLines = parsed;
        i += 1;
        break;
      }
      default:
        if (arg.startsWith("--")) {
          throw new Error(`Unknown option: ${arg}`);
        }
    }
  }

  return options;
}

function collectPaths(dataset: DatasetFile): Map<string, PathUsage> {
  const map = new Map<string, PathUsage>();

  function addPath(path: string, queryId: string): void {
    if (!path) return;
    if (!map.has(path)) {
      map.set(path, { queryIds: new Set<string>() });
    }
    map.get(path)!.queryIds.add(queryId);
  }

  function extractEntries(entry: unknown): string[] {
    if (!entry) return [];
    if (typeof entry === "string") return [entry];
    if (Array.isArray(entry)) {
      return entry.flatMap((value) => extractEntries(value));
    }
    if (typeof entry === "object") {
      const record = entry as Record<string, unknown>;
      const paths: string[] = [];
      if (typeof record.path === "string") {
        paths.push(record.path);
      }
      if (Array.isArray(record.paths)) {
        for (const value of record.paths) {
          if (typeof value === "string") {
            paths.push(value);
          }
        }
      }
      if (record.reference && typeof record.reference === "object") {
        const { paths: referencePaths } = record.reference as { paths?: unknown };
        paths.push(...extractEntries(referencePaths));
      }
      return paths;
    }
    return [];
  }

  if (Array.isArray(dataset.queries)) {
    for (const query of dataset.queries) {
      const queryId = typeof query.id === "string" ? query.id : "unknown";
      const expected = query.metadata?.expected;
      for (const path of extractEntries(expected)) {
        addPath(path, queryId);
      }
    }
  }

  if (Array.isArray(dataset.expected)) {
    for (const entry of dataset.expected) {
      const queryId = typeof entry.id === "string" ? entry.id : "reference";
      for (const path of extractEntries(entry.reference?.paths)) {
        addPath(path, queryId);
      }
    }
  }

  return map;
}

async function resolveRepoId(db: DuckDBClient, repoRoot: string): Promise<number> {
  const rows = await db.all<{ id: number }>(
    `SELECT id FROM repo WHERE root = ? OR normalized_root = ? LIMIT 1`,
    [repoRoot, repoRoot]
  );
  if (rows.length === 0) {
    throw new Error(`Repository ${repoRoot} not found in DuckDB. Run the indexer first.`);
  }
  return rows[0]!.id;
}

async function fetchSnippets(
  db: DuckDBClient,
  repoId: number,
  paths: string[]
): Promise<Map<string, SnippetRow[]>> {
  const results = new Map<string, SnippetRow[]>();
  const CHUNK_SIZE = 20;

  for (let index = 0; index < paths.length; index += CHUNK_SIZE) {
    const chunk = paths.slice(index, index + CHUNK_SIZE);
    const placeholders = chunk.map(() => "?").join(", ");
    const rows = await db.all<SnippetRow>(
      `
        SELECT s.path, s.start_line, s.end_line, b.content
        FROM snippet s
        JOIN file f
          ON f.repo_id = s.repo_id
         AND f.path = s.path
        JOIN blob b
          ON b.hash = f.blob_hash
        WHERE s.repo_id = ?
          AND s.path IN (${placeholders})
        ORDER BY s.path, s.start_line
      `,
      [repoId, ...chunk]
    );

    for (const row of rows) {
      if (!results.has(row.path)) {
        results.set(row.path, []);
      }
      results.get(row.path)!.push(row);
    }
  }

  return results;
}

function formatSnippet(row: SnippetRow, maxLines: number): string {
  if (!row.content) {
    return "(binary file or empty content)";
  }

  const lines = row.content.split(/\r?\n/);
  const startIndex = Math.max(0, row.start_line - 1);
  const endIndex = Math.min(lines.length, row.end_line);
  const slice = lines.slice(startIndex, Math.min(endIndex, startIndex + maxLines));
  return slice.join("\n");
}

async function main(): Promise<void> {
  const options = parseCliArgs(process.argv.slice(2));
  const repoRoot = resolve(options.repoRoot);
  const datasetPath = resolve(repoRoot, options.datasetPath);
  const dbPath = resolve(repoRoot, options.dbPath);

  const datasetContent = await readFile(datasetPath, "utf-8");
  const dataset = yaml.parse(datasetContent) as DatasetFile;
  const pathMap = collectPaths(dataset);
  if (pathMap.size === 0) {
    console.info("No expected paths found in dataset.");
    return;
  }

  const db = await DuckDBClient.connect({ databasePath: dbPath });
  try {
    const repoId = await resolveRepoId(db, repoRoot);
    const paths = Array.from(pathMap.keys());
    const snippetMap = await fetchSnippets(db, repoId, paths);
    const missing = paths.filter((path) => !snippetMap.has(path));

    console.info(`Dataset: ${options.datasetPath}`);
    console.info(`Repo:    ${repoRoot}`);
    console.info(`DuckDB:  ${options.dbPath}`);
    console.info("");
    console.info(`Total expected paths: ${paths.length}`);
    console.info(`Paths with snippets:  ${snippetMap.size}`);
    console.info(`Paths without data:   ${missing.length}`);
    console.info("");

    if (missing.length > 0) {
      console.info("⚠️  Paths without snippets:");
      for (const path of missing) {
        const usage = pathMap.get(path);
        console.info(
          `- ${path} (queries: ${usage ? Array.from(usage.queryIds).join(", ") : "n/a"})`
        );
      }
      console.info("");
    }

    for (const [path, rows] of snippetMap) {
      const usage = pathMap.get(path);
      console.info(
        `=== ${path} (queries: ${usage ? Array.from(usage.queryIds).join(", ") : "n/a"}) ===`
      );
      for (const row of rows) {
        console.info(`Lines ${row.start_line}-${row.end_line}`);
        console.info(formatSnippet(row, options.maxLines));
        console.info("---");
      }
      console.info("");
    }
  } finally {
    await db.close();
  }
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : String(error));
  process.exitCode = 1;
});
