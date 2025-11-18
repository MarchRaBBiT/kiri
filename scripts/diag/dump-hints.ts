import { writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import process from "node:process";

import { DuckDBClient } from "../../src/shared/duckdb.js";
import { normalizeRepoPath } from "../../src/shared/utils/path.js";

interface DumpArgs {
  databasePath: string;
  outPath?: string;
  repoRoot?: string;
  limit: number;
}

function parseArgs(argv: string[]): DumpArgs {
  let databasePath: string | undefined;
  let outPath: string | undefined;
  let repoRoot: string | undefined;
  let limit = 5000;
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--db") {
      databasePath = argv[++i];
    } else if (arg === "--out") {
      outPath = argv[++i];
    } else if (arg === "--repo") {
      repoRoot = argv[++i];
    } else if (arg === "--limit") {
      const value = Number.parseInt(argv[++i] ?? "", 10);
      if (Number.isFinite(value) && value > 0) {
        limit = value;
      }
    }
  }
  if (!databasePath) {
    throw new Error("dump-hints requires --db <path> argument");
  }
  const result: DumpArgs = { databasePath, limit };
  if (outPath !== undefined) {
    result.outPath = outPath;
  }
  if (repoRoot !== undefined) {
    result.repoRoot = repoRoot;
  }
  return result;
}

export async function main(argv = process.argv.slice(2)): Promise<void> {
  const args = parseArgs(argv);
  const db = await DuckDBClient.connect({
    databasePath: args.databasePath,
    ensureDirectory: false,
  });
  try {
    let repoId: number | null = null;
    if (args.repoRoot) {
      const normalizedRepoRoot = normalizeRepoPath(resolve(args.repoRoot));
      const repoRows = await db.all<{ id: number }>(
        `SELECT id FROM repo WHERE root = ? OR normalized_root = ? LIMIT 1`,
        [normalizedRepoRoot, normalizedRepoRoot]
      );
      if (repoRows.length === 0) {
        throw new Error(`Repository not found for root: ${normalizedRepoRoot}`);
      }
      repoId = repoRows[0]!.id;
    }

    const rows = await db.all<{
      repo_id: number;
      root: string | null;
      hint_value: string;
      expansion_kind: string;
      target_path: string | null;
      payload: unknown;
      created_at: string;
    }>(
      `
        SELECT he.repo_id,
               r.root,
               he.hint_value,
               he.expansion_kind,
               he.target_path,
               he.payload,
               he.created_at
        FROM hint_expansion he
        LEFT JOIN repo r ON r.id = he.repo_id
        WHERE (? IS NULL OR he.repo_id = ?)
        ORDER BY he.created_at DESC
        LIMIT ?
      `,
      [repoId, repoId, args.limit]
    );

    const serialized = JSON.stringify(rows, null, 2);
    if (args.outPath) {
      await writeFile(args.outPath, `${serialized}\n`, "utf8");
      console.info(`Hint expansion log written to ${args.outPath} (${rows.length} rows).`);
    } else {
      console.info(serialized);
    }
  } finally {
    await db.close();
  }
}

const executedDirectly =
  typeof process.argv[1] === "string" && new URL(import.meta.url).pathname === process.argv[1];

if (executedDirectly) {
  main().catch((error) => {
    console.error("Failed to dump hint expansions:", error);
    process.exitCode = 1;
  });
}
