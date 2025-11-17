import process from "node:process";
import { resolve } from "node:path";

import { DuckDBClient } from "../../src/shared/duckdb.js";
import { normalizeRepoPath } from "../../src/shared/utils/path.js";

interface BuildArgs {
  databasePath: string;
  repoRoot: string;
  minFreq: number;
}

function parseArgs(argv: string[]): BuildArgs {
  let databasePath: string | undefined;
  let repoRoot: string | undefined;
  let minFreq = 1;
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--db") {
      databasePath = argv[++i];
    } else if (arg === "--repo") {
      repoRoot = argv[++i];
    } else if (arg === "--min-freq") {
      const value = Number.parseInt(argv[++i] ?? "", 10);
      if (Number.isFinite(value) && value >= 1) {
        minFreq = value;
      }
    }
  }
  if (!databasePath || !repoRoot) {
    throw new Error("build-hint-dictionary requires --db <path> and --repo <root>");
  }
  return { databasePath, repoRoot, minFreq };
}

export async function main(argv = process.argv.slice(2)): Promise<void> {
  const args = parseArgs(argv);
  const normalizedRepoRoot = normalizeRepoPath(resolve(args.repoRoot));
  const db = await DuckDBClient.connect({
    databasePath: args.databasePath,
    ensureDirectory: false,
  });
  try {
    const repoRows = await db.all<{ id: number }>(
      `SELECT id FROM repo WHERE root = ? OR normalized_root = ? LIMIT 1`,
      [normalizedRepoRoot, normalizedRepoRoot]
    );
    if (repoRows.length === 0) {
      throw new Error(`Repository not found for root: ${normalizedRepoRoot}`);
    }
    const repoId = repoRows[0]!.id;

    await db.run(`DELETE FROM hint_dictionary WHERE repo_id = ?`, [repoId]);

    await db.run(
      `
        INSERT INTO hint_dictionary (repo_id, hint_value, target_path, freq, updated_at)
        SELECT ?, hint_value, target_path, cnt, CURRENT_TIMESTAMP
        FROM (
          SELECT hint_value,
                 target_path,
                 COUNT(*) AS cnt
          FROM hint_expansion
          WHERE repo_id = ?
            AND target_path IS NOT NULL
          GROUP BY hint_value, target_path
        )
        WHERE cnt >= ?
      `,
      [repoId, repoId, args.minFreq]
    );

    console.info(
      `Hint dictionary rebuilt for repo_id=${repoId} (root=${normalizedRepoRoot}) with min_freq=${args.minFreq}.`
    );
  } finally {
    await db.close();
  }
}

const executedDirectly =
  typeof process.argv[1] === "string" && new URL(import.meta.url).pathname === process.argv[1];

if (executedDirectly) {
  main().catch((error) => {
    console.error("Failed to build hint dictionary:", error);
    process.exitCode = 1;
  });
}
