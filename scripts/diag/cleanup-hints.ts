import process from "node:process";

import { DuckDBClient } from "../../src/shared/duckdb.js";

interface CleanupArgs {
  databasePath: string;
  days: number;
}

function parseArgs(argv: string[]): CleanupArgs {
  let databasePath: string | undefined;
  let days = 14;
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--db") {
      databasePath = argv[++i];
    } else if (arg === "--days") {
      const value = Number.parseInt(argv[++i] ?? "", 10);
      if (Number.isFinite(value) && value >= 1) {
        days = value;
      }
    }
  }
  if (!databasePath) {
    throw new Error("cleanup-hints requires --db <path>");
  }
  return { databasePath, days };
}

export async function main(argv = process.argv.slice(2)): Promise<void> {
  const args = parseArgs(argv);
  const db = await DuckDBClient.connect({
    databasePath: args.databasePath,
    ensureDirectory: false,
  });
  try {
    await db.run(
      `
        DELETE FROM hint_expansion
        WHERE created_at < NOW() - INTERVAL ? DAY
      `,
      [args.days]
    );
    console.info(`Deleted hint_expansion rows older than ${args.days} day(s).`);
  } finally {
    await db.close();
  }
}

const executedDirectly =
  typeof process.argv[1] === "string" && new URL(import.meta.url).pathname === process.argv[1];

if (executedDirectly) {
  main().catch((error) => {
    console.error("Failed to cleanup hint_expansion table:", error);
    process.exitCode = 1;
  });
}
