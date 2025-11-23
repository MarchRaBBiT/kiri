/**
 * Add hint_dictionary entries for schema-related terms
 * Maps "schema" keyword to schema file paths for better search relevance
 */
import { DuckDBClient } from "../src/shared/duckdb.js";

async function main() {
  const dbPath = process.argv[2] || "external/assay-kit/.kiri/index.duckdb";

  const db = await DuckDBClient.connect({
    databasePath: dbPath,
    ensureDirectory: false,
  });

  try {
    // Get repo_id for assay-kit
    const repoRows = await db.all<{ id: number }>(`SELECT id FROM repo LIMIT 1`);
    if (repoRows.length === 0) {
      throw new Error("No repository found in database");
    }
    const repoId = repoRows[0]!.id;
    console.log(`Using repo_id=${repoId}`);

    // Schema file paths to add as hint targets
    const schemaHints = [
      {
        hint: "schema",
        path: "packages/assay-kit/src/dataset/schemas/dataset.schema.ts",
        freq: 10,
      },
      { hint: "schema", path: "packages/assay-kit/src/dataset/schemas/query.schema.ts", freq: 8 },
      { hint: "schema", path: "packages/assay-kit/src/dataset/schemas/metrics.schema.ts", freq: 6 },
      {
        hint: "validation",
        path: "packages/assay-kit/src/dataset/schemas/dataset.schema.ts",
        freq: 8,
      },
      { hint: "validation", path: "packages/assay-kit/src/cli/commands/validate.ts", freq: 6 },
      { hint: "dataset", path: "packages/assay-kit/src/dataset/loader.ts", freq: 10 },
      {
        hint: "dataset",
        path: "packages/assay-kit/src/dataset/schemas/dataset.schema.ts",
        freq: 8,
      },
      { hint: "loader", path: "packages/assay-kit/src/dataset/loader.ts", freq: 10 },
    ];

    // Insert hint_dictionary entries
    for (const entry of schemaHints) {
      // Check if entry exists
      const existing = await db.all<{ cnt: number }>(
        `SELECT COUNT(*) as cnt FROM hint_dictionary
         WHERE repo_id = ? AND hint_value = ? AND target_path = ?`,
        [repoId, entry.hint, entry.path]
      );

      if (existing[0]?.cnt === 0) {
        await db.run(
          `INSERT INTO hint_dictionary (repo_id, hint_value, target_path, freq)
           VALUES (?, ?, ?, ?)`,
          [repoId, entry.hint, entry.path, entry.freq]
        );
        console.log(`Added: "${entry.hint}" → ${entry.path} (freq=${entry.freq})`);
      } else {
        await db.run(
          `UPDATE hint_dictionary SET freq = ?
           WHERE repo_id = ? AND hint_value = ? AND target_path = ?`,
          [entry.freq, repoId, entry.hint, entry.path]
        );
        console.log(`Updated: "${entry.hint}" → ${entry.path} (freq=${entry.freq})`);
      }
    }

    // Verify insertion
    const count = await db.all<{ cnt: number }>(
      `SELECT COUNT(*) as cnt FROM hint_dictionary WHERE repo_id = ?`,
      [repoId]
    );
    console.log(`\nTotal hint_dictionary entries for repo_id=${repoId}: ${count[0]?.cnt}`);

    // Show all entries
    const entries = await db.all<{ hint_value: string; target_path: string; freq: number }>(
      `SELECT hint_value, target_path, freq FROM hint_dictionary WHERE repo_id = ? ORDER BY hint_value, freq DESC`,
      [repoId]
    );
    console.log("\nAll hint_dictionary entries:");
    for (const e of entries) {
      console.log(`  "${e.hint_value}" → ${e.target_path} (freq=${e.freq})`);
    }
  } finally {
    await db.close();
  }
}

main().catch(console.error);
