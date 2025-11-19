import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { describe, expect, it } from "vitest";

import { ensureDatabaseIndexed } from "../../src/server/indexBootstrap.js";
import { createTempRepo } from "../helpers/test-repo.js";

async function createTempDbPath(): Promise<{ path: string; cleanup: () => Promise<void> }> {
  const dir = await mkdtemp(join(tmpdir(), "kiri-bootstrap-db-"));
  const dbPath = join(dir, "index.duckdb");
  return {
    path: dbPath,
    cleanup: async () => {
      await rm(dir, { recursive: true, force: true });
    },
  };
}

describe("ensureDatabaseIndexed", () => {
  it("indexes a missing database and releases the lock for subsequent runs", async () => {
    const repo = await createTempRepo({
      "src/index.ts": "console.log('bootstrap test');\n",
    });
    const db = await createTempDbPath();

    try {
      const firstRun = await ensureDatabaseIndexed(repo.path, db.path, false, true);
      expect(firstRun).toBe(true);

      // Second run should detect the existing DB and skip reindex without hitting lock errors
      const secondRun = await ensureDatabaseIndexed(repo.path, db.path, false, false);
      expect(secondRun).toBe(true);
    } finally {
      await repo.cleanup();
      await db.cleanup();
    }
  });

  it("detects migration and triggers reindex when files exist but metadata is empty", async () => {
    const { DuckDBClient } = await import("../../src/shared/duckdb.js");
    const { ensureBaseSchema, ensureRepoMetaColumns } = await import("../../src/indexer/schema.js");

    const repo = await createTempRepo({
      "docs/README.md": "---\ntitle: Test\n---\n# Hello\n",
    });
    const db = await createTempDbPath();

    try {
      // Step 1: Create a database with files but without document_metadata tables (simulates old version)
      const dbClient = await DuckDBClient.connect({ databasePath: db.path });
      await ensureBaseSchema(dbClient);
      await ensureRepoMetaColumns(dbClient);

      // Insert a file record to simulate existing indexed data
      await dbClient.run(`INSERT INTO repo (root) VALUES (?)`, [repo.path]);
      const repoResult = await dbClient.all<{ id: number }>(`SELECT id FROM repo WHERE root = ?`, [
        repo.path,
      ]);
      const repoId = repoResult[0]?.id;
      expect(repoId).toBeDefined();

      await dbClient.run(
        `INSERT INTO file (repo_id, path, blob_hash, ext, lang, is_binary, mtime) VALUES (?, ?, ?, ?, ?, ?, ?)`,
        [repoId, "docs/README.md", "test-hash", ".md", "markdown", false, new Date().toISOString()]
      );
      await dbClient.close();

      // Step 2: Run ensureDatabaseIndexed - should detect migration and trigger reindex
      const result = await ensureDatabaseIndexed(repo.path, db.path, false, false);
      expect(result).toBe(true);

      // Step 3: Verify document_metadata tables were created and populated
      const dbClient2 = await DuckDBClient.connect({ databasePath: db.path });
      const metadataTables = await dbClient2.all<{ table_name: string }>(
        `SELECT table_name FROM duckdb_tables() WHERE table_name = 'document_metadata'`
      );
      expect(metadataTables.length).toBe(1);

      // Verify metadata was extracted (frontmatter should be captured)
      const metadataRecords = await dbClient2.all<{ count: number }>(
        `SELECT COUNT(*) as count FROM document_metadata`
      );
      expect(metadataRecords[0]?.count).toBeGreaterThan(0);

      await dbClient2.close();
    } finally {
      await repo.cleanup();
      await db.cleanup();
    }
  });
});
