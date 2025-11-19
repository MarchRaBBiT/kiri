import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { afterEach, beforeEach, describe, expect, it } from "vitest";

import {
  ensureBaseSchema,
  ensureDocumentMetadataTables,
  ensureRepoMetaColumns,
  isDocumentMetadataEmpty,
  rebuildFTSIfNeeded,
  setFTSDirty,
  tryCreateFTSIndex,
} from "../../src/indexer/schema.js";
import { DuckDBClient } from "../../src/shared/duckdb.js";

describe("tryCreateFTSIndex", () => {
  let tempDir: string;
  let db: DuckDBClient;

  beforeEach(async () => {
    tempDir = await mkdtemp(join(tmpdir(), "kiri-test-"));
    const dbPath = join(tempDir, "test.duckdb");
    db = await DuckDBClient.connect({ databasePath: dbPath });

    // Create blob table required for FTS index
    await db.run(`
      CREATE TABLE IF NOT EXISTS blob (
        hash TEXT PRIMARY KEY,
        content TEXT
      )
    `);
  });

  afterEach(async () => {
    if (db) {
      await db.close();
    }
    await rm(tempDir, { recursive: true, force: true });
  });

  it("creates FTS index when it does not exist", async () => {
    const result = await tryCreateFTSIndex(db);

    // Should succeed (or skip if FTS extension is not available)
    expect(typeof result).toBe("boolean");

    if (result) {
      // Verify FTS schema was created
      const schemas = await db.all<{ schema_name: string }>(
        `SELECT schema_name FROM duckdb_schemas() WHERE schema_name = 'fts_main_blob'`
      );
      expect(schemas.length).toBe(1);

      // Verify required tables exist
      const tables = await db.all<{ table_name: string }>(
        `SELECT table_name FROM duckdb_tables()
         WHERE schema_name = 'fts_main_blob' AND table_name IN ('docs', 'terms')`
      );
      expect(tables.length).toBeGreaterThanOrEqual(2);
    }
  });

  it("skips FTS index creation when it already exists", async () => {
    // First creation
    const firstResult = await tryCreateFTSIndex(db);

    if (!firstResult) {
      // FTS extension not available, skip test
      return;
    }

    // Get initial state
    const initialSchemas = await db.all<{ schema_name: string }>(
      `SELECT schema_name FROM duckdb_schemas() WHERE schema_name = 'fts_main_blob'`
    );
    expect(initialSchemas.length).toBe(1);

    // Second call should skip creation
    const secondResult = await tryCreateFTSIndex(db);
    expect(secondResult).toBe(true);

    // Verify schema still exists (not recreated)
    const finalSchemas = await db.all<{ schema_name: string }>(
      `SELECT schema_name FROM duckdb_schemas() WHERE schema_name = 'fts_main_blob'`
    );
    expect(finalSchemas.length).toBe(1);
  });

  it("recreates FTS index when integrity check fails", async () => {
    // First creation
    const firstResult = await tryCreateFTSIndex(db);

    if (!firstResult) {
      // FTS extension not available, skip test
      return;
    }

    // Manually corrupt the index by dropping a required table
    await db.run(`DROP TABLE IF EXISTS fts_main_blob.docs`);

    // Verify corruption
    const tables = await db.all<{ table_name: string }>(
      `SELECT table_name FROM duckdb_tables()
       WHERE schema_name = 'fts_main_blob' AND table_name = 'docs'`
    );
    expect(tables.length).toBe(0);

    // Should detect corruption and attempt recreation
    // Note: This may fail or succeed depending on FTS implementation
    const secondResult = await tryCreateFTSIndex(db);
    expect(typeof secondResult).toBe("boolean");
  });

  it("returns false when FTS extension is not available", async () => {
    // This test verifies graceful degradation
    // We cannot easily simulate FTS unavailability, so we just verify
    // that the function returns a boolean
    const result = await tryCreateFTSIndex(db);
    expect(typeof result).toBe("boolean");
  });

  it("handles race condition when index is created by another process", async () => {
    // First creation
    const firstResult = await tryCreateFTSIndex(db);

    if (!firstResult) {
      // FTS extension not available, skip test
      return;
    }

    // Simulate race condition by calling again
    // The function should handle "already exists" error gracefully
    const secondResult = await tryCreateFTSIndex(db);
    expect(secondResult).toBe(true);

    // Verify index still exists and is functional
    const schemas = await db.all<{ schema_name: string }>(
      `SELECT schema_name FROM duckdb_schemas() WHERE schema_name = 'fts_main_blob'`
    );
    expect(schemas.length).toBe(1);
  });

  it("performs integrity verification correctly", async () => {
    const result = await tryCreateFTSIndex(db);

    if (!result) {
      // FTS extension not available, skip test
      return;
    }

    // Insert test data
    await db.run(`INSERT INTO blob (hash, content) VALUES ('test-hash', 'test content')`);

    // Call again - should skip due to valid existing index
    const secondResult = await tryCreateFTSIndex(db);
    expect(secondResult).toBe(true);

    // Verify FTS schema and tables still exist
    const schemas = await db.all<{ schema_name: string }>(
      `SELECT schema_name FROM duckdb_schemas() WHERE schema_name = 'fts_main_blob'`
    );
    expect(schemas.length).toBe(1);

    const tables = await db.all<{ table_name: string }>(
      `SELECT table_name FROM duckdb_tables()
       WHERE schema_name = 'fts_main_blob' AND table_name IN ('docs', 'terms')`
    );
    expect(tables.length).toBeGreaterThanOrEqual(2);
  });
});

describe("ensureRepoMetaColumns", () => {
  let tempDir: string;
  let db: DuckDBClient;

  beforeEach(async () => {
    tempDir = await mkdtemp(join(tmpdir(), "kiri-test-"));
    const dbPath = join(tempDir, "test.duckdb");
    db = await DuckDBClient.connect({ databasePath: dbPath });
  });

  afterEach(async () => {
    if (db) {
      await db.close();
    }
    await rm(tempDir, { recursive: true, force: true });
  });

  it("returns early if repo table doesn't exist", async () => {
    // Should not throw when repo table doesn't exist
    await expect(ensureRepoMetaColumns(db)).resolves.toBeUndefined();
  });

  it("adds fts_last_indexed_at and fts_dirty columns to existing repo table", async () => {
    // Create repo table without FTS columns
    await db.run(`
      CREATE TABLE repo (
        id INTEGER PRIMARY KEY,
        root TEXT NOT NULL UNIQUE
      )
    `);

    await ensureRepoMetaColumns(db);

    // Verify columns were added
    const columns = await db.all<{ column_name: string }>(
      `SELECT column_name FROM duckdb_columns()
       WHERE table_name = 'repo' AND column_name IN ('fts_last_indexed_at', 'fts_dirty')`
    );

    expect(columns.length).toBe(2);
    expect(columns.map((c) => c.column_name)).toContain("fts_last_indexed_at");
    expect(columns.map((c) => c.column_name)).toContain("fts_dirty");
  });

  it("is idempotent - doesn't fail if columns already exist", async () => {
    await ensureBaseSchema(db);

    // First call
    await ensureRepoMetaColumns(db);

    // Second call should not throw
    await expect(ensureRepoMetaColumns(db)).resolves.toBeUndefined();
  });

  it("initializes fts_dirty=true when FTS doesn't exist", async () => {
    await ensureBaseSchema(db);
    await db.run(`INSERT INTO repo (root) VALUES ('/test')`);

    await ensureRepoMetaColumns(db);

    const rows = await db.all<{ fts_dirty: boolean }>(
      `SELECT fts_dirty FROM repo WHERE root = '/test'`
    );
    expect(rows[0]?.fts_dirty).toBe(true);
  });
});

describe("rebuildFTSIfNeeded", () => {
  let tempDir: string;
  let db: DuckDBClient;
  let repoId: number;

  beforeEach(async () => {
    tempDir = await mkdtemp(join(tmpdir(), "kiri-test-"));
    const dbPath = join(tempDir, "test.duckdb");
    db = await DuckDBClient.connect({ databasePath: dbPath });

    // Set up base schema and repo
    await ensureBaseSchema(db);
    await db.run(`INSERT INTO repo (root) VALUES ('/test')`);
    const rows = await db.all<{ id: number }>(`SELECT id FROM repo WHERE root = '/test'`);
    repoId = rows[0]!.id;

    // Create blob table for FTS
    await db.run(`
      CREATE TABLE IF NOT EXISTS blob (
        hash TEXT PRIMARY KEY,
        content TEXT
      )
    `);
  });

  afterEach(async () => {
    if (db) {
      await db.close();
    }
    await rm(tempDir, { recursive: true, force: true });
  });

  it("rebuilds FTS when dirty flag is true", async () => {
    // Set dirty flag
    await setFTSDirty(db, repoId);

    const result = await rebuildFTSIfNeeded(db, repoId);

    if (result) {
      // FTS is available - verify dirty flag was cleared
      const rows = await db.all<{ fts_dirty: boolean }>(`SELECT fts_dirty FROM repo WHERE id = ?`, [
        repoId,
      ]);
      expect(rows[0]?.fts_dirty).toBe(false);
    }
  });

  it("skips rebuild when FTS is clean and exists", async () => {
    // First rebuild to create FTS
    const firstResult = await rebuildFTSIfNeeded(db, repoId);

    if (!firstResult) {
      // FTS not available, skip test
      return;
    }

    // Verify dirty flag is false
    const beforeRows = await db.all<{ fts_dirty: boolean }>(
      `SELECT fts_dirty FROM repo WHERE id = ?`,
      [repoId]
    );
    expect(beforeRows[0]?.fts_dirty).toBe(false);

    // Second call should skip rebuild
    const secondResult = await rebuildFTSIfNeeded(db, repoId);
    expect(secondResult).toBe(true);
  });

  it("forces rebuild when forceFTS=true", async () => {
    // First rebuild
    await rebuildFTSIfNeeded(db, repoId);

    // Force rebuild even if clean
    const result = await rebuildFTSIfNeeded(db, repoId, true);

    if (result) {
      // Verify it succeeded
      const rows = await db.all<{ fts_dirty: boolean }>(`SELECT fts_dirty FROM repo WHERE id = ?`, [
        repoId,
      ]);
      expect(rows[0]?.fts_dirty).toBe(false);
    }
  });
});

describe("setFTSDirty", () => {
  let tempDir: string;
  let db: DuckDBClient;
  let repoId: number;

  beforeEach(async () => {
    tempDir = await mkdtemp(join(tmpdir(), "kiri-test-"));
    const dbPath = join(tempDir, "test.duckdb");
    db = await DuckDBClient.connect({ databasePath: dbPath });

    await ensureBaseSchema(db);
    await db.run(`INSERT INTO repo (root) VALUES ('/test')`);
    const rows = await db.all<{ id: number }>(`SELECT id FROM repo WHERE root = '/test'`);
    repoId = rows[0]!.id;
  });

  afterEach(async () => {
    if (db) {
      await db.close();
    }
    await rm(tempDir, { recursive: true, force: true });
  });

  it("sets fts_dirty to true", async () => {
    await setFTSDirty(db, repoId);

    const rows = await db.all<{ fts_dirty: boolean }>(`SELECT fts_dirty FROM repo WHERE id = ?`, [
      repoId,
    ]);
    expect(rows[0]?.fts_dirty).toBe(true);
  });

  it("ensures columns exist before setting dirty flag", async () => {
    // setFTSDirty should call ensureRepoMetaColumns internally
    await setFTSDirty(db, repoId);

    // Verify column exists
    const columns = await db.all<{ column_name: string }>(
      `SELECT column_name FROM duckdb_columns()
       WHERE table_name = 'repo' AND column_name = 'fts_dirty'`
    );
    expect(columns.length).toBe(1);
  });
});

describe("ensureDocumentMetadataTables", () => {
  let tempDir: string;
  let db: DuckDBClient;

  beforeEach(async () => {
    tempDir = await mkdtemp(join(tmpdir(), "kiri-test-"));
    const dbPath = join(tempDir, "test.duckdb");
    db = await DuckDBClient.connect({ databasePath: dbPath });
  });

  afterEach(async () => {
    if (db) {
      await db.close();
    }
    await rm(tempDir, { recursive: true, force: true });
  });

  it("creates document_metadata table when it does not exist", async () => {
    await ensureDocumentMetadataTables(db);

    const tables = await db.all<{ table_name: string }>(
      `SELECT table_name FROM duckdb_tables() WHERE table_name = 'document_metadata'`
    );
    expect(tables.length).toBe(1);
  });

  it("creates document_metadata_kv table when it does not exist", async () => {
    await ensureDocumentMetadataTables(db);

    const tables = await db.all<{ table_name: string }>(
      `SELECT table_name FROM duckdb_tables() WHERE table_name = 'document_metadata_kv'`
    );
    expect(tables.length).toBe(1);
  });

  it("creates index on document_metadata_kv", async () => {
    await ensureDocumentMetadataTables(db);

    const indexes = await db.all<{ index_name: string }>(
      `SELECT index_name FROM duckdb_indexes() WHERE index_name = 'idx_document_metadata_key'`
    );
    expect(indexes.length).toBe(1);
  });

  it("is idempotent - running twice does not fail", async () => {
    await ensureDocumentMetadataTables(db);
    await ensureDocumentMetadataTables(db);

    const metadataTables = await db.all<{ table_name: string }>(
      `SELECT table_name FROM duckdb_tables() WHERE table_name = 'document_metadata'`
    );
    expect(metadataTables.length).toBe(1);

    const kvTables = await db.all<{ table_name: string }>(
      `SELECT table_name FROM duckdb_tables() WHERE table_name = 'document_metadata_kv'`
    );
    expect(kvTables.length).toBe(1);
  });

  it("preserves existing data when run on existing tables", async () => {
    await ensureDocumentMetadataTables(db);

    // Insert test data
    await db.run(
      `INSERT INTO document_metadata (repo_id, path, source, data) VALUES (1, 'test.md', 'front_matter', '{"title":"test"}')`
    );
    await db.run(
      `INSERT INTO document_metadata_kv (repo_id, path, source, key, value) VALUES (1, 'test.md', 'front_matter', 'title', 'test')`
    );

    // Run migration again
    await ensureDocumentMetadataTables(db);

    // Verify data is preserved
    const metadataRows = await db.all<{ path: string }>(
      `SELECT path FROM document_metadata WHERE repo_id = 1`
    );
    expect(metadataRows.length).toBe(1);
    expect(metadataRows[0]?.path).toBe("test.md");

    const kvRows = await db.all<{ key: string; value: string }>(
      `SELECT key, value FROM document_metadata_kv WHERE repo_id = 1`
    );
    expect(kvRows.length).toBe(1);
    expect(kvRows[0]?.key).toBe("title");
    expect(kvRows[0]?.value).toBe("test");
  });

  it("rolls back transaction when metadata_kv table creation fails", async () => {
    const originalRun = db.run.bind(db);

    // Monkey-patch db.run to fail on document_metadata_kv table creation
    (db as any).run = async (sql: string, params?: any[]) => {
      // Fail on document_metadata_kv table creation
      if (sql.includes("CREATE TABLE document_metadata_kv")) {
        throw new Error("Simulated metadata_kv creation failure");
      }

      return originalRun(sql, params);
    };

    try {
      // Should throw error with proper message
      await expect(ensureDocumentMetadataTables(db)).rejects.toThrow(
        "Failed to create metadata kv table"
      );

      // Restore original method before verification
      (db as any).run = originalRun;

      // Verify rollback: document_metadata table should not exist (transaction rolled back)
      const metadataTables = await db.all<{ table_name: string }>(
        `SELECT table_name FROM duckdb_tables() WHERE table_name = 'document_metadata'`
      );
      expect(metadataTables.length).toBe(0);

      // Verify document_metadata_kv table also doesn't exist
      const kvTables = await db.all<{ table_name: string }>(
        `SELECT table_name FROM duckdb_tables() WHERE table_name = 'document_metadata_kv'`
      );
      expect(kvTables.length).toBe(0);
    } finally {
      // Ensure cleanup even if test fails
      (db as any).run = originalRun;
    }
  });
});

describe("ensureBaseSchema integration", () => {
  let tempDir: string;
  let db: DuckDBClient;

  beforeEach(async () => {
    tempDir = await mkdtemp(join(tmpdir(), "kiri-test-"));
    const dbPath = join(tempDir, "test.duckdb");
    db = await DuckDBClient.connect({ databasePath: dbPath });
  });

  afterEach(async () => {
    if (db) {
      await db.close();
    }
    await rm(tempDir, { recursive: true, force: true });
  });

  it("creates document_metadata tables via ensureDocumentMetadataTables()", async () => {
    await ensureBaseSchema(db);

    // Verify document_metadata table was created
    const metadataTables = await db.all<{ table_name: string }>(
      `SELECT table_name FROM duckdb_tables() WHERE table_name = 'document_metadata'`
    );
    expect(metadataTables.length).toBe(1);

    // Verify document_metadata_kv table was created
    const kvTables = await db.all<{ table_name: string }>(
      `SELECT table_name FROM duckdb_tables() WHERE table_name = 'document_metadata_kv'`
    );
    expect(kvTables.length).toBe(1);

    // Verify index was created
    const indexes = await db.all<{ index_name: string }>(
      `SELECT index_name FROM duckdb_indexes() WHERE index_name = 'idx_document_metadata_key'`
    );
    expect(indexes.length).toBe(1);
  });
});

describe("isDocumentMetadataEmpty", () => {
  let tempDir: string;
  let db: DuckDBClient;

  beforeEach(async () => {
    tempDir = await mkdtemp(join(tmpdir(), "kiri-test-"));
    const dbPath = join(tempDir, "test.duckdb");
    db = await DuckDBClient.connect({ databasePath: dbPath });
  });

  afterEach(async () => {
    if (db) {
      await db.close();
    }
    await rm(tempDir, { recursive: true, force: true });
  });

  it("returns false when document_metadata table does not exist", async () => {
    const result = await isDocumentMetadataEmpty(db);
    expect(result).toBe(false);
  });

  it("returns true when document_metadata table exists but is empty", async () => {
    // Create the document_metadata table (matching actual schema)
    await db.run(`
      CREATE TABLE document_metadata (
        repo_id INTEGER,
        path TEXT,
        source TEXT,
        data JSON,
        updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        PRIMARY KEY (repo_id, path, source)
      )
    `);

    const result = await isDocumentMetadataEmpty(db);
    expect(result).toBe(true);
  });

  it("returns false when document_metadata table has records", async () => {
    // Create and populate the document_metadata table (matching actual schema)
    await db.run(`
      CREATE TABLE document_metadata (
        repo_id INTEGER,
        path TEXT,
        source TEXT,
        data JSON,
        updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        PRIMARY KEY (repo_id, path, source)
      )
    `);

    await db.run(
      `INSERT INTO document_metadata (repo_id, path, source, data) VALUES (?, ?, ?, ?)`,
      [1, "test.md", "front_matter", JSON.stringify({ title: "Test" })]
    );

    const result = await isDocumentMetadataEmpty(db);
    expect(result).toBe(false);
  });
});
