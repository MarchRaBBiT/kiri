import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { DuckDBClient } from "../../src/shared/duckdb.js";

/**
 * Create a temporary DuckDB database for testing
 *
 * @returns Object with db instance, temp directory path, and cleanup function
 */
export async function createTestDb(): Promise<{
  db: DuckDBClient;
  tempDir: string;
  dbPath: string;
  cleanup: () => Promise<void>;
}> {
  const tempDir = await mkdtemp(join(tmpdir(), "kiri-test-"));
  const dbPath = join(tempDir, "test.duckdb");
  const db = await DuckDBClient.connect({ databasePath: dbPath });

  return {
    db,
    tempDir,
    dbPath,
    cleanup: async () => {
      await db.close();
      await rm(tempDir, { recursive: true, force: true });
    },
  };
}

/**
 * Create a temporary database path (without connecting)
 * Useful for tests that need to control DB connection lifecycle
 *
 * @returns Object with path and cleanup function
 */
export async function createTempDbPath(): Promise<{
  path: string;
  cleanup: () => Promise<void>;
}> {
  const dir = await mkdtemp(join(tmpdir(), "kiri-bootstrap-db-"));
  const dbPath = join(dir, "index.duckdb");
  return {
    path: dbPath,
    cleanup: async () => {
      await rm(dir, { recursive: true, force: true });
    },
  };
}
