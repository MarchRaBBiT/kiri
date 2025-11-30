import {
  ensureBaseSchema,
  ensureDocumentMetadataTables,
  ensureRepoMetaColumns,
} from "../../src/indexer/schema.js";
import { DuckDBClient } from "../../src/shared/duckdb.js";

import { createTempDbPath } from "./db-setup.js";
import {
  buildInsertStatement,
  createDocumentMetadataRecord,
  createFileRecord,
} from "./fixtures.js";
import { createTempRepo } from "./test-repo.js";

/**
 * Options for creating migration test scenarios
 */
export interface MigrationScenarioOptions {
  /** Whether to include document_metadata tables (simulates migrated state) */
  withMetadata?: boolean;
  /** Content for the test repository */
  repoContent?: Record<string, string>;
}

/**
 * Temporary repository handle
 */
export interface TempRepo {
  path: string;
  cleanup: () => Promise<void>;
}

/**
 * Temporary database handle
 */
export interface TempDb {
  path: string;
  cleanup: () => Promise<void>;
}

/**
 * Create a migration test scenario with pre-configured database state
 *
 * @param options Configuration options for the test scenario
 * @returns Object with repo, db, and repoId
 */
export async function createMigrationTestScenario(options: MigrationScenarioOptions = {}): Promise<{
  repo: TempRepo;
  db: TempDb;
  repoId: number;
}> {
  const repoContent = options.repoContent ?? {
    "docs/README.md": "---\ntitle: Test\n---\n# Hello\n",
  };

  const repo = await createTempRepo(repoContent);
  const db = await createTempDbPath();

  const dbClient = await DuckDBClient.connect({ databasePath: db.path });

  try {
    // Create base schema (always needed)
    await ensureBaseSchema(dbClient);
    await ensureRepoMetaColumns(dbClient);

    // Optionally create document_metadata tables (simulates migrated state)
    if (options.withMetadata) {
      await ensureDocumentMetadataTables(dbClient);
    }

    // Insert a file record to simulate existing indexed data
    await dbClient.run(`INSERT INTO repo (root) VALUES (?)`, [repo.path]);
    const repoResult = await dbClient.all<{ id: number }>(`SELECT id FROM repo WHERE root = ?`, [
      repo.path,
    ]);
    const repoId = repoResult[0]?.id;

    if (!repoId) {
      throw new Error("Failed to create repo record");
    }

    // Use fixture factory to create file record (maintains consistency with schema changes)
    const fileRecord = createFileRecord(repoId);
    const fileInsert = buildInsertStatement("file", fileRecord);
    await dbClient.run(fileInsert.sql, fileInsert.values);

    // If metadata tables exist, populate them to simulate migrated state
    if (options.withMetadata) {
      const metadataRecord = createDocumentMetadataRecord(repoId);
      const metadataInsert = buildInsertStatement("document_metadata", metadataRecord);
      await dbClient.run(metadataInsert.sql, metadataInsert.values);
    }

    return { repo, db, repoId };
  } finally {
    await dbClient.close();
  }
}
