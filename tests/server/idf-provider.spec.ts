/**
 * IDF Provider Tests
 *
 * @see Issue #48: Improve context_bundle stop word coverage and configurability
 * @see Phase 2: IDF-based keyword weighting
 */

import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { afterEach, beforeEach, describe, expect, it } from "vitest";

import { createIdfProvider } from "../../src/server/idf-provider.js";
import { DuckDBClient } from "../../src/shared/duckdb.js";

let db: DuckDBClient;
let tempDir: string;
let repoId: number;

beforeEach(async () => {
  tempDir = await mkdtemp(join(tmpdir(), "idf-test-"));
  const dbPath = join(tempDir, "test.duckdb");

  db = await DuckDBClient.connect({ databasePath: dbPath, ensureDirectory: true });

  // Setup basic schema
  await db.run(`
    CREATE TABLE repo (
      id INTEGER PRIMARY KEY,
      root TEXT NOT NULL
    )
  `);

  await db.run(`
    CREATE TABLE blob (
      hash TEXT PRIMARY KEY,
      content TEXT
    )
  `);

  await db.run(`
    CREATE TABLE file (
      repo_id INTEGER,
      path TEXT,
      blob_hash TEXT,
      PRIMARY KEY (repo_id, path)
    )
  `);

  // Create a test repository
  await db.run(`INSERT INTO repo (id, root) VALUES (1, '/test/repo')`);
  repoId = 1;
});

afterEach(async () => {
  await db.close();
  await rm(tempDir, { recursive: true, force: true });
});

describe("DuckDbIdfProvider", () => {
  describe("getDocumentCount", () => {
    it("returns the number of files in the repository", async () => {
      // Add test files
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'content 1')`);
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash2', 'content 2')`);
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash3', 'content 3')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file1.ts', 'hash1')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file2.ts', 'hash2')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file3.ts', 'hash3')`);

      const provider = createIdfProvider(db, repoId);
      const count = await provider.getDocumentCount();

      expect(count).toBe(3);
    });

    it("returns at least 1 for empty repository", async () => {
      const provider = createIdfProvider(db, repoId);
      const count = await provider.getDocumentCount();

      // Minimum 1 to prevent division by zero
      expect(count).toBeGreaterThanOrEqual(1);
    });

    it("caches the document count", async () => {
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'content')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file.ts', 'hash1')`);

      const provider = createIdfProvider(db, repoId);
      const count1 = await provider.getDocumentCount();

      // Add another file (should not affect cached count)
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash2', 'content 2')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file2.ts', 'hash2')`);

      const count2 = await provider.getDocumentCount();

      expect(count1).toBe(count2);
    });
  });

  describe("getDocumentFrequency", () => {
    it("returns the number of documents containing a term", async () => {
      // Create files with different content
      await db.run(
        `INSERT INTO blob (hash, content) VALUES ('hash1', 'function hello() { return true; }')`
      );
      await db.run(
        `INSERT INTO blob (hash, content) VALUES ('hash2', 'function world() { return false; }')`
      );
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash3', 'const hello = "world";')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file1.ts', 'hash1')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file2.ts', 'hash2')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file3.ts', 'hash3')`);

      const provider = createIdfProvider(db, repoId);

      // "function" appears in 2 files
      const functionDf = await provider.getDocumentFrequency("function");
      expect(functionDf).toBe(2);

      // "hello" appears in 2 files
      const helloDf = await provider.getDocumentFrequency("hello");
      expect(helloDf).toBe(2);

      // "world" appears in 2 files
      const worldDf = await provider.getDocumentFrequency("world");
      expect(worldDf).toBe(2);

      // "return" appears in 2 files
      const returnDf = await provider.getDocumentFrequency("return");
      expect(returnDf).toBe(2);

      // "const" appears in 1 file
      const constDf = await provider.getDocumentFrequency("const");
      expect(constDf).toBe(1);
    });

    it("returns 0 for terms not in any document", async () => {
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'hello world')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file.ts', 'hash1')`);

      const provider = createIdfProvider(db, repoId);
      const df = await provider.getDocumentFrequency("nonexistent");

      expect(df).toBe(0);
    });
  });

  describe("computeIdf", () => {
    it("returns higher weight for rare terms", async () => {
      // Create 10 files
      for (let i = 0; i < 10; i++) {
        const hash = `hash${i}`;
        // "common" appears in all files, "rare" appears in only one
        const content = i === 0 ? "common term rare term" : "common term";
        await db.run(`INSERT INTO blob (hash, content) VALUES (?, ?)`, [hash, content]);
        await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, ?, ?)`, [
          `file${i}.ts`,
          hash,
        ]);
      }

      const provider = createIdfProvider(db, repoId);

      const commonWeight = await provider.computeIdf("common");
      const rareWeight = await provider.computeIdf("rare");

      // Rare terms should have higher IDF weight
      expect(rareWeight).toBeGreaterThan(commonWeight);
    });

    it("returns weight in 0-1 range", async () => {
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'test content here')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file.ts', 'hash1')`);

      const provider = createIdfProvider(db, repoId);

      const weight = await provider.computeIdf("test");

      expect(weight).toBeGreaterThanOrEqual(0);
      expect(weight).toBeLessThanOrEqual(1);
    });

    it("returns max weight for OOV (out-of-vocabulary) terms", async () => {
      // Create files without the search term
      for (let i = 0; i < 5; i++) {
        await db.run(`INSERT INTO blob (hash, content) VALUES (?, ?)`, [
          `hash${i}`,
          "some content",
        ]);
        await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, ?, ?)`, [
          `file${i}.ts`,
          `hash${i}`,
        ]);
      }

      const provider = createIdfProvider(db, repoId);

      const oovWeight = await provider.computeIdf("nonexistent");

      // OOV terms should have maximum weight (close to 1.0)
      expect(oovWeight).toBeGreaterThan(0.9);
    });

    it("caches computed IDF values", async () => {
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'test content')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file.ts', 'hash1')`);

      const provider = createIdfProvider(db, repoId);

      await provider.computeIdf("test");
      expect(provider.cacheSize).toBe(1);

      await provider.computeIdf("test"); // Should hit cache
      expect(provider.cacheSize).toBe(1);

      await provider.computeIdf("content");
      expect(provider.cacheSize).toBe(2);
    });

    it("normalizes tokens before computing", async () => {
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'TEST content')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file.ts', 'hash1')`);

      const provider = createIdfProvider(db, repoId);

      const weight1 = await provider.computeIdf("test");
      const weight2 = await provider.computeIdf("TEST");
      const weight3 = await provider.computeIdf("Test");

      // All should return the same normalized weight
      expect(weight1).toBe(weight2);
      expect(weight2).toBe(weight3);
    });

    it("returns 0 for empty string", async () => {
      const provider = createIdfProvider(db, repoId);
      const weight = await provider.computeIdf("");

      expect(weight).toBe(0);
    });
  });

  describe("computeIdfBatch", () => {
    it("computes IDF for multiple terms efficiently", async () => {
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'hello world test')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file.ts', 'hash1')`);

      const provider = createIdfProvider(db, repoId);

      const weights = await provider.computeIdfBatch(["hello", "world", "test"]);

      expect(weights.size).toBe(3);
      expect(weights.has("hello")).toBe(true);
      expect(weights.has("world")).toBe(true);
      expect(weights.has("test")).toBe(true);
    });

    it("handles duplicate terms", async () => {
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'test content')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file.ts', 'hash1')`);

      const provider = createIdfProvider(db, repoId);

      const weights = await provider.computeIdfBatch(["test", "TEST", "Test"]);

      // All normalize to "test", so should have 1 entry
      expect(weights.size).toBe(1);
    });

    it("uses cache for already computed terms", async () => {
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'hello world')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file.ts', 'hash1')`);

      const provider = createIdfProvider(db, repoId);

      // Pre-compute one term
      await provider.computeIdf("hello");
      expect(provider.cacheSize).toBe(1);

      // Batch compute with one cached and one new
      const weights = await provider.computeIdfBatch(["hello", "world"]);

      expect(weights.size).toBe(2);
      expect(provider.cacheSize).toBe(2);
    });
  });

  describe("getIdf (synchronous)", () => {
    it("returns cached value if available", async () => {
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'test content')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file.ts', 'hash1')`);

      const provider = createIdfProvider(db, repoId);

      // Pre-compute and cache
      const computed = await provider.computeIdf("test");

      // Synchronous get should return cached value
      const sync = provider.getIdf("test");

      expect(sync).toBe(computed);
    });

    it("returns 1.0 for uncached terms", async () => {
      const provider = createIdfProvider(db, repoId);

      // Synchronous get without prior computation
      const sync = provider.getIdf("uncached");

      expect(sync).toBe(1.0);
    });

    it("returns 0 for empty string", async () => {
      const provider = createIdfProvider(db, repoId);
      const weight = provider.getIdf("");

      expect(weight).toBe(0);
    });
  });

  describe("clearCache", () => {
    it("clears all cached values", async () => {
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'test content')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file.ts', 'hash1')`);

      const provider = createIdfProvider(db, repoId);

      await provider.computeIdf("test");
      await provider.computeIdf("content");
      expect(provider.cacheSize).toBe(2);

      provider.clearCache();
      expect(provider.cacheSize).toBe(0);
    });

    it("forces recalculation of document count", async () => {
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash1', 'content')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file.ts', 'hash1')`);

      const provider = createIdfProvider(db, repoId);

      const count1 = await provider.getDocumentCount();
      expect(count1).toBe(1);

      // Add a new file
      await db.run(`INSERT INTO blob (hash, content) VALUES ('hash2', 'content 2')`);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, 'file2.ts', 'hash2')`);

      // Without clearing, should return cached count
      const count2 = await provider.getDocumentCount();
      expect(count2).toBe(1);

      // After clearing, should return updated count
      provider.clearCache();
      const count3 = await provider.getDocumentCount();
      expect(count3).toBe(2);
    });
  });
});

describe("IDF formula verification", () => {
  it("follows BM25-style IDF formula", async () => {
    tempDir = await mkdtemp(join(tmpdir(), "idf-formula-"));
    const dbPath = join(tempDir, "test.duckdb");
    db = await DuckDBClient.connect({ databasePath: dbPath, ensureDirectory: true });

    await db.run(`CREATE TABLE repo (id INTEGER PRIMARY KEY, root TEXT NOT NULL)`);
    await db.run(`CREATE TABLE blob (hash TEXT PRIMARY KEY, content TEXT)`);
    await db.run(
      `CREATE TABLE file (repo_id INTEGER, path TEXT, blob_hash TEXT, PRIMARY KEY (repo_id, path))`
    );
    await db.run(`INSERT INTO repo (id, root) VALUES (1, '/test')`);

    // Create 100 files
    const N = 100;
    for (let i = 0; i < N; i++) {
      // "common" appears in all files, "medium" in 50, "rare" in 10
      let content = "common";
      if (i < 50) content += " medium";
      if (i < 10) content += " rare";
      if (i < 1) content += " unique";

      await db.run(`INSERT INTO blob (hash, content) VALUES (?, ?)`, [`hash${i}`, content]);
      await db.run(`INSERT INTO file (repo_id, path, blob_hash) VALUES (1, ?, ?)`, [
        `file${i}.ts`,
        `hash${i}`,
      ]);
    }

    const provider = createIdfProvider(db, 1);

    const commonWeight = await provider.computeIdf("common"); // df = 100
    const mediumWeight = await provider.computeIdf("medium"); // df = 50
    const rareWeight = await provider.computeIdf("rare"); // df = 10
    const uniqueWeight = await provider.computeIdf("unique"); // df = 1
    const oovWeight = await provider.computeIdf("nonexistent"); // df = 0

    // Verify ordering: oov > unique > rare > medium > common
    expect(oovWeight).toBeGreaterThan(uniqueWeight);
    expect(uniqueWeight).toBeGreaterThan(rareWeight);
    expect(rareWeight).toBeGreaterThan(mediumWeight);
    expect(mediumWeight).toBeGreaterThan(commonWeight);

    // All weights should be in [0, 1]
    expect(commonWeight).toBeGreaterThanOrEqual(0);
    expect(oovWeight).toBeLessThanOrEqual(1);

    // Common words (appearing in all docs) should have very low weight
    expect(commonWeight).toBeLessThan(0.2);

    // OOV words should have maximum weight
    expect(oovWeight).toBeGreaterThan(0.95);

    // Note: db.close() and rm() are handled by afterEach
  });
});
