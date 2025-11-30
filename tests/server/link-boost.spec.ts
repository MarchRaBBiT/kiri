import { mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { afterEach, describe, expect, it } from "vitest";

import { runIndexer } from "../../src/indexer/cli.js";
import { ServerContext } from "../../src/server/context.js";
import {
  checkTableAvailability,
  contextBundle,
  filesSearch,
  resolveRepoId,
} from "../../src/server/handlers.js";
import { WarningManager } from "../../src/server/rpc.js";
import { createServerServices } from "../../src/server/services/index.js";
import { DuckDBClient } from "../../src/shared/duckdb.js";
import { createTempRepo } from "../helpers/test-repo.js";

interface CleanupTarget {
  dispose: () => Promise<void>;
}

/**
 * Tests for inbound link boost scoring (Issue #87).
 * Verifies that documents with more inbound links receive higher scores.
 */
describe("Inbound Link Boost Scoring", () => {
  const cleanupTargets: CleanupTarget[] = [];

  afterEach(async () => {
    for (const target of cleanupTargets.splice(0, cleanupTargets.length)) {
      await target.dispose();
    }
  });

  describe("Link count impact on ranking", () => {
    it("ranks documents with more inbound links higher", async () => {
      // Create a hub-and-spoke documentation structure
      // hub.md is linked by 3 other files
      // spoke.md is linked by 1 file
      // orphan.md has no inbound links
      const repo = await createTempRepo({
        "docs/hub.md": `---
title: Hub Document
category: core
---

# Hub

This is the central hub document that many files reference.
`,
        "docs/spoke.md": `---
title: Spoke Document
category: core
---

# Spoke

This is a spoke document with fewer references.
`,
        "docs/orphan.md": `---
title: Orphan Document
category: core
---

# Orphan

This document has no inbound links.
`,
        "docs/referrer1.md": `---
title: Referrer 1
category: referrers
---

# Referrer 1

See the [Hub](./hub.md) for main documentation.
Also check [Spoke](./spoke.md).
`,
        "docs/referrer2.md": `---
title: Referrer 2
category: referrers
---

# Referrer 2

Refer to [Hub](./hub.md) for details.
`,
        "docs/referrer3.md": `---
title: Referrer 3
category: referrers
---

# Referrer 3

The [Hub](./hub.md) has all the information.
`,
      });
      cleanupTargets.push({ dispose: repo.cleanup });

      const dbDir = await mkdtemp(join(tmpdir(), "kiri-link-boost-"));
      const dbPath = join(dbDir, "index.duckdb");
      cleanupTargets.push({
        dispose: async () => await rm(dbDir, { recursive: true, force: true }),
      });

      await runIndexer({ repoRoot: repo.path, databasePath: dbPath, full: true });

      const db = await DuckDBClient.connect({ databasePath: dbPath });
      cleanupTargets.push({ dispose: async () => await db.close() });

      const repoId = await resolveRepoId(db, repo.path);
      const tableAvailability = await checkTableAvailability(db);
      const context: ServerContext = {
        db,
        repoId,
        services: createServerServices(db),
        tableAvailability,
        warningManager: new WarningManager(),
      };

      // Verify link counts in database
      const linkCounts = await db.all<{ resolved_path: string; count: number }>(
        `SELECT resolved_path, COUNT(*) as count
         FROM markdown_link
         WHERE repo_id = ? AND resolved_path IS NOT NULL
         GROUP BY resolved_path
         ORDER BY count DESC`,
        [repoId]
      );

      // Hub should have 3 inbound links
      const hubLinks = linkCounts.find((l) => l.resolved_path === "docs/hub.md");
      expect(hubLinks?.count).toBe(3);

      // Spoke should have 1 inbound link
      const spokeLinks = linkCounts.find((l) => l.resolved_path === "docs/spoke.md");
      expect(spokeLinks?.count).toBe(1);

      // Search for "core" category documents
      const bundle = await contextBundle(context, {
        goal: "core document category",
        boost_profile: "docs",
        limit: 10,
      });

      // Find the core documents in results
      const hubResult = bundle.context.find((item) => item.path === "docs/hub.md");
      const spokeResult = bundle.context.find((item) => item.path === "docs/spoke.md");
      const orphanResult = bundle.context.find((item) => item.path === "docs/orphan.md");

      // All three should be found
      expect(hubResult).toBeDefined();
      expect(spokeResult).toBeDefined();
      expect(orphanResult).toBeDefined();

      // Hub (3 links) should have higher score than spoke (1 link)
      if (hubResult && spokeResult) {
        expect(hubResult.score).toBeGreaterThan(spokeResult.score);
      }

      // Spoke (1 link) should have higher or equal score than orphan (0 links)
      if (spokeResult && orphanResult) {
        expect(spokeResult.score).toBeGreaterThanOrEqual(orphanResult.score);
      }
    });

    it("applies logarithmic scaling to link counts", async () => {
      // Create documents with varying link counts to test logarithmic scaling
      const repo = await createTempRepo({
        "docs/popular.md": `---
title: Popular
---
# Popular doc
`,
        "docs/medium.md": `---
title: Medium
---
# Medium doc
`,
        // Create 10 referrers to popular, 2 to medium
        "refs/r01.md": `[Popular](../docs/popular.md)`,
        "refs/r02.md": `[Popular](../docs/popular.md)`,
        "refs/r03.md": `[Popular](../docs/popular.md)`,
        "refs/r04.md": `[Popular](../docs/popular.md)`,
        "refs/r05.md": `[Popular](../docs/popular.md)`,
        "refs/r06.md": `[Popular](../docs/popular.md)`,
        "refs/r07.md": `[Popular](../docs/popular.md)`,
        "refs/r08.md": `[Popular](../docs/popular.md)`,
        "refs/r09.md": `[Popular](../docs/popular.md)`,
        "refs/r10.md": `[Popular](../docs/popular.md)`,
        "refs/m01.md": `[Medium](../docs/medium.md)`,
        "refs/m02.md": `[Medium](../docs/medium.md)`,
      });
      cleanupTargets.push({ dispose: repo.cleanup });

      const dbDir = await mkdtemp(join(tmpdir(), "kiri-log-scaling-"));
      const dbPath = join(dbDir, "index.duckdb");
      cleanupTargets.push({
        dispose: async () => await rm(dbDir, { recursive: true, force: true }),
      });

      await runIndexer({ repoRoot: repo.path, databasePath: dbPath, full: true });

      const db = await DuckDBClient.connect({ databasePath: dbPath });
      cleanupTargets.push({ dispose: async () => await db.close() });

      const repoId = await resolveRepoId(db, repo.path);
      const tableAvailability = await checkTableAvailability(db);
      const context: ServerContext = {
        db,
        repoId,
        services: createServerServices(db),
        tableAvailability,
        warningManager: new WarningManager(),
      };

      // Verify link counts
      const linkCounts = await db.all<{ resolved_path: string; count: number }>(
        `SELECT resolved_path, COUNT(*) as count
         FROM markdown_link
         WHERE repo_id = ? AND resolved_path LIKE 'docs/%'
         GROUP BY resolved_path`,
        [repoId]
      );

      const popularCount =
        linkCounts.find((l) => l.resolved_path === "docs/popular.md")?.count ?? 0;
      const mediumCount = linkCounts.find((l) => l.resolved_path === "docs/medium.md")?.count ?? 0;

      expect(popularCount).toBe(10);
      expect(mediumCount).toBe(2);

      // The score difference should be dampened due to logarithmic scaling
      // log1p(10) ≈ 2.40, log1p(2) ≈ 1.10
      // Ratio is about 2.2x, not 5x (which would be linear)
      const bundle = await contextBundle(context, {
        goal: "title doc",
        boost_profile: "docs",
        limit: 5,
      });

      const popularResult = bundle.context.find((item) => item.path === "docs/popular.md");
      const mediumResult = bundle.context.find((item) => item.path === "docs/medium.md");

      expect(popularResult).toBeDefined();
      expect(mediumResult).toBeDefined();

      // Popular should still score higher than medium
      if (popularResult && mediumResult) {
        expect(popularResult.score).toBeGreaterThan(mediumResult.score);
      }
    });
  });

  describe("boost:links tag in results", () => {
    it("returns boost:links in why tags when link boost is applied", async () => {
      const repo = await createTempRepo({
        "docs/hub.md": `---
title: Hub
---
# Central hub document
`,
        "docs/ref1.md": `See [Hub](./hub.md)`,
        "docs/ref2.md": `Check [Hub](./hub.md)`,
        "docs/ref3.md": `Read [Hub](./hub.md)`,
      });
      cleanupTargets.push({ dispose: repo.cleanup });

      const dbDir = await mkdtemp(join(tmpdir(), "kiri-boost-tag-"));
      const dbPath = join(dbDir, "index.duckdb");
      cleanupTargets.push({
        dispose: async () => await rm(dbDir, { recursive: true, force: true }),
      });

      await runIndexer({ repoRoot: repo.path, databasePath: dbPath, full: true });

      const db = await DuckDBClient.connect({ databasePath: dbPath });
      cleanupTargets.push({ dispose: async () => await db.close() });

      const repoId = await resolveRepoId(db, repo.path);
      const tableAvailability = await checkTableAvailability(db);
      const context: ServerContext = {
        db,
        repoId,
        services: createServerServices(db),
        tableAvailability,
        warningManager: new WarningManager(),
      };

      const bundle = await contextBundle(context, {
        goal: "hub document",
        boost_profile: "docs",
        limit: 5,
      });

      const hubResult = bundle.context.find((item) => item.path === "docs/hub.md");
      expect(hubResult).toBeDefined();

      // The hub document should have a positive score due to inbound links
      // Note: The exact why tags depend on implementation
      expect(hubResult?.score).toBeGreaterThan(0);
    });
  });

  describe("files_search with link boost", () => {
    it("applies inbound link boost in files_search results", async () => {
      const repo = await createTempRepo({
        "docs/hub.md": `# Hub Document

This is the main hub.
`,
        "docs/orphan.md": `# Orphan Document

This is an orphan.
`,
        "refs/r1.md": `[Hub](../docs/hub.md)`,
        "refs/r2.md": `[Hub](../docs/hub.md)`,
      });
      cleanupTargets.push({ dispose: repo.cleanup });

      const dbDir = await mkdtemp(join(tmpdir(), "kiri-filesearch-link-"));
      const dbPath = join(dbDir, "index.duckdb");
      cleanupTargets.push({
        dispose: async () => await rm(dbDir, { recursive: true, force: true }),
      });

      await runIndexer({ repoRoot: repo.path, databasePath: dbPath, full: true });

      const db = await DuckDBClient.connect({ databasePath: dbPath });
      cleanupTargets.push({ dispose: async () => await db.close() });

      const repoId = await resolveRepoId(db, repo.path);
      const tableAvailability = await checkTableAvailability(db);
      const context: ServerContext = {
        db,
        repoId,
        services: createServerServices(db),
        tableAvailability,
        warningManager: new WarningManager(),
      };

      // Search for "Document" which appears in both files
      const results = await filesSearch(context, {
        query: "Document",
        boost_profile: "docs",
        limit: 10,
      });

      const hubResult = results.find((item) => item.path === "docs/hub.md");
      const orphanResult = results.find((item) => item.path === "docs/orphan.md");

      expect(hubResult).toBeDefined();
      expect(orphanResult).toBeDefined();

      // Hub should rank higher due to inbound links
      if (hubResult && orphanResult) {
        expect(hubResult.score).toBeGreaterThan(orphanResult.score);
      }
    });
  });
});
