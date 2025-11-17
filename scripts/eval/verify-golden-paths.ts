#!/usr/bin/env tsx
/**
 * Verify that all expected paths in golden set queries actually exist
 */
import { readFileSync, existsSync } from "node:fs";
import { join } from "node:path";
import { parse as parseYAML } from "yaml";

interface GoldenQuery {
  id: string;
  query: string;
  category: string;
  repo?: string;
  expected: {
    paths: string[];
  };
}

interface GoldenSet {
  queries: GoldenQuery[];
}

interface ValidationResult {
  totalQueries: number;
  totalExpectedPaths: number;
  missingPaths: Array<{
    queryId: string;
    repo: string;
    path: string;
  }>;
  queriesWithMissing: Set<string>;
}

const REPO_ROOTS: Record<string, string> = {
  vscode: "external/vscode",
  "kiri-docs": ".", // kiri-docs queries use absolute paths from repo root
  "kiri-docs-plain": ".", // kiri-docs-plain queries use absolute paths from repo root
};

function main(): void {
  const goldenPath = join(process.cwd(), "tests/eval/goldens/queries.yaml");

  if (!existsSync(goldenPath)) {
    console.error(`❌ Golden set not found: ${goldenPath}`);
    process.exit(1);
  }

  const content = readFileSync(goldenPath, "utf8");
  const goldenSet = parseYAML(content) as GoldenSet;

  console.log("\n🔍 Verifying Golden Set Expected Paths...\n");

  const result: ValidationResult = {
    totalQueries: goldenSet.queries.length,
    totalExpectedPaths: 0,
    missingPaths: [],
    queriesWithMissing: new Set(),
  };

  for (const query of goldenSet.queries) {
    const repo = query.repo ?? "vscode";
    const repoRoot = REPO_ROOTS[repo];

    if (!repoRoot) {
      console.warn(`⚠️  Unknown repo '${repo}' for query '${query.id}'`);
      continue;
    }

    const expectedPaths = query.expected.paths ?? [];
    result.totalExpectedPaths += expectedPaths.length;

    for (const expectedPath of expectedPaths) {
      const fullPath = join(process.cwd(), repoRoot, expectedPath);

      if (!existsSync(fullPath)) {
        result.missingPaths.push({
          queryId: query.id,
          repo,
          path: expectedPath,
        });
        result.queriesWithMissing.add(query.id);
      }
    }
  }

  // Print results
  console.log(`Total queries: ${result.totalQueries}`);
  console.log(`Total expected paths: ${result.totalExpectedPaths}`);
  console.log(`Missing paths: ${result.missingPaths.length}`);
  console.log(`Queries with missing paths: ${result.queriesWithMissing.size}\n`);

  if (result.missingPaths.length === 0) {
    console.log("✅ All expected paths exist!\n");
    process.exit(0);
  }

  console.log("❌ Missing Paths:\n");

  // Group by query
  const byQuery = new Map<string, Array<{ repo: string; path: string }>>();
  for (const missing of result.missingPaths) {
    if (!byQuery.has(missing.queryId)) {
      byQuery.set(missing.queryId, []);
    }
    byQuery.get(missing.queryId)!.push({ repo: missing.repo, path: missing.path });
  }

  for (const [queryId, paths] of byQuery.entries()) {
    console.log(`  Query: ${queryId}`);
    for (const { repo, path } of paths) {
      console.log(`    - ${repo}: ${path}`);
    }
    console.log();
  }

  console.log(
    `\n⚠️  Found ${result.missingPaths.length} missing paths in ${result.queriesWithMissing.size} queries.`
  );
  console.log(
    "   These queries may have incorrect expected paths or the repo structure has changed.\n"
  );

  process.exit(1);
}

main();
