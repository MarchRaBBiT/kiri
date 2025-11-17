#!/usr/bin/env tsx
/**
 * Front matter stripping utility.
 *
 * Copies the repository's `docs/` tree into `tmp/docs-plain/`,
 * removes YAML front matter blocks, and optionally runs the indexer
 * so the corpus can be benchmarked independently.
 */

import { spawn } from "node:child_process";
import { cp, mkdir, readFile, readdir, rm, stat, writeFile } from "node:fs/promises";
import { basename, dirname, extname, join, relative } from "node:path";

import { parse as parseYAML } from "yaml";

const SOURCE_DIR = process.argv.includes("--source")
  ? resolveArgValue("--source")
  : join(process.cwd(), "docs");
const DEST_DIR = process.argv.includes("--out")
  ? resolveArgValue("--out")
  : join(process.cwd(), "tmp", "docs-plain");
const DOCS_ROOT = join(DEST_DIR, "docs");
const DOCMETA_ROOT = join(DEST_DIR, "docmeta");
const SHOULD_INDEX = process.argv.includes("--index");

interface StripResult {
  updated: boolean;
  content: string;
  frontMatter: Record<string, unknown> | null;
}

function resolveArgValue(flag: string): string {
  const index = process.argv.indexOf(flag);
  if (index === -1 || index + 1 >= process.argv.length) {
    throw new Error(`${flag} requires a value`);
  }
  return process.argv[index + 1]!;
}

async function removeDirectory(path: string): Promise<void> {
  try {
    await rm(path, { recursive: true, force: true });
  } catch (error) {
    console.warn(`⚠️  Failed to remove ${path}`, error);
  }
}

async function copyDocsTree(): Promise<void> {
  await removeDirectory(DEST_DIR);
  await mkdir(DOCS_ROOT, { recursive: true });
  await mkdir(DOCMETA_ROOT, { recursive: true });
  await cp(SOURCE_DIR, DOCS_ROOT, { recursive: true });
}

function stripFrontMatter(filePath: string, content: string): StripResult {
  if (!content.startsWith("---")) {
    return { updated: false, content, frontMatter: null };
  }
  const fmMatch = content.match(/^---\r?\n([\s\S]*?)\r?\n---\r?\n?/);
  if (!fmMatch) {
    return { updated: false, content, frontMatter: null };
  }
  const remainder = content.slice(fmMatch[0].length).replace(/^\s*\r?\n/, "");
  let parsed: Record<string, unknown> | null = null;
  try {
    const block = fmMatch[1] ?? "";
    const result = parseYAML(block);
    if (result && typeof result === "object" && !Array.isArray(result)) {
      parsed = JSON.parse(JSON.stringify(result)) as Record<string, unknown>;
    }
  } catch (error) {
    console.warn(
      `⚠️  Failed to parse front matter for ${filePath}:`,
      error instanceof Error ? error.message : String(error)
    );
  }
  return { updated: true, content: remainder, frontMatter: parsed };
}

async function* walk(dir: string): AsyncGenerator<string> {
  const entries = await readdir(dir, { withFileTypes: true });
  for (const entry of entries) {
    const entryPath = join(dir, entry.name);
    if (entry.isDirectory()) {
      yield* walk(entryPath);
      continue;
    }
    yield entryPath;
  }
}

function toPosixPath(value: string): string {
  return value.replace(/\\/g, "/");
}

function buildDocmetaPath(relativeDocPath: string): { outputPath: string; targetPath: string } {
  const repoRelative = toPosixPath(join("docs", relativeDocPath));
  const dirName = dirname(relativeDocPath);
  const baseName = basename(relativeDocPath, extname(relativeDocPath));
  const outputDir = dirName === "." ? DOCMETA_ROOT : join(DOCMETA_ROOT, dirName);
  const outputPath = join(outputDir, `${baseName}.json`);
  return { outputPath, targetPath: repoRelative };
}

async function writeDocmetaSnapshot(
  relativeDocPath: string,
  frontMatter: Record<string, unknown>
): Promise<void> {
  if (!frontMatter || Object.keys(frontMatter).length === 0) {
    return;
  }
  const { outputPath, targetPath } = buildDocmetaPath(relativeDocPath);
  await mkdir(dirname(outputPath), { recursive: true });
  const payload = {
    target_path: targetPath,
    front_matter: frontMatter,
  };
  await writeFile(outputPath, `${JSON.stringify(payload, null, 2)}\n`, "utf8");
}

async function processMarkdownFiles(): Promise<{
  total: number;
  stripped: number;
  snapshots: number;
}> {
  let total = 0;
  let stripped = 0;
  let snapshots = 0;
  for await (const filePath of walk(DOCS_ROOT)) {
    if (extname(filePath) !== ".md") {
      continue;
    }
    total += 1;
    const original = await readFile(filePath, "utf8");
    const result = stripFrontMatter(filePath, original);
    if (!result.updated) {
      continue;
    }
    stripped += 1;
    await writeFile(filePath, result.content, "utf8");
    const relativePath = relative(DOCS_ROOT, filePath);
    if (result.frontMatter) {
      await writeDocmetaSnapshot(relativePath, result.frontMatter);
      snapshots += 1;
    }
  }
  return { total, stripped, snapshots };
}

async function runIndexer(): Promise<void> {
  const dbPath = join(DEST_DIR, ".kiri", "index.duckdb");
  await mkdir(dirname(dbPath), { recursive: true });
  await new Promise<void>((resolve, reject) => {
    const proc = spawn(
      "pnpm",
      ["exec", "tsx", "src/indexer/cli.ts", "--repo", DEST_DIR, "--db", dbPath, "--full"],
      {
        stdio: "inherit",
        env: { ...process.env, KIRI_ALLOW_UNSAFE_PATHS: "1" },
      }
    );
    proc.on("exit", (code) => {
      if (code === 0) resolve();
      else reject(new Error(`Indexer exited with code ${code}`));
    });
  });
}

async function main(): Promise<void> {
  const sourceStats = await stat(SOURCE_DIR).catch(() => null);
  if (!sourceStats || !sourceStats.isDirectory()) {
    throw new Error(`Source directory not found: ${SOURCE_DIR}`);
  }

  console.log(`🧹 Creating plain docs corpus from ${SOURCE_DIR}`);
  await copyDocsTree();
  const { total, stripped, snapshots } = await processMarkdownFiles();
  console.log(
    `✅ Plain corpus ready at ${DOCS_ROOT} (${stripped}/${total} markdown files stripped, ${snapshots} metadata snapshots)`
  );

  if (SHOULD_INDEX) {
    console.log("📦 Running indexer for plain corpus...");
    await runIndexer();
    console.log("✅ Indexer finished");
  }
}

main().catch((error) => {
  console.error("❌ Failed to create plain docs corpus:", error);
  process.exit(1);
});
