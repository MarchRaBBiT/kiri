import { createHash } from "node:crypto";
import { readFile, stat } from "node:fs/promises";
import { join, resolve, extname } from "node:path";
import { pathToFileURL } from "node:url";

import { detectLanguage } from "./language";
import { ensureBaseSchema } from "./schema";
import { getDefaultBranch, getHeadCommit, gitLsFiles } from "./git";
import { DuckDBClient } from "../shared/duckdb";

interface IndexerOptions {
  repoRoot: string;
  databasePath: string;
  full: boolean;
  since?: string;
}

interface BlobRecord {
  hash: string;
  sizeBytes: number;
  lineCount: number | null;
  content: string | null;
}

interface FileRecord {
  path: string;
  blobHash: string;
  ext: string | null;
  lang: string | null;
  isBinary: boolean;
  mtimeIso: string;
}

const MAX_SAMPLE_BYTES = 32_768;

function countLines(content: string): number {
  if (content.length === 0) {
    return 0;
  }
  return content.split(/\r?\n/).length;
}

function isBinaryBuffer(buffer: Buffer): boolean {
  const sample = buffer.subarray(0, Math.min(buffer.length, MAX_SAMPLE_BYTES));
  if (sample.includes(0)) {
    return true;
  }
  const decoded = sample.toString("utf8");
  return decoded.includes("\uFFFD");
}

async function ensureRepo(db: DuckDBClient, repoRoot: string, defaultBranch: string | null): Promise<number> {
  const existing = await db.all<{ id: number }>("SELECT id FROM repo WHERE root = ?", [repoRoot]);
  if (existing.length > 0) {
    const repoId = existing[0]?.id;
    if (defaultBranch) {
      await db.run("UPDATE repo SET default_branch = ? WHERE id = ?", [defaultBranch, repoId]);
    }
    return repoId;
  }
  const [{ next }] = await db.all<{ next: number }>("SELECT COALESCE(MAX(id), 0) + 1 AS next FROM repo");
  const repoId = next;
  await db.run(
    "INSERT INTO repo (id, root, default_branch, indexed_at) VALUES (?, ?, ?, CURRENT_TIMESTAMP)",
    [repoId, repoRoot, defaultBranch]
  );
  return repoId;
}

async function persistBlobs(db: DuckDBClient, blobs: Map<string, BlobRecord>): Promise<void> {
  for (const blob of blobs.values()) {
    await db.run(
      "INSERT OR REPLACE INTO blob (hash, size_bytes, line_count, content) VALUES (?, ?, ?, ?)",
      [blob.hash, blob.sizeBytes, blob.lineCount, blob.content]
    );
  }
}

async function persistTrees(
  db: DuckDBClient,
  repoId: number,
  commitHash: string,
  records: FileRecord[]
): Promise<void> {
  for (const record of records) {
    await db.run(
      "INSERT OR REPLACE INTO tree (repo_id, commit_hash, path, blob_hash, ext, lang, is_binary, mtime) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
      [
        repoId,
        commitHash,
        record.path,
        record.blobHash,
        record.ext,
        record.lang,
        record.isBinary,
        record.mtimeIso,
      ]
    );
  }
}

async function persistFiles(db: DuckDBClient, repoId: number, records: FileRecord[]): Promise<void> {
  for (const record of records) {
    await db.run(
      "INSERT OR REPLACE INTO file (repo_id, path, blob_hash, ext, lang, is_binary, mtime) VALUES (?, ?, ?, ?, ?, ?, ?)",
      [repoId, record.path, record.blobHash, record.ext, record.lang, record.isBinary, record.mtimeIso]
    );
  }
}

async function scanFiles(repoRoot: string, paths: string[]): Promise<{ blobs: Map<string, BlobRecord>; files: FileRecord[] }> {
  const blobs = new Map<string, BlobRecord>();
  const files: FileRecord[] = [];

  for (const relativePath of paths) {
    const absolutePath = join(repoRoot, relativePath);
    try {
      const fileStat = await stat(absolutePath);
      if (!fileStat.isFile()) {
        continue;
      }
      const buffer = await readFile(absolutePath);
      const isBinary = isBinaryBuffer(buffer);
      const hash = createHash("sha1").update(buffer).digest("hex");
      const ext = extname(relativePath) || null;
      const lang = ext ? detectLanguage(ext) : null;
      const mtimeIso = fileStat.mtime.toISOString();

      let content: string | null = null;
      let lineCount: number | null = null;
      if (!isBinary) {
        content = buffer.toString("utf8");
        lineCount = countLines(content);
      }

      if (!blobs.has(hash)) {
        blobs.set(hash, {
          hash,
          sizeBytes: buffer.length,
          lineCount,
          content,
        });
      }

      files.push({
        path: relativePath,
        blobHash: hash,
        ext,
        lang,
        isBinary,
        mtimeIso,
      });
    } catch (error) {
      console.warn(
        `Skipped ${relativePath} due to read error. Resolve filesystem permissions or remove the file to include it.`
      );
      console.warn(error);
    }
  }

  return { blobs, files };
}

export async function runIndexer(options: IndexerOptions): Promise<void> {
  if (!options.full && options.since) {
    console.warn("Incremental indexing is not yet supported. Falling back to full reindex.");
  }

  const repoRoot = resolve(options.repoRoot);
  const databasePath = resolve(options.databasePath);

  const [paths, headCommit, defaultBranch] = await Promise.all([
    gitLsFiles(repoRoot),
    getHeadCommit(repoRoot),
    getDefaultBranch(repoRoot),
  ]);

  const { blobs, files } = await scanFiles(repoRoot, paths);

  const db = await DuckDBClient.connect({ databasePath, ensureDirectory: true });
  try {
    await ensureBaseSchema(db);
    const repoId = await ensureRepo(db, repoRoot, defaultBranch);
    await db.transaction(async () => {
      await db.run("DELETE FROM tree WHERE repo_id = ?", [repoId]);
      await db.run("DELETE FROM file WHERE repo_id = ?", [repoId]);
      await persistBlobs(db, blobs);
      await persistTrees(db, repoId, headCommit, files);
      await persistFiles(db, repoId, files);
    });
    if (defaultBranch) {
      await db.run("UPDATE repo SET indexed_at = CURRENT_TIMESTAMP, default_branch = ? WHERE id = ?", [defaultBranch, repoId]);
    } else {
      await db.run("UPDATE repo SET indexed_at = CURRENT_TIMESTAMP WHERE id = ?", [repoId]);
    }
  } finally {
    await db.close();
  }

  console.info(
    `Indexed ${files.length} files for repo ${repoRoot} at ${databasePath} (commit ${headCommit.slice(0, 12)})`
  );
}

function parseArg(flag: string): string | undefined {
  const index = process.argv.indexOf(flag);
  if (index >= 0) {
    return process.argv[index + 1];
  }
  return undefined;
}

if (import.meta.url === pathToFileURL(process.argv[1] ?? "").href) {
  const repoRoot = resolve(parseArg("--repo") ?? ".");
  const databasePath = resolve(parseArg("--db") ?? "var/index.duckdb");
  const full = process.argv.includes("--full");
  const since = parseArg("--since");

  runIndexer({ repoRoot, databasePath, full: full || !since, since }).catch((error) => {
    console.error("Failed to index repository. Retry after resolving the logged error.");
    console.error(error);
    process.exitCode = 1;
  });
}
