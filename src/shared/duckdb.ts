import { access, mkdir, writeFile } from "node:fs/promises";
import { dirname, join } from "node:path";

import { DuckDBInstance } from "@duckdb/node-api";
import type { DuckDBConnection, DuckDBValue } from "@duckdb/node-api";

export interface DuckDBClientOptions {
  databasePath: string;
  ensureDirectory?: boolean;
  autoGitignore?: boolean;
}

/**
 * パラメータの型定義。
 * - 配列: 位置パラメータ (? プレースホルダ用)
 * - オブジェクト: 名前付きパラメータ ($param プレースホルダ用)
 */
type QueryParams = unknown[] | Record<string, unknown>;

/** @duckdb/node-api が受け付けるパラメータ型 */
type DuckDBParams = DuckDBValue[] | Record<string, DuckDBValue>;

function hasDefinedParams(params: QueryParams): boolean {
  return Array.isArray(params) ? params.length > 0 : Object.keys(params).length > 0;
}

function assertNoUndefined(sql: string, params: QueryParams): void {
  if (Array.isArray(params)) {
    const index = params.findIndex((value) => value === undefined);
    if (index >= 0) {
      throw new Error(`Parameter ${index} is undefined for SQL: ${sql}`);
    }
  } else {
    for (const [key, value] of Object.entries(params)) {
      if (value === undefined) {
        throw new Error(`Parameter ${key} is undefined for SQL: ${sql}`);
      }
    }
  }
}

function coerceBigInts<T>(value: T): T {
  if (typeof value === "bigint") {
    const asNumber = Number(value);
    if (!Number.isSafeInteger(asNumber)) {
      throw new Error(
        `DuckDB returned bigint ${value.toString()} which exceeds Number.MAX_SAFE_INTEGER. Reduce dataset size or use smaller aggregates.`
      );
    }
    return asNumber as unknown as T;
  }
  if (Array.isArray(value)) {
    return value.map((item) => coerceBigInts(item)) as unknown as T;
  }
  if (value && typeof value === "object") {
    const result: Record<string, unknown> = {};
    for (const [key, entry] of Object.entries(value as Record<string, unknown>)) {
      result[key] = coerceBigInts(entry);
    }
    return result as unknown as T;
  }
  return value;
}

/**
 * Check if a directory is inside a Git repository by walking up the directory tree
 * looking for a .git directory.
 */
async function isInGitRepository(dirPath: string): Promise<boolean> {
  let currentPath = dirPath;

  // Walk up the directory tree until we reach the root
  while (true) {
    const gitPath = join(currentPath, ".git");
    try {
      await access(gitPath);
      return true;
    } catch {
      // .git not found at this level, continue up
    }

    const parentPath = dirname(currentPath);
    // If we've reached the root (parent is same as current), stop
    if (parentPath === currentPath) {
      return false;
    }
    currentPath = parentPath;
  }
}

/**
 * Create a .gitignore file in the specified directory if it doesn't already exist.
 * The .gitignore will contain a wildcard pattern to ignore all files in the directory.
 */
async function createGitignoreIfNeeded(dirPath: string): Promise<void> {
  const gitignorePath = join(dirPath, ".gitignore");

  try {
    await access(gitignorePath);
    // .gitignore already exists, skip to respect user's configuration
  } catch {
    // .gitignore does not exist, create it
    const content =
      "# This directory is managed by the application's database client.\n" +
      "# All files in this directory are ignored to prevent committing database files.\n" +
      "*\n";
    await writeFile(gitignorePath, content, "utf-8");
  }
}

export class DuckDBClient {
  private readonly instance: DuckDBInstance;
  private readonly connection: DuckDBConnection;

  private constructor(instance: DuckDBInstance, connection: DuckDBConnection) {
    this.instance = instance;
    this.connection = connection;
  }

  static async connect(options: DuckDBClientOptions): Promise<DuckDBClient> {
    const dbDir = dirname(options.databasePath);

    if (options.ensureDirectory) {
      await mkdir(dbDir, { recursive: true });
    }

    // Auto-create .gitignore if enabled (default: true)
    const shouldAutoGitignore = options.autoGitignore ?? true;
    if (shouldAutoGitignore) {
      const isInGit = await isInGitRepository(dbDir);
      if (isInGit) {
        await createGitignoreIfNeeded(dbDir);
      }
    }

    const instance = await DuckDBInstance.create(options.databasePath);
    const connection = await instance.connect();
    return new DuckDBClient(instance, connection);
  }

  async run(sql: string, params: QueryParams = []): Promise<void> {
    assertNoUndefined(sql, params);
    try {
      if (hasDefinedParams(params)) {
        // QueryParams は DuckDBParams と互換性がある（プリミティブ値のみを使用する前提）
        await this.connection.run(sql, params as DuckDBParams);
      } else {
        await this.connection.run(sql);
      }
    } catch (error: unknown) {
      const message = error instanceof Error ? error.message : String(error);
      throw new Error(`${message} | SQL: ${sql} | Params: ${JSON.stringify(params)}`);
    }
  }

  async all<T>(sql: string, params: QueryParams = []): Promise<T[]> {
    assertNoUndefined(sql, params);
    try {
      let reader;
      if (hasDefinedParams(params)) {
        // QueryParams は DuckDBParams と互換性がある（プリミティブ値のみを使用する前提）
        reader = await this.connection.runAndReadAll(sql, params as DuckDBParams);
      } else {
        reader = await this.connection.runAndReadAll(sql);
      }
      const rows = reader.getRowObjects() as T[];
      return rows.map((row) => coerceBigInts(row));
    } catch (error: unknown) {
      const message = error instanceof Error ? error.message : String(error);
      throw new Error(`${message} | SQL: ${sql} | Params: ${JSON.stringify(params)}`);
    }
  }

  async transaction<T>(fn: () => Promise<T>): Promise<T> {
    await this.run("BEGIN TRANSACTION");
    try {
      const result = await fn();
      await this.run("COMMIT");
      return result;
    } catch (error) {
      await this.run("ROLLBACK").catch((rollbackError: unknown) => {
        // ROLLBACKエラーは握りつぶすが、デバッグのためstderrに出力
        // 元のエラーを優先して伝播させるため、ここでは再throwしない
        const msg = rollbackError instanceof Error ? rollbackError.message : String(rollbackError);
        process.stderr.write(`[DuckDBClient] ROLLBACK failed: ${msg}\n`);
      });
      throw error;
    }
  }

  async close(): Promise<void> {
    // Checkpoint WAL to ensure all writes are flushed to the main database file
    // This is critical for multi-connection scenarios where subsequent connections
    // need to see all changes from previous connections
    try {
      await this.run("CHECKPOINT");
    } catch {
      // Ignore checkpoint errors - database might be in read-only mode or already checkpointed
    }

    // DuckDBConnection.closeSync() を呼び出すと、接続が閉じられる
    // DuckDBInstance は接続経由で使用され、明示的なclose APIは提供されていない
    // （@duckdb/node-api の設計上、Instance のリソースは GC で解放される）
    this.connection.closeSync();
  }
}
