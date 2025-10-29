import { createServer, IncomingMessage, Server } from "node:http";
import { resolve } from "node:path";
import { performance } from "node:perf_hooks";
import process from "node:process";
import { pathToFileURL } from "node:url";

import { DuckDBClient } from "../shared/duckdb.js";
import { maskValue } from "../shared/security/masker.js";

import { bootstrapServer } from "./bootstrap.js";
import { ServerContext } from "./context.js";
import { DegradeController } from "./fallbacks/degradeController.js";
import {
  ContextBundleParams,
  DepsClosureParams,
  FilesSearchParams,
  SemanticRerankParams,
  SnippetsGetParams,
  contextBundle,
  depsClosure,
  filesSearch,
  resolveRepoId,
  semanticRerank,
  snippetsGet,
} from "./handlers.js";
import { MetricsRegistry, writeMetricsResponse } from "./observability/metrics.js";
import { withSpan } from "./observability/tracing.js";

export interface ServerOptions {
  port: number;
  databasePath: string;
  repoRoot: string;
  allowDegrade?: boolean;
  securityConfigPath?: string;
  securityLockPath?: string;
}

interface JsonRpcRequest {
  jsonrpc?: string;
  id?: unknown;
  method?: string;
  params?: unknown;
}

interface JsonRpcSuccess {
  jsonrpc: "2.0";
  id: unknown;
  result: unknown;
}

interface JsonRpcError {
  jsonrpc: "2.0";
  id: unknown;
  error: {
    code: number;
    message: string;
  };
}

function parseFilesSearchParams(input: unknown): FilesSearchParams {
  if (!input || typeof input !== "object") {
    return { query: "" };
  }
  const record = input as Record<string, unknown>;
  const limitValue = record.limit;
  let limit: number | undefined;
  if (typeof limitValue === "number") {
    limit = limitValue;
  } else if (typeof limitValue === "string") {
    const parsed = Number(limitValue);
    if (!Number.isNaN(parsed)) {
      limit = parsed;
    }
  }
  const params: FilesSearchParams = {
    query: typeof record.query === "string" ? record.query : "",
  };
  if (typeof record.lang === "string") params.lang = record.lang;
  if (typeof record.ext === "string") params.ext = record.ext;
  if (typeof record.path_prefix === "string") params.path_prefix = record.path_prefix;
  if (limit !== undefined) params.limit = limit;
  return params;
}

function parseSnippetsGetParams(input: unknown): SnippetsGetParams {
  if (!input || typeof input !== "object") {
    return { path: "" };
  }
  const record = input as Record<string, unknown>;
  const toNumber = (value: unknown): number | undefined => {
    if (typeof value === "number") {
      return value;
    }
    if (typeof value === "string") {
      const parsed = Number(value);
      return Number.isNaN(parsed) ? undefined : parsed;
    }
    return undefined;
  };
  const startLine = toNumber(record.start_line);
  const endLine = toNumber(record.end_line);
  const params: SnippetsGetParams = {
    path: typeof record.path === "string" ? record.path : "",
  };
  if (startLine !== undefined) params.start_line = startLine;
  if (endLine !== undefined) params.end_line = endLine;
  return params;
}

function parseDepsClosureParams(input: unknown): DepsClosureParams {
  if (!input || typeof input !== "object") {
    return { path: "" };
  }
  const record = input as Record<string, unknown>;
  const toNumber = (value: unknown): number | undefined => {
    if (typeof value === "number") {
      return value;
    }
    if (typeof value === "string") {
      const parsed = Number(value);
      return Number.isNaN(parsed) ? undefined : parsed;
    }
    return undefined;
  };
  const direction =
    record.direction === "inbound" || record.direction === "outbound"
      ? (record.direction as "inbound" | "outbound")
      : undefined;
  const includePackages =
    typeof record.include_packages === "boolean" ? record.include_packages : undefined;
  const maxDepth = toNumber(record.max_depth);
  const params: DepsClosureParams = {
    path: typeof record.path === "string" ? record.path : "",
  };
  if (maxDepth !== undefined) params.max_depth = maxDepth;
  if (direction !== undefined) params.direction = direction;
  if (includePackages !== undefined) params.include_packages = includePackages;
  return params;
}

function parseContextBundleParams(input: unknown): ContextBundleParams {
  if (!input || typeof input !== "object") {
    return { goal: "" };
  }
  const record = input as Record<string, unknown>;
  const params: ContextBundleParams = {
    goal: typeof record.goal === "string" ? record.goal : "",
  };
  const limitValue = record.limit;
  if (typeof limitValue === "number") {
    params.limit = limitValue;
  } else if (typeof limitValue === "string") {
    const parsed = Number(limitValue);
    if (!Number.isNaN(parsed)) {
      params.limit = parsed;
    }
  }

  const artifactsValue = record.artifacts;
  if (artifactsValue && typeof artifactsValue === "object") {
    const artifactsRecord = artifactsValue as Record<string, unknown>;
    const artifacts: ContextBundleParams["artifacts"] = {};
    if (typeof artifactsRecord.editing_path === "string") {
      artifacts.editing_path = artifactsRecord.editing_path;
    }
    if (Array.isArray(artifactsRecord.failing_tests)) {
      const failingTests = artifactsRecord.failing_tests.filter(
        (value): value is string => typeof value === "string"
      );
      if (failingTests.length > 0) {
        artifacts.failing_tests = failingTests;
      }
    }
    if (typeof artifactsRecord.last_diff === "string") {
      artifacts.last_diff = artifactsRecord.last_diff;
    }
    if (artifacts.editing_path || artifacts.failing_tests || artifacts.last_diff) {
      params.artifacts = artifacts;
    }
  }

  if (typeof record.profile === "string") {
    params.profile = record.profile;
  }

  return params;
}

function parseSemanticRerankParams(input: unknown): SemanticRerankParams {
  if (!input || typeof input !== "object") {
    return { text: "", candidates: [] };
  }
  const record = input as Record<string, unknown>;
  const params: SemanticRerankParams = {
    text: typeof record.text === "string" ? record.text : "",
    candidates: [],
  };

  const candidatesValue = record.candidates;
  if (Array.isArray(candidatesValue)) {
    for (const candidate of candidatesValue) {
      if (!candidate || typeof candidate !== "object") {
        continue;
      }
      const candidateRecord = candidate as Record<string, unknown>;
      if (typeof candidateRecord.path !== "string" || candidateRecord.path.length === 0) {
        continue;
      }
      const candidateInput: SemanticRerankParams["candidates"][number] = {
        path: candidateRecord.path,
      };
      if (typeof candidateRecord.score === "number" && Number.isFinite(candidateRecord.score)) {
        candidateInput.score = candidateRecord.score;
      }
      params.candidates.push(candidateInput);
    }
  }

  const limitValue = record.k;
  if (typeof limitValue === "number" && Number.isFinite(limitValue)) {
    params.k = limitValue;
  } else if (typeof limitValue === "string") {
    const parsed = Number(limitValue);
    if (!Number.isNaN(parsed)) {
      params.k = parsed;
    }
  }

  if (typeof record.profile === "string") {
    params.profile = record.profile;
  }

  return params;
}

async function readBody(request: IncomingMessage): Promise<string> {
  return await new Promise<string>((resolveBody, rejectBody) => {
    const chunks: Array<string> = [];
    request.setEncoding("utf8");
    request.on("data", (chunk: string) => {
      chunks.push(chunk);
    });
    request.on("end", () => {
      resolveBody(chunks.join(""));
    });
    request.on("error", (error) => {
      rejectBody(error);
    });
  });
}

function successResponse(id: unknown, result: unknown): JsonRpcSuccess {
  return { jsonrpc: "2.0", id, result };
}

function errorResponse(id: unknown, message: string, code = -32603): JsonRpcError {
  return { jsonrpc: "2.0", id, error: { code, message } };
}

export async function startServer(options: ServerOptions): Promise<Server> {
  const bootstrap = bootstrapServer({
    securityConfigPath: options.securityConfigPath,
    securityLockPath: options.securityLockPath,
  });
  const databasePath = resolve(options.databasePath);
  const repoRoot = resolve(options.repoRoot);
  let db: DuckDBClient | null = null;
  try {
    db = await DuckDBClient.connect({ databasePath, ensureDirectory: true });
    const repoId = await resolveRepoId(db, repoRoot);
    const context: ServerContext = { db, repoId };
    const degrade = new DegradeController(repoRoot);
    const metrics = new MetricsRegistry();
    const allowDegrade = options.allowDegrade ?? false;
    const tokens = bootstrap.security.config.sensitive_tokens;

    const server = createServer(async (req, res) => {
      if (req.method === "GET" && req.url === "/metrics") {
        writeMetricsResponse(res, metrics);
        return;
      }

      if (req.method !== "POST") {
        res.statusCode = 405;
        res.setHeader("Content-Type", "application/json");
        res.end(
          JSON.stringify(
            errorResponse(null, "Only POST is supported. Send a JSON-RPC request via POST.")
          )
        );
        return;
      }

      let body: string;
      try {
        body = await readBody(req);
      } catch {
        res.statusCode = 500;
        res.setHeader("Content-Type", "application/json");
        res.end(
          JSON.stringify(
            errorResponse(
              null,
              "Failed to read request body. Retry the call with a smaller payload."
            )
          )
        );
        return;
      }

      let payload: JsonRpcRequest;
      try {
        payload = JSON.parse(body) as JsonRpcRequest;
      } catch {
        res.statusCode = 400;
        res.setHeader("Content-Type", "application/json");
        res.end(
          JSON.stringify(
            errorResponse(null, "Invalid JSON payload. Submit a JSON-RPC 2.0 compliant request.")
          )
        );
        return;
      }

      if (payload.jsonrpc !== "2.0" || typeof payload.method !== "string") {
        res.statusCode = 400;
        res.setHeader("Content-Type", "application/json");
        res.end(
          JSON.stringify(
            errorResponse(
              payload.id ?? null,
              "Malformed JSON-RPC request. Provide method and jsonrpc=2.0."
            )
          )
        );
        return;
      }

      res.setHeader("Content-Type", "application/json");

      const start = performance.now();
      try {
        let result: unknown;
        switch (payload.method) {
          case "context.bundle": {
            const params = parseContextBundleParams(payload.params);
            const handler = async () =>
              await withSpan("context.bundle", async () => await contextBundle(context, params));
            result = await degrade.withResource(handler, "duckdb:context.bundle");
            break;
          }
          case "semantic.rerank": {
            const params = parseSemanticRerankParams(payload.params);
            const handler = async () =>
              await withSpan("semantic.rerank", async () => await semanticRerank(context, params));
            result = await degrade.withResource(handler, "duckdb:semantic.rerank");
            break;
          }
          case "files.search": {
            const params = parseFilesSearchParams(payload.params);
            if (degrade.current.active && allowDegrade) {
              result = {
                hits: degrade.search(params.query, params.limit ?? 20).map((hit) => ({
                  path: hit.path,
                  preview: hit.preview,
                  matchLine: hit.matchLine,
                  lang: null,
                  ext: null,
                  score: 0,
                })),
                degrade: true,
              };
            } else {
              const handler = async () =>
                await withSpan("files.search", async () => await filesSearch(context, params));
              result = await degrade.withResource(handler, "duckdb:files.search");
            }
            break;
          }
          case "snippets.get": {
            const params = parseSnippetsGetParams(payload.params);
            const handler = async () =>
              await withSpan("snippets.get", async () => await snippetsGet(context, params));
            result = await degrade.withResource(handler, "duckdb:snippets.get");
            break;
          }
          case "deps.closure": {
            const params = parseDepsClosureParams(payload.params);
            const handler = async () =>
              await withSpan("deps.closure", async () => await depsClosure(context, params));
            result = await degrade.withResource(handler, "duckdb:deps.closure");
            break;
          }
          default: {
            res.statusCode = 404;
            res.end(
              errorResponse(
                payload.id ?? null,
                "Requested method is not available. Use context.bundle, semantic.rerank, files.search, snippets.get, or deps.closure."
              )
            );
            return;
          }
        }
        const masked = maskValue(result, { tokens });
        if (masked.applied > 0) {
          metrics.recordMask(masked.applied);
        }
        const response = successResponse(payload.id ?? null, masked.masked);
        res.statusCode = 200;
        res.end(JSON.stringify(response));
      } catch (error) {
        if (degrade.current.active && !allowDegrade) {
          res.statusCode = 503;
          res.end(
            JSON.stringify(
              errorResponse(
                payload.id ?? null,
                "Backend degraded and --allow-degrade not set. Restore DuckDB availability or restart server."
              )
            )
          );
          return;
        }
        if (degrade.current.active && allowDegrade) {
          res.statusCode = 503;
          res.end(
            JSON.stringify(
              errorResponse(
                payload.id ?? null,
                degrade.current.reason
                  ? `Backend degraded due to ${degrade.current.reason}. Only files.search is operational.`
                  : "Backend degraded. Only files.search is operational."
              )
            )
          );
          return;
        }
        const message =
          error instanceof Error
            ? error.message
            : "Unknown error occurred. Inspect server logs and retry the request.";
        res.statusCode = 500;
        res.end(JSON.stringify(errorResponse(payload.id ?? null, message)));
      } finally {
        const elapsed = performance.now() - start;
        metrics.recordRequest(elapsed);
      }
    });

    await new Promise<void>((resolveListen) => {
      server.listen(options.port, () => {
        console.info(`KIRI MCP server listening on port ${options.port}`);
        resolveListen();
      });
    });

    server.on("close", () => {
      if (db) {
        void db.close();
      }
    });

    return server;
  } catch (error) {
    if (db) {
      await db.close();
    }
    throw error;
  }
}

function parseArg(flag: string): string | undefined {
  const index = process.argv.indexOf(flag);
  if (index >= 0) {
    return process.argv[index + 1];
  }
  return undefined;
}

function hasFlag(flag: string): boolean {
  return process.argv.includes(flag);
}

function parsePort(argv: string[]): number {
  const index = argv.indexOf("--port");
  if (index >= 0 && argv[index + 1]) {
    const parsed = Number(argv[index + 1]);
    if (!Number.isNaN(parsed)) {
      return parsed;
    }
  }
  return 8765;
}

if (import.meta.url === pathToFileURL(process.argv[1] ?? "").href) {
  const port = parsePort(process.argv);
  const repoRoot = resolve(parseArg("--repo") ?? ".");
  const databasePath = resolve(parseArg("--db") ?? "var/index.duckdb");

  startServer({
    port,
    repoRoot,
    databasePath,
    allowDegrade: hasFlag("--allow-degrade"),
    securityConfigPath: parseArg("--security-config"),
    securityLockPath: parseArg("--security-lock"),
  }).catch((error) => {
    console.error("Failed to start MCP server. Check DuckDB path and repo index before retrying.");
    console.error(error);
    process.exitCode = 1;
  });
}
