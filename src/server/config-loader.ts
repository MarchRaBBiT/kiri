import fs from "node:fs";
import path from "node:path";

import { parse } from "yaml";
import { z } from "zod";

import type { PathMultiplier } from "./boost-profiles.js";

const ENV_PREFIX = "KIRI_PATH_PENALTY_";
const penaltyCache = new Map<string, PathMultiplier[]>();

const PathPenaltySchema = z.object({
  prefix: z.string().trim().min(1, "prefix is required"),
  multiplier: z.number().finite().nonnegative(),
});

const ConfigSchema = z.object({
  path_penalties: z.array(PathPenaltySchema).optional(),
});

function normalizePrefix(raw: string): string {
  const trimmed = raw.trim();
  if (trimmed.length === 0) {
    throw new Error("Path penalty prefix cannot be empty");
  }

  const hadTrailingSlash = /[\\/]+$/.test(trimmed);
  const normalized = path.posix
    .normalize(trimmed.replace(/\\/g, "/"))
    .replace(/^([A-Za-z]:)?\//, "") // drop drive letter or leading slash
    .replace(/^\.\//, "");

  if (normalized === "" || normalized === ".") {
    throw new Error(`Path penalty prefix "${raw}" resolves to an empty path`);
  }
  if (normalized.startsWith("../") || normalized.includes("/../")) {
    throw new Error(`Path penalty prefix "${raw}" must not contain ".." segments`);
  }

  // Re-append trailing slash only when the original explicitly had it
  return hadTrailingSlash && !normalized.endsWith("/") ? `${normalized}/` : normalized;
}

function sortByPrefixLength(entries: PathMultiplier[]): PathMultiplier[] {
  return [...entries].sort((a, b) => b.prefix.length - a.prefix.length);
}

function decodeEnvKey(key: string): string {
  const encoded = key.slice(ENV_PREFIX.length);
  if (!encoded) {
    throw new Error("KIRI_PATH_PENALTY_* must include a prefix segment");
  }
  // Spec: "/" ↔ "__" encoding
  const decoded = encoded.replace(/__/g, "/");
  return normalizePrefix(decoded);
}

function parseEnvPathPenalties(env: NodeJS.ProcessEnv = process.env): PathMultiplier[] {
  const entries: PathMultiplier[] = [];

  for (const [key, rawValue] of Object.entries(env)) {
    if (!key.startsWith(ENV_PREFIX) || rawValue === undefined) {
      continue;
    }
    const prefix = decodeEnvKey(key);
    const multiplier = Number.parseFloat(rawValue);
    if (!Number.isFinite(multiplier)) {
      throw new Error(`Invalid multiplier for ${key}: ${rawValue}`);
    }
    if (multiplier < 0) {
      throw new Error(`Multiplier for ${key} must be >= 0`);
    }
    entries.push({ prefix, multiplier });
  }

  return entries;
}

function readYamlConfig(cwd: string): PathMultiplier[] {
  const candidates = [
    path.join(cwd, ".kiri/config.yaml"),
    path.join(cwd, ".kiri/config.yml"),
    path.join(cwd, "config/kiri.yaml"),
    path.join(cwd, "config/kiri.yml"),
  ];

  for (const candidate of candidates) {
    if (!fs.existsSync(candidate)) {
      continue;
    }

    const raw = fs.readFileSync(candidate, "utf8");
    const parsed = parse(raw);
    const result = ConfigSchema.safeParse(parsed);
    if (!result.success) {
      const details = result.error.issues.map((issue) => issue.message).join(", ");
      throw new Error(`Invalid path penalty config in ${candidate}: ${details}`);
    }

    const entries =
      result.data.path_penalties?.map<PathMultiplier>((entry) => ({
        prefix: normalizePrefix(entry.prefix),
        multiplier: entry.multiplier,
      })) ?? [];

    return entries;
  }

  return [];
}

function mergePathPenalties(priorityOrdered: PathMultiplier[][]): PathMultiplier[] {
  const merged = new Map<string, PathMultiplier>();
  for (const entries of priorityOrdered) {
    for (const entry of entries) {
      merged.set(entry.prefix, entry);
    }
  }
  return sortByPrefixLength(Array.from(merged.values()));
}

/**
 * Global resolver for path penalties (Issue #106)
 * Precedence: profile < env < YAML (last definition wins)
 */
export function loadPathPenalties(
  basePathMultipliers: PathMultiplier[] = [],
  cwd: string = process.cwd()
): PathMultiplier[] {
  const envEntries = Object.entries(process.env)
    .filter(([key]) => key.startsWith(ENV_PREFIX))
    .sort(([a], [b]) => a.localeCompare(b));
  const cacheKey = JSON.stringify({ cwd, base: basePathMultipliers, env: envEntries });
  const cached = penaltyCache.get(cacheKey);
  if (cached) {
    return cached;
  }

  const envPenalties = parseEnvPathPenalties();
  const yamlPenalties = readYamlConfig(cwd);
  const merged = mergePathPenalties([basePathMultipliers, envPenalties, yamlPenalties]);
  penaltyCache.set(cacheKey, merged);
  return merged;
}

/** Test helper: merge logic without disk/env side effects */
export function mergePathPenaltyEntries(
  base: PathMultiplier[],
  env: PathMultiplier[],
  yaml: PathMultiplier[]
): PathMultiplier[] {
  return mergePathPenalties([base, env, yaml]);
}
