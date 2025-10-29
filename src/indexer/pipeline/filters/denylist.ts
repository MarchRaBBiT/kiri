import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { parseSimpleYaml } from "../../../shared/utils/simpleYaml.js";

export interface DenylistConfig {
  patterns: string[];
}

export interface DenylistFilter {
  isDenied(path: string): boolean;
  diff(): string[];
}

function toRegex(pattern: string): RegExp {
  const normalized = pattern.endsWith("/") ? pattern.slice(0, -1) : pattern;
  const escaped = normalized
    .replace(/[.+^${}()|[\]\\]/g, "\\$&")
    .replace(/\*\*/g, "::DOUBLESTAR::");
  const withWildcards = escaped
    .replace(/::DOUBLESTAR::/g, ".*")
    .replace(/\*/g, "[^/]*")
    .replace(/\?/g, ".");
  const suffix = pattern.endsWith("/") ? "(?:/.*)?" : "";
  return new RegExp(`^${withWildcards}${suffix}$`);
}

function loadGitignore(repoRoot: string): string[] {
  try {
    const raw = readFileSync(resolve(repoRoot, ".gitignore"), "utf8");
    return raw
      .split(/\r?\n/)
      .map((line) => line.trim())
      .filter((line) => line.length > 0 && !line.startsWith("#"));
  } catch {
    return [];
  }
}

export function loadDenylistConfig(configPath?: string): DenylistConfig {
  const path = resolve(configPath ?? "config/denylist.yml");
  const content = readFileSync(path, "utf8");
  const parsed = parseSimpleYaml(content) as Record<string, unknown>;
  const patterns = Array.isArray(parsed.patterns)
    ? parsed.patterns.filter((value): value is string => typeof value === "string")
    : [];
  if (patterns.length === 0) {
    throw new Error("config/denylist.yml must contain patterns array");
  }
  return { patterns };
}

export function createDenylistFilter(repoRoot: string, configPath?: string): DenylistFilter {
  const { patterns } = loadDenylistConfig(configPath);
  const gitignorePatterns = loadGitignore(repoRoot);
  const combined = Array.from(new Set([...patterns, ...gitignorePatterns]));
  const regexList = combined.map(toRegex);
  const diffEntries = gitignorePatterns.filter((pattern) => !patterns.includes(pattern));

  return {
    isDenied(path: string) {
      const normalized = path.startsWith("/") ? path.slice(1) : path;
      return regexList.some((regex) => regex.test(normalized));
    },
    diff() {
      return diffEntries;
    },
  };
}
