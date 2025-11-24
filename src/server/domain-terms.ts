import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { parse } from "yaml";
import { z } from "zod";

const SAFE_PATH_PATTERN = /^[a-zA-Z0-9_.\-/]+$/;
const DEFAULT_CANDIDATE_FILES = [
  "config/domain-terms.yml",
  "config/domain-terms.yaml",
  ".kiri/domain-terms.yml",
  ".kiri/domain-terms.yaml",
];

const TermDefinitionSchema = z
  .object({
    aliases: z.array(z.string().trim().min(1)).optional(),
    files: z.array(z.string().trim().min(1)).optional(),
  })
  .strict();

export interface DomainTermEntry {
  canonical: string;
  normalizedCanonical: string;
  aliases: string[];
  normalizedAliases: string[];
  files: string[];
  category: string;
}

export interface DomainFileHint {
  path: string;
  source: string;
}

export interface DomainExpansion {
  matched: string[];
  aliases: string[];
  fileHints: DomainFileHint[];
}

function normalizeTermId(raw: string): string {
  const trimmed = raw.trim();
  if (!trimmed) {
    throw new Error("Domain term is empty → YAML内のkey/aliasesを確認してください");
  }
  const decamelized = trimmed.replace(/([a-z0-9])([A-Z])/g, "$1-$2");
  const replaced = decamelized.replace(/[\s_]+/g, "-");
  const collapsed = replaced.replace(/[^a-zA-Z0-9-]/g, "-").replace(/-+/g, "-");
  const normalized = collapsed.replace(/^-|-$/g, "").toLowerCase();
  if (normalized.length < 2) {
    throw new Error(
      `Domain term \"${raw}\" is too short after normalization → 2文字以上の識別子にしてください`
    );
  }
  return normalized;
}

function normalizePath(raw: string): string | null {
  const trimmed = raw.trim();
  if (!trimmed) {
    return null;
  }
  const normalized = trimmed.replace(/^\.\/?/, "").replace(/\\/g, "/");
  if (!SAFE_PATH_PATTERN.test(normalized)) {
    return null;
  }
  return normalized;
}

function splitTermParts(term: string): string[] {
  const parts = term
    .split(/[-_]/)
    .flatMap((p) => p.split(/(?=[A-Z])/)) // simple camelCase split
    .map((p) => p.trim().toLowerCase())
    .filter((p) => p.length >= 3);
  return Array.from(new Set(parts));
}

function buildEntries(input: Record<string, Array<Record<string, unknown>>>): DomainTermEntry[] {
  const entries: DomainTermEntry[] = [];
  for (const [category, items] of Object.entries(input)) {
    for (const item of items) {
      for (const [canonical, definition] of Object.entries(item)) {
        const normalizedCanonical = normalizeTermId(canonical);
        const schemaResult = TermDefinitionSchema.safeParse(definition);
        if (!schemaResult.success) {
          const message = schemaResult.error.issues.map((issue) => issue.message).join(", ");
          throw new Error(
            `Invalid domain term definition for ${canonical}: ${message} → YAMLの形式を修正してください`
          );
        }
        const aliases = schemaResult.data.aliases ?? [];
        const normalizedAliases = new Set<string>();
        normalizedAliases.add(normalizedCanonical);
        for (const alias of aliases) {
          const main = normalizeTermId(alias);
          normalizedAliases.add(main);
          for (const part of splitTermParts(alias)) {
            normalizedAliases.add(part);
          }
        }
        // canonicalも分割パーツを追加
        for (const part of splitTermParts(canonical)) {
          normalizedAliases.add(part);
        }
        const files = (schemaResult.data.files ?? [])
          .map((file) => normalizePath(file))
          .filter((value): value is string => Boolean(value));

        entries.push({
          canonical,
          normalizedCanonical,
          aliases,
          normalizedAliases,
          files,
          category,
        });
      }
    }
  }
  return entries;
}

function extractCandidateTerms(text: string): string[] {
  const matches = text.match(/[A-Za-z0-9_-]+/g) ?? [];
  const candidates = new Set<string>();
  for (const token of matches) {
    try {
      const normalized = normalizeTermId(token);
      candidates.add(normalized);
    } catch {
      continue;
    }
  }
  return Array.from(candidates);
}

export class DomainTermsDictionary {
  private readonly lookup: Map<string, DomainTermEntry>;

  constructor(entries: DomainTermEntry[]) {
    this.lookup = new Map();
    for (const entry of entries) {
      this.lookup.set(entry.normalizedCanonical, entry);
      for (const alias of entry.normalizedAliases) {
        this.lookup.set(alias, entry);
      }
    }
  }

  expandFromText(text: string): DomainExpansion {
    const candidates = extractCandidateTerms(text);
    return this.expandCandidates(candidates);
  }

  expandCandidates(candidates: string[]): DomainExpansion {
    const matchedEntries = new Map<string, DomainTermEntry>();
    for (const candidate of candidates) {
      const entry = this.lookup.get(candidate);
      if (entry) {
        matchedEntries.set(entry.normalizedCanonical, entry);
      }
    }

    if (matchedEntries.size === 0) {
      return { matched: [], aliases: [], fileHints: [] };
    }

    const aliasKeywords = new Set<string>();
    const fileHints: DomainFileHint[] = [];

    for (const entry of matchedEntries.values()) {
      for (const alias of entry.normalizedAliases) {
        aliasKeywords.add(alias);
      }
      if (!aliasKeywords.has(entry.normalizedCanonical)) {
        aliasKeywords.add(entry.normalizedCanonical);
      }
      for (const file of entry.files) {
        if (fileHints.some((hint) => hint.path === file)) {
          continue;
        }
        fileHints.push({ path: file, source: entry.canonical });
      }
    }

    return {
      matched: Array.from(matchedEntries.keys()),
      aliases: Array.from(aliasKeywords),
      fileHints,
    };
  }
}

function resolveConfigPath(configPath?: string, cwd: string = process.cwd()): string | undefined {
  const explicit = configPath ?? process.env.KIRI_DOMAIN_TERMS_CONFIG;
  if (explicit) {
    const resolved = path.isAbsolute(explicit) ? explicit : path.join(cwd, explicit);
    if (!fs.existsSync(resolved)) {
      throw new Error(
        `Domain terms config not found at ${resolved} → パスを確認するかファイルを配置してください`
      );
    }
    return resolved;
  }

  const currentDir = path.dirname(fileURLToPath(import.meta.url));
  const candidates = [
    ...DEFAULT_CANDIDATE_FILES.map((candidate) => path.join(cwd, candidate)),
    path.join(currentDir, "../../../config/domain-terms.yml"),
    path.join(currentDir, "../../../config/domain-terms.yaml"),
  ];

  for (const candidate of candidates) {
    if (fs.existsSync(candidate)) {
      return candidate;
    }
  }
  return undefined;
}

export function loadDomainTerms(
  options: { configPath?: string; cwd?: string } = {}
): DomainTermsDictionary {
  const resolvedPath = resolveConfigPath(options.configPath, options.cwd);
  if (!resolvedPath) {
    return new DomainTermsDictionary([]);
  }
  const raw = fs.readFileSync(resolvedPath, "utf8");
  const parsed = parse(raw);
  if (!parsed || typeof parsed !== "object" || Array.isArray(parsed)) {
    throw new Error(
      "Invalid domain terms config: top-level must be a mapping → YAMLを修正してください"
    );
  }
  const dictionary: Record<string, Array<Record<string, unknown>>> = {};
  for (const [category, value] of Object.entries(parsed)) {
    if (!Array.isArray(value)) {
      throw new Error(
        `Invalid domain terms config: category \"${category}\" must be an array of terms → YAMLを修正してください`
      );
    }
    dictionary[category] = value.map((entry, idx) => {
      if (!entry || typeof entry !== "object" || Array.isArray(entry)) {
        throw new Error(
          `Invalid domain terms config: entry #${idx + 1} in category \"${category}\" must be a mapping → YAMLを修正してください`
        );
      }
      return entry as Record<string, unknown>;
    });
  }
  const entries = buildEntries(dictionary);
  return new DomainTermsDictionary(entries);
}
