import process from "node:process";

import type { AdaptiveKConfig } from "../shared/adaptive-k.js";
import { validateAdaptiveKConfig } from "../shared/config-validate-adaptive-k.js";

import type { PathMultiplier } from "./boost-profiles.js";
import { loadPathPenalties } from "./config-loader.js";

export interface ServerConfig {
  features: {
    suppressNonCode: boolean;
    suppressFinalResults: boolean;
    clampSnippets: boolean;
    snippetWindow: number;
  };
  hints: {
    enabled: boolean;
    priority: {
      textMultiplier: number;
      pathMultiplier: number;
      baseBonus: number;
    };
    directory: {
      enabled: boolean;
      limit: number;
      maxFiles: number;
    };
    dependency: {
      enabled: boolean;
      outLimit: number;
      inLimit: number;
    };
    semantic: {
      enabled: boolean;
      limit: number;
      dirCandidateLimit: number;
      threshold: number;
    };
    substring: {
      enabled: boolean;
      limit: number;
      boost: number;
    };
    perHintLimit: number;
    dbQueryLimit: number;
  };
  penalties: {
    pathMissDelta: number;
    largeFileDelta: number;
  };
  adaptiveK: AdaptiveKConfig;
  pathPenalties: PathMultiplier[];
}

let cachedConfig: ServerConfig | null = null;

function envFlagEnabled(value: string | undefined, defaultEnabled: boolean): boolean {
  if (value === undefined) {
    return defaultEnabled;
  }
  const normalized = value.trim().toLowerCase();
  return normalized !== "0" && normalized !== "false" && normalized !== "off";
}

function parseEnvNumber(value: string | undefined, fallback: number): number {
  if (value === undefined) {
    return fallback;
  }
  const parsed = Number.parseInt(value, 10);
  if (Number.isFinite(parsed) && parsed >= 0) {
    return parsed;
  }
  return fallback;
}

function parseEnvFloat(value: string | undefined, fallback: number): number {
  if (value === undefined) {
    return fallback;
  }
  const parsed = Number.parseFloat(value);
  if (Number.isFinite(parsed)) {
    return parsed;
  }
  return fallback;
}

function parseEnvNumberList(value: string | undefined, fallback: number[]): number[] {
  if (value === undefined) {
    return fallback;
  }
  const parts = value
    .split(",")
    .map((part) => part.trim())
    .filter((part) => part.length > 0)
    .map((part) => Number.parseFloat(part));
  const allFinite = parts.every((n) => Number.isFinite(n));
  return allFinite && parts.length > 0 ? parts : fallback;
}

function validateServerConfig(config: ServerConfig): void {
  const { features, hints, penalties } = config;
  if (features.snippetWindow < 8) {
    throw new Error("snippetWindow must be >= 8 to keep bundle context useful");
  }
  if (hints.priority.textMultiplier <= 0 || hints.priority.pathMultiplier <= 0) {
    throw new Error("Hint priority multipliers must be positive numbers");
  }
  if (hints.priority.baseBonus <= 0) {
    throw new Error("Hint priority base bonus must be positive");
  }
  if (hints.directory.limit < 0 || hints.directory.maxFiles < 1) {
    throw new Error("Directory hint limits must be non-negative and maxFiles >= 1");
  }
  if (hints.dependency.outLimit < 0 || hints.dependency.inLimit < 0) {
    throw new Error("Dependency hint limits must be non-negative");
  }
  if (hints.semantic.limit < 0 || hints.semantic.dirCandidateLimit < 1) {
    throw new Error("Semantic hint limits must be non-negative and candidate limit >= 1");
  }
  if (hints.semantic.threshold <= 0 || hints.semantic.threshold > 1) {
    throw new Error("Semantic hint threshold must be within (0, 1]");
  }
  if (hints.perHintLimit < 0) {
    throw new Error("Per-hint limit must be >= 0");
  }
  if (hints.enabled && hints.perHintLimit < 1) {
    throw new Error("Per-hint limit must be >= 1 when hints are enabled");
  }
  if (hints.dbQueryLimit < 0) {
    throw new Error("Hint DB query budget must be >= 0");
  }
  if (hints.enabled && hints.dbQueryLimit < 1) {
    throw new Error("Hint DB query budget must be >= 1 when hints are enabled");
  }
  if (hints.substring.limit < 0) {
    throw new Error("Substring hint limit must be non-negative");
  }
  if (penalties.pathMissDelta > 0 || penalties.largeFileDelta > 0) {
    throw new Error("Penalty deltas should be <= 0 (they reduce scores)");
  }
  for (const entry of config.pathPenalties) {
    if (!entry.prefix || typeof entry.prefix !== "string") {
      throw new Error("Path penalty prefix must be a non-empty string");
    }
    if (!Number.isFinite(entry.multiplier) || entry.multiplier < 0) {
      throw new Error(
        `Path penalty multiplier for ${entry.prefix} must be a non-negative finite number`
      );
    }
  }

  validateAdaptiveKConfig(config.adaptiveK);
}

export function loadServerConfig(): ServerConfig {
  if (cachedConfig) {
    return cachedConfig;
  }

  const suppressNonCode = envFlagEnabled(process.env.KIRI_SUPPRESS_NON_CODE, true);
  const suppressFinalResults = envFlagEnabled(process.env.KIRI_SUPPRESS_FINAL_RESULTS, true);
  const clampSnippets = envFlagEnabled(process.env.KIRI_CLAMP_SNIPPETS, true);
  const snippetWindow = Math.max(8, parseEnvNumber(process.env.KIRI_SNIPPET_WINDOW, 16));

  const directoryEnabled = envFlagEnabled(process.env.KIRI_HINT_ENABLE_DIR, false);
  const dependencyEnabled = envFlagEnabled(process.env.KIRI_HINT_ENABLE_DEP, false);
  const semanticEnabled = envFlagEnabled(process.env.KIRI_HINT_ENABLE_SEM, false);
  const substringEnabled = envFlagEnabled(process.env.KIRI_HINT_ENABLE_SUBSTRING, true);

  const hintsEnabled = directoryEnabled || dependencyEnabled || semanticEnabled;

  const pathPenalties = loadPathPenalties();

  const adaptiveKEnabled = envFlagEnabled(process.env.KIRI_ADAPTIVE_K_ENABLED, false);
  const adaptiveKAllowedSet = parseEnvNumberList(
    process.env.KIRI_ADAPTIVE_K_ALLOWED_SET,
    [5, 10, 20]
  );
  const adaptiveKMin = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_MIN, 3);
  const adaptiveKMax = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_MAX, 50);
  const adaptiveKBugfix = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_BUGFIX, 5);
  const adaptiveKIntegration = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_INTEGRATION, 5);
  const adaptiveKTestfail = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_TESTFAIL, 20);
  const adaptiveKPerformance = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_PERFORMANCE, 20);
  const adaptiveKDefault = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_DEFAULT, 10);
  const adaptiveKWhenDisabled = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_DISABLED_VALUE, 10);
  // 追加カテゴリ: golden評価で使用される分類
  const adaptiveKDebug = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_DEBUG, 15);
  const adaptiveKApi = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_API, 15);
  const adaptiveKDocs = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_DOCS, 8);
  const adaptiveKFeature = parseEnvNumber(process.env.KIRI_ADAPTIVE_K_FEATURE, 10);

  const adaptiveK: AdaptiveKConfig = {
    enabled: adaptiveKEnabled,
    allowedSet: adaptiveKAllowedSet,
    kMin: adaptiveKMin,
    kMax: adaptiveKMax,
    kMap: {
      bugfix: adaptiveKBugfix,
      integration: adaptiveKIntegration,
      testfail: adaptiveKTestfail,
      performance: adaptiveKPerformance,
      // golden評価カテゴリ
      debug: adaptiveKDebug,
      api: adaptiveKApi,
      docs: adaptiveKDocs,
      "docs-plain": adaptiveKDocs,
      feature: adaptiveKFeature,
    },
    kDefault: adaptiveKDefault,
    kWhenDisabled: adaptiveKWhenDisabled,
  };

  const config: ServerConfig = {
    features: {
      suppressNonCode,
      suppressFinalResults,
      clampSnippets,
      snippetWindow,
    },
    hints: {
      enabled: hintsEnabled,
      priority: {
        textMultiplier: parseEnvFloat(process.env.KIRI_HINT_TEXT_MULTIPLIER, 6),
        pathMultiplier: parseEnvFloat(process.env.KIRI_HINT_PATH_MULTIPLIER, 2),
        baseBonus: parseEnvFloat(process.env.KIRI_HINT_BASE_BONUS, 5),
      },
      directory: {
        enabled: directoryEnabled,
        limit: directoryEnabled
          ? Math.max(0, parseEnvNumber(process.env.KIRI_HINT_NEAR_LIMIT_DIR, 2))
          : 0,
        maxFiles: Math.max(1, parseEnvNumber(process.env.KIRI_HINT_NEAR_MAX_FILES, 10)),
      },
      dependency: {
        enabled: dependencyEnabled,
        outLimit: dependencyEnabled
          ? Math.max(0, parseEnvNumber(process.env.KIRI_HINT_DEP_OUT_LIMIT, 1))
          : 0,
        inLimit: dependencyEnabled
          ? Math.max(0, parseEnvNumber(process.env.KIRI_HINT_DEP_IN_LIMIT, 1))
          : 0,
      },
      semantic: {
        enabled: semanticEnabled,
        limit: semanticEnabled
          ? Math.max(0, parseEnvNumber(process.env.KIRI_HINT_SEM_LIMIT, 2))
          : 0,
        dirCandidateLimit: Math.max(
          1,
          parseEnvNumber(process.env.KIRI_HINT_SEM_DIR_CANDIDATES, 20)
        ),
        threshold: parseEnvFloat(process.env.KIRI_HINT_SEM_THRESHOLD, 0.65),
      },
      substring: {
        enabled: substringEnabled,
        limit: substringEnabled
          ? Math.max(0, parseEnvNumber(process.env.KIRI_HINT_SUBSTRING_LIMIT, 3))
          : 0,
        boost: parseEnvFloat(process.env.KIRI_HINT_SUBSTRING_BOOST, 3),
      },
      perHintLimit: hintsEnabled
        ? Math.max(1, parseEnvNumber(process.env.KIRI_HINT_PER_HINT_LIMIT, 6))
        : 0,
      dbQueryLimit: hintsEnabled
        ? Math.max(1, parseEnvNumber(process.env.KIRI_HINT_DB_QUERY_LIMIT, 12))
        : 0,
    },
    penalties: {
      pathMissDelta: parseEnvFloat(process.env.KIRI_PATH_MISS_DELTA, -0.5),
      largeFileDelta: parseEnvFloat(process.env.KIRI_LARGE_FILE_DELTA, -0.8),
    },
    adaptiveK,
    pathPenalties,
  };

  validateServerConfig(config);
  cachedConfig = config;
  return config;
}
