/**
 * Boost Profile Configurations
 *
 * This module provides centralized configuration for boost_profile options.
 * Each profile defines how different file types should be ranked in search results.
 *
 * Profiles:
 * - default: Prioritizes implementation files over documentation
 * - docs: Prioritizes documentation over implementation
 * - balanced: Equal weight for both docs and implementation
 * - none: No file type boosting (pure keyword scoring)
 */

/**
 * Boost profile configuration
 * Defines how different file types should be ranked
 */
export interface BoostProfileConfig {
  /**
   * Directories to allow even if they match global denylist patterns.
   * Example: ["docs/"] allows docs/ files despite being blacklisted by default.
   * This overrides the global blacklist in applyFileTypeBoost/applyAdditiveFilePenalties.
   */
  denylistOverrides: string[];

  /** Multiplicative factors for different file types */
  fileTypeMultipliers: {
    /** Documentation files (.md, .yaml, .yml, .mdc) */
    doc: number;
    /** Implementation files (src/**) */
    impl: number;
    /** Configuration files (tsconfig.json, package.json, etc.) */
    config: number;
  };

  /**
   * Path-specific multipliers (e.g., src/app/ gets higher boost than src/)
   * Array is sorted by prefix length (longest first) to ensure correct matching priority
   */
  pathMultipliers: Array<{ prefix: string; multiplier: number }>;

  /**
   * Skip additive penalty for config files (-1.5 score penalty)
   * and only apply multiplicative penalty (e.g., 0.3x multiplier)
   * @default false
   */
  skipConfigAdditivePenalty?: boolean;
}

export type BoostProfileName =
  | "default"
  | "docs"
  | "none"
  | "balanced"
  | "feature"
  | "bugfix"
  | "debug"
  | "api"
  | "editor"
  | "testfail"
  | "typeerror";

/**
 * Boost profile definitions
 * Centralized configuration for all boost profiles
 */
export const BOOST_PROFILES: Record<BoostProfileName, BoostProfileConfig> = {
  default: {
    denylistOverrides: [],
    fileTypeMultipliers: {
      doc: 0.5, // 50% penalty for docs
      impl: 1.3, // 30% boost for implementation
      config: 0.05, // 95% penalty for config files
    },
    // ✅ Sorted by prefix length (longest first) for correct matching priority
    pathMultipliers: [
      { prefix: "src/components/", multiplier: 1.3 },
      { prefix: "src/app/", multiplier: 1.4 },
      { prefix: "src/lib/", multiplier: 1.2 },
      { prefix: "src/", multiplier: 1.0 },
    ],
  },

  docs: {
    denylistOverrides: ["docs/"],
    fileTypeMultipliers: {
      doc: 1.5, // 50% boost for docs
      impl: 0.5, // 50% penalty for implementation
      config: 0.05, // Config files still penalized
    },
    pathMultipliers: [], // No path-specific boosts in docs mode
  },

  balanced: {
    denylistOverrides: ["docs/"],
    fileTypeMultipliers: {
      doc: 1.0, // No penalty for docs
      impl: 1.0, // No boost for implementation
      // Config files in balanced mode are considered more relevant for understanding
      // a project's structure alongside its documentation. Therefore, we use a
      // higher multiplier (0.3x vs 0.05x in default) to keep them accessible.
      config: 0.3,
    },
    pathMultipliers: [], // No path-specific boosts in balanced mode
    // Skip additive penalty (-1.5) for config files; use only multiplicative penalty.
    // This prevents config files from being completely deprioritized in balanced searches
    // where understanding project setup is often as important as code/docs.
    skipConfigAdditivePenalty: true,
  },

  none: {
    denylistOverrides: [],
    fileTypeMultipliers: {
      doc: 1.0, // No penalty/boost
      impl: 1.0, // No penalty/boost
      config: 1.0, // No penalty/boost
    },
    pathMultipliers: [],
  },

  feature: {
    denylistOverrides: [],
    fileTypeMultipliers: {
      doc: 0.65, // Docs penalty
      impl: 1.25, // Implementation boost
      config: 0.05, // Config penalty
    },
    pathMultipliers: [
      { prefix: "src/server/handlers/", multiplier: 2.5 }, // 新機能ハンドラー
      { prefix: "src/indexer/pipeline/", multiplier: 2.3 }, // パイプライン機能
      { prefix: "src/server/", multiplier: 2.0 },
      { prefix: "src/indexer/", multiplier: 1.8 },
      { prefix: "src/shared/", multiplier: 1.6 },
      { prefix: "scripts/assay/", multiplier: 1.5 }, // 評価スクリプト
      { prefix: "src/", multiplier: 0.7 }, // 抑制: 0.8 → 0.7
    ],
  },

  bugfix: {
    denylistOverrides: [],
    fileTypeMultipliers: {
      doc: 0.65, // Docs penalty
      impl: 1.2, // Implementation boost
      config: 0.05, // Config penalty
    },
    pathMultipliers: [
      { prefix: "src/shared/security/", multiplier: 2.5 }, // セキュリティ修正
      { prefix: "src/shared/utils/", multiplier: 2.3 }, // ユーティリティ修正
      { prefix: "src/server/fallbacks/", multiplier: 2.2 }, // フォールバック
      { prefix: "src/shared/", multiplier: 2.0 },
      { prefix: "src/server/", multiplier: 1.8 },
      { prefix: "src/indexer/", multiplier: 1.6 },
      { prefix: "tests/", multiplier: 1.5 }, // バグ再現テスト
      { prefix: "src/", multiplier: 0.7 }, // 抑制: 0.8 → 0.7
    ],
  },

  debug: {
    denylistOverrides: [],
    fileTypeMultipliers: {
      doc: 0.65, // Docs penalty
      impl: 1.25, // Implementation boost
      config: 0.05, // Config penalty
    },
    pathMultipliers: [
      { prefix: "src/server/observability/", multiplier: 2.5 }, // 監視・トレース
      { prefix: "src/shared/utils/retry.ts", multiplier: 2.4 }, // リトライロジック
      { prefix: "src/server/fallbacks/", multiplier: 2.3 }, // デグレード制御
      { prefix: "src/shared/utils/", multiplier: 2.0 },
      { prefix: "scripts/diag/", multiplier: 1.8 }, // 診断スクリプト
      { prefix: "src/server/", multiplier: 1.6 },
      { prefix: "tests/", multiplier: 1.5 },
      { prefix: "src/", multiplier: 0.7 }, // 抑制: 0.8 → 0.7
    ],
  },

  api: {
    denylistOverrides: ["docs/"],
    fileTypeMultipliers: {
      doc: 0.65, // Docs penalty
      impl: 1.2, // Implementation boost
      config: 0.05, // Config penalty
    },
    pathMultipliers: [
      { prefix: "src/api/", multiplier: 2.5 }, // 強化: 1.4 → 2.5
      { prefix: "src/routes/", multiplier: 2.3 },
      { prefix: "src/controllers/", multiplier: 2.0 },
      { prefix: "src/middleware/", multiplier: 1.8 },
      { prefix: "src/app/", multiplier: 1.3 },
      { prefix: "src/", multiplier: 0.7 }, // 抑制: 1.0 → 0.7
    ],
  },

  editor: {
    denylistOverrides: [],
    fileTypeMultipliers: {
      doc: 0.65, // Docs penalty
      impl: 1.2, // Implementation boost
      config: 0.05, // Config penalty
    },
    pathMultipliers: [
      { prefix: "src/components/", multiplier: 2.2 }, // 強化: 1.3 → 2.2
      { prefix: "src/editor/", multiplier: 2.5 },
      { prefix: "src/ui/", multiplier: 2.0 },
      { prefix: "src/views/", multiplier: 2.0 },
      { prefix: "src/app/", multiplier: 1.5 },
      { prefix: "src/", multiplier: 0.7 }, // 抑制: 1.0 → 0.7
    ],
  },

  testfail: {
    denylistOverrides: [],
    fileTypeMultipliers: {
      doc: 0.65, // Docs penalty
      impl: 1.2, // Implementation boost
      config: 0.05, // Config penalty
    },
    pathMultipliers: [
      { prefix: "tests/", multiplier: 2.5 }, // 強化: 1.5 → 2.5
      { prefix: "test/", multiplier: 2.5 }, // 強化: 1.5 → 2.5
      { prefix: "__tests__/", multiplier: 2.5 },
      { prefix: "spec/", multiplier: 2.3 },
      { prefix: "src/", multiplier: 0.5 }, // 大幅抑制: 1.0 → 0.5
    ],
  },

  typeerror: {
    denylistOverrides: [],
    fileTypeMultipliers: {
      doc: 0.65, // Docs penalty
      impl: 1.2, // Implementation boost
      config: 0.05, // Config penalty
    },
    pathMultipliers: [
      { prefix: "src/types/", multiplier: 3.0 }, // 強化: 1.4 → 3.0
      { prefix: "types/", multiplier: 3.0 }, // 強化: 1.4 → 3.0
      { prefix: "@types/", multiplier: 2.8 },
      { prefix: "src/interfaces/", multiplier: 2.5 },
      { prefix: "src/models/", multiplier: 1.8 },
      { prefix: "src/", multiplier: 0.6 }, // 抑制: 1.0 → 0.6
    ],
  },
};

/**
 * Get boost profile configuration by name
 * @throws Error if profile name is invalid
 */
export function getBoostProfile(name: BoostProfileName): BoostProfileConfig {
  const profile = BOOST_PROFILES[name];
  if (!profile) {
    throw new Error(
      `Invalid boost profile: "${name}". ` +
        `Valid profiles are: ${Object.keys(BOOST_PROFILES).join(", ")}`
    );
  }
  return profile;
}

/**
 * Check if a profile name is valid
 */
export function isValidBoostProfile(name: string): name is BoostProfileName {
  return name in BOOST_PROFILES;
}
