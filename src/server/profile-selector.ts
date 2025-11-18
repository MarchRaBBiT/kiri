/**
 * Dynamic Boost Profile Selector
 *
 * Analyzes query text and automatically selects the most appropriate boost profile
 * based on query intent and keywords.
 */

import type { BoostProfileName } from "./boost-profiles.js";

/**
 * Query category detection patterns
 */
interface ProfilePattern {
  profile: BoostProfileName;
  keywords: string[];
  weight: number; // Higher weight = higher priority
}

const PROFILE_PATTERNS: ProfilePattern[] = [
  // Test-related queries (English + Japanese)
  {
    profile: "testfail",
    keywords: [
      // English
      "test fail",
      "test error",
      "test crash",
      "failing test",
      "broken test",
      "test suite",
      "test case",
      "unit test",
      "integration test",
      "spec fail",
      "flaky test",
      "test timeout",
      "snapshot test",
      "e2e test",
      // Japanese (shorter for better partial matching, specific to tests)
      "テストが", // More specific
      "テスト",
      "失敗",
      "壊れ",
      "スイート",
      "ケース",
      "ユニット",
      "統合",
      "通らない",
      "スナップショット",
    ],
    weight: 10,
  },

  // Type error queries (English + Japanese)
  {
    profile: "typeerror",
    keywords: [
      // English
      "type error",
      "typescript error",
      "type mismatch",
      "cannot assign",
      "property does not exist",
      "type definition",
      "interface",
      "type check",
      "type guard",
      "generic type",
      "return type",
      // Japanese (shorter for better partial matching)
      "型エラー", // More specific first
      "型",
      "type",
      "typescript",
      "不一致",
      "定義",
      "インターフェース",
      "チェック",
      "推論",
      "ジェネリック",
      "返り値",
      "プロパティ",
    ],
    weight: 11, // Higher weight to beat "error" in testfail
  },

  // Bug fix queries (English + Japanese)
  {
    profile: "bugfix",
    keywords: [
      // English
      "fix bug",
      "bug fix",
      "resolve issue",
      "crash",
      "error",
      "broken",
      "not working",
      "regression",
      "memory leak",
      "race condition",
      "null pointer",
      // Japanese (shorter for better partial matching)
      "バグ",
      "修正",
      "不具合",
      "クラッシュ",
      "動かない",
      "リグレッション",
      "メモリリーク",
      "競合",
    ],
    weight: 8,
  },

  // Debug queries (English + Japanese)
  {
    profile: "debug",
    keywords: [
      // English
      "debug",
      "debugger",
      "console log",
      "trace",
      "inspect",
      "troubleshoot",
      "diagnose",
      // Japanese (shorter for better partial matching)
      "デバッグ",
      "デバッガ",
      "ログ",
      "トレース",
      "診断",
      "トラブル",
      "調査",
    ],
    weight: 8,
  },

  // API-related queries (English + Japanese)
  {
    profile: "api",
    keywords: [
      // English
      "api",
      "endpoint",
      "rest",
      "graphql",
      "request",
      "response",
      "route",
      "controller",
      "http",
      "handler",
      // Japanese (shorter for better partial matching)
      "エンドポイント",
      "リクエスト",
      "レスポンス",
      "ルート",
      "コントローラ",
      "ハンドラ",
    ],
    weight: 7,
  },

  // Editor/UI queries (English + Japanese)
  {
    profile: "editor",
    keywords: [
      // English
      "editor",
      "ui",
      "component",
      "render",
      "display",
      "view",
      "layout",
      "style",
      // Japanese (shorter for better partial matching)
      "エディタ",
      "コンポーネント",
      "レンダリング",
      "表示",
      "ビュー",
      "レイアウト",
      "スタイル",
    ],
    weight: 7,
  },

  // Feature development queries (English + Japanese)
  {
    profile: "feature",
    keywords: [
      // English
      "add feature",
      "new feature",
      "implement",
      "create",
      "build",
      "develop",
      // Japanese (shorter for better partial matching)
      "新機能",
      "機能",
      "実装",
      "開発",
      "作成",
      "構築",
    ],
    weight: 5,
  },

  // Performance queries (English + Japanese)
  {
    profile: "debug", // Map performance queries to debug
    keywords: [
      // English
      "performance",
      "slow",
      "bottleneck",
      "latency",
      "optimization",
      "optimize",
      // Japanese (shorter for better partial matching)
      "パフォーマンス",
      "遅い",
      "ボトルネック",
      "最適化",
      "高速",
    ],
    weight: 6,
  },
];

/**
 * Pre-compiled patterns for efficient keyword matching.
 * Each pattern combines all keywords into a single regex with capturing groups.
 */
interface CompiledPattern {
  profile: BoostProfileName;
  regex: RegExp;
  weight: number;
  keywords: string[]; // Keep original keywords for explainProfileSelection
}

const COMPILED_PATTERNS: CompiledPattern[] = PROFILE_PATTERNS.map((pattern) => {
  // Escape special regex characters and create alternation pattern
  const escapedKeywords = pattern.keywords.map((k) =>
    k.toLowerCase().replace(/[.*+?^${}()|[\]\\]/g, "\\$&")
  );
  const regexPattern = escapedKeywords.join("|");

  return {
    profile: pattern.profile,
    regex: new RegExp(regexPattern, "gi"), // 'g' for global matching, 'i' for case-insensitive
    weight: pattern.weight,
    keywords: pattern.keywords,
  };
});

/**
 * Analyzes query text and returns the most appropriate boost profile
 *
 * Performance: O(n) where n is the number of profiles (uses pre-compiled regex)
 *
 * @param query - Query text to analyze
 * @param fallback - Fallback profile if no match found (default: "default")
 * @returns Selected boost profile name
 */
export function selectProfileFromQuery(
  query: string,
  fallback: BoostProfileName = "default"
): BoostProfileName {
  const normalizedQuery = query.toLowerCase().trim();

  if (normalizedQuery.length === 0) {
    return fallback;
  }

  let bestMatch: BoostProfileName = fallback;
  let highestScore = 0;

  for (const pattern of COMPILED_PATTERNS) {
    // Count all matches using the regex
    const matches = normalizedQuery.match(pattern.regex);
    const matchCount = matches ? matches.length : 0;

    if (matchCount > 0) {
      const score = matchCount * pattern.weight;
      if (score > highestScore) {
        highestScore = score;
        bestMatch = pattern.profile;
      }
    }
  }

  return bestMatch;
}

/**
 * Explains why a particular profile was selected (for debugging/logging)
 *
 * @param query - Query text
 * @param selectedProfile - The profile that was selected
 * @returns Explanation string
 */
export function explainProfileSelection(query: string, selectedProfile: BoostProfileName): string {
  const normalizedQuery = query.toLowerCase().trim();
  const matchedKeywords: string[] = [];

  for (const pattern of COMPILED_PATTERNS) {
    if (pattern.profile === selectedProfile) {
      // Use original keywords for more readable explanation
      for (const keyword of pattern.keywords) {
        if (normalizedQuery.includes(keyword.toLowerCase())) {
          matchedKeywords.push(keyword);
        }
      }
      break;
    }
  }

  if (matchedKeywords.length === 0) {
    return `Using fallback profile: ${selectedProfile}`;
  }

  return `Selected "${selectedProfile}" based on keywords: ${matchedKeywords.join(", ")}`;
}

/**
 * Returns all available profiles and their patterns (for documentation)
 */
export function getAvailableProfiles(): Array<{
  profile: BoostProfileName;
  keywords: string[];
}> {
  return PROFILE_PATTERNS.map((p) => ({
    profile: p.profile,
    keywords: p.keywords,
  }));
}
