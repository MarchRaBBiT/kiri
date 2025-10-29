import { readFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

import { parse as parseYAML } from "yaml";

/**
 * スコアリングウェイトの設定
 * context.bundle の候補ファイルに対するスコアリング重みを定義
 */
export interface ScoringWeights {
  /** テキストマッチ（キーワード検索）の重み */
  textMatch: number;
  /** 編集中ファイル（editing_path）の重み */
  editingPath: number;
  /** 依存関係の重み */
  dependency: number;
  /** 近接ファイル（同一ディレクトリ）の重み */
  proximity: number;
  /** セマンティック類似度の重み */
  semantic: number;
}

export type ScoringProfileName = "default" | "bugfix" | "testfail" | "typeerror" | "feature";

// プロファイルキャッシュ（起動時に一度だけロード）
let profilesCache: Record<ScoringProfileName, ScoringWeights> | null = null;

function loadProfilesFromConfig(): Record<ScoringProfileName, ScoringWeights> {
  if (profilesCache) {
    return profilesCache;
  }

  try {
    // 環境変数でカスタムパスを指定可能
    const configPath =
      process.env.KIRI_SCORING_CONFIG ??
      join(fileURLToPath(import.meta.url), "../../../config/scoring-profiles.yml");

    const configContent = readFileSync(configPath, "utf-8");
    const parsed = parseYAML(configContent) as Record<string, ScoringWeights>;

    // 必須プロファイルの検証
    const requiredProfiles: ScoringProfileName[] = [
      "default",
      "bugfix",
      "testfail",
      "typeerror",
      "feature",
    ];
    for (const profile of requiredProfiles) {
      if (!parsed[profile]) {
        throw new Error(`Missing required scoring profile: ${profile}`);
      }
    }

    profilesCache = parsed as Record<ScoringProfileName, ScoringWeights>;
    return profilesCache;
  } catch (error) {
    console.warn("Failed to load scoring profiles from config, using fallback defaults", error);
    // フォールバック: ハードコードされたデフォルト値
    profilesCache = {
      default: {
        textMatch: 1.0,
        editingPath: 2.0,
        dependency: 0.5,
        proximity: 0.25,
        semantic: 0.75,
      },
      bugfix: { textMatch: 1.0, editingPath: 1.8, dependency: 0.7, proximity: 0.35, semantic: 0.9 },
      testfail: {
        textMatch: 1.0,
        editingPath: 1.6,
        dependency: 0.85,
        proximity: 0.3,
        semantic: 0.8,
      },
      typeerror: {
        textMatch: 1.0,
        editingPath: 1.4,
        dependency: 0.6,
        proximity: 0.4,
        semantic: 0.6,
      },
      feature: {
        textMatch: 1.0,
        editingPath: 1.5,
        dependency: 0.45,
        proximity: 0.5,
        semantic: 0.7,
      },
    };
    return profilesCache;
  }
}

export function coerceProfileName(name?: string | null): ScoringProfileName | null {
  if (!name) {
    return null;
  }
  const profiles = loadProfilesFromConfig();
  const normalized = name.toLowerCase() as ScoringProfileName;
  return normalized in profiles ? normalized : null;
}

export function loadScoringProfile(profileName?: ScoringProfileName | null): ScoringWeights {
  const profiles = loadProfilesFromConfig();
  if (profileName && profileName in profiles) {
    return profiles[profileName];
  }
  return profiles.default;
}
