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

const PROFILE_WEIGHTS: Record<ScoringProfileName, ScoringWeights> = {
  default: {
    textMatch: 1.0,
    editingPath: 2.0,
    dependency: 0.5,
    proximity: 0.25,
    semantic: 0.75,
  },
  bugfix: {
    textMatch: 1.0,
    editingPath: 1.8,
    dependency: 0.7,
    proximity: 0.35,
    semantic: 0.9,
  },
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

export function coerceProfileName(name?: string | null): ScoringProfileName | null {
  if (!name) {
    return null;
  }
  const normalized = name.toLowerCase() as ScoringProfileName;
  return normalized in PROFILE_WEIGHTS ? normalized : null;
}

export function loadScoringProfile(profileName?: ScoringProfileName | null): ScoringWeights {
  if (profileName && profileName in PROFILE_WEIGHTS) {
    return PROFILE_WEIGHTS[profileName];
  }
  return PROFILE_WEIGHTS.default;
}
