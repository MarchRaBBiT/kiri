export const ADAPTIVE_K_CATEGORIES = [
  "bugfix",
  "testfail",
  "debug",
  "api",
  "docs",
  "feature",
  "integration",
  "performance",
] as const;

export type AdaptiveKCategory = (typeof ADAPTIVE_K_CATEGORIES)[number];

export const ADAPTIVE_K_CATEGORY_SET = new Set<string>(ADAPTIVE_K_CATEGORIES);

export const ADAPTIVE_K_CATEGORY_ALIASES: Record<string, AdaptiveKCategory> = {
  editor: "feature",
  infra: "integration",
  "docs-plain": "docs",
};
