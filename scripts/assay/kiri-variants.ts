import { KiriSearchAdapter, type KiriAdapterConfig } from "./kiri-adapter.js";

export interface KiriVariantConfig extends KiriAdapterConfig {
  name: string;
  description: string;
  port?: number;
}

export const KIRI_VARIANTS: Record<string, KiriVariantConfig> = {
  default: {
    name: "default",
    description: "Default KIRI configuration (Phase 1 compatible)",
    limit: 5,
    compact: true,
  },
  balanced: {
    name: "balanced",
    description: "Balanced boost with higher limit",
    limit: 15,
    compact: false,
    boostProfile: "balanced",
    port: 20099,
  },
  docs: {
    name: "docs",
    description: "Documentation-focused profile",
    limit: 10,
    compact: true,
    boostProfile: "docs",
    port: 20199,
  },
  noBoost: {
    name: "noBoost",
    description: "Boost profile disabled (baseline)",
    limit: 10,
    compact: true,
    boostProfile: "none",
    port: 20299,
  },
  feature: {
    name: "feature",
    description: "Feature development profile",
    limit: 6,
    compact: true,
    boostProfile: "feature",
    port: 20399,
  },
  bugfix: {
    name: "bugfix",
    description: "Bug fix profile",
    limit: 6,
    compact: true,
    boostProfile: "bugfix",
    port: 20499,
  },
  debug: {
    name: "debug",
    description: "Debug profile",
    limit: 6,
    compact: true,
    boostProfile: "debug",
    port: 20599,
  },
  api: {
    name: "api",
    description: "API development profile",
    limit: 6,
    compact: true,
    boostProfile: "api",
    port: 20699,
  },
  editor: {
    name: "editor",
    description: "Editor integration profile",
    limit: 6,
    compact: true,
    boostProfile: "editor",
    port: 20799,
  },
  testfail: {
    name: "testfail",
    description: "Test failure diagnosis profile",
    limit: 6,
    compact: true,
    boostProfile: "testfail",
    port: 20899,
  },
  typeerror: {
    name: "typeerror",
    description: "Type error debugging profile",
    limit: 6,
    compact: true,
    boostProfile: "typeerror",
    port: 20999,
  },
};

export function getVariantConfig(name: string): KiriVariantConfig {
  const config = KIRI_VARIANTS[name];
  if (!config) {
    throw new Error(
      `Unknown variant: ${name}. Available: ${Object.keys(KIRI_VARIANTS).join(", ")}`
    );
  }
  return config;
}

export function getAvailableVariants(): string[] {
  return Object.keys(KIRI_VARIANTS);
}

export function createKiriAdapter(
  variantName: string,
  databasePath: string,
  repoRoot: string,
  kiriServerPath?: string
): KiriSearchAdapter {
  const config = getVariantConfig(variantName);
  const adapterConfig: KiriAdapterConfig = {};
  if (config.limit !== undefined) {
    adapterConfig.limit = config.limit;
  }
  if (config.compact !== undefined) {
    adapterConfig.compact = config.compact;
  }
  if (config.boostProfile !== undefined) {
    adapterConfig.boostProfile = config.boostProfile;
  }

  return new KiriSearchAdapter(
    databasePath,
    repoRoot,
    kiriServerPath,
    config.port ?? 19999,
    adapterConfig
  );
}
