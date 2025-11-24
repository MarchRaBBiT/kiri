export interface AdaptiveKConfig {
  enabled: boolean;
  allowedSet: number[];
  kMin: number;
  kMax: number;
  kMap: Record<string, number>;
  kDefault: number;
  kWhenDisabled: number;
}

export type QueryCategory = string | undefined;

export function getAdaptiveK(category: QueryCategory, config: AdaptiveKConfig): number {
  if (!config.enabled) {
    return config.kWhenDisabled;
  }
  const value =
    category !== undefined ? (config.kMap[category] ?? config.kDefault) : config.kDefault;
  return value;
}
