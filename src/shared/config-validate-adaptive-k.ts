import type { AdaptiveKConfig } from "./adaptive-k.js";

function assertFinite(value: number, name: string): void {
  if (!Number.isFinite(value)) {
    throw new Error(`${name} must be a finite number`);
  }
}

export function validateAdaptiveKConfig(config: AdaptiveKConfig): void {
  assertFinite(config.kMin, "adaptiveK.kMin");
  assertFinite(config.kMax, "adaptiveK.kMax");
  if (config.kMin < 0) {
    throw new Error("adaptiveK.kMin must be >= 0");
  }
  if (config.kMax <= config.kMin) {
    throw new Error("adaptiveK.kMax must be greater than kMin");
  }

  if (!Array.isArray(config.allowedSet) || config.allowedSet.length === 0) {
    throw new Error("adaptiveK.allowedSet must be a non-empty array");
  }
  for (const value of config.allowedSet) {
    assertFinite(value, "adaptiveK.allowedSet value");
    if (value < config.kMin || value > config.kMax) {
      throw new Error("adaptiveK.allowedSet values must be within [kMin, kMax]");
    }
  }

  for (const [key, value] of Object.entries(config.kMap)) {
    assertFinite(value, `adaptiveK.kMap[${key}]`);
    if (config.enabled && !config.allowedSet.includes(value)) {
      throw new Error(`adaptiveK.kMap[${key}] must belong to allowedSet when adaptiveK is enabled`);
    }
    if (value < config.kMin || value > config.kMax) {
      throw new Error(`adaptiveK.kMap[${key}] must be within [kMin, kMax]`);
    }
  }

  const defaults = [config.kDefault, config.kWhenDisabled];
  for (const [idx, value] of defaults.entries()) {
    assertFinite(value, idx === 0 ? "adaptiveK.kDefault" : "adaptiveK.kWhenDisabled");
    if (value < config.kMin || value > config.kMax) {
      throw new Error("adaptiveK default values must be within [kMin, kMax]");
    }
  }

  if (config.enabled && !config.allowedSet.includes(config.kDefault)) {
    throw new Error("adaptiveK.kDefault must belong to allowedSet when adaptiveK is enabled");
  }
}
