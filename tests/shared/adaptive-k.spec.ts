import { describe, it, expect } from "vitest";

import { getAdaptiveK } from "../../src/shared/adaptive-k.js";
import { validateAdaptiveKConfig } from "../../src/shared/config-validate-adaptive-k.js";

const baseConfig = {
  enabled: true,
  allowedSet: [5, 10, 20],
  kMin: 3,
  kMax: 50,
  kMap: {
    bugfix: 5,
    integration: 5,
    testfail: 20,
    performance: 20,
  },
  kDefault: 10,
  kWhenDisabled: 10,
};

describe("getAdaptiveK", () => {
  it("returns category mapping when enabled", () => {
    expect(getAdaptiveK("bugfix", baseConfig)).toBe(5);
    expect(getAdaptiveK("testfail", baseConfig)).toBe(20);
    expect(getAdaptiveK("performance", baseConfig)).toBe(20);
    expect(getAdaptiveK("unknown", baseConfig)).toBe(10);
  });

  it("returns kWhenDisabled when disabled", () => {
    const cfg = { ...baseConfig, enabled: false, kWhenDisabled: 7 };
    expect(getAdaptiveK("bugfix", cfg)).toBe(7);
    expect(getAdaptiveK(undefined, cfg)).toBe(7);
  });
});

describe("validateAdaptiveKConfig", () => {
  it("accepts valid config", () => {
    expect(() => validateAdaptiveKConfig(baseConfig)).not.toThrow();
  });

  it("rejects allowedSet outside range", () => {
    const cfg = { ...baseConfig, allowedSet: [2] };
    expect(() => validateAdaptiveKConfig(cfg)).toThrow();
  });

  it("rejects empty allowedSet", () => {
    const cfg = { ...baseConfig, allowedSet: [] };
    expect(() => validateAdaptiveKConfig(cfg)).toThrow();
  });

  it("rejects kDefault not in allowedSet when enabled", () => {
    const cfg = { ...baseConfig, kDefault: 15 };
    expect(() => validateAdaptiveKConfig(cfg)).toThrow();
  });
});
