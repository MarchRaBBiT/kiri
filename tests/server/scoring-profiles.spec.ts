import { describe, it, expect } from "vitest";

import { loadScoringProfile } from "../../src/server/scoring.js";

describe("scoring profiles", () => {
  it("default profile stays within regression guardrails", () => {
    const profile = loadScoringProfile("default");
    expect(profile.textMatch).toBeGreaterThanOrEqual(0.8);
    expect(profile.docPenaltyMultiplier).toBeLessThanOrEqual(0.7);
    expect(profile.configPenaltyMultiplier).toBeLessThanOrEqual(0.1);
    expect(profile.implBoostMultiplier).toBeGreaterThanOrEqual(1);
  });
});
