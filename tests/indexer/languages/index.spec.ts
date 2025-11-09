import { describe, expect, it } from "vitest";

import {
  getLanguageAnalyzer,
  getSupportedLanguages,
  LANGUAGE_ANALYZERS,
} from "../../../src/indexer/languages/index.js";

describe("Language analyzer registry", () => {
  it("exposes analyzers for every supported language", () => {
    const supported = getSupportedLanguages();
    expect(supported.length).toBeGreaterThan(0);

    for (const language of supported) {
      const analyzer = getLanguageAnalyzer(language);
      expect(analyzer).toBeTruthy();
    }
  });

  it("returns null for unknown languages", () => {
    expect(getLanguageAnalyzer("COBOL")).toBeNull();
    expect(getLanguageAnalyzer(null)).toBeNull();
  });

  it("keeps the registry consistent with supported languages list", () => {
    const supported = new Set(getSupportedLanguages());
    for (const key of LANGUAGE_ANALYZERS.keys()) {
      expect(supported.has(key)).toBe(true);
    }
  });
});
