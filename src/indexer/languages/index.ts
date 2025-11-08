import { dartAnalyzer } from "./dart.js";
import { javaAnalyzer } from "./java.js";
import { phpAnalyzer } from "./php.js";
import { swiftAnalyzer } from "./swift.js";
import { typescriptAnalyzer } from "./typescript.js";
import type { LanguageAnalyzer } from "./types.js";

const LANGUAGE_ANALYZERS = new Map<string, LanguageAnalyzer>([
  ["TypeScript", typescriptAnalyzer],
  ["Swift", swiftAnalyzer],
  ["PHP", phpAnalyzer],
  ["Java", javaAnalyzer],
  ["Dart", dartAnalyzer],
]);

export function getLanguageAnalyzer(language: string | null | undefined): LanguageAnalyzer | null {
  if (!language) return null;
  return LANGUAGE_ANALYZERS.get(language) ?? null;
}

export function getSupportedLanguages(): string[] {
  return Array.from(LANGUAGE_ANALYZERS.keys());
}

export { LANGUAGE_ANALYZERS };
