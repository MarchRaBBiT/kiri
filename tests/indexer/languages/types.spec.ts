import { describe, expect, it } from "vitest";

import {
  buildFallbackSnippet,
  buildSnippetsFromSymbols,
  type SnippetRecord,
  type SymbolRecord,
} from "../../../src/indexer/languages/types.js";

describe("Language analyzer shared helpers", () => {
  it("buildSnippetsFromSymbols mirrors symbol ranges", () => {
    const symbols: SymbolRecord[] = [
      {
        symbolId: 1,
        name: "Example",
        kind: "class",
        rangeStartLine: 2,
        rangeEndLine: 10,
        signature: "class Example {}",
        doc: null,
      },
      {
        symbolId: 2,
        name: "greet",
        kind: "method",
        rangeStartLine: 4,
        rangeEndLine: 8,
        signature: "greet(): string",
        doc: null,
      },
    ];

    const snippets = buildSnippetsFromSymbols(symbols);
    const expected: SnippetRecord[] = [
      { startLine: 2, endLine: 10, symbolId: 1 },
      { startLine: 4, endLine: 8, symbolId: 2 },
    ];

    expect(snippets).toEqual(expected);
  });

  it("buildFallbackSnippet spans the entire file when no symbols exist", () => {
    const fallback = buildFallbackSnippet(42);
    expect(fallback).toEqual({ startLine: 1, endLine: 42, symbolId: null });
  });
});
