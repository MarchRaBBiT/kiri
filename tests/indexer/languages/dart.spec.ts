import { describe, expect, it, vi } from "vitest";

vi.mock("../../../src/indexer/dart/analyze.js", () => ({
  analyzeDartSource: vi.fn(),
}));

import { analyzeDartSource } from "../../../src/indexer/dart/analyze.js";
import { dartAnalyzer } from "../../../src/indexer/languages/dart.js";

const analyzeDartSourceMock = analyzeDartSource as ReturnType<typeof vi.fn>;

describe("Dart analyzer", () => {
  it("returns empty analysis when workspaceRoot is missing", async () => {
    const result = await dartAnalyzer.analyze({
      pathInRepo: "lib/main.dart",
      content: "class Foo {}",
      fileSet: new Set(),
    });

    expect(result).toEqual({ symbols: [], snippets: [], dependencies: [] });
    expect(analyzeDartSourceMock).not.toHaveBeenCalled();
  });

  it("delegates to analyzeDartSource when workspaceRoot is provided", async () => {
    const analysis = {
      symbols: [
        {
          symbolId: 1,
          name: "Foo",
          kind: "class",
          rangeStartLine: 1,
          rangeEndLine: 3,
          signature: null,
          doc: null,
        },
      ],
      snippets: [{ startLine: 1, endLine: 3, symbolId: 1 }],
      dependencies: [],
    };
    analyzeDartSourceMock.mockResolvedValueOnce(analysis);

    const result = await dartAnalyzer.analyze({
      pathInRepo: "lib/foo.dart",
      content: "class Foo {}",
      fileSet: new Set(),
      workspaceRoot: "/workspace",
    });

    expect(result).toEqual(analysis);
    expect(analyzeDartSourceMock).toHaveBeenCalledWith(
      "lib/foo.dart",
      "class Foo {}",
      "/workspace"
    );
  });
});
