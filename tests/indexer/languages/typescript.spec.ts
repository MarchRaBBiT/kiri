import { describe, expect, it } from "vitest";

import { typescriptAnalyzer } from "../../../src/indexer/languages/typescript.js";

describe("TypeScript analyzer", () => {
  it("extracts class and method symbols plus path dependencies", async () => {
    const content = `
import { helper } from "./utils";

export class Greeter {
  constructor(private readonly name: string) {}

  greet(): string {
    return helper(this.name);
  }
}
`;

    const fileSet = new Set(["src/utils.ts"]);
    const result = await typescriptAnalyzer.analyze({
      pathInRepo: "src/greeter.ts",
      content,
      fileSet,
    });

    expect(result.symbols.map((symbol) => symbol.kind)).toEqual(["class", "method"]);
    expect(result.dependencies).toContainEqual({
      dstKind: "path",
      dst: "src/utils.ts",
      rel: "import",
    });
    expect(result.snippets).toHaveLength(result.symbols.length);
  });
});
