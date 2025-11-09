import { describe, expect, it } from "vitest";

import { javaAnalyzer } from "../../../src/indexer/languages/java.js";

describe("Java analyzer", () => {
  it("extracts classes, fields, constructors, and methods", async () => {
    const content = `
package app;

public class Greeter {
  private final String name;

  public Greeter(String name) {
    this.name = name;
  }

  public String greet() {
    return "Hello " + this.name;
  }
}
`;

    const result = await javaAnalyzer.analyze({
      pathInRepo: "src/app/Greeter.java",
      content,
      fileSet: new Set(["src/app/Greeter.java"]),
    });

    expect(result.symbols.map((symbol) => symbol.kind)).toEqual([
      "class",
      "field",
      "constructor",
      "method",
    ]);
  });
});
