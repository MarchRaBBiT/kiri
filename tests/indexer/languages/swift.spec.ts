import { describe, expect, it } from "vitest";

import { swiftAnalyzer } from "../../../src/indexer/languages/swift.js";

describe("Swift analyzer", () => {
  it("captures type members without leaking local variables", async () => {
    const content = `
class Greeter {
  var message: String

  init(message: String) {
    let temp = message.uppercased()
    self.message = temp
  }

  func greet() -> String {
    return message
  }
}

func helper() {}
`.trim();

    const result = await swiftAnalyzer.analyze({
      pathInRepo: "Sources/Greeter.swift",
      content,
      fileSet: new Set(),
    });

    const symbolKinds = result.symbols.map((symbol) => symbol.kind);
    expect(symbolKinds).toEqual(["class", "property", "initializer", "method", "function"]);
    expect(result.symbols.find((symbol) => symbol.name === "temp")).toBeUndefined();
  });
});
