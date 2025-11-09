import { describe, expect, it } from "vitest";

import { phpAnalyzer } from "../../../src/indexer/languages/php.js";

describe("PHP analyzer", () => {
  it("extracts traits, properties, constants, and methods", async () => {
    const content = `<?php
trait FeatureToggle {
  private $enabled;
  const VERSION = '1.0.0';

  public function enable() {
    $this->enabled = true;
  }
}
`;

    const result = await phpAnalyzer.analyze({
      pathInRepo: "src/FeatureToggle.php",
      content,
      fileSet: new Set(),
    });

    expect(result.symbols.map((symbol) => symbol.kind)).toEqual([
      "trait",
      "property",
      "constant",
      "method",
    ]);
    expect(result.snippets).toHaveLength(result.symbols.length);
  });
});
