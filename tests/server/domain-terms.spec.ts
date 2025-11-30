import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { afterEach, describe, expect, it } from "vitest";

import { DomainTermsDictionary, loadDomainTerms } from "../../src/server/domain-terms.js";

const cleanups: Array<() => Promise<void>> = [];

afterEach(async () => {
  for (const cleanup of cleanups.splice(0, cleanups.length)) {
    await cleanup();
  }
});

describe("domain terms dictionary", () => {
  it("normalizes camelCase and hyphenated aliases and returns path hints", async () => {
    const dir = await mkdtemp(join(tmpdir(), "domain-terms-"));
    cleanups.push(async () => rm(dir, { recursive: true, force: true }));
    const configPath = join(dir, "domain-terms.yml");
    await writeFile(
      configPath,
      `stats:\n  - mann-whitney-u:\n      aliases:\n        - mannWhitneyU\n        - Wilcoxon_Test\n      files:\n        - src/stats/mann.ts\n  - rank-biserial:\n      aliases:\n        - rankBiserialEffect\n        - effect-size\n      files:\n        - src/stats/rank-biserial.ts\n`
    );

    const dictionary = loadDomainTerms({ configPath });
    const expansion = dictionary.expandFromText("wilcoxon-test and effect-size");

    expect(expansion.aliases).toEqual(
      expect.arrayContaining(["mann-whitney-u", "rank-biserial", "effect-size", "wilcoxon-test"])
    );
    expect(expansion.fileHints).toEqual([
      { path: "src/stats/mann.ts", source: "mann-whitney-u" },
      { path: "src/stats/rank-biserial.ts", source: "rank-biserial" },
    ]);
  });

  it("returns an empty expansion when no terms match", () => {
    const dictionary = new DomainTermsDictionary([]);
    const expansion = dictionary.expandFromText("unrelated phrase");
    expect(expansion.aliases).toHaveLength(0);
    expect(expansion.fileHints).toHaveLength(0);
  });
});
