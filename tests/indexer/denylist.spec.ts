import { writeFile } from "node:fs/promises";
import { join } from "node:path";

import { describe, expect, it } from "vitest";

import { createDenylistFilter } from "../../src/indexer/pipeline/filters/denylist.js";
import { createTempRepo } from "../helpers/test-repo.js";

describe("createDenylistFilter", () => {
  it("excludes configured and gitignore patterns", async () => {
    const repo = await createTempRepo({
      ".gitignore": "dist/\n.env.local\n",
      "src/index.ts": "console.log('ok');\n",
    });
    const configPath = join(repo.path, "deny.yml");
    await writeFile(
      configPath,
      ["patterns:", "  - secrets/**", "  - *.pem", "  - .env*"].join("\n"),
      "utf8"
    );

    const filter = createDenylistFilter(repo.path, configPath);
    expect(filter.isDenied("secrets/token.txt")).toBe(true);
    expect(filter.isDenied("dist/app.js")).toBe(true);
    expect(filter.isDenied("README.md")).toBe(false);

    const diff = filter.diff();
    expect(diff).toContain("dist/");
    await repo.cleanup();
  });
});
