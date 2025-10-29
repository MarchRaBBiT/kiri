import { mkdir, mkdtemp, writeFile } from "node:fs/promises";
import { join } from "node:path";

import { afterEach, describe, expect, it } from "vitest";

import { DegradeController } from "../../src/server/fallbacks/degradeController.js";

const tempDirs: string[] = [];

afterEach(async () => {
  const fs = await import("node:fs/promises");
  for (const dir of tempDirs.splice(0)) {
    await fs.rm(dir, { recursive: true, force: true });
  }
});

describe("DegradeController", () => {
  it("enters degrade mode on failure and provides fallback search", async () => {
    const dir = await mkdtemp("degrade-test-");
    tempDirs.push(dir);
    await mkdir(join(dir, "src"));
    await writeFile(join(dir, "src", "file.ts"), "export const value = 42;\nconsole.log(value);\n");

    const controller = new DegradeController(dir);
    await expect(
      controller.withResource(async () => {
        throw new Error("duckdb down");
      }, "duckdb")
    ).rejects.toThrow();

    expect(controller.current.active).toBe(true);
    const results = controller.search("console value");
    expect(results[0]?.path).toContain("src/file.ts");
  });
});
