import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { describe, expect, it, afterEach } from "vitest";

import type { PathMultiplier } from "../../src/server/boost-profiles.js";
import { loadPathPenalties } from "../../src/server/config-loader.js";

describe("config-loader: path penalties", () => {
  const originalCwd = process.cwd();
  const createdEnv: string[] = [];
  let tempDir: string | null = null;

  afterEach(async () => {
    for (const key of createdEnv.splice(0)) {
      delete process.env[key];
    }
    if (tempDir) {
      await rm(tempDir, { recursive: true, force: true });
      tempDir = null;
    }
    process.chdir(originalCwd);
  });

  it("merges profile < env < YAML with longest-prefix ordering", async () => {
    tempDir = await mkdtemp(join(tmpdir(), "kiri-config-"));
    const configDir = join(tempDir, ".kiri");
    await mkdir(configDir, { recursive: true });
    await writeFile(
      join(configDir, "config.yaml"),
      `path_penalties:
  - prefix: src/
    multiplier: 2.0
  - prefix: external/
    multiplier: 0.25
`
    );

    const envKey = "KIRI_PATH_PENALTY_src__api__";
    process.env[envKey] = "0.5";
    createdEnv.push(envKey);

    process.chdir(tempDir);

    const base: PathMultiplier[] = [
      { prefix: "src/", multiplier: 1.0 },
      { prefix: "external/", multiplier: 0.9 },
    ];

    const merged = loadPathPenalties(base);

    expect(merged).toEqual([
      { prefix: "external/", multiplier: 0.25 }, // YAML overrides profile
      { prefix: "src/api/", multiplier: 0.5 }, // env adds nested prefix
      { prefix: "src/", multiplier: 2.0 }, // YAML overrides profile
    ]);
  });

  it("normalizes prefixes and rejects invalid env multipliers", async () => {
    tempDir = await mkdtemp(join(tmpdir(), "kiri-config-"));
    const configDir = join(tempDir, ".kiri");
    await mkdir(configDir, { recursive: true });
    await writeFile(
      join(configDir, "config.yaml"),
      `path_penalties:
  - prefix: src\\\\feature\\\\
    multiplier: 1.1
`
    );

    process.chdir(tempDir);

    const normalized = loadPathPenalties();
    expect(normalized).toEqual([{ prefix: "src/feature/", multiplier: 1.1 }]);

    const badEnvKey = "KIRI_PATH_PENALTY_external__";
    process.env[badEnvKey] = "not-a-number";
    createdEnv.push(badEnvKey);

    expect(() => loadPathPenalties()).toThrow(/Invalid multiplier/);
  });
});
