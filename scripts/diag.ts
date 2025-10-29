import { execSync } from "node:child_process";
import process from "node:process";

import { createDenylistFilter } from "../src/indexer/pipeline/filters/denylist.js";

import { checkHealth } from "./diag/health.js";

function run(command: string): string {
  return execSync(command, { encoding: "utf8" }).trim();
}

export function collectDiagnostics(): Record<string, string> {
  return {
    node: run("node --version"),
    pnpm: run("pnpm --version"),
    gitStatus: run("git status -sb"),
  };
}

export function checkDenylist(repoRoot = process.cwd()): string[] {
  const filter = createDenylistFilter(repoRoot);
  return filter.diff();
}

export async function main(argv = process.argv.slice(2)): Promise<number> {
  const [command] = argv;
  try {
    switch (command) {
      case "check-denylist": {
        const diff = checkDenylist();
        if (diff.length === 0) {
          console.info("Denylist matches .gitignore patterns.");
          return 0;
        }
        console.warn("Patterns present in .gitignore but missing from config/denylist.yml:");
        for (const entry of diff) {
          console.warn(`  - ${entry}`);
        }
        return 1;
      }
      case "health": {
        const report = await checkHealth();
        console.info(JSON.stringify(report, null, 2));
        return report.metricsReachable ? 0 : 1;
      }
      case undefined:
        console.info(JSON.stringify(collectDiagnostics(), null, 2));
        return 0;
      default:
        console.error(`Unknown diag command: ${command}`);
        return 1;
    }
  } catch (error) {
    console.error("診断コマンドの実行に失敗しました", error);
    return 1;
  }
}

const executedDirectly =
  typeof process.argv[1] === "string" && new URL(import.meta.url).pathname === process.argv[1];

if (executedDirectly) {
  main().then((code) => {
    process.exitCode = code;
  });
}
