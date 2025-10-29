#!/usr/bin/env node
import process from "node:process";

import { bootstrapServer } from "../server/bootstrap.js";
import { evaluateSecurityStatus, updateSecurityLock } from "../shared/security/config.js";

function printUsage(): void {
  console.info(`Usage: pnpm exec tsx src/client/cli.ts <command> [options]\n`);
  console.info(`Commands:`);
  console.info(`  security verify [--write-lock]    Verify security baseline matches lock file`);
}

function formatStatus(): string {
  const status = evaluateSecurityStatus();
  const lockInfo = status.lockHash ? `hash=${status.lockHash}` : "missing";
  const matchState = status.matches ? "MATCH" : "MISMATCH";
  return [
    `config: ${status.configPath}`,
    `lock: ${status.lockPath} (${lockInfo})`,
    `state: ${matchState}`,
  ].join("\n");
}

function handleSecurityVerify(argv: string[]): number {
  const writeLock = argv.includes("--write-lock");
  const status = evaluateSecurityStatus();
  if (!status.lockHash && writeLock) {
    updateSecurityLock(status.hash);
    console.info("Security lock created.");
    const refreshed = evaluateSecurityStatus();
    console.info(
      [
        `config: ${refreshed.configPath}`,
        `lock: ${refreshed.lockPath} (hash=${refreshed.lockHash})`,
        "state: MATCH",
      ].join("\n")
    );
    return 0;
  }
  try {
    bootstrapServer({ allowWriteLock: writeLock });
    console.info("Security baseline verified.");
    console.info(formatStatus());
    return 0;
  } catch (error) {
    console.error(error instanceof Error ? error.message : String(error));
    console.info(formatStatus());
    return 1;
  }
}

export function main(argv = process.argv.slice(2)): number {
  const [command, ...rest] = argv;
  switch (command) {
    case "security": {
      const [subcommand, ...subArgs] = rest;
      if (subcommand === "verify") {
        return handleSecurityVerify(subArgs);
      }
      break;
    }
    case undefined:
      printUsage();
      return 1;
    default:
      break;
  }
  printUsage();
  return 1;
}

if (process.argv[1] && new URL(import.meta.url).pathname === process.argv[1]) {
  process.exitCode = main();
}
