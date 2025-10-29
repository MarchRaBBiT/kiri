import { createHash } from "node:crypto";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, resolve } from "node:path";

import { parseSimpleYaml } from "../utils/simpleYaml.js";

export interface SecurityConfig {
  allowed_paths: string[];
  allow_network_egress: boolean;
  allow_subprocess: boolean;
  sensitive_tokens: string[];
}

export interface SecurityStatus {
  config: SecurityConfig;
  configPath: string;
  lockPath: string;
  hash: string;
  lockHash: string | null;
  matches: boolean;
}

function assertStringArray(value: unknown, field: string): string[] {
  if (!Array.isArray(value) || !value.every((item) => typeof item === "string")) {
    throw new Error(`${field} must be an array of strings`);
  }
  return value;
}

function assertBoolean(value: unknown, field: string): boolean {
  if (typeof value !== "boolean") {
    throw new Error(`${field} must be a boolean`);
  }
  return value;
}

export function loadSecurityConfig(configPath?: string): { config: SecurityConfig; hash: string } {
  const path = resolve(configPath ?? "config/security.yml");
  const content = readFileSync(path, "utf8");
  const parsed = parseSimpleYaml(content) as Record<string, unknown>;

  const config: SecurityConfig = {
    allowed_paths: assertStringArray(parsed.allowed_paths, "allowed_paths"),
    allow_network_egress: assertBoolean(parsed.allow_network_egress, "allow_network_egress"),
    allow_subprocess: assertBoolean(parsed.allow_subprocess, "allow_subprocess"),
    sensitive_tokens: assertStringArray(parsed.sensitive_tokens, "sensitive_tokens"),
  };

  const hash = createHash("sha256").update(content).digest("hex");
  return { config, hash };
}

export function readSecurityLock(lockPath?: string): string | null {
  try {
    return readFileSync(resolve(lockPath ?? "var/security.lock"), "utf8").trim();
  } catch {
    return null;
  }
}

export function evaluateSecurityStatus(configPath?: string, lockPath?: string): SecurityStatus {
  const { config, hash } = loadSecurityConfig(configPath);
  const stored = readSecurityLock(lockPath);
  return {
    config,
    configPath: resolve(configPath ?? "config/security.yml"),
    lockPath: resolve(lockPath ?? "var/security.lock"),
    hash,
    lockHash: stored,
    matches: stored === null ? false : stored === hash,
  };
}

export function assertSecurityBaseline(configPath?: string, lockPath?: string): SecurityStatus {
  const status = evaluateSecurityStatus(configPath, lockPath);
  if (!status.lockHash) {
    throw new Error(
      `Security lock is missing at ${status.lockPath}. Run 'pnpm exec tsx src/client/cli.ts security verify --write-lock' to establish baseline.`
    );
  }
  if (!status.matches) {
    throw new Error(
      `Security configuration at ${status.configPath} does not match lock. Investigate differences before proceeding.`
    );
  }
  return status;
}

export function updateSecurityLock(hash: string, lockPath?: string): string {
  const path = resolve(lockPath ?? "var/security.lock");
  mkdirSync(dirname(path), { recursive: true });
  writeFileSync(path, `${hash}\n`, "utf8");
  return path;
}
