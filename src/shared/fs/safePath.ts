import { resolve, relative, sep } from "node:path";
import process from "node:process";

const SAFE_PATH_PATTERN = /^[\w .:\\/-]+$/;

interface SafePathOptions {
  baseDir?: string;
  allowOutsideBase?: boolean;
}

export function resolveSafePath(inputPath: string, options?: SafePathOptions): string {
  if (!inputPath || typeof inputPath !== "string") {
    throw new Error("Path must be a non-empty string");
  }

  const trimmed = inputPath.trim();
  const allowOutsideBase = options?.allowOutsideBase ?? false;
  const baseDir = resolve(options?.baseDir ?? process.cwd());

  if (!allowOutsideBase && !SAFE_PATH_PATTERN.test(trimmed)) {
    throw new Error(`Invalid characters in path: ${trimmed}`);
  }

  const resolved = resolve(baseDir, trimmed);

  if (allowOutsideBase) {
    return resolved;
  }

  const relativePath = relative(baseDir, resolved);
  if (relativePath === "" || relativePath === ".") {
    return resolved;
  }

  if (relativePath.startsWith(`..${sep}`) || relativePath === "..") {
    throw new Error(`Path traversal attempt detected: ${inputPath}`);
  }

  return resolved;
}
