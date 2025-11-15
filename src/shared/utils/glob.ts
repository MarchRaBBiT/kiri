/**
 * シンプルな glob マッチング - `*` と複数階層の `**` をサポート
 */
export function matchesGlob(path: string, pattern: string): boolean {
  if (!pattern) {
    return false;
  }

  const normalizedPath = path.replace(/^[.][/\\]/u, "");
  const normalizedPattern = pattern.replace(/^[.][/\\]/u, "");

  let regexPattern = normalizedPattern
    .replace(/[.+?^${}()|[\]\\]/g, "\\$&")
    .replace(/\*\*\//g, "DOUBLESTAR_SLASH")
    .replace(/\/\*\*/g, "SLASH_DOUBLESTAR")
    .replace(/\*\*/g, "DOUBLESTAR")
    .replace(/\*/g, "[^/]*")
    .replace(/DOUBLESTAR_SLASH/g, "(?:.*/)?")
    .replace(/SLASH_DOUBLESTAR/g, "(?:/.*)?")
    .replace(/DOUBLESTAR/g, ".*");

  regexPattern = `^${regexPattern}$`;
  return new RegExp(regexPattern).test(normalizedPath);
}
