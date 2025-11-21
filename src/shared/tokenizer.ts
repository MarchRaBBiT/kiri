export function encode(text: string): number[] {
  const codePoints = Array.from(text);
  return codePoints.map((_, index) => index);
}

/**
 * 共有トークン化ユーティリティ
 * handlers.tsとembedding.tsで一貫したトークン化を提供
 */

export type TokenizationStrategy = "phrase-aware" | "legacy" | "hybrid";

const LEGACY_TOKEN_PATTERN = /[\p{L}\p{N}_]+/gu;
const DEFAULT_TOKEN_PATTERN = /[\p{L}\p{N}_-]+/gu;

/**
 * 環境変数からトークン化戦略を取得
 */
export function getTokenizationStrategy(): TokenizationStrategy {
  const strategy = process.env.KIRI_TOKENIZATION_STRATEGY?.toLowerCase();
  if (strategy === "legacy" || strategy === "hybrid") {
    return strategy;
  }
  return "phrase-aware"; // デフォルト
}

/**
 * テキストをトークンに分割
 * Unicode文字に対応し、camelCase / snake_case / hyphenated の両立を実現
 *
 * @param text - トークン化するテキスト
 * @param strategy - トークン化戦略（省略時は環境変数から取得）
 * @returns トークンの配列
 */
export function tokenizeText(text: string, strategy?: TokenizationStrategy): string[] {
  const effectiveStrategy = strategy ?? getTokenizationStrategy();
  const pattern = effectiveStrategy === "legacy" ? LEGACY_TOKEN_PATTERN : DEFAULT_TOKEN_PATTERN;
  const matches = text.match(pattern);
  if (!matches) {
    return [];
  }

  const tokens: string[] = [];
  const seen = new Set<string>();

  for (const rawToken of matches) {
    for (const variant of expandTokenVariants(rawToken)) {
      const normalized = variant.toLowerCase();
      if (normalized.length === 0 || seen.has(normalized)) {
        continue;
      }
      seen.add(normalized);
      tokens.push(normalized);
    }
  }

  return tokens;
}

/**
 * ハイフン/アンダースコアを維持しつつ、分割語も生成
 */
function expandTokenVariants(rawToken: string): string[] {
  const variants = new Set<string>();
  variants.add(rawToken);

  // snake_case / kebab-case
  const compoundParts = rawToken.split(/[-_]/);
  if (compoundParts.length > 1) {
    for (const part of compoundParts) {
      for (const segment of splitIdentifierSegments(part)) {
        variants.add(segment);
      }
    }
  } else {
    for (const segment of splitIdentifierSegments(rawToken)) {
      variants.add(segment);
    }
  }

  return Array.from(variants).filter((token) => token.length > 0);
}

/**
 * camelCase / 数値混在の識別子を分割
 *
 * 例: workerPoolScheduler → ["worker", "Pool", "Scheduler"]
 * 例: ISO8601Parser → ["ISO", "8601", "Parser"]
 */
function splitIdentifierSegments(value: string): string[] {
  if (value.length === 0) {
    return [];
  }

  const segments: string[] = [];
  let current = value[0] ?? "";

  for (let index = 1; index < value.length; index += 1) {
    const char = value[index]!;
    const previous = value[index - 1]!;
    const next = value[index + 1];

    if (shouldSplit(previous, char, next)) {
      segments.push(current);
      current = char;
    } else {
      current += char;
    }
  }

  segments.push(current);
  return segments;
}

function shouldSplit(previous: string, current: string, next?: string): boolean {
  if (isLower(previous) && isUpper(current)) {
    return true;
  }
  if (isLetter(previous) && isDigit(current)) {
    return true;
  }
  if (isDigit(previous) && isLetter(current)) {
    return true;
  }
  if (isUpper(previous) && isUpper(current) && next !== undefined && isLower(next)) {
    return true;
  }
  return false;
}

function isLetter(char: string): boolean {
  return /\p{L}/u.test(char);
}

function isLower(char: string): boolean {
  return /\p{Ll}/u.test(char);
}

function isUpper(char: string): boolean {
  return /\p{Lu}/u.test(char);
}

function isDigit(char: string): boolean {
  return /\p{N}/u.test(char);
}
