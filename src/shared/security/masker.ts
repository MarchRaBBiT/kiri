export interface MaskingOptions {
  tokens: string[];
  replacement?: string;
}

export interface MaskResult<T> {
  masked: T;
  applied: number;
}

/**
 * トークンパターンの妥当性を検証してReDoS攻撃を防ぐ
 * @param token 検証対象のトークン文字列
 * @throws パターンが長すぎる、またはネストした量指定子を含む場合
 */
function validateTokenPattern(token: string): void {
  if (token.length > 100) {
    throw new Error("Token pattern exceeds maximum length. Use shorter patterns.");
  }
  // ネストした量指定子による壊滅的バックトラッキングを防ぐ
  if (/(\*|\+|\{)\s*(\*|\+|\{)/.test(token)) {
    throw new Error("Invalid pattern contains nested quantifiers. Simplify the pattern.");
  }
}

function maskString(input: string, tokens: string[], replacement: string): MaskResult<string> {
  let applied = 0;
  let output = input;
  for (const token of tokens) {
    if (!token) continue;
    validateTokenPattern(token); // ReDoS対策の検証を追加
    const escaped = token.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    const pattern = new RegExp(escaped, "g");
    const matches = output.match(pattern);
    if (matches && matches.length > 0) {
      applied += matches.length;
      output = output.replace(pattern, replacement);
    }
  }
  return { masked: output, applied };
}

export function maskValue(value: unknown, options: MaskingOptions): MaskResult<unknown> {
  if (typeof value === "string") {
    return maskString(value, options.tokens, options.replacement ?? "***");
  }
  if (Array.isArray(value)) {
    let applied = 0;
    const maskedArray = value.map((item) => {
      const result = maskValue(item, options);
      applied += result.applied;
      return result.masked;
    });
    return { masked: maskedArray, applied };
  }
  if (value && typeof value === "object") {
    let applied = 0;
    const entries = Object.entries(value as Record<string, unknown>).map(([key, item]) => {
      const result = maskValue(item, options);
      applied += result.applied;
      return [key, result.masked];
    });
    return { masked: Object.fromEntries(entries), applied };
  }
  return { masked: value, applied: 0 };
}
