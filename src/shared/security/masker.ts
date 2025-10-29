export interface MaskingOptions {
  tokens: string[];
  replacement?: string;
}

export interface MaskResult<T> {
  masked: T;
  applied: number;
}

function maskString(input: string, tokens: string[], replacement: string): MaskResult<string> {
  let applied = 0;
  let output = input;
  for (const token of tokens) {
    if (!token) continue;
    const pattern = new RegExp(token.replace(/[.*+?^${}()|[\]\\]/g, "\\$&"), "g");
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
