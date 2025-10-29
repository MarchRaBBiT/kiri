export function encode(text: string): number[] {
  const codePoints = Array.from(text);
  return codePoints.map((_, index) => index);
}
