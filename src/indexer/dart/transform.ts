/**
 * Dart Analysis Server の Outline から KIRI の SymbolRecord への変換
 */

import type { SymbolRecord, SnippetRecord } from "../codeintel.js";
import type { Outline, ElementKind } from "./types.js";

/**
 * Outline を SymbolRecord と SnippetRecord に変換
 *
 * @param outline - Analysis Server の Outline
 * @param content - ファイルの内容（行番号計算用）
 * @returns { symbols, snippets }
 */
export function outlineToSymbols(
  outline: Outline,
  content: string
): { symbols: SymbolRecord[]; snippets: SnippetRecord[] } {
  const symbols: Array<Omit<SymbolRecord, "symbolId">> = [];

  // offset → line 変換のためのマップを事前構築
  const offsetToLine = buildOffsetToLineMap(content);

  function visit(node: Outline): void {
    const kind = mapElementKind(node.element.kind as ElementKind);
    if (kind) {
      const startLine = offsetToLine.get(node.offset) ?? 1;
      const endLine = offsetToLine.get(node.offset + node.length) ?? startLine;

      symbols.push({
        name: node.element.name,
        kind,
        rangeStartLine: startLine,
        rangeEndLine: endLine,
        signature: buildSignature(node),
        doc: node.element.dartdoc ?? null,
      });
    }

    // 子要素を再帰的に処理
    node.children?.forEach(visit);
  }

  visit(outline);

  // symbolId を採番
  const symbolRecords = symbols
    .sort((a, b) => a.rangeStartLine - b.rangeStartLine)
    .map((item, index) => ({ symbolId: index + 1, ...item }));

  // snippets を生成（各シンボルの範囲に対応）
  const snippets = symbolRecords.map((symbol) => ({
    startLine: symbol.rangeStartLine,
    endLine: symbol.rangeEndLine,
    symbolId: symbol.symbolId,
  }));

  return { symbols: symbolRecords, snippets };
}

/**
 * Dart ElementKind を KIRI の symbol kind にマッピング
 *
 * Phase 2: EXTENSION_TYPE, OPERATOR, TYPE_ALIAS を追加
 */
function mapElementKind(kind: ElementKind): string | null {
  switch (kind) {
    case "CLASS":
    case "CLASS_TYPE_ALIAS":
    case "ENUM":
    case "MIXIN":
    case "EXTENSION":
    case "EXTENSION_TYPE": // Phase 2: Dart 3.0+ extension type
      return "class";

    case "FUNCTION":
    case "METHOD":
    case "GETTER":
    case "SETTER":
    case "CONSTRUCTOR":
    case "OPERATOR": // Phase 2: operator overloading
      return "function";

    case "FIELD":
    case "TOP_LEVEL_VARIABLE":
    case "ENUM_CONSTANT":
      return "property";

    case "FUNCTION_TYPE_ALIAS":
    case "TYPE_ALIAS": // Phase 2: type Foo = Bar;
      return "type";

    case "LIBRARY":
    case "COMPILATION_UNIT":
      // KIRI ではファイル単位なので個別に記録しない
      return null;

    case "PARAMETER":
    case "TYPE_PARAMETER":
    case "UNIT_TEST_GROUP":
    case "UNIT_TEST_TEST":
    case "UNKNOWN":
      // これらの要素は個別にシンボルとして記録しない
      return null;

    default:
      // その他の要素は無視
      return null;
  }
}

/**
 * Outline からシグネチャ文字列を生成
 *
 * 形式: {returnType} {name}{typeParameters}{parameters}
 */
function buildSignature(node: Outline): string | null {
  const element = node.element;
  const parts: string[] = [];

  // 返り値の型
  if (element.returnType) {
    parts.push(element.returnType);
  }

  // 名前
  parts.push(element.name);

  // 型パラメータ
  if (element.typeParameters) {
    parts.push(element.typeParameters);
  }

  // パラメータ
  if (element.parameters) {
    parts.push(element.parameters);
  }

  const signature = parts.join(" ").trim();

  // シグネチャが名前だけの場合は null を返す（フィールドなど）
  return signature === element.name ? null : signature;
}

/**
 * ファイル内容から offset → line 番号のマップを構築
 *
 * @param content - ファイル内容
 * @returns offset → line (1-based) のMap
 */
function buildOffsetToLineMap(content: string): Map<number, number> {
  const map = new Map<number, number>();
  let offset = 0;
  let line = 1;

  map.set(0, 1); // offset 0 は 1 行目

  for (let i = 0; i < content.length; i++) {
    if (content[i] === "\n") {
      line++;
      map.set(i + 1, line); // 改行の次の文字から新しい行
    }
  }

  // 全ての offset に対応できるよう、中間の offset を補完
  const offsets = Array.from(map.keys()).sort((a, b) => a - b);
  for (let i = 0; i < offsets.length - 1; i++) {
    const startOffset = offsets[i]!;
    const endOffset = offsets[i + 1]!;
    const lineNumber = map.get(startOffset)!;

    for (let offset = startOffset; offset < endOffset; offset++) {
      map.set(offset, lineNumber);
    }
  }

  // 最後のオフセット以降も最後の行番号で埋める
  const lastOffset = offsets[offsets.length - 1] ?? 0;
  const lastLine = map.get(lastOffset) ?? 1;
  for (let offset = lastOffset; offset <= content.length; offset++) {
    if (!map.has(offset)) {
      map.set(offset, lastLine);
    }
  }

  return map;
}
