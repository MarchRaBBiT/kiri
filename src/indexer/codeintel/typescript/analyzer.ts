/**
 * TypeScript Language Analyzer
 *
 * TypeScript Compiler APIを使用したシンボル抽出と依存関係解析。
 * TypeScript/TSX両方をサポート。
 */

import path from "node:path";

import ts from "typescript";

import type {
  LanguageAnalyzer,
  AnalysisContext,
  AnalysisResult,
  SymbolRecord,
  SnippetRecord,
  DependencyRecord,
} from "../types.js";
import { assignSymbolIds, symbolsToSnippets, createDependencyRecorder } from "../utils.js";

/**
 * TypeScript Compiler API の位置情報を 1-based 行番号に変換
 */
function toLineNumber(source: ts.SourceFile, position: number): number {
  return source.getLineAndCharacterOfPosition(position).line + 1;
}

/**
 * シグネチャテキストをサニタイズ
 * - ブロック本体 ({...}) を除去
 * - 最大200文字に切り詰め
 * - 最初の行のみを取得
 */
function sanitizeSignature(source: ts.SourceFile, node: ts.Node): string {
  const start = node.getStart(source);
  const endCandidate = node.forEachChild((child) => {
    if (ts.isBlock(child) || ts.isModuleBlock(child)) {
      return child.getFullStart();
    }
    return undefined;
  });
  const end = typeof endCandidate === "number" ? endCandidate : node.getEnd();
  const snippet = source.text.slice(start, Math.min(end, start + 200));
  return snippet.split(/\r?\n/)[0]?.trim().replace(/\s+/g, " ") ?? "";
}

/**
 * JSDoc コメントを抽出
 */
function getDocComment(node: ts.Node): string | null {
  const tags = ts.getJSDocCommentsAndTags(node);
  const parts: string[] = [];
  for (const tag of tags) {
    if (ts.isJSDoc(tag)) {
      if (typeof tag.comment === "string") {
        parts.push(tag.comment);
      } else if (Array.isArray(tag.comment)) {
        parts.push(
          tag.comment.map((part) => (typeof part === "string" ? part : part.text)).join("")
        );
      }
    }
  }
  if (parts.length === 0) {
    return null;
  }
  return parts.join("\n").trim() || null;
}

/**
 * AST を走査してシンボルを抽出
 */
function extractSymbols(source: ts.SourceFile): SymbolRecord[] {
  const results: Array<Omit<SymbolRecord, "symbolId">> = [];

  const visit = (node: ts.Node): void => {
    if (ts.isFunctionDeclaration(node) && node.name) {
      results.push({
        name: node.name.getText(source),
        kind: "function",
        rangeStartLine: toLineNumber(source, node.getStart(source)),
        rangeEndLine: toLineNumber(source, node.getEnd()),
        signature: sanitizeSignature(source, node),
        doc: getDocComment(node),
      });
    } else if (ts.isClassDeclaration(node) && node.name) {
      results.push({
        name: node.name.getText(source),
        kind: "class",
        rangeStartLine: toLineNumber(source, node.getStart(source)),
        rangeEndLine: toLineNumber(source, node.getEnd()),
        signature: sanitizeSignature(source, node),
        doc: getDocComment(node),
      });
    } else if (ts.isInterfaceDeclaration(node) && node.name) {
      results.push({
        name: node.name.getText(source),
        kind: "interface",
        rangeStartLine: toLineNumber(source, node.getStart(source)),
        rangeEndLine: toLineNumber(source, node.getEnd()),
        signature: sanitizeSignature(source, node),
        doc: getDocComment(node),
      });
    } else if (ts.isEnumDeclaration(node) && node.name) {
      results.push({
        name: node.name.getText(source),
        kind: "enum",
        rangeStartLine: toLineNumber(source, node.getStart(source)),
        rangeEndLine: toLineNumber(source, node.getEnd()),
        signature: sanitizeSignature(source, node),
        doc: getDocComment(node),
      });
    } else if (ts.isMethodDeclaration(node) && node.name) {
      results.push({
        name: node.name.getText(source),
        kind: "method",
        rangeStartLine: toLineNumber(source, node.getStart(source)),
        rangeEndLine: toLineNumber(source, node.getEnd()),
        signature: sanitizeSignature(source, node),
        doc: getDocComment(node),
      });
    }

    ts.forEachChild(node, visit);
  };

  ts.forEachChild(source, visit);

  return assignSymbolIds(results);
}

/**
 * import/export/require 文からモジュールパスを正規化
 * 相対パスはファイルセットと照合してpath、それ以外はpackageとして分類
 */
function normalizePathSpecifier(
  sourcePath: string,
  specifier: string,
  fileSet: Set<string>
): { kind: "path" | "package"; target: string } | null {
  if (specifier.startsWith(".") || specifier.startsWith("/")) {
    const baseDir = path.posix.dirname(sourcePath);
    // Strip .js extension if present (ESM imports use .js but source files are .ts)
    const pathWithoutJs = specifier.endsWith(".js") ? specifier.slice(0, -3) : specifier;
    const joined = path.posix.normalize(path.posix.join(baseDir, pathWithoutJs));
    const candidates = [
      joined,
      `${joined}.ts`,
      `${joined}.tsx`,
      `${joined}.js`,
      `${joined}.jsx`,
      `${joined}/index.ts`,
      `${joined}/index.tsx`,
    ];
    for (const candidate of candidates) {
      if (fileSet.has(candidate)) {
        return { kind: "path", target: candidate };
      }
    }
    return null;
  }

  return { kind: "package", target: specifier };
}

/**
 * import/export 文を解析して依存関係を収集
 */
function collectDependencies(
  sourcePath: string,
  source: ts.SourceFile,
  fileSet: Set<string>
): DependencyRecord[] {
  const { record, getDependencies } = createDependencyRecorder();

  const visit = (node: ts.Node): void => {
    if (
      ts.isImportDeclaration(node) &&
      node.moduleSpecifier &&
      ts.isStringLiteral(node.moduleSpecifier)
    ) {
      const target = normalizePathSpecifier(sourcePath, node.moduleSpecifier.text, fileSet);
      if (target) {
        record(target.kind, target.target);
      }
    } else if (
      ts.isExportDeclaration(node) &&
      node.moduleSpecifier &&
      ts.isStringLiteral(node.moduleSpecifier)
    ) {
      const target = normalizePathSpecifier(sourcePath, node.moduleSpecifier.text, fileSet);
      if (target) {
        record(target.kind, target.target);
      }
    } else if (ts.isCallExpression(node)) {
      const firstArg = node.arguments[0];
      if (
        node.expression.getText(source) === "require" &&
        node.arguments.length === 1 &&
        firstArg &&
        ts.isStringLiteral(firstArg)
      ) {
        const target = normalizePathSpecifier(sourcePath, firstArg.text, fileSet);
        if (target) {
          record(target.kind, target.target);
        }
      }
    }

    ts.forEachChild(node, visit);
  };

  ts.forEachChild(source, visit);

  return getDependencies();
}

/**
 * TypeScript Language Analyzer
 *
 * LanguageAnalyzer インターフェースを実装し、
 * TypeScript/TSX ファイルのシンボル抽出と依存関係解析を提供
 */
export class TypeScriptAnalyzer implements LanguageAnalyzer {
  readonly language = "TypeScript";

  async analyze(context: AnalysisContext): Promise<AnalysisResult> {
    const { pathInRepo, content, fileSet } = context;

    // TypeScript Compiler API でパース
    const sourceFile = ts.createSourceFile(pathInRepo, content, ts.ScriptTarget.Latest, true);

    // シンボル抽出
    const symbols = extractSymbols(sourceFile);

    // シンボルからスニペットを生成
    const snippets: SnippetRecord[] = symbolsToSnippets(symbols);

    // 依存関係を収集
    const dependencies = collectDependencies(pathInRepo, sourceFile, fileSet);

    return { symbols, snippets, dependencies };
  }

  // TypeScript Compiler API はステートレスのためクリーンアップ不要
}

/**
 * TypeScript アナライザーのファクトリ関数
 */
export function createTypeScriptAnalyzer(): TypeScriptAnalyzer {
  return new TypeScriptAnalyzer();
}
