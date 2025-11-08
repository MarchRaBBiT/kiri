import path from "node:path";

import ts from "typescript";

import {
  buildSnippetsFromSymbols,
  type AnalysisResult,
  type DependencyRecord,
  type LanguageAnalyzer,
  type LanguageAnalyzerParams,
  type SymbolRecord,
} from "./types.js";

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

function toLineNumber(source: ts.SourceFile, position: number): number {
  return source.getLineAndCharacterOfPosition(position).line + 1;
}

function createSymbolRecords(source: ts.SourceFile): SymbolRecord[] {
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
      const name = node.name.getText(source);
      results.push({
        name,
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

  return results
    .sort((a, b) => a.rangeStartLine - b.rangeStartLine)
    .map((item, index) => ({ symbolId: index + 1, ...item }));
}

function normalizePathSpecifier(
  sourcePath: string,
  specifier: string,
  fileSet: Set<string>
): { kind: "path" | "package"; target: string } | null {
  if (specifier.startsWith(".") || specifier.startsWith("/")) {
    const baseDir = path.posix.dirname(sourcePath);
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

function collectDependencies(
  sourcePath: string,
  source: ts.SourceFile,
  fileSet: Set<string>
): DependencyRecord[] {
  const dependencies = new Map<string, DependencyRecord>();

  const record = (kind: "path" | "package", dst: string) => {
    const key = `${kind}:${dst}`;
    if (!dependencies.has(key)) {
      dependencies.set(key, { dstKind: kind, dst, rel: "import" });
    }
  };

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

  return Array.from(dependencies.values());
}

export const typescriptAnalyzer: LanguageAnalyzer = {
  async analyze({ pathInRepo, content, fileSet }: LanguageAnalyzerParams): Promise<AnalysisResult> {
    const sourceFile = ts.createSourceFile(pathInRepo, content, ts.ScriptTarget.Latest, true);
    const symbols = createSymbolRecords(sourceFile);

    return {
      symbols,
      snippets: buildSnippetsFromSymbols(symbols),
      dependencies: collectDependencies(pathInRepo, sourceFile, fileSet),
    };
  },
};
