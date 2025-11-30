/**
 * Python Language Analyzer
 *
 * tree-sitter-python を用いたシンボル抽出と依存関係解析。
 * class/function/async function/property/staticmethod/classmethod を対象にし、
 * import/from 文から依存を収集する。
 */

import path from "node:path";

import Parser from "tree-sitter";
import Python from "tree-sitter-python";

import type { AnalysisContext, AnalysisResult, LanguageAnalyzer, SymbolRecord } from "../types.js";
import {
  assignSymbolIds,
  createDependencyRecorder,
  sanitizeTreeSitterSignature,
  symbolsToSnippets,
  treeSitterPointToLine,
} from "../utils.js";

type PyNode = Parser.SyntaxNode;

function slice(content: string, node: PyNode): string {
  return content.substring(node.startIndex, node.endIndex);
}

function cleanDocstring(text: string): string {
  const trimmed = text.trim();
  const match = trimmed.match(/^(?:[rbuRBUfF]{0,2})?(['\"]{3}|['\"])([\s\S]*?)\1$/);
  if (!match) return trimmed;
  return match[2]?.trim() ?? trimmed;
}

function getDocstring(bodyNode: PyNode | null | undefined, content: string): string | null {
  if (!bodyNode) return null;
  const first = bodyNode.namedChildren.find(
    (child) =>
      child.type === "expression_statement" &&
      child.namedChildren[0] &&
      child.namedChildren[0].type === "string"
  );
  if (!first) return null;
  const strNode = first.namedChildren[0];
  return strNode ? cleanDocstring(slice(content, strNode)) : null;
}

function getIdentifier(node: PyNode, content: string): string | null {
  const nameField = node.childForFieldName("name");
  if (nameField) {
    return slice(content, nameField);
  }
  const ident = node.namedChildren.find((child) => child.type === "identifier");
  return ident ? slice(content, ident) : null;
}

function isDecorator(node: PyNode, name: string, content: string): boolean {
  const text = slice(content, node).replace(/^@/, "").trim();
  return text === name || text.startsWith(`${name}.`);
}

function hasDecorator(nodes: PyNode[], names: string[], content: string): boolean {
  return nodes.some((n) => names.some((name) => isDecorator(n, name, content)));
}

function isMethod(node: PyNode): boolean {
  let current: PyNode | null = node.parent;
  while (current) {
    if (current.type === "class_definition") return true;
    current = current.parent;
  }
  return false;
}

function createPythonSymbolRecords(tree: Parser.Tree, content: string): SymbolRecord[] {
  const raw: Array<Omit<SymbolRecord, "symbolId">> = [];

  function addSymbol(node: PyNode, kind: string, name: string | null, doc: string | null): void {
    if (!name) return;
    raw.push({
      name,
      kind,
      rangeStartLine: treeSitterPointToLine(node.startPosition),
      rangeEndLine: treeSitterPointToLine(node.endPosition),
      signature: sanitizeTreeSitterSignature(slice(content, node)),
      doc,
    });
  }

  function handleFunction(node: PyNode): void {
    const name = getIdentifier(node, content);
    const decorators =
      node.parent?.type === "decorated_definition" ? node.parent.namedChildren : [];
    const isClsMethod = hasDecorator(decorators, ["classmethod"], content);
    const isStatic = hasDecorator(decorators, ["staticmethod"], content);
    const isProp = hasDecorator(decorators, ["property"], content) || name === "__get__";

    let kind = "function";
    if (isMethod(node)) {
      if (isProp) kind = "property";
      else if (isClsMethod) kind = "classmethod";
      else if (isStatic) kind = "staticmethod";
      else kind = "method";
    }

    const body = node.childForFieldName("body");
    addSymbol(node, kind, name, getDocstring(body, content));
  }

  function visit(node: PyNode): void {
    if (node.type === "decorated_definition") {
      const defNode = node.namedChildren.find(
        (child) =>
          child.type === "function_definition" ||
          child.type === "async_function_definition" ||
          child.type === "class_definition"
      );
      if (defNode) {
        visit(defNode);
      }
      return;
    }

    switch (node.type) {
      case "class_definition": {
        const name = getIdentifier(node, content);
        const body = node.childForFieldName("body");
        addSymbol(node, "class", name, getDocstring(body, content));
        break;
      }
      case "function_definition":
      case "async_function_definition":
        handleFunction(node);
        break;
      default:
        break;
    }

    for (const child of node.namedChildren) {
      visit(child);
    }
  }

  visit(tree.rootNode);
  return assignSymbolIds(raw);
}

function resolvePythonModulePath(
  base: string,
  segments: string[],
  fileSet: Set<string>
): string | null {
  if (segments.length === 0) return null;
  const joined = path.posix.join(base, ...segments);
  const candidates = [`${joined}.py`, path.posix.join(joined, "__init__.py")];
  return candidates.find((candidate) => fileSet.has(candidate)) ?? null;
}

function resolveModuleLikePath(
  base: string,
  segments: string[],
  fileSet: Set<string>
): string | null {
  const direct = resolvePythonModulePath(base, segments, fileSet);
  if (direct) return direct;
  if (segments.length > 1) {
    return resolvePythonModulePath(base, segments.slice(0, -1), fileSet);
  }
  return null;
}

function resolveImport(
  moduleSegments: string[],
  level: number,
  pathInRepo: string,
  fileSet: Set<string>
): { kind: "path" | "package"; target: string } | null {
  const baseDir = path.posix.dirname(pathInRepo);
  let base = "";
  if (level > 0) {
    base = baseDir;
    for (let i = 1; i < level; i++) {
      base = path.posix.dirname(base);
    }
  }

  const resolved = resolveModuleLikePath(base, moduleSegments, fileSet);
  if (resolved) {
    return { kind: "path", target: resolved };
  }

  const pkg = moduleSegments.join(".") || (level > 0 ? ".".repeat(level) : "");
  return pkg ? { kind: "package", target: pkg } : null;
}

function parseImportStatement(node: PyNode, content: string): string[] {
  const text = slice(content, node);
  const body = text.replace(/^import\s+/, "");
  return body
    .split(",")
    .map((part) => part.trim())
    .filter(Boolean)
    .map((part) => part.replace(/\s+as\s+.*$/, "").trim())
    .filter(Boolean);
}

function parseImportFrom(
  node: PyNode,
  content: string
): {
  level: number;
  moduleSegments: string[];
  names: string[];
} | null {
  const text = slice(content, node);
  const match = text.match(/^from\s+(\.*)([A-Za-z0-9_\.]*)\s+import\s+(.+)$/);
  if (!match) return null;
  const [, dots, modulePath, namesPart] = match;
  const level = dots.length || 0;
  const moduleSegments = modulePath ? modulePath.split(".").filter(Boolean) : [];
  const names = namesPart
    .split(",")
    .map((n) => n.trim().replace(/\s+as\s+.*$/, ""))
    .filter(Boolean);
  return { level, moduleSegments, names };
}

function collectDependencies(
  pathInRepo: string,
  tree: Parser.Tree,
  content: string,
  fileSet: Set<string>
): AnalysisResult["dependencies"] {
  const { record, getDependencies } = createDependencyRecorder();

  function visit(node: PyNode): void {
    if (node.type === "import_statement") {
      const modules = parseImportStatement(node, content);
      for (const mod of modules) {
        const segments = mod.split(".").filter(Boolean);
        const dep = resolveImport(segments, 0, pathInRepo, fileSet);
        if (dep) record(dep.kind, dep.target);
      }
    } else if (node.type === "import_from_statement") {
      const parsed = parseImportFrom(node, content);
      if (!parsed) {
        return;
      }
      const { level, moduleSegments, names } = parsed;
      if (moduleSegments.length > 0) {
        const dep = resolveImport(moduleSegments, level, pathInRepo, fileSet);
        if (dep) record(dep.kind, dep.target);
        for (const name of names) {
          const segments = [...moduleSegments, ...name.split(".").filter(Boolean)];
          const nameDep = resolveImport(segments, level, pathInRepo, fileSet);
          if (nameDep) record(nameDep.kind, nameDep.target);
        }
      } else {
        for (const name of names) {
          const segments = name.split(".").filter(Boolean);
          const dep = resolveImport(segments, Math.max(1, level), pathInRepo, fileSet);
          if (dep) record(dep.kind, dep.target);
        }
      }
    }

    for (const child of node.namedChildren) {
      visit(child);
    }
  }

  visit(tree.rootNode);
  return getDependencies();
}

export class PythonAnalyzer implements LanguageAnalyzer {
  readonly language = "Python";

  async analyze(context: AnalysisContext): Promise<AnalysisResult> {
    const { pathInRepo, content, fileSet } = context;

    if (!content.trim()) {
      return { symbols: [], snippets: [], dependencies: [] };
    }

    try {
      const parser = new Parser();
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      parser.setLanguage(Python as any);
      const tree = parser.parse(content);

      const symbols = createPythonSymbolRecords(tree, content);
      const snippets = symbolsToSnippets(symbols);
      const dependencies = collectDependencies(pathInRepo, tree, content, fileSet);

      return { symbols, snippets, dependencies };
    } catch (error) {
      console.error(`Failed to parse Python file ${pathInRepo}:`, error);
      return { symbols: [], snippets: [], dependencies: [] };
    }
  }
}

export function createPythonAnalyzer(): PythonAnalyzer {
  return new PythonAnalyzer();
}
