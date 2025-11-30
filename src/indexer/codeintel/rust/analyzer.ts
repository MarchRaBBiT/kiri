/**
 * Rust Language Analyzer
 *
 * tree-sitter-rust を使用して Rust コードのシンボルと依存関係を抽出する。
 * 構造化シンボルは struct/enum/trait/impl/fn/mod/type/const/static/macro を対象とし、
 * use/extern crate/mod から依存関係を推定する。
 */

import path from "node:path";

import Parser from "tree-sitter";
import Rust from "tree-sitter-rust";

import type { AnalysisContext, AnalysisResult, LanguageAnalyzer, SymbolRecord } from "../types.js";
import {
  assignSymbolIds,
  cleanDocComment,
  createDependencyRecorder,
  sanitizeTreeSitterSignature,
  symbolsToSnippets,
  treeSitterPointToLine,
} from "../utils.js";

type RustNode = Parser.SyntaxNode;

const DOC_COMMENT_TYPES = new Set([
  "line_doc_comment",
  "block_doc_comment",
  "inner_line_doc_comment",
  "inner_block_doc_comment",
]);

const IDENTIFIER_NODE_TYPES = new Set([
  "identifier",
  "type_identifier",
  "scoped_identifier",
  "primitive_type",
]);

function sliceContent(content: string, node: RustNode): string {
  return content.substring(node.startIndex, node.endIndex);
}

/**
 * 直前のドキュメントコメントを収集
 */
function getDocComment(node: RustNode, content: string): string | null {
  const parent = node.parent;
  if (!parent) return null;

  const siblings = parent.children;
  const nodeIndex = siblings.indexOf(node);
  const preceding: string[] = [];

  const isDocCommentText = (text: string): boolean =>
    text.startsWith("///") ||
    text.startsWith("/**") ||
    text.startsWith("/*!") ||
    text.startsWith("//!");

  for (let i = nodeIndex - 1; i >= 0; i--) {
    const sibling = siblings[i];
    if (!sibling) continue;

    if (
      DOC_COMMENT_TYPES.has(sibling.type) ||
      (sibling.type.includes("comment") && isDocCommentText(sliceContent(content, sibling)))
    ) {
      preceding.unshift(cleanDocComment(sliceContent(content, sibling)));
      continue;
    }

    if (!sibling.text.trim()) {
      continue; // 空白やトリビアルなノードは無視
    }

    break; // 別の意味ノードに到達したら終了
  }

  if (preceding.length === 0) {
    return null;
  }

  return preceding.join("\n");
}

function getNameFromNode(node: RustNode, content: string): string | null {
  const fields = ["name", "type"];

  for (const field of fields) {
    const fieldNode = node.childForFieldName(field);
    if (fieldNode) {
      return sliceContent(content, fieldNode);
    }
  }

  const namedIdentifier = node.namedChildren.find((child) => IDENTIFIER_NODE_TYPES.has(child.type));
  if (namedIdentifier) {
    return sliceContent(content, namedIdentifier);
  }

  return null;
}

function createRustSymbolRecords(tree: Parser.Tree, content: string): SymbolRecord[] {
  const rawSymbols: Array<Omit<SymbolRecord, "symbolId">> = [];

  function isInContext(node: RustNode, types: string[]): boolean {
    let current: RustNode | null = node.parent;
    while (current) {
      if (types.includes(current.type)) {
        return true;
      }
      current = current.parent;
    }
    return false;
  }

  function addSymbol(node: RustNode, kind: string, name: string | null): void {
    if (!name) return;

    rawSymbols.push({
      name,
      kind,
      rangeStartLine: treeSitterPointToLine(node.startPosition),
      rangeEndLine: treeSitterPointToLine(node.endPosition),
      signature: sanitizeTreeSitterSignature(sliceContent(content, node)),
      doc: getDocComment(node, content),
    });
  }

  function visit(node: RustNode): void {
    switch (node.type) {
      case "function_item": {
        const name = getNameFromNode(node, content);
        const isMethod = isInContext(node, ["impl_item", "trait_item"]);
        const kind = isMethod ? "method" : "function";
        addSymbol(node, kind, name);
        break;
      }
      case "function_signature_item": {
        // Trait methods without bodies (e.g., `fn foo(&self);`)
        const name = getNameFromNode(node, content);
        addSymbol(node, "method", name);
        break;
      }
      case "struct_item":
        addSymbol(node, "struct", getNameFromNode(node, content));
        break;
      case "enum_item":
        addSymbol(node, "enum", getNameFromNode(node, content));
        break;
      case "trait_item":
        addSymbol(node, "trait", getNameFromNode(node, content));
        break;
      case "impl_item":
        addSymbol(
          node,
          "impl",
          (() => {
            const implTarget = getNameFromNode(node, content);
            return implTarget ? `impl ${implTarget}` : null;
          })()
        );
        break;
      case "mod_item":
        addSymbol(node, "mod", getNameFromNode(node, content));
        break;
      case "type_item":
        addSymbol(node, "type", getNameFromNode(node, content));
        break;
      case "const_item":
        addSymbol(node, "const", getNameFromNode(node, content));
        break;
      case "static_item":
        addSymbol(node, "static", getNameFromNode(node, content));
        break;
      case "macro_definition":
        addSymbol(node, "macro", getNameFromNode(node, content));
        break;
      default:
        break;
    }

    for (const child of node.namedChildren) {
      visit(child);
    }
  }

  visit(tree.rootNode);

  return assignSymbolIds(rawSymbols);
}

function findCrateSrcRoot(pathInRepo: string): string {
  const segments = pathInRepo.split("/");
  const srcIndex = segments.lastIndexOf("src");
  if (srcIndex === -1) {
    return path.posix.dirname(pathInRepo);
  }
  return segments.slice(0, srcIndex + 1).join("/");
}

function resolveSegmentsToPath(
  base: string,
  segments: string[],
  fileSet: Set<string>
): string | null {
  if (segments.length === 0) return null;
  const joined = path.posix.join(base, ...segments);
  const candidates = [`${joined}.rs`, path.posix.join(joined, "mod.rs")];
  return candidates.find((candidate) => fileSet.has(candidate)) ?? null;
}

function resolveTarget(
  rawTarget: string,
  pathInRepo: string,
  fileSet: Set<string>
): { kind: "path" | "package"; target: string } | null {
  const normalized = rawTarget.replace(/^::/, "").trim();
  if (!normalized) return null;

  const normalizedSegments = normalized.split("::").filter(Boolean);
  const hasWildcard = normalizedSegments.includes("*");
  const segmentsWithoutWildcard = hasWildcard
    ? normalizedSegments.filter((segment) => segment !== "*")
    : normalizedSegments;

  const baseDir = path.posix.dirname(pathInRepo);
  const crateRoot = findCrateSrcRoot(pathInRepo);

  if (normalized.startsWith("crate::")) {
    const segments = segmentsWithoutWildcard.slice(1); // drop "crate"
    if (segments.length === 0) {
      return null;
    }
    const resolved = resolveSegmentsToPath(crateRoot, segments, fileSet);
    if (resolved) {
      return { kind: "path", target: resolved };
    }
    return null;
  }

  if (normalized.startsWith("self::")) {
    const segments = segmentsWithoutWildcard.slice(1); // drop "self"
    if (segments.length === 0) {
      return null;
    }
    const resolved = resolveSegmentsToPath(baseDir, segments, fileSet);
    if (resolved) {
      return { kind: "path", target: resolved };
    }
    return null;
  }

  if (normalized.startsWith("super::")) {
    const segments = segmentsWithoutWildcard.slice(1); // drop initial "super"
    let parentDir = baseDir;
    while (segments.length > 0 && segments[0] === "super") {
      parentDir = path.posix.dirname(parentDir);
      segments.shift();
    }
    if (segments.length === 0) {
      return null;
    }
    const resolved = resolveSegmentsToPath(parentDir, segments, fileSet);
    if (resolved) {
      return { kind: "path", target: resolved };
    }
    return null;
  }

  const resolved = resolveSegmentsToPath(baseDir, segmentsWithoutWildcard, fileSet);
  if (resolved) {
    return { kind: "path", target: resolved };
  }

  const packageName = segmentsWithoutWildcard[0] ?? normalized;
  return packageName ? { kind: "package", target: packageName } : null;
}

function extractUsePaths(node: RustNode, content: string): string[] {
  // Prefer AST traversal to keep prefixes for grouped imports
  const targets: string[] = [];

  function splitSegments(text: string): string[] {
    return text
      .split("::")
      .map((seg) => seg.trim())
      .filter(Boolean);
  }

  function recordTarget(segments: string[]): void {
    if (segments.length === 0) return;
    targets.push(segments.join("::"));
  }

  function visitUseTree(current: RustNode, prefix: string[]): void {
    if (current.type === "use_list") {
      for (const child of current.namedChildren) {
        visitUseTree(child, prefix);
      }
      return;
    }

    if (current.type === "asterisk") {
      recordTarget([...prefix, "*"]);
      return;
    }

    if (current.type === "use_as_clause") {
      const targetNode = current.namedChildren[0];
      if (targetNode) {
        recordTarget([...prefix, ...splitSegments(sliceContent(content, targetNode))]);
      }
      return;
    }

    if (current.type === "scoped_use_list") {
      const [head, ...rest] = current.namedChildren;
      if (!head) return;

      const headSegments = splitSegments(sliceContent(content, head));
      const newPrefix = [...prefix, ...headSegments];

      const listNode = rest.find((child) => child.type === "use_list");
      if (listNode) {
        visitUseTree(listNode, newPrefix);
      } else {
        recordTarget(newPrefix);
      }
      return;
    }

    // Identifier or scoped_identifier
    if (current.type === "identifier" || current.type === "scoped_identifier") {
      recordTarget([...prefix, ...splitSegments(sliceContent(content, current))]);
      return;
    }

    for (const child of current.namedChildren) {
      visitUseTree(child, prefix);
    }
  }

  visitUseTree(node, []);

  return targets;
}

function extractExternCrateName(node: RustNode, content: string): string | null {
  const rawText = sliceContent(content, node);
  const match = rawText.match(/extern\s+crate\s+([A-Za-z0-9_]+)/);
  return match ? match[1] : null;
}

function extractModName(node: RustNode, content: string): string | null {
  return getNameFromNode(node, content);
}

function hasInlineModuleBody(node: RustNode): boolean {
  return node.text.includes("{");
}

function collectRustDependencies(
  pathInRepo: string,
  tree: Parser.Tree,
  content: string,
  fileSet: Set<string>
): AnalysisResult["dependencies"] {
  const { record, getDependencies } = createDependencyRecorder();

  function visit(node: RustNode): void {
    if (node.type === "use_declaration") {
      const targets = extractUsePaths(node, content);
      for (const target of targets) {
        const resolved = resolveTarget(target, pathInRepo, fileSet);
        if (resolved) {
          record(resolved.kind, resolved.target);
        }
      }
    } else if (node.type === "extern_crate_declaration") {
      const name = extractExternCrateName(node, content);
      if (name) {
        record("package", name, "extern_crate");
      }
    } else if (node.type === "mod_item") {
      const modName = extractModName(node, content);
      if (modName && !hasInlineModuleBody(node)) {
        const resolved = resolveSegmentsToPath(path.posix.dirname(pathInRepo), [modName], fileSet);
        if (resolved) {
          record("path", resolved, "mod");
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

export class RustAnalyzer implements LanguageAnalyzer {
  readonly language = "Rust";

  async analyze(context: AnalysisContext): Promise<AnalysisResult> {
    const { pathInRepo, content, fileSet } = context;

    if (!content.trim()) {
      return { symbols: [], snippets: [], dependencies: [] };
    }

    try {
      const parser = new Parser();

      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      parser.setLanguage(Rust as any);
      const tree = parser.parse(content);

      const symbols = createRustSymbolRecords(tree, content);
      const snippets = symbolsToSnippets(symbols);
      const dependencies = collectRustDependencies(pathInRepo, tree, content, fileSet);

      return { symbols, snippets, dependencies };
    } catch (error) {
      console.error(`Failed to parse Rust file ${pathInRepo}:`, error);
      return { symbols: [], snippets: [], dependencies: [] };
    }
  }
}

export function createRustAnalyzer(): RustAnalyzer {
  return new RustAnalyzer();
}
