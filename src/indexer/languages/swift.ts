import path from "node:path";

import Parser from "tree-sitter";
import Swift from "tree-sitter-swift";

import {
  buildSnippetsFromSymbols,
  type AnalysisResult,
  type DependencyRecord,
  type LanguageAnalyzer,
  type LanguageAnalyzerParams,
  type SymbolRecord,
} from "./types.js";

type SwiftNode = Parser.SyntaxNode;
const TYPE_BODY_NODES = new Set([
  "class_body",
  "struct_body",
  "extension_body",
  "enum_body",
  "protocol_body",
]);

function sanitizeSwiftSignature(node: SwiftNode, content: string): string {
  const nodeText = content.substring(node.startIndex, node.endIndex);
  const bodyIndex = nodeText.indexOf("{");
  const signatureText = bodyIndex >= 0 ? nodeText.substring(0, bodyIndex) : nodeText;
  const truncated = signatureText.substring(0, 200);
  return truncated.split(/\r?\n/)[0]?.trim().replace(/\s+/g, " ") ?? "";
}

function getSwiftDocComment(node: SwiftNode, content: string): string | null {
  const parent = node.parent;
  if (!parent) return null;

  const precedingComments: string[] = [];
  const siblings = parent.children;
  const nodeIndex = siblings.indexOf(node);

  for (let i = nodeIndex - 1; i >= 0; i--) {
    const sibling = siblings[i];
    if (!sibling) continue;

    if (sibling.type === "comment" || sibling.type === "multiline_comment") {
      const commentText = content.substring(sibling.startIndex, sibling.endIndex);
      if (commentText.startsWith("///") || commentText.startsWith("/**")) {
        const cleanedComment = commentText
          .replace(/^\/\/\/\s?/gm, "")
          .replace(/^\/\*\*\s?|\s?\*\/$/g, "")
          .replace(/^\s*\*\s?/gm, "")
          .trim();
        precedingComments.unshift(cleanedComment);
      }
    } else if (
      sibling.type !== "{" &&
      sibling.type !== "}" &&
      !sibling.text.trim().match(/^\s*$/)
    ) {
      break;
    }
  }

  if (precedingComments.length === 0) {
    return null;
  }

  return precedingComments.join("\n");
}

function toSwiftLineNumber(position: Parser.Point): number {
  return position.row + 1;
}

function createSwiftSymbolRecords(tree: Parser.Tree, content: string): SymbolRecord[] {
  const results: Array<Omit<SymbolRecord, "symbolId">> = [];
  function isTypeMember(node: SwiftNode): boolean {
    let current: SwiftNode | null = node.parent;
    while (current) {
      if (TYPE_BODY_NODES.has(current.type)) {
        return true;
      }
      if (current.type === "function_body" || current.type === "code_block") {
        return false;
      }
      current = current.parent;
    }
    return false;
  }

  function extractName(node: SwiftNode): string | null {
    function findIdentifier(n: SwiftNode): SwiftNode | null {
      if (n.type === "type_identifier" || n.type === "simple_identifier") {
        return n;
      }
      for (const child of n.namedChildren) {
        const found = findIdentifier(child);
        if (found) return found;
      }
      return null;
    }

    const identifierNode = findIdentifier(node);
    return identifierNode
      ? content.substring(identifierNode.startIndex, identifierNode.endIndex)
      : null;
  }

  function getClassDeclKind(node: SwiftNode): string | null {
    for (const child of node.children) {
      if (child.type === "class") return "class";
      if (child.type === "struct") return "struct";
      if (child.type === "enum") return "enum";
      if (child.type === "extension") return "extension";
    }
    return null;
  }

  function visit(node: SwiftNode): void {
    if (node.type === "class_declaration") {
      const kind = getClassDeclKind(node);
      const name = extractName(node);
      if (kind && name) {
        results.push({
          name,
          kind,
          rangeStartLine: toSwiftLineNumber(node.startPosition),
          rangeEndLine: toSwiftLineNumber(node.endPosition),
          signature: sanitizeSwiftSignature(node, content),
          doc: getSwiftDocComment(node, content),
        });
      }
    } else if (node.type === "protocol_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "protocol",
          rangeStartLine: toSwiftLineNumber(node.startPosition),
          rangeEndLine: toSwiftLineNumber(node.endPosition),
          signature: sanitizeSwiftSignature(node, content),
          doc: getSwiftDocComment(node, content),
        });
      }
    } else if (node.type === "function_declaration") {
      const name = extractName(node);
      if (name) {
        const kind = node.parent?.type === "class_body" ? "method" : "function";
        results.push({
          name,
          kind,
          rangeStartLine: toSwiftLineNumber(node.startPosition),
          rangeEndLine: toSwiftLineNumber(node.endPosition),
          signature: sanitizeSwiftSignature(node, content),
          doc: getSwiftDocComment(node, content),
        });
      }
    } else if (node.type === "struct_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "struct",
          rangeStartLine: toSwiftLineNumber(node.startPosition),
          rangeEndLine: toSwiftLineNumber(node.endPosition),
          signature: sanitizeSwiftSignature(node, content),
          doc: getSwiftDocComment(node, content),
        });
      }
    } else if (node.type === "enum_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "enum",
          rangeStartLine: toSwiftLineNumber(node.startPosition),
          rangeEndLine: toSwiftLineNumber(node.endPosition),
          signature: sanitizeSwiftSignature(node, content),
          doc: getSwiftDocComment(node, content),
        });
      }
    } else if (node.type === "extension_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "extension",
          rangeStartLine: toSwiftLineNumber(node.startPosition),
          rangeEndLine: toSwiftLineNumber(node.endPosition),
          signature: sanitizeSwiftSignature(node, content),
          doc: getSwiftDocComment(node, content),
        });
      }
    } else if (node.type === "initializer_declaration" || node.type === "init_declaration") {
      const name = "init";
      results.push({
        name,
        kind: "initializer",
        rangeStartLine: toSwiftLineNumber(node.startPosition),
        rangeEndLine: toSwiftLineNumber(node.endPosition),
        signature: sanitizeSwiftSignature(node, content),
        doc: getSwiftDocComment(node, content),
      });
    } else if (node.type === "deinitializer_declaration") {
      results.push({
        name: "deinit",
        kind: "deinitializer",
        rangeStartLine: toSwiftLineNumber(node.startPosition),
        rangeEndLine: toSwiftLineNumber(node.endPosition),
        signature: sanitizeSwiftSignature(node, content),
        doc: getSwiftDocComment(node, content),
      });
    } else if (node.type === "property_declaration" && isTypeMember(node)) {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "property",
          rangeStartLine: toSwiftLineNumber(node.startPosition),
          rangeEndLine: toSwiftLineNumber(node.endPosition),
          signature: sanitizeSwiftSignature(node, content),
          doc: getSwiftDocComment(node, content),
        });
      }
    } else if (node.type === "protocol_function_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "protocol_method",
          rangeStartLine: toSwiftLineNumber(node.startPosition),
          rangeEndLine: toSwiftLineNumber(node.endPosition),
          signature: sanitizeSwiftSignature(node, content),
          doc: getSwiftDocComment(node, content),
        });
      }
    }

    for (const child of node.namedChildren) {
      visit(child);
    }
  }

  visit(tree.rootNode);

  return results
    .sort((a, b) => a.rangeStartLine - b.rangeStartLine)
    .map((item, index) => ({ symbolId: index + 1, ...item }));
}

function collectSwiftDependencies(
  sourcePath: string,
  tree: Parser.Tree,
  content: string,
  fileSet: Set<string>
): DependencyRecord[] {
  const dependencies = new Map<string, DependencyRecord>();

  const record = (kind: "path" | "package", dst: string) => {
    const key = `${kind}:${dst}`;
    if (!dependencies.has(key)) {
      dependencies.set(key, { dstKind: kind, dst, rel: "import" });
    }
  };

  function visit(node: SwiftNode): void {
    if (node.type === "import_declaration") {
      const identifier = node.namedChildren.find((child) => child.type === "identifier");
      if (identifier) {
        const moduleName = content.substring(identifier.startIndex, identifier.endIndex);
        const baseDir = path.posix.dirname(sourcePath);
        const swiftPath = path.posix.normalize(path.posix.join(baseDir, `${moduleName}.swift`));

        if (fileSet.has(swiftPath)) {
          record("path", swiftPath);
        } else {
          record("package", moduleName);
        }
      }
    }

    for (const child of node.namedChildren) {
      visit(child);
    }
  }

  visit(tree.rootNode);

  return Array.from(dependencies.values());
}

export const swiftAnalyzer: LanguageAnalyzer = {
  async analyze({ pathInRepo, content, fileSet }: LanguageAnalyzerParams): Promise<AnalysisResult> {
    try {
      const parser = new Parser();
      if (!Swift || typeof Swift !== "object") {
        throw new Error("Tree-sitter language for Swift is invalid or undefined");
      }

      parser.setLanguage(Swift as Parser.Language);
      const tree = parser.parse(content);
      const symbols = createSwiftSymbolRecords(tree, content);

      return {
        symbols,
        snippets: buildSnippetsFromSymbols(symbols),
        dependencies: collectSwiftDependencies(pathInRepo, tree, content, fileSet),
      };
    } catch (error) {
      console.error(`Failed to parse Swift file ${pathInRepo}:`, error);
      return { symbols: [], snippets: [], dependencies: [] };
    }
  },
};
