import { createRequire } from "node:module";

import Parser from "tree-sitter";

import {
  buildSnippetsFromSymbols,
  type AnalysisResult,
  type DependencyRecord,
  type LanguageAnalyzer,
  type LanguageAnalyzerParams,
  type SymbolRecord,
} from "./types.js";

const require = createRequire(import.meta.url);
const PHPModule = require("tree-sitter-php");
const PHP_ONLY: Parser.Language = PHPModule.php_only;
const PHP_MIXED: Parser.Language = PHPModule.php;

type PHPNode = Parser.SyntaxNode;
type NullableNode = PHPNode | null | undefined;

function detectPHPType(content: string): "pure" | "html-mixed" {
  const phpTagRegex = /^(?:\s*|#!\/.*?\n|\uFEFF)*<\?(?:php|=)?/i;
  const match = content.match(phpTagRegex);

  if (!match) {
    return "html-mixed";
  }

  return "pure";
}

function sanitizePHPSignature(node: PHPNode, content: string): string {
  const nodeText = content.substring(node.startIndex, node.endIndex);
  const bodyIndex = nodeText.indexOf("{");
  const signatureText = bodyIndex >= 0 ? nodeText.substring(0, bodyIndex) : nodeText;
  const truncated = signatureText.substring(0, 200);
  return truncated.split(/\r?\n/)[0]?.trim().replace(/\s+/g, " ") ?? "";
}

function getPHPDocComment(node: PHPNode, content: string): string | null {
  const parent = node.parent;
  if (!parent) return null;

  const precedingComments: string[] = [];
  const siblings = parent.children;
  const nodeIndex = siblings.indexOf(node);

  for (let i = nodeIndex - 1; i >= 0; i--) {
    const sibling = siblings[i];
    if (!sibling) continue;

    if (sibling.type === "comment") {
      const commentText = content.substring(sibling.startIndex, sibling.endIndex);
      if (commentText.startsWith("/**") && commentText.endsWith("*/")) {
        const cleanedComment = commentText
          .replace(/^\/\*\*\s?|\s?\*\/$/g, "")
          .replace(/^\s*\*\s?/gm, "")
          .trim();
        precedingComments.unshift(cleanedComment);
      }
    } else if (sibling.type !== "text" && !sibling.text.trim().match(/^\s*$/)) {
      break;
    }
  }

  if (precedingComments.length === 0) {
    return null;
  }

  return precedingComments.join("\n");
}

function toPHPLineNumber(position: Parser.Point): number {
  return position.row + 1;
}

function findDescendant(node: PHPNode, predicate: (candidate: PHPNode) => boolean): PHPNode | null {
  if (predicate(node)) {
    return node;
  }

  for (const child of node.namedChildren) {
    const found = findDescendant(child as PHPNode, predicate);
    if (found) {
      return found;
    }
  }

  return null;
}

function extractVariableName(node: PHPNode, content: string): string | null {
  const variableNode = findDescendant(node, (candidate) => candidate.type === "variable_name");
  if (!variableNode) {
    return null;
  }

  const nameNode =
    variableNode.namedChildren.find((child) => child.type === "name") ??
    (variableNode as NullableNode);
  if (!nameNode) return null;
  const raw = content.substring(nameNode.startIndex, nameNode.endIndex);
  return raw.replace(/^\$/, "");
}

function extractConstName(node: PHPNode, content: string): string | null {
  const nameNode = findDescendant(node, (candidate) => candidate.type === "name");
  if (!nameNode) return null;
  return content.substring(nameNode.startIndex, nameNode.endIndex);
}

function createPHPSymbolRecords(tree: Parser.Tree, content: string): SymbolRecord[] {
  const results: Array<Omit<SymbolRecord, "symbolId">> = [];

  function extractName(node: PHPNode): string | null {
    function findName(n: PHPNode): PHPNode | null {
      if (n.type === "name") {
        return n;
      }
      for (const child of n.namedChildren) {
        const found = findName(child);
        if (found) return found;
      }
      return null;
    }

    const nameNode = findName(node);
    return nameNode ? content.substring(nameNode.startIndex, nameNode.endIndex) : null;
  }

  function visit(node: PHPNode): void {
    if (node.type === "class_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "class",
          rangeStartLine: toPHPLineNumber(node.startPosition),
          rangeEndLine: toPHPLineNumber(node.endPosition),
          signature: sanitizePHPSignature(node, content),
          doc: getPHPDocComment(node, content),
        });
      }
    } else if (node.type === "trait_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "trait",
          rangeStartLine: toPHPLineNumber(node.startPosition),
          rangeEndLine: toPHPLineNumber(node.endPosition),
          signature: sanitizePHPSignature(node, content),
          doc: getPHPDocComment(node, content),
        });
      }
    } else if (node.type === "interface_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "interface",
          rangeStartLine: toPHPLineNumber(node.startPosition),
          rangeEndLine: toPHPLineNumber(node.endPosition),
          signature: sanitizePHPSignature(node, content),
          doc: getPHPDocComment(node, content),
        });
      }
    } else if (node.type === "method_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "method",
          rangeStartLine: toPHPLineNumber(node.startPosition),
          rangeEndLine: toPHPLineNumber(node.endPosition),
          signature: sanitizePHPSignature(node, content),
          doc: getPHPDocComment(node, content),
        });
      }
    } else if (node.type === "function_definition") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "function",
          rangeStartLine: toPHPLineNumber(node.startPosition),
          rangeEndLine: toPHPLineNumber(node.endPosition),
          signature: sanitizePHPSignature(node, content),
          doc: getPHPDocComment(node, content),
        });
      }
    } else if (node.type === "namespace_definition") {
      const namespaceName = node.namedChildren.find((child) => child.type === "namespace_name");
      if (namespaceName) {
        const name = content.substring(namespaceName.startIndex, namespaceName.endIndex);
        results.push({
          name,
          kind: "namespace",
          rangeStartLine: toPHPLineNumber(node.startPosition),
          rangeEndLine: toPHPLineNumber(node.endPosition),
          signature: sanitizePHPSignature(node, content),
          doc: getPHPDocComment(node, content),
        });
      }
    } else if (node.type === "property_declaration") {
      const propertyElements = node.namedChildren.filter(
        (child) => child.type === "property_element"
      );
      for (const propertyElement of propertyElements) {
        const name = extractVariableName(propertyElement as PHPNode, content);
        if (!name) continue;
        results.push({
          name,
          kind: "property",
          rangeStartLine: toPHPLineNumber(propertyElement.startPosition),
          rangeEndLine: toPHPLineNumber(propertyElement.endPosition),
          signature: sanitizePHPSignature(node, content),
          doc: getPHPDocComment(node, content),
        });
      }
    } else if (node.type === "const_declaration") {
      const constElements = node.namedChildren.filter((child) => child.type === "const_element");
      for (const constElement of constElements) {
        const name = extractConstName(constElement as PHPNode, content);
        if (!name) continue;
        results.push({
          name,
          kind: "constant",
          rangeStartLine: toPHPLineNumber(constElement.startPosition),
          rangeEndLine: toPHPLineNumber(constElement.endPosition),
          signature: sanitizePHPSignature(node, content),
          doc: getPHPDocComment(node, content),
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

function collectPHPDependencies(
  sourcePath: string,
  tree: Parser.Tree,
  content: string,
  _fileSet: Set<string>
): DependencyRecord[] {
  const dependencies = new Map<string, DependencyRecord>();

  const record = (kind: "path" | "package", dst: string) => {
    const key = `${kind}:${dst}`;
    if (!dependencies.has(key)) {
      dependencies.set(key, { dstKind: kind, dst, rel: "import" });
    }
  };

  function visit(node: PHPNode): void {
    if (node.type === "namespace_use_declaration") {
      const useClauses = node.namedChildren.filter(
        (child) => child.type === "namespace_use_clause"
      );
      for (const useClause of useClauses) {
        const qualifiedName = useClause.namedChildren.find(
          (child) => child.type === "qualified_name" || child.type === "name"
        );
        if (qualifiedName) {
          const importName = content.substring(qualifiedName.startIndex, qualifiedName.endIndex);
          record("package", importName);
        }
      }

      const useGroups = node.namedChildren.filter((child) => child.type === "namespace_use_group");
      if (useGroups.length > 0) {
        const prefixNode = node.namedChildren.find((child) => child.type === "namespace_name");
        const prefix = prefixNode
          ? content.substring(prefixNode.startIndex, prefixNode.endIndex)
          : "";

        for (const useGroup of useGroups) {
          const groupClauses = useGroup.namedChildren.filter(
            (child) => child.type === "namespace_use_group_clause"
          );
          for (const groupClause of groupClauses) {
            const namespaceName = groupClause.namedChildren.find(
              (child) => child.type === "namespace_name" || child.type === "name"
            );
            if (namespaceName) {
              const suffix = content.substring(namespaceName.startIndex, namespaceName.endIndex);
              const fullName = prefix ? `${prefix}\\${suffix}` : suffix;
              record("package", fullName);
            }
          }
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

export const phpAnalyzer: LanguageAnalyzer = {
  async analyze({ pathInRepo, content, fileSet }: LanguageAnalyzerParams): Promise<AnalysisResult> {
    try {
      const parser = new Parser();
      const phpType = detectPHPType(content);
      const language = phpType === "html-mixed" ? PHP_MIXED : PHP_ONLY;

      if (!language || typeof language !== "object") {
        throw new Error(`Tree-sitter language for PHP type "${phpType}" is invalid or undefined`);
      }

      parser.setLanguage(language);
      const tree = parser.parse(content);
      const symbols = createPHPSymbolRecords(tree, content);

      return {
        symbols,
        snippets: buildSnippetsFromSymbols(symbols),
        dependencies: collectPHPDependencies(pathInRepo, tree, content, fileSet),
      };
    } catch (error) {
      console.error(`Failed to parse PHP file ${pathInRepo}:`, error);
      return { symbols: [], snippets: [], dependencies: [] };
    }
  },
};
