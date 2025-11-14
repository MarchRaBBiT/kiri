import Parser from "tree-sitter";
import Java from "tree-sitter-java";

import {
  buildSnippetsFromSymbols,
  type AnalysisResult,
  type DependencyRecord,
  type LanguageAnalyzer,
  type LanguageAnalyzerParams,
  type SymbolRecord,
} from "./types.js";

type JavaNode = Parser.SyntaxNode;

function sanitizeJavaSignature(node: JavaNode, content: string): string {
  const nodeText = content.substring(node.startIndex, node.endIndex);
  const bodyIndex = nodeText.indexOf("{");
  const signatureText = bodyIndex >= 0 ? nodeText.substring(0, bodyIndex) : nodeText;
  const normalized = signatureText.replace(/\s+/g, " ").trim();
  return normalized.substring(0, 200);
}

function getJavaDocComment(node: JavaNode, content: string): string | null {
  const parent = node.parent;
  if (!parent) return null;

  const precedingComments: string[] = [];
  const siblings = parent.children;
  const nodeIndex = siblings.indexOf(node);

  for (let i = nodeIndex - 1; i >= 0; i--) {
    const sibling = siblings[i];
    if (!sibling) continue;

    if (sibling.type === "block_comment") {
      const commentText = content.substring(sibling.startIndex, sibling.endIndex);
      if (commentText.startsWith("/**") && commentText.endsWith("*/")) {
        const cleanedComment = commentText
          .replace(/^\/\*\*\s?|\s?\*\/$/g, "")
          .replace(/^\s*\*\s?/gm, "")
          .trim();
        precedingComments.unshift(cleanedComment);
      }
    } else if (!sibling.text.trim().match(/^\s*$/)) {
      break;
    }
  }

  if (precedingComments.length === 0) {
    return null;
  }

  return precedingComments.join("\n");
}

function toJavaLineNumber(position: Parser.Point): number {
  return position.row + 1;
}

function createJavaSymbolRecords(tree: Parser.Tree, content: string): SymbolRecord[] {
  const results: Array<Omit<SymbolRecord, "symbolId">> = [];

  function extractName(node: JavaNode): string | null {
    const identifierNode = node.namedChildren.find((child) => child.type === "identifier");
    return identifierNode
      ? content.substring(identifierNode.startIndex, identifierNode.endIndex)
      : null;
  }

  function visit(node: JavaNode): void {
    if (node.type === "class_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "class",
          rangeStartLine: toJavaLineNumber(node.startPosition),
          rangeEndLine: toJavaLineNumber(node.endPosition),
          signature: sanitizeJavaSignature(node, content),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    if (node.type === "interface_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "interface",
          rangeStartLine: toJavaLineNumber(node.startPosition),
          rangeEndLine: toJavaLineNumber(node.endPosition),
          signature: sanitizeJavaSignature(node, content),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    if (node.type === "enum_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "enum",
          rangeStartLine: toJavaLineNumber(node.startPosition),
          rangeEndLine: toJavaLineNumber(node.endPosition),
          signature: sanitizeJavaSignature(node, content),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    if (node.type === "annotation_type_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "annotation",
          rangeStartLine: toJavaLineNumber(node.startPosition),
          rangeEndLine: toJavaLineNumber(node.endPosition),
          signature: sanitizeJavaSignature(node, content),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    if (node.type === "field_declaration") {
      const declarators = node.namedChildren.filter(
        (child) => child.type === "variable_declarator"
      );
      for (const declarator of declarators) {
        const name = extractName(declarator);
        if (name) {
          results.push({
            name,
            kind: "field",
            rangeStartLine: toJavaLineNumber(declarator.startPosition),
            rangeEndLine: toJavaLineNumber(declarator.endPosition),
            signature: sanitizeJavaSignature(node, content),
            doc: getJavaDocComment(node, content),
          });
        }
      }
    }

    if (node.type === "method_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "method",
          rangeStartLine: toJavaLineNumber(node.startPosition),
          rangeEndLine: toJavaLineNumber(node.endPosition),
          signature: sanitizeJavaSignature(node, content),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    if (node.type === "constructor_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "constructor",
          rangeStartLine: toJavaLineNumber(node.startPosition),
          rangeEndLine: toJavaLineNumber(node.endPosition),
          signature: sanitizeJavaSignature(node, content),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    if (node.type === "annotation_type_member_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "annotation_member",
          rangeStartLine: toJavaLineNumber(node.startPosition),
          rangeEndLine: toJavaLineNumber(node.endPosition),
          signature: sanitizeJavaSignature(node, content),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    if (node.type === "annotation_type_element_declaration") {
      const name = extractName(node);
      if (name) {
        results.push({
          name,
          kind: "method",
          rangeStartLine: toJavaLineNumber(node.startPosition),
          rangeEndLine: toJavaLineNumber(node.endPosition),
          signature: sanitizeJavaSignature(node, content),
          doc: getJavaDocComment(node, content),
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

function collectJavaDependencies(
  _sourcePath: string,
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

  function visit(node: JavaNode): void {
    if (node.type === "import_declaration") {
      const identifierNode = node.namedChildren.find(
        (child) => child.type === "scoped_identifier" || child.type === "identifier"
      );
      if (identifierNode) {
        let importName = content.substring(identifierNode.startIndex, identifierNode.endIndex);
        const hasAsterisk = node.namedChildren.some((child) => child.type === "asterisk");
        if (hasAsterisk) {
          importName += ".*";
        }

        let kind: "path" | "package" = "package";
        if (!hasAsterisk) {
          const filePath = importName.replace(/\./g, "/") + ".java";
          const matchingFile = Array.from(fileSet).find((f) => {
            const normalizedPath = f
              .replace(/^src\/main\/java\//, "")
              .replace(/^src\/test\/java\//, "")
              .replace(/^src\//, "");

            return normalizedPath === filePath;
          });

          kind = matchingFile ? "path" : "package";
        }

        record(kind, importName);
      }
    }

    for (const child of node.namedChildren) {
      visit(child);
    }
  }

  visit(tree.rootNode);

  return Array.from(dependencies.values());
}

export const javaAnalyzer: LanguageAnalyzer = {
  async analyze({ pathInRepo, content, fileSet }: LanguageAnalyzerParams): Promise<AnalysisResult> {
    try {
      const parser = new Parser();
      if (!Java || typeof Java !== "object") {
        throw new Error("Tree-sitter language for Java is invalid or undefined");
      }

      parser.setLanguage(Java as Parser.Language);
      const tree = parser.parse(content);
      const symbols = createJavaSymbolRecords(tree, content);

      return {
        symbols,
        snippets: buildSnippetsFromSymbols(symbols),
        dependencies: collectJavaDependencies(pathInRepo, tree, content, fileSet),
      };
    } catch (error) {
      console.error(`Failed to parse Java file ${pathInRepo}:`, error);
      return { symbols: [], snippets: [], dependencies: [] };
    }
  },
};
