/**
 * Swift Language Analyzer
 *
 * tree-sitter-swift を使用したシンボル抽出と依存関係解析。
 * class, struct, enum, protocol, function, method, initializer, property をサポート。
 */

import path from "node:path";

import Parser from "tree-sitter";
import Swift from "tree-sitter-swift";

import type { LanguageAnalyzer, AnalysisContext, AnalysisResult, SymbolRecord } from "../types.js";
import {
  treeSitterPointToLine,
  sanitizeTreeSitterSignature,
  assignSymbolIds,
  symbolsToSnippets,
  createDependencyRecorder,
  cleanDocComment,
} from "../utils.js";

type SwiftNode = Parser.SyntaxNode;

/**
 * Swift のドキュメントコメント (/// コメントまたはブロックコメント) を抽出
 */
function getSwiftDocComment(node: SwiftNode, content: string): string | null {
  const parent = node.parent;
  if (!parent) return null;

  // 親ノードのすべての子から、このノードの直前にあるコメントを探す
  const precedingComments: string[] = [];
  const siblings = parent.children; // namedChildrenではなくchildrenを使用
  const nodeIndex = siblings.indexOf(node);

  // このノードより前の兄弟を逆順で調べる
  for (let i = nodeIndex - 1; i >= 0; i--) {
    const sibling = siblings[i];
    if (!sibling) continue;

    // commentまたはmultiline_commentをチェック
    if (sibling.type === "comment" || sibling.type === "multiline_comment") {
      const commentText = content.substring(sibling.startIndex, sibling.endIndex);
      // /// または /** */ 形式のドキュメントコメントのみ抽出
      if (commentText.startsWith("///") || commentText.startsWith("/**")) {
        precedingComments.unshift(cleanDocComment(commentText));
      }
    } else if (
      sibling.type !== "{" &&
      sibling.type !== "}" &&
      !sibling.text.trim().match(/^\s*$/)
    ) {
      // コメント以外の実質的なノードに到達したら終了
      break;
    }
  }

  if (precedingComments.length === 0) {
    return null;
  }

  return precedingComments.join("\n");
}

/**
 * 子ノードから識別子名を抽出（再帰的に探索）
 */
function extractName(node: SwiftNode, content: string): string | null {
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

/**
 * class_declaration のキーワードから種類を判定
 */
function getClassDeclKind(node: SwiftNode): string | null {
  for (const child of node.children) {
    if (child.type === "class") return "class";
    if (child.type === "struct") return "struct";
    if (child.type === "enum") return "enum";
    if (child.type === "extension") return "extension";
  }
  return null;
}

/**
 * シンボルレコードを作成
 */
function createSwiftSymbolRecords(tree: Parser.Tree, content: string): SymbolRecord[] {
  const results: Array<Omit<SymbolRecord, "symbolId">> = [];

  /**
   * ノードからシグネチャを取得
   */
  function getSignature(node: SwiftNode): string {
    const nodeText = content.substring(node.startIndex, node.endIndex);
    return sanitizeTreeSitterSignature(nodeText);
  }

  /**
   * ツリーを再帰的にトラバースしてシンボルを抽出
   */
  function visit(node: SwiftNode): void {
    // class_declaration: class/struct/enum/extension
    if (node.type === "class_declaration") {
      const kind = getClassDeclKind(node);
      const name = extractName(node, content);
      if (kind && name) {
        results.push({
          name,
          kind,
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getSwiftDocComment(node, content),
        });
      }
    }
    // protocol_declaration
    else if (node.type === "protocol_declaration") {
      const name = extractName(node, content);
      if (name) {
        results.push({
          name,
          kind: "protocol",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getSwiftDocComment(node, content),
        });
      }
    }
    // function_declaration: トップレベル関数またはメソッド
    else if (node.type === "function_declaration") {
      const name = extractName(node, content);
      if (name) {
        // 親がclass_bodyの場合はmethod、それ以外はfunction
        const kind = node.parent?.type === "class_body" ? "method" : "function";
        results.push({
          name,
          kind,
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getSwiftDocComment(node, content),
        });
      }
    }
    // init_declaration: イニシャライザ
    else if (node.type === "init_declaration") {
      results.push({
        name: "init",
        kind: "initializer",
        rangeStartLine: treeSitterPointToLine(node.startPosition),
        rangeEndLine: treeSitterPointToLine(node.endPosition),
        signature: getSignature(node),
        doc: getSwiftDocComment(node, content),
      });
    }
    // property_declaration: プロパティ（クラス/構造体/プロトコル/エクステンション内のみ）
    else if (node.type === "property_declaration") {
      // 親がclass_body、struct_body、protocol_body、enum_class_body、extension_bodyの場合のみプロパティとして扱う
      const isClassMember =
        node.parent?.type === "class_body" ||
        node.parent?.type === "struct_body" ||
        node.parent?.type === "protocol_body" ||
        node.parent?.type === "enum_class_body" ||
        node.parent?.type === "extension_body";

      if (isClassMember) {
        const name = extractName(node, content);
        if (name) {
          results.push({
            name,
            kind: "property",
            rangeStartLine: treeSitterPointToLine(node.startPosition),
            rangeEndLine: treeSitterPointToLine(node.endPosition),
            signature: getSignature(node),
            doc: getSwiftDocComment(node, content),
          });
        }
      }
    }
    // protocol_function_declaration: プロトコル内のメソッド宣言
    else if (node.type === "protocol_function_declaration") {
      const name = extractName(node, content);
      if (name) {
        results.push({
          name,
          kind: "protocol_method",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getSwiftDocComment(node, content),
        });
      }
    }

    // 子ノードを再帰的に訪問
    for (const child of node.namedChildren) {
      visit(child);
    }
  }

  visit(tree.rootNode);

  return assignSymbolIds(results);
}

/**
 * Swift の import 文を解析して依存関係を収集
 */
function collectSwiftDependencies(
  sourcePath: string,
  tree: Parser.Tree,
  content: string,
  fileSet: Set<string>
): Array<{ dstKind: "path" | "package"; dst: string; rel: string }> {
  const { record, getDependencies } = createDependencyRecorder();

  function visit(node: SwiftNode): void {
    if (node.type === "import_declaration") {
      // import_declarationの子からidentifierを抽出
      const identifier = node.namedChildren.find((child) => child.type === "identifier");
      if (identifier) {
        const moduleName = content.substring(identifier.startIndex, identifier.endIndex);

        // Swiftファイルへの相対パスかどうかをチェック
        // 通常はシステムモジュール（Foundation, UIKit等）が多いため"package"として扱う
        const baseDir = path.posix.dirname(sourcePath);
        const swiftPath = path.posix.normalize(path.posix.join(baseDir, `${moduleName}.swift`));

        if (fileSet.has(swiftPath)) {
          record("path", swiftPath);
        } else {
          record("package", moduleName);
        }
      }
    }

    // 子ノードを再帰的に訪問
    for (const child of node.namedChildren) {
      visit(child);
    }
  }

  visit(tree.rootNode);

  return getDependencies();
}

/**
 * Swift Language Analyzer
 *
 * LanguageAnalyzer インターフェースを実装し、
 * Swift ファイルのシンボル抽出と依存関係解析を提供
 */
export class SwiftAnalyzer implements LanguageAnalyzer {
  readonly language = "Swift";

  async analyze(context: AnalysisContext): Promise<AnalysisResult> {
    const { pathInRepo, content, fileSet } = context;

    try {
      // 各ファイルごとに新しいパーサーインスタンスを作成（並行処理の安全性のため）
      const parser = new Parser();

      // Validate language object before setting it
      if (!Swift || typeof Swift !== "object") {
        throw new Error("Tree-sitter language for Swift is invalid or undefined");
      }

      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      parser.setLanguage(Swift as any);
      const tree = parser.parse(content);

      // シンボル抽出
      const symbols = createSwiftSymbolRecords(tree, content);

      // シンボルからスニペットを生成
      const snippets = symbolsToSnippets(symbols);

      // 依存関係を収集
      const dependencies = collectSwiftDependencies(pathInRepo, tree, content, fileSet);

      return { symbols, snippets, dependencies };
    } catch (error) {
      // パース失敗時は空の結果を返して他のファイルの処理を継続
      console.error(`Failed to parse Swift file ${pathInRepo}:`, error);
      return { symbols: [], snippets: [], dependencies: [] };
    }
  }

  // tree-sitter はステートレスのためクリーンアップ不要
}

/**
 * Swift アナライザーのファクトリ関数
 */
export function createSwiftAnalyzer(): SwiftAnalyzer {
  return new SwiftAnalyzer();
}
