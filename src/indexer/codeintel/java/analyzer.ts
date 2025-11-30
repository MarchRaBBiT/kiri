/**
 * Java Language Analyzer
 *
 * tree-sitter-java を使用したシンボル抽出と依存関係解析。
 * class, interface, enum, annotation, method, constructor, field をサポート。
 */

import Parser from "tree-sitter";
import Java from "tree-sitter-java";

import type { LanguageAnalyzer, AnalysisContext, AnalysisResult, SymbolRecord } from "../types.js";
import {
  treeSitterPointToLine,
  sanitizeTreeSitterSignature,
  assignSymbolIds,
  symbolsToSnippets,
  createDependencyRecorder,
  cleanDocComment,
} from "../utils.js";

type JavaNode = Parser.SyntaxNode;

/**
 * Javadoc コメント (ブロックコメント形式) を抽出
 */
function getJavaDocComment(node: JavaNode, content: string): string | null {
  const parent = node.parent;
  if (!parent) return null;

  // 親ノードのすべての子から、このノードの直前にあるコメントを探す
  const precedingComments: string[] = [];
  const siblings = parent.children;
  const nodeIndex = siblings.indexOf(node);

  // このノードより前の兄弟を逆順で調べる
  for (let i = nodeIndex - 1; i >= 0; i--) {
    const sibling = siblings[i];
    if (!sibling) continue;

    // block_commentをチェック
    if (sibling.type === "block_comment") {
      const commentText = content.substring(sibling.startIndex, sibling.endIndex);
      // Javadoc コメント形式のみ抽出
      if (commentText.startsWith("/**") && commentText.endsWith("*/")) {
        precedingComments.unshift(cleanDocComment(commentText));
      }
    } else if (!sibling.text.trim().match(/^\s*$/)) {
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
 * 子ノードから識別子名を抽出
 */
function extractName(node: JavaNode, content: string): string | null {
  const identifierNode = node.namedChildren.find((child) => child.type === "identifier");
  return identifierNode
    ? content.substring(identifierNode.startIndex, identifierNode.endIndex)
    : null;
}

/**
 * シンボルレコードを作成
 */
function createJavaSymbolRecords(tree: Parser.Tree, content: string): SymbolRecord[] {
  const results: Array<Omit<SymbolRecord, "symbolId">> = [];

  /**
   * ノードからシグネチャを取得
   * Java はシグネチャの改行を先に正規化してから切り詰め
   */
  function getSignature(node: JavaNode): string {
    const nodeText = content.substring(node.startIndex, node.endIndex);
    return sanitizeTreeSitterSignature(nodeText, { normalizeFirst: true });
  }

  /**
   * ツリーを再帰的にトラバースしてシンボルを抽出
   */
  function visit(node: JavaNode): void {
    // class_declaration: クラス宣言
    if (node.type === "class_declaration") {
      const name = extractName(node, content);
      if (name) {
        results.push({
          name,
          kind: "class",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    // interface_declaration: インターフェース宣言
    if (node.type === "interface_declaration") {
      const name = extractName(node, content);
      if (name) {
        results.push({
          name,
          kind: "interface",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    // enum_declaration: 列挙型宣言
    if (node.type === "enum_declaration") {
      const name = extractName(node, content);
      if (name) {
        results.push({
          name,
          kind: "enum",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    // annotation_type_declaration: アノテーション型宣言
    if (node.type === "annotation_type_declaration") {
      const name = extractName(node, content);
      if (name) {
        results.push({
          name,
          kind: "annotation",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    // field_declaration: フィールド宣言
    if (node.type === "field_declaration") {
      // variable_declaratorから変数名を抽出
      const declarators = node.namedChildren.filter(
        (child) => child.type === "variable_declarator"
      );
      for (const declarator of declarators) {
        const name = extractName(declarator, content);
        if (name) {
          results.push({
            name,
            kind: "field",
            rangeStartLine: treeSitterPointToLine(node.startPosition),
            rangeEndLine: treeSitterPointToLine(node.endPosition),
            signature: getSignature(node),
            doc: getJavaDocComment(node, content),
          });
        }
      }
    }

    // constructor_declaration: コンストラクタ宣言
    if (node.type === "constructor_declaration") {
      const name = extractName(node, content);
      if (name) {
        results.push({
          name,
          kind: "constructor",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    // method_declaration: メソッド宣言
    if (node.type === "method_declaration") {
      const name = extractName(node, content);
      if (name) {
        results.push({
          name,
          kind: "method",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getJavaDocComment(node, content),
        });
      }
    }

    // annotation_type_element_declaration: アノテーション内のメソッド宣言
    if (node.type === "annotation_type_element_declaration") {
      const name = extractName(node, content);
      if (name) {
        results.push({
          name,
          kind: "method",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getJavaDocComment(node, content),
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
 * Java の import 文を解析して依存関係を収集
 */
function collectJavaDependencies(
  _sourcePath: string,
  tree: Parser.Tree,
  content: string,
  fileSet: Set<string>
): Array<{ dstKind: "path" | "package"; dst: string; rel: string }> {
  const { record, getDependencies } = createDependencyRecorder();

  function visit(node: JavaNode): void {
    // import_declaration: import文
    if (node.type === "import_declaration") {
      // scoped_identifier または identifier を探す
      const identifierNode = node.namedChildren.find(
        (child) => child.type === "scoped_identifier" || child.type === "identifier"
      );
      if (identifierNode) {
        let importName = content.substring(identifierNode.startIndex, identifierNode.endIndex);

        // ワイルドカードインポートのチェック (import java.util.*)
        // asteriskノードを探す
        const hasAsterisk = node.namedChildren.some((child) => child.type === "asterisk");
        if (hasAsterisk) {
          importName += ".*";
        }

        // ローカルファイル判定: com.example.MyClass -> com/example/MyClass.java
        // ワイルドカードの場合はパッケージとして扱う
        let kind: "path" | "package" = "package";
        if (!hasAsterisk) {
          const filePath = importName.replace(/\./g, "/") + ".java";

          // Maven/Gradle標準構造のプレフィックスを除去して完全一致でチェック
          // これにより、同名ファイルが異なるパッケージに存在する場合も正確に解決できる
          const matchingFile = Array.from(fileSet).find((f) => {
            // 標準的なソースディレクトリプレフィックスを除去
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

    // 子ノードを再帰的に訪問
    for (const child of node.namedChildren) {
      visit(child);
    }
  }

  visit(tree.rootNode);

  return getDependencies();
}

/**
 * Java Language Analyzer
 *
 * LanguageAnalyzer インターフェースを実装し、
 * Java ファイルのシンボル抽出と依存関係解析を提供
 */
export class JavaAnalyzer implements LanguageAnalyzer {
  readonly language = "Java";

  async analyze(context: AnalysisContext): Promise<AnalysisResult> {
    const { pathInRepo, content, fileSet } = context;

    try {
      // 各ファイルごとに新しいパーサーインスタンスを作成（並行処理の安全性のため）
      const parser = new Parser();

      // Validate language object before setting it
      if (!Java || typeof Java !== "object") {
        throw new Error("Tree-sitter language for Java is invalid or undefined");
      }

      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      parser.setLanguage(Java as any);
      const tree = parser.parse(content);

      // シンボル抽出
      const symbols = createJavaSymbolRecords(tree, content);

      // シンボルからスニペットを生成
      const snippets = symbolsToSnippets(symbols);

      // 依存関係を収集
      const dependencies = collectJavaDependencies(pathInRepo, tree, content, fileSet);

      return { symbols, snippets, dependencies };
    } catch (error) {
      // パース失敗時は空の結果を返して他のファイルの処理を継続
      console.error(`Failed to parse Java file ${pathInRepo}:`, error);
      return { symbols: [], snippets: [], dependencies: [] };
    }
  }

  // tree-sitter はステートレスのためクリーンアップ不要
}

/**
 * Java アナライザーのファクトリ関数
 */
export function createJavaAnalyzer(): JavaAnalyzer {
  return new JavaAnalyzer();
}
