/**
 * PHP Language Analyzer
 *
 * tree-sitter-php を使用したシンボル抽出と依存関係解析。
 * class, interface, trait, function, method, property, constant, namespace をサポート。
 * Pure PHP ファイルと HTML-mixed PHP ファイルの両方に対応。
 */

import { createRequire } from "node:module";

import Parser from "tree-sitter";

import type { LanguageAnalyzer, AnalysisContext, AnalysisResult, SymbolRecord } from "../types.js";
import {
  treeSitterPointToLine,
  sanitizeTreeSitterSignature,
  assignSymbolIds,
  symbolsToSnippets,
  createDependencyRecorder,
  cleanDocComment,
} from "../utils.js";

// tree-sitter-php is a CommonJS module, so import it using require.
// tree-sitter-php: Using version 0.22.8 for compatibility with tree-sitter 0.22.4.
// Version 0.24.2 had a nodeTypeInfo bug that caused runtime errors.
// php_only: for pure PHP files (<?php at start)
// php: for HTML-mixed PHP files (HTML with <?php ... ?> tags)
const require = createRequire(import.meta.url);
const PHPModule = require("tree-sitter-php");
const PHP_ONLY = PHPModule.php_only;
const PHP_MIXED = PHPModule.php;

type PHPNode = Parser.SyntaxNode;

/**
 * PHP ファイルが pure PHP か HTML-mixed かを検出
 *
 * Pure PHP: ファイル先頭が <?php タグで始まる (空白、shebang、BOM は許容)
 * HTML-mixed: <?php タグより前に HTML コンテンツがある
 *
 * 対応するケース:
 * - 大文字小文字を無視した PHP タグ (<?php, <?PHP)
 * - ショートタグ (<?=)
 * - shebang (#!/usr/bin/env php)
 * - UTF-8 BOM (\uFEFF)
 */
function detectPHPType(content: string): "pure" | "html-mixed" {
  // Regex to find the first PHP open tag, ignoring shebangs, whitespace, and BOM.
  // It checks for <?php (case-insensitive), <?=, or <? (short tag)
  const phpTagRegex = /^(?:\s*|#!\/.*?\n|\uFEFF)*<\?(?:php|=)?/i;
  const match = content.match(phpTagRegex);

  if (!match) {
    // No PHP tags found at the beginning - treat as HTML-mixed
    return "html-mixed";
  }

  // If the match occurs at or near the beginning (after only whitespace/shebang/BOM),
  // it's a pure PHP file
  return "pure";
}

/**
 * PHPDoc コメント (ブロックコメント形式) を抽出
 */
function getPHPDocComment(node: PHPNode, content: string): string | null {
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

    // commentをチェック
    if (sibling.type === "comment") {
      const commentText = content.substring(sibling.startIndex, sibling.endIndex);
      // PHPDoc コメント形式のみ抽出
      if (commentText.startsWith("/**") && commentText.endsWith("*/")) {
        precedingComments.unshift(cleanDocComment(commentText));
      }
    } else if (sibling.type !== "text" && !sibling.text.trim().match(/^\s*$/)) {
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
 * 子ノードから名前を抽出
 */
function extractName(node: PHPNode, content: string): string | null {
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

/**
 * シンボルレコードを作成
 */
function createPHPSymbolRecords(tree: Parser.Tree, content: string): SymbolRecord[] {
  const results: Array<Omit<SymbolRecord, "symbolId">> = [];

  /**
   * ノードからシグネチャを取得
   */
  function getSignature(node: PHPNode): string {
    const nodeText = content.substring(node.startIndex, node.endIndex);
    return sanitizeTreeSitterSignature(nodeText);
  }

  /**
   * ツリーを再帰的にトラバースしてシンボルを抽出
   */
  function visit(node: PHPNode): void {
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
          doc: getPHPDocComment(node, content),
        });
      }
    }
    // interface_declaration: インターフェース宣言
    else if (node.type === "interface_declaration") {
      const name = extractName(node, content);
      if (name) {
        results.push({
          name,
          kind: "interface",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getPHPDocComment(node, content),
        });
      }
    }
    // trait_declaration: トレイト宣言
    else if (node.type === "trait_declaration") {
      const name = extractName(node, content);
      if (name) {
        results.push({
          name,
          kind: "trait",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getPHPDocComment(node, content),
        });
      }
    }
    // function_definition: トップレベル関数またはメソッド
    else if (node.type === "function_definition" || node.type === "method_declaration") {
      const name = extractName(node, content);
      if (name) {
        // 親がclass_declaration/trait_declaration/interface_declarationの子孫の場合はmethod、それ以外はfunction
        let isMethod = false;
        let parentNode = node.parent;
        while (parentNode) {
          if (
            parentNode.type === "class_declaration" ||
            parentNode.type === "trait_declaration" ||
            parentNode.type === "interface_declaration"
          ) {
            isMethod = true;
            break;
          }
          parentNode = parentNode.parent;
        }
        const kind = isMethod ? "method" : "function";
        results.push({
          name,
          kind,
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getPHPDocComment(node, content),
        });
      }
    }
    // property_declaration: プロパティ
    else if (node.type === "property_declaration") {
      // property_element から変数名を抽出
      const propertyElement = node.namedChildren.find((child) => child.type === "property_element");
      if (propertyElement) {
        const variableNameNode = propertyElement.namedChildren.find(
          (child) => child.type === "variable_name"
        );
        if (variableNameNode) {
          const name = content
            .substring(variableNameNode.startIndex, variableNameNode.endIndex)
            .replace(/^\$/, ""); // $を除去
          results.push({
            name,
            kind: "property",
            rangeStartLine: treeSitterPointToLine(node.startPosition),
            rangeEndLine: treeSitterPointToLine(node.endPosition),
            signature: getSignature(node),
            doc: getPHPDocComment(node, content),
          });
        }
      }
    }
    // const_declaration: 定数（クラス定数）
    else if (node.type === "const_declaration") {
      const constElement = node.namedChildren.find((child) => child.type === "const_element");
      if (constElement) {
        const name = extractName(constElement, content);
        if (name) {
          results.push({
            name,
            kind: "constant",
            rangeStartLine: treeSitterPointToLine(node.startPosition),
            rangeEndLine: treeSitterPointToLine(node.endPosition),
            signature: getSignature(node),
            doc: getPHPDocComment(node, content),
          });
        }
      }
    }
    // namespace_definition: 名前空間
    else if (node.type === "namespace_definition") {
      const namespaceName = node.namedChildren.find((child) => child.type === "namespace_name");
      if (namespaceName) {
        const name = content.substring(namespaceName.startIndex, namespaceName.endIndex);
        results.push({
          name,
          kind: "namespace",
          rangeStartLine: treeSitterPointToLine(node.startPosition),
          rangeEndLine: treeSitterPointToLine(node.endPosition),
          signature: getSignature(node),
          doc: getPHPDocComment(node, content),
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
 * PHP の use 文を解析して依存関係を収集
 */
function collectPHPDependencies(
  _sourcePath: string,
  tree: Parser.Tree,
  content: string,
  _fileSet: Set<string>
): Array<{ dstKind: "path" | "package"; dst: string; rel: string }> {
  const { record, getDependencies } = createDependencyRecorder();

  function visit(node: PHPNode): void {
    // namespace_use_declaration: use文
    if (node.type === "namespace_use_declaration") {
      // namespace_use_clauseを探す（通常のuse文）
      const useClauses = node.namedChildren.filter(
        (child) => child.type === "namespace_use_clause"
      );
      for (const useClause of useClauses) {
        // qualified_nameまたはnameを抽出
        const qualifiedName = useClause.namedChildren.find(
          (child) => child.type === "qualified_name" || child.type === "name"
        );
        if (qualifiedName) {
          const importName = content.substring(qualifiedName.startIndex, qualifiedName.endIndex);
          // Treat all namespaced imports as packages until composer.json parsing is implemented.
          // PSR-4 maps namespace prefixes to base directories (e.g., App\ -> src/),
          // not relative paths from the current file's directory.
          // TODO: Implement proper PSR-4 resolution by parsing composer.json
          record("package", importName);
        }
      }

      // namespace_use_groupを探す（グループ化されたuse文: use Foo\{Bar, Baz};）
      const useGroups = node.namedChildren.filter((child) => child.type === "namespace_use_group");
      if (useGroups.length > 0) {
        // プレフィックスを取得（例: App\Services）
        const prefixNode = node.namedChildren.find((child) => child.type === "namespace_name");
        const prefix = prefixNode
          ? content.substring(prefixNode.startIndex, prefixNode.endIndex)
          : "";

        for (const useGroup of useGroups) {
          // namespace_use_group_clauseを処理
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
              // Treat all namespaced imports as packages (same reasoning as above)
              record("package", fullName);
            }
          }
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
 * PHP Language Analyzer
 *
 * LanguageAnalyzer インターフェースを実装し、
 * PHP ファイルのシンボル抽出と依存関係解析を提供
 */
export class PHPAnalyzer implements LanguageAnalyzer {
  readonly language = "PHP";

  async analyze(context: AnalysisContext): Promise<AnalysisResult> {
    const { pathInRepo, content, fileSet } = context;

    try {
      // Create new parser instance for each file (thread-safety for concurrent processing)
      const parser = new Parser();

      // tree-sitter-php provides two parsers:
      // - php_only: for pure PHP files (<?php at start)
      // - php: for HTML-mixed PHP files (HTML with <?php ... ?> tags)
      const phpType = detectPHPType(content);
      const language = phpType === "html-mixed" ? PHP_MIXED : PHP_ONLY;

      // Validate language object before setting it
      if (!language || typeof language !== "object") {
        throw new Error(`Tree-sitter language for PHP type "${phpType}" is invalid or undefined`);
      }

      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      parser.setLanguage(language as any);
      const tree = parser.parse(content);

      // シンボル抽出
      const symbols = createPHPSymbolRecords(tree, content);

      // シンボルからスニペットを生成
      const snippets = symbolsToSnippets(symbols);

      // 依存関係を収集
      const dependencies = collectPHPDependencies(pathInRepo, tree, content, fileSet);

      return { symbols, snippets, dependencies };
    } catch (error) {
      // パース失敗時は空の結果を返して他のファイルの処理を継続
      console.error(`Failed to parse PHP file ${pathInRepo}:`, error);
      return { symbols: [], snippets: [], dependencies: [] };
    }
  }

  // tree-sitter はステートレスのためクリーンアップ不要
}

/**
 * PHP アナライザーのファクトリ関数
 */
export function createPHPAnalyzer(): PHPAnalyzer {
  return new PHPAnalyzer();
}
