/**
 * Dart Language Analyzer Adapter
 *
 * 既存の Dart Analysis Server 実装をラップして LanguageAnalyzer インターフェースを提供。
 * Dart はLSPベースの Analysis Server を使用するため、他の tree-sitter ベースの
 * アナライザーとは異なるアーキテクチャを持つ。
 */

import { analyzeDartSource, cleanup } from "../../dart/analyze.js";
import type { LanguageAnalyzer, AnalysisContext, AnalysisResult } from "../types.js";
import { emptyResult } from "../types.js";

// 既存の Dart 解析実装をインポート
// Note: analyzeDartSource と cleanup は src/indexer/dart/ にある既存実装を使用

/**
 * Dart Language Analyzer
 *
 * LanguageAnalyzer インターフェースを実装し、
 * Dart Analysis Server を使用したシンボル抽出と依存関係解析を提供。
 *
 * 特徴:
 * - LSPベースの Analysis Server を使用
 * - プロセスプーリングによるリソース効率化
 * - 参照カウントとアイドルTTLによるライフサイクル管理
 * - workspaceRoot が必須 (Analysis Server は絶対パスを要求)
 */
export class DartAnalyzer implements LanguageAnalyzer {
  readonly language = "Dart";

  async analyze(context: AnalysisContext): Promise<AnalysisResult> {
    const { pathInRepo, content, workspaceRoot } = context;

    // Dart Analysis Server は workspaceRoot を要求する
    if (!workspaceRoot) {
      console.warn(
        `[DartAnalyzer] workspaceRoot required for Dart analysis, skipping ${pathInRepo}`
      );
      return emptyResult();
    }

    // 既存の Dart 解析実装を呼び出し
    const result = await analyzeDartSource(pathInRepo, content, workspaceRoot);

    // exactOptionalPropertyTypes対応: errorはundefinedの場合は省略
    return {
      symbols: result.symbols,
      snippets: result.snippets,
      dependencies: result.dependencies,
      status: result.status,
      ...(result.error !== undefined && { error: result.error }),
    };
  }

  /**
   * 全ての Dart Analysis Server プロセスをクリーンアップ
   *
   * このメソッドは LanguageRegistry.cleanup() から呼び出され、
   * プール内の全クライアントを適切に終了する
   */
  async dispose(): Promise<void> {
    await cleanup();
  }
}

/**
 * Dart アナライザーのファクトリ関数
 */
export function createDartAnalyzer(): DartAnalyzer {
  return new DartAnalyzer();
}
