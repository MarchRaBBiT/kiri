/**
 * Language Analyzer Registry
 *
 * Alloyで検証済みのPlan A (Central Registry) 設計に基づく実装。
 *
 * 検証済みの不変条件:
 * - NoConflictingAnalyzers: 各言語に対して最大1つのアナライザー
 * - DeterministicLookup: レジストリ検索は決定的
 * - LockConsistency: ファイルレベルのロック整合性
 * - NoDeadlock: デッドロックなし
 */

import type { AnalysisContext, AnalysisResult, LanguageAnalyzer } from "./types.js";
import { emptyResult } from "./types.js";

/**
 * 言語アナライザーを管理するシングルトンレジストリ
 */
export class LanguageRegistry {
  private static instance: LanguageRegistry | null = null;
  private readonly analyzers = new Map<string, LanguageAnalyzer>();

  private constructor() {
    // シングルトンパターン: 外部からのインスタンス化を防止
  }

  /**
   * レジストリのシングルトンインスタンスを取得
   */
  static getInstance(): LanguageRegistry {
    if (!LanguageRegistry.instance) {
      LanguageRegistry.instance = new LanguageRegistry();
    }
    return LanguageRegistry.instance;
  }

  /**
   * テスト用: レジストリをリセット
   */
  static resetForTesting(): void {
    if (LanguageRegistry.instance) {
      // 既存のアナライザーをクリーンアップ (同期的)
      LanguageRegistry.instance.analyzers.clear();
    }
    LanguageRegistry.instance = null;
  }

  /**
   * アナライザーを登録
   *
   * @param analyzer - 登録するアナライザー
   * @throws Error - 同じ言語のアナライザーが既に登録されている場合
   */
  register(analyzer: LanguageAnalyzer): void {
    if (this.analyzers.has(analyzer.language)) {
      throw new Error(
        `Analyzer already registered for language: ${analyzer.language}. ` +
          `Use replace() to update an existing analyzer.`
      );
    }
    this.analyzers.set(analyzer.language, analyzer);
  }

  /**
   * 既存のアナライザーを置換
   * 既存のアナライザーがあればdispose()を呼び出してから置換
   *
   * @param analyzer - 新しいアナライザー
   */
  async replace(analyzer: LanguageAnalyzer): Promise<void> {
    const existing = this.analyzers.get(analyzer.language);
    if (existing?.dispose) {
      await existing.dispose();
    }
    this.analyzers.set(analyzer.language, analyzer);
  }

  /**
   * 指定した言語のアナライザーを取得
   *
   * @param language - 言語識別子
   * @returns アナライザー (未登録の場合はundefined)
   */
  getAnalyzer(language: string): LanguageAnalyzer | undefined {
    return this.analyzers.get(language);
  }

  /**
   * 指定した言語がサポートされているかを確認
   *
   * @param language - 言語識別子
   * @returns サポートされていればtrue
   */
  isSupported(language: string): boolean {
    return this.analyzers.has(language);
  }

  /**
   * 登録されている全ての言語を取得
   *
   * @returns 言語識別子の配列
   */
  getRegisteredLanguages(): string[] {
    return Array.from(this.analyzers.keys());
  }

  /**
   * ソースコードを解析
   *
   * @param language - 言語識別子 (nullの場合は空の結果を返す)
   * @param context - 解析コンテキスト
   * @returns 解析結果
   */
  async analyze(language: string | null, context: AnalysisContext): Promise<AnalysisResult> {
    if (!language) {
      return emptyResult();
    }

    const analyzer = this.analyzers.get(language);
    if (!analyzer) {
      return emptyResult();
    }

    return analyzer.analyze(context);
  }

  /**
   * 全てのアナライザーのリソースを解放
   * プロセス終了時やテスト終了時に呼び出す
   */
  async cleanup(): Promise<void> {
    const disposePromises: Promise<void>[] = [];

    for (const analyzer of this.analyzers.values()) {
      if (analyzer.dispose) {
        disposePromises.push(
          analyzer.dispose().catch((err) => {
            console.error(`Failed to dispose analyzer for ${analyzer.language}:`, err);
          })
        );
      }
    }

    await Promise.allSettled(disposePromises);
    this.analyzers.clear();
  }
}
