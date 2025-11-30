/**
 * Dart Analyzer Adapter テスト
 *
 * DartAnalyzer アダプタークラスの単体テスト
 * 既存の analyzeDartSource をラップするアダプター層の振る舞いを検証
 */

import { describe, it, expect, vi, beforeEach, afterEach } from "vitest";

import {
  DartAnalyzer,
  createDartAnalyzer,
} from "../../../../src/indexer/codeintel/dart/adapter.js";
import type { AnalysisContext } from "../../../../src/indexer/codeintel/types.js";

// 既存の Dart 解析実装をモック
vi.mock("../../../../src/indexer/dart/analyze.js");

describe("DartAnalyzer", () => {
  let mockAnalyzeDartSource: ReturnType<typeof vi.fn>;
  let mockCleanup: ReturnType<typeof vi.fn>;

  beforeEach(async () => {
    vi.resetModules();

    // デフォルトの成功レスポンスを設定
    mockAnalyzeDartSource = vi.fn().mockResolvedValue({
      symbols: [
        {
          symbolId: 1,
          name: "TestClass",
          kind: "class",
          rangeStartLine: 1,
          rangeEndLine: 10,
        },
      ],
      snippets: [
        {
          snippetId: 1,
          symbolId: 1,
          startLine: 1,
          endLine: 10,
        },
      ],
      dependencies: [],
      status: "success",
      error: undefined,
    });

    mockCleanup = vi.fn().mockResolvedValue(undefined);

    const analyzeModule = await import("../../../../src/indexer/dart/analyze.js");
    vi.mocked(analyzeModule.analyzeDartSource).mockImplementation(mockAnalyzeDartSource);
    vi.mocked(analyzeModule.cleanup).mockImplementation(mockCleanup);
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe("language property", () => {
    it("言語識別子は 'Dart' を返す", () => {
      const analyzer = new DartAnalyzer();
      expect(analyzer.language).toBe("Dart");
    });
  });

  describe("analyze - workspaceRoot 必須チェック", () => {
    it("workspaceRoot がない場合は空の結果を返す", async () => {
      const analyzer = new DartAnalyzer();
      const consoleSpy = vi.spyOn(console, "warn").mockImplementation(() => {});

      const context: AnalysisContext = {
        pathInRepo: "lib/main.dart",
        content: "class TestClass {}",
        fileSet: new Set(),
        // workspaceRoot が未指定
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toEqual([]);
      expect(result.snippets).toEqual([]);
      expect(result.dependencies).toEqual([]);
      expect(consoleSpy).toHaveBeenCalledWith(expect.stringContaining("workspaceRoot required"));

      consoleSpy.mockRestore();
    });

    it("workspaceRoot がある場合は analyzeDartSource を呼び出す", async () => {
      const analyzer = new DartAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "lib/main.dart",
        content: "class TestClass {}",
        fileSet: new Set(),
        workspaceRoot: "/projects/my_app",
      };

      await analyzer.analyze(context);

      expect(mockAnalyzeDartSource).toHaveBeenCalledWith(
        "lib/main.dart",
        "class TestClass {}",
        "/projects/my_app"
      );
    });
  });

  describe("analyze - 結果の変換", () => {
    it("analyzeDartSource の結果を AnalysisResult 形式で返す", async () => {
      const analyzer = new DartAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "lib/main.dart",
        content: "class TestClass {}",
        fileSet: new Set(),
        workspaceRoot: "/projects/my_app",
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]).toMatchObject({
        name: "TestClass",
        kind: "class",
      });
      expect(result.snippets).toHaveLength(1);
      expect(result.dependencies).toEqual([]);
      expect(result.status).toBe("success");
      expect(result.error).toBeUndefined();
    });

    it("エラー時は status と error を含む結果を返す", async () => {
      mockAnalyzeDartSource.mockResolvedValue({
        symbols: [],
        snippets: [],
        dependencies: [],
        status: "error",
        error: "Analysis failed",
      });

      const analyzer = new DartAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "lib/main.dart",
        content: "invalid code",
        fileSet: new Set(),
        workspaceRoot: "/projects/my_app",
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toEqual([]);
      expect(result.status).toBe("error");
      expect(result.error).toBe("Analysis failed");
    });

    it("SDK 未利用時は sdk_unavailable status を返す", async () => {
      mockAnalyzeDartSource.mockResolvedValue({
        symbols: [],
        snippets: [],
        dependencies: [],
        status: "sdk_unavailable",
        error: undefined,
      });

      const analyzer = new DartAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "lib/main.dart",
        content: "class TestClass {}",
        fileSet: new Set(),
        workspaceRoot: "/projects/my_app",
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toEqual([]);
      expect(result.status).toBe("sdk_unavailable");
    });
  });

  describe("dispose", () => {
    it("cleanup を呼び出して全クライアントを終了する", async () => {
      const analyzer = new DartAnalyzer();
      await analyzer.dispose();

      expect(mockCleanup).toHaveBeenCalledTimes(1);
    });
  });

  describe("createDartAnalyzer", () => {
    it("ファクトリ関数で DartAnalyzer を生成", () => {
      const analyzer = createDartAnalyzer();

      expect(analyzer).toBeInstanceOf(DartAnalyzer);
      expect(analyzer.language).toBe("Dart");
    });
  });
});
