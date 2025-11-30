import { describe, it, expect } from "vitest";

import {
  treeSitterPointToLine,
  sanitizeTreeSitterSignature,
  assignSymbolIds,
  symbolsToSnippets,
  createDependencyRecorder,
  buildLineStartsArray,
  offsetToLine,
  cleanDocComment,
  buildFallbackSnippet,
} from "../../../src/indexer/codeintel/utils.js";

describe("codeintel/utils", () => {
  describe("treeSitterPointToLine", () => {
    it("0-based rowを1-based行番号に変換", () => {
      expect(treeSitterPointToLine({ row: 0, column: 0 })).toBe(1);
      expect(treeSitterPointToLine({ row: 5, column: 10 })).toBe(6);
      expect(treeSitterPointToLine({ row: 99, column: 0 })).toBe(100);
    });
  });

  describe("sanitizeTreeSitterSignature", () => {
    it("関数本体を除去", () => {
      const nodeText = "function foo() { return 1; }";
      expect(sanitizeTreeSitterSignature(nodeText)).toBe("function foo()");
    });

    it("本体がない場合はそのまま返す", () => {
      const nodeText = "function foo()";
      expect(sanitizeTreeSitterSignature(nodeText)).toBe("function foo()");
    });

    it("デフォルトで200文字に切り詰め", () => {
      const longSignature = "function " + "a".repeat(300) + "() { }";
      const result = sanitizeTreeSitterSignature(longSignature);
      expect(result.length).toBeLessThanOrEqual(200);
    });

    it("カスタム最大長を指定できる", () => {
      const nodeText = "function verylongname() { }";
      const result = sanitizeTreeSitterSignature(nodeText, { maxLength: 10 });
      expect(result.length).toBeLessThanOrEqual(10);
    });

    it("複数行の場合、最初の行を取得 (normalizeFirst=false)", () => {
      const nodeText = "function foo(\n  x: number\n) { }";
      expect(sanitizeTreeSitterSignature(nodeText)).toBe("function foo(");
    });

    it("normalizeFirst=trueの場合、空白を正規化してから切り詰め (Java用)", () => {
      const nodeText = "public  void   foo(\n  int x\n) { }";
      const result = sanitizeTreeSitterSignature(nodeText, { normalizeFirst: true });
      expect(result).toBe("public void foo( int x )");
    });

    it("空白を正規化", () => {
      const nodeText = "function   foo  () { }";
      expect(sanitizeTreeSitterSignature(nodeText)).toBe("function foo ()");
    });
  });

  describe("assignSymbolIds", () => {
    it("行番号でソートしてIDを割り当て", () => {
      const symbols = [
        {
          name: "b",
          kind: "function",
          rangeStartLine: 10,
          rangeEndLine: 15,
          signature: null,
          doc: null,
        },
        {
          name: "a",
          kind: "class",
          rangeStartLine: 1,
          rangeEndLine: 20,
          signature: null,
          doc: null,
        },
        {
          name: "c",
          kind: "method",
          rangeStartLine: 5,
          rangeEndLine: 8,
          signature: null,
          doc: null,
        },
      ];

      const result = assignSymbolIds(symbols);

      expect(result).toHaveLength(3);
      expect(result[0]).toMatchObject({ symbolId: 1, name: "a", rangeStartLine: 1 });
      expect(result[1]).toMatchObject({ symbolId: 2, name: "c", rangeStartLine: 5 });
      expect(result[2]).toMatchObject({ symbolId: 3, name: "b", rangeStartLine: 10 });
    });

    it("空配列は空配列を返す", () => {
      expect(assignSymbolIds([])).toEqual([]);
    });

    it("元の配列を変更しない", () => {
      const symbols = [
        {
          name: "b",
          kind: "function",
          rangeStartLine: 10,
          rangeEndLine: 15,
          signature: null,
          doc: null,
        },
        {
          name: "a",
          kind: "class",
          rangeStartLine: 1,
          rangeEndLine: 20,
          signature: null,
          doc: null,
        },
      ];
      const original = [...symbols];

      assignSymbolIds(symbols);

      expect(symbols[0]?.name).toBe(original[0]?.name);
    });
  });

  describe("symbolsToSnippets", () => {
    it("シンボルからスニペットを生成", () => {
      const symbols = [
        {
          symbolId: 1,
          name: "foo",
          kind: "function",
          rangeStartLine: 1,
          rangeEndLine: 5,
          signature: null,
          doc: null,
        },
        {
          symbolId: 2,
          name: "bar",
          kind: "class",
          rangeStartLine: 10,
          rangeEndLine: 20,
          signature: null,
          doc: null,
        },
      ];

      const snippets = symbolsToSnippets(symbols);

      expect(snippets).toEqual([
        { startLine: 1, endLine: 5, symbolId: 1 },
        { startLine: 10, endLine: 20, symbolId: 2 },
      ]);
    });

    it("空配列は空配列を返す", () => {
      expect(symbolsToSnippets([])).toEqual([]);
    });
  });

  describe("createDependencyRecorder", () => {
    it("依存関係を記録できる", () => {
      const { record, getDependencies } = createDependencyRecorder();

      record("package", "lodash");
      record("path", "./utils");

      const deps = getDependencies();
      expect(deps).toHaveLength(2);
      expect(deps).toContainEqual({ dstKind: "package", dst: "lodash", rel: "import" });
      expect(deps).toContainEqual({ dstKind: "path", dst: "./utils", rel: "import" });
    });

    it("重複を自動排除", () => {
      const { record, getDependencies } = createDependencyRecorder();

      record("package", "lodash");
      record("package", "lodash");
      record("package", "lodash");

      expect(getDependencies()).toHaveLength(1);
    });

    it("同じdstでもkindが異なれば別扱い", () => {
      const { record, getDependencies } = createDependencyRecorder();

      record("package", "foo");
      record("path", "foo");

      expect(getDependencies()).toHaveLength(2);
    });

    it("カスタムrelを指定できる", () => {
      const { record, getDependencies } = createDependencyRecorder();

      record("package", "lodash", "require");

      expect(getDependencies()[0]?.rel).toBe("require");
    });
  });

  describe("buildLineStartsArray", () => {
    it("行の開始位置を配列で返す", () => {
      const content = "line1\nline2\nline3";
      const lineStarts = buildLineStartsArray(content);

      expect(lineStarts).toEqual([0, 6, 12]); // "line1\n" = 6文字, "line2\n" = 6文字
    });

    it("空文字列は[0]を返す", () => {
      expect(buildLineStartsArray("")).toEqual([0]);
    });

    it("改行のみは[0, 1]を返す", () => {
      expect(buildLineStartsArray("\n")).toEqual([0, 1]);
    });

    it("複数の連続改行を処理", () => {
      const content = "a\n\nb";
      const lineStarts = buildLineStartsArray(content);
      expect(lineStarts).toEqual([0, 2, 3]);
    });
  });

  describe("offsetToLine", () => {
    it("オフセットから行番号を取得", () => {
      const lineStarts = [0, 6, 12, 18]; // 4行

      expect(offsetToLine(lineStarts, 0)).toBe(1); // 1行目の先頭
      expect(offsetToLine(lineStarts, 5)).toBe(1); // 1行目の末尾
      expect(offsetToLine(lineStarts, 6)).toBe(2); // 2行目の先頭
      expect(offsetToLine(lineStarts, 11)).toBe(2); // 2行目の末尾
      expect(offsetToLine(lineStarts, 12)).toBe(3); // 3行目の先頭
      expect(offsetToLine(lineStarts, 20)).toBe(4); // 4行目
    });

    it("境界値を正しく処理", () => {
      const lineStarts = [0, 5];

      expect(offsetToLine(lineStarts, 0)).toBe(1);
      expect(offsetToLine(lineStarts, 4)).toBe(1);
      expect(offsetToLine(lineStarts, 5)).toBe(2);
    });
  });

  describe("cleanDocComment", () => {
    it("Swift /// コメントをクリーンアップ", () => {
      const comment = "/// This is a doc comment\n/// Second line";
      expect(cleanDocComment(comment)).toBe("This is a doc comment\nSecond line");
    });

    it("/** */ コメントをクリーンアップ", () => {
      const comment = "/** This is a doc comment */";
      expect(cleanDocComment(comment)).toBe("This is a doc comment");
    });

    it("複数行の /** */ コメントをクリーンアップ", () => {
      const comment = `/**
 * First line
 * Second line
 */`;
      expect(cleanDocComment(comment)).toBe("First line\nSecond line");
    });

    it("空コメントは空文字列を返す", () => {
      expect(cleanDocComment("")).toBe("");
    });
  });

  describe("buildFallbackSnippet", () => {
    it("ファイル全体をカバーするスニペットを生成", () => {
      const snippet = buildFallbackSnippet(100);

      expect(snippet).toEqual({
        startLine: 1,
        endLine: 100,
        symbolId: null,
      });
    });

    it("1行のファイル", () => {
      const snippet = buildFallbackSnippet(1);

      expect(snippet).toEqual({
        startLine: 1,
        endLine: 1,
        symbolId: null,
      });
    });
  });
});
