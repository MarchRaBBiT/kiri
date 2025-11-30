/**
 * TypeScript Analyzer テスト
 *
 * TypeScriptAnalyzer クラスの単体テスト
 */

import { describe, it, expect } from "vitest";

import type { AnalysisContext } from "../../../../src/indexer/codeintel/types.js";
import {
  TypeScriptAnalyzer,
  createTypeScriptAnalyzer,
} from "../../../../src/indexer/codeintel/typescript/analyzer.js";

describe("TypeScriptAnalyzer", () => {
  describe("language property", () => {
    it("言語識別子は 'TypeScript' を返す", () => {
      const analyzer = new TypeScriptAnalyzer();
      expect(analyzer.language).toBe("TypeScript");
    });
  });

  describe("analyze - シンボル抽出", () => {
    it("関数宣言を抽出", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.ts",
        content: `function greet(name: string): string {
  return "Hello, " + name;
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]).toMatchObject({
        name: "greet",
        kind: "function",
        rangeStartLine: 1,
        rangeEndLine: 3,
      });
      expect(result.symbols[0]?.signature).toContain("function greet");
    });

    it("クラス宣言を抽出", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.ts",
        content: `class MyClass {
  private value: number;

  constructor(value: number) {
    this.value = value;
  }
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols.some((s) => s.name === "MyClass" && s.kind === "class")).toBe(true);
    });

    it("インターフェース宣言を抽出", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.ts",
        content: `interface User {
  id: number;
  name: string;
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]).toMatchObject({
        name: "User",
        kind: "interface",
      });
    });

    it("enum 宣言を抽出", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.ts",
        content: `enum Color {
  Red,
  Green,
  Blue,
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]).toMatchObject({
        name: "Color",
        kind: "enum",
      });
    });

    it("メソッド宣言を抽出", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.ts",
        content: `class Calculator {
  add(a: number, b: number): number {
    return a + b;
  }

  subtract(a: number, b: number): number {
    return a - b;
  }
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      const methods = result.symbols.filter((s) => s.kind === "method");
      expect(methods).toHaveLength(2);
      expect(methods.map((m) => m.name)).toContain("add");
      expect(methods.map((m) => m.name)).toContain("subtract");
    });

    it("JSDoc コメントを抽出", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.ts",
        content: `/**
 * Adds two numbers together.
 * @param a First number
 * @param b Second number
 */
function add(a: number, b: number): number {
  return a + b;
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]?.doc).toContain("Adds two numbers together");
    });

    it("複数のシンボルを行番号順にソート", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.ts",
        content: `interface A {}
class B {}
function c() {}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(3);
      expect(result.symbols[0]?.name).toBe("A");
      expect(result.symbols[1]?.name).toBe("B");
      expect(result.symbols[2]?.name).toBe("c");

      // symbolId は行番号順に割り当て
      expect(result.symbols[0]?.symbolId).toBe(1);
      expect(result.symbols[1]?.symbolId).toBe(2);
      expect(result.symbols[2]?.symbolId).toBe(3);
    });

    it("空のファイルは空の結果を返す", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "empty.ts",
        content: "",
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toEqual([]);
      expect(result.snippets).toEqual([]);
      expect(result.dependencies).toEqual([]);
    });
  });

  describe("analyze - スニペット生成", () => {
    it("シンボルからスニペットを生成", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.ts",
        content: `function foo() {
  return 1;
}

function bar() {
  return 2;
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.snippets).toHaveLength(2);
      expect(result.snippets[0]).toMatchObject({
        startLine: 1,
        endLine: 3,
        symbolId: 1,
      });
      expect(result.snippets[1]).toMatchObject({
        startLine: 5,
        endLine: 7,
        symbolId: 2,
      });
    });
  });

  describe("analyze - 依存関係解析", () => {
    it("import 文からパッケージ依存を検出", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "src/index.ts",
        content: `import lodash from "lodash";
import * as path from "node:path";`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(2);
      expect(result.dependencies).toContainEqual({
        dstKind: "package",
        dst: "lodash",
        rel: "import",
      });
      expect(result.dependencies).toContainEqual({
        dstKind: "package",
        dst: "node:path",
        rel: "import",
      });
    });

    it("相対パス import をファイルセットと照合", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "src/index.ts",
        content: `import { helper } from "./utils.js";`,
        fileSet: new Set(["src/utils.ts", "src/index.ts"]),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(1);
      expect(result.dependencies[0]).toMatchObject({
        dstKind: "path",
        dst: "src/utils.ts",
        rel: "import",
      });
    });

    it("export from 文を依存として検出", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "src/index.ts",
        content: `export { foo } from "./foo.js";
export * from "./bar.js";`,
        fileSet: new Set(["src/foo.ts", "src/bar.ts"]),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(2);
      expect(result.dependencies).toContainEqual({
        dstKind: "path",
        dst: "src/foo.ts",
        rel: "import",
      });
      expect(result.dependencies).toContainEqual({
        dstKind: "path",
        dst: "src/bar.ts",
        rel: "import",
      });
    });

    it("require() 呼び出しを依存として検出", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "src/index.ts",
        content: `const fs = require("fs");`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(1);
      expect(result.dependencies[0]).toMatchObject({
        dstKind: "package",
        dst: "fs",
        rel: "import",
      });
    });

    it("存在しない相対パス import は無視", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "src/index.ts",
        content: `import { missing } from "./not-exist.js";`,
        fileSet: new Set(["src/index.ts"]),
      };

      const result = await analyzer.analyze(context);

      // ファイルセットに存在しないパスは依存として記録されない
      expect(result.dependencies).toHaveLength(0);
    });

    it("重複した依存は1つにマージ", async () => {
      const analyzer = new TypeScriptAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "src/index.ts",
        content: `import { a } from "lodash";
import { b } from "lodash";
import { c } from "lodash";`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(1);
      expect(result.dependencies[0]?.dst).toBe("lodash");
    });
  });

  describe("createTypeScriptAnalyzer", () => {
    it("ファクトリ関数で TypeScriptAnalyzer を生成", () => {
      const analyzer = createTypeScriptAnalyzer();

      expect(analyzer).toBeInstanceOf(TypeScriptAnalyzer);
      expect(analyzer.language).toBe("TypeScript");
    });
  });
});
