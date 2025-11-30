/**
 * Swift Analyzer テスト
 *
 * SwiftAnalyzer クラスの単体テスト
 */

import { describe, it, expect } from "vitest";

import {
  SwiftAnalyzer,
  createSwiftAnalyzer,
} from "../../../../src/indexer/codeintel/swift/analyzer.js";
import type { AnalysisContext } from "../../../../src/indexer/codeintel/types.js";

describe("SwiftAnalyzer", () => {
  describe("language property", () => {
    it("言語識別子は 'Swift' を返す", () => {
      const analyzer = new SwiftAnalyzer();
      expect(analyzer.language).toBe("Swift");
    });
  });

  describe("analyze - シンボル抽出", () => {
    it("クラス宣言とメソッド・プロパティを抽出", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `/// A sample class with documentation
class MyClass {
  var property: String

  init(value: String) {
    self.property = value
  }

  func myMethod() -> String {
    return property
  }
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(4);

      // Class
      expect(result.symbols[0]).toMatchObject({
        symbolId: 1,
        name: "MyClass",
        kind: "class",
        doc: "A sample class with documentation",
      });

      // Property
      expect(result.symbols[1]).toMatchObject({
        symbolId: 2,
        name: "property",
        kind: "property",
      });

      // Initializer
      expect(result.symbols[2]).toMatchObject({
        symbolId: 3,
        name: "init",
        kind: "initializer",
      });

      // Method
      expect(result.symbols[3]).toMatchObject({
        symbolId: 4,
        name: "myMethod",
        kind: "method",
      });
    });

    it("struct 宣言を抽出", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `struct Point {
  let x: Int
  let y: Int
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(3);
      expect(result.symbols[0]).toMatchObject({
        name: "Point",
        kind: "struct",
      });
      expect(result.symbols[1]).toMatchObject({
        name: "x",
        kind: "property",
      });
      expect(result.symbols[2]).toMatchObject({
        name: "y",
        kind: "property",
      });
    });

    it("protocol 宣言とメソッドを抽出", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `/// Protocol documentation
protocol MyProtocol {
  func protocolMethod()
  func anotherMethod(param: String) -> Int
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(3);
      expect(result.symbols[0]).toMatchObject({
        name: "MyProtocol",
        kind: "protocol",
        doc: "Protocol documentation",
      });
      expect(result.symbols[1]).toMatchObject({
        name: "protocolMethod",
        kind: "protocol_method",
      });
      expect(result.symbols[2]).toMatchObject({
        name: "anotherMethod",
        kind: "protocol_method",
      });
    });

    it("enum 宣言を抽出", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `enum Direction {
  case north
  case south
  case east
  case west
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]).toMatchObject({
        name: "Direction",
        kind: "enum",
      });
    });

    it("extension 宣言を抽出", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `extension String {
  var isNotEmpty: Bool {
    return !self.isEmpty
  }

  func customMethod() -> Bool {
    return !self.isEmpty
  }
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(3);
      expect(result.symbols[0]).toMatchObject({
        name: "String",
        kind: "extension",
      });
      expect(result.symbols[1]).toMatchObject({
        name: "isNotEmpty",
        kind: "property",
      });
      expect(result.symbols[2]).toMatchObject({
        name: "customMethod",
        kind: "method",
      });
    });

    it("トップレベル関数を抽出", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `/// Function documentation
func topLevelFunction(param: Int) -> String {
  return "\\(param)"
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]).toMatchObject({
        name: "topLevelFunction",
        kind: "function",
        doc: "Function documentation",
      });
      expect(result.symbols[0]?.signature).toContain("func topLevelFunction");
    });

    it("ネストされたクラスとstructを処理", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `class OuterClass {
  struct InnerStruct {
    let value: Int
  }

  func outerMethod() {}
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(4);
      expect(result.symbols.map((s) => s.name)).toContain("OuterClass");
      expect(result.symbols.map((s) => s.name)).toContain("InnerStruct");
      expect(result.symbols.map((s) => s.name)).toContain("value");
      expect(result.symbols.map((s) => s.name)).toContain("outerMethod");
    });

    it("ブロックコメントからドキュメントを抽出", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `/**
 * Multi-line documentation
 * for a function
 */
func documentedFunction() {}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      const symbol = result.symbols[0];
      expect(symbol?.doc).toBeTruthy();
      expect(symbol?.doc).toContain("Multi-line documentation");
    });

    it("空のファイルは空の結果を返す", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "empty.swift",
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
    it("シンボル境界に揃えたスニペットを生成", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `class MyClass {
  func method1() {}
  func method2() {}
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.snippets).toHaveLength(3);
      // 各スニペットはシンボルに対応
      expect(result.snippets[0]?.symbolId).toBe(1);
      expect(result.snippets[1]?.symbolId).toBe(2);
      expect(result.snippets[2]?.symbolId).toBe(3);
    });
  });

  describe("analyze - 依存関係解析", () => {
    it("import 文をパッケージ依存として検出", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `import Foundation
import UIKit

class MyClass {}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(2);
      expect(result.dependencies[0]).toMatchObject({
        dstKind: "package",
        dst: "Foundation",
        rel: "import",
      });
      expect(result.dependencies[1]).toMatchObject({
        dstKind: "package",
        dst: "UIKit",
        rel: "import",
      });
    });

    it("ローカルファイル import をパス依存として検出", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `import MyModule

class MyClass {}`,
        fileSet: new Set(["MyModule.swift"]),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(1);
      expect(result.dependencies[0]).toMatchObject({
        dstKind: "path",
        dst: "MyModule.swift",
        rel: "import",
      });
    });

    it("複数の import 文を処理", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `import Foundation
import CoreData
import Combine`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(3);
      const moduleNames = result.dependencies.map((d) => d.dst);
      expect(moduleNames).toContain("Foundation");
      expect(moduleNames).toContain("CoreData");
      expect(moduleNames).toContain("Combine");
    });
  });

  describe("analyze - シグネチャ", () => {
    it("シグネチャを200文字に切り詰め", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `func veryLongFunctionNameWithManyParameters(param1: String, param2: Int, param3: Bool, param4: Double, param5: Array<String>, param6: Dictionary<String, Any>, param7: Set<Int>, param8: Optional<String>) -> Result<String, Error> {
  return .success("test")
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      const signature = result.symbols[0]?.signature;
      expect(signature).toBeTruthy();
      expect(signature!.length).toBeLessThanOrEqual(200);
      expect(signature).toContain("veryLongFunctionNameWithManyParameters");
    });

    it("シグネチャから関数本体を除外", async () => {
      const analyzer = new SwiftAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.swift",
        content: `func myFunction() -> Int {
  let x = 42
  return x
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      const signature = result.symbols[0]?.signature;
      expect(signature).not.toContain("let x");
      expect(signature).not.toContain("return x");
    });
  });

  describe("createSwiftAnalyzer", () => {
    it("ファクトリ関数で SwiftAnalyzer を生成", () => {
      const analyzer = createSwiftAnalyzer();

      expect(analyzer).toBeInstanceOf(SwiftAnalyzer);
      expect(analyzer.language).toBe("Swift");
    });
  });
});
