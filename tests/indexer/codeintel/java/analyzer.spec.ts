/**
 * Java Analyzer テスト
 *
 * JavaAnalyzer クラスの単体テスト
 */

import { describe, it, expect } from "vitest";

import {
  JavaAnalyzer,
  createJavaAnalyzer,
} from "../../../../src/indexer/codeintel/java/analyzer.js";
import type { AnalysisContext } from "../../../../src/indexer/codeintel/types.js";

describe("JavaAnalyzer", () => {
  describe("language property", () => {
    it("言語識別子は 'Java' を返す", () => {
      const analyzer = new JavaAnalyzer();
      expect(analyzer.language).toBe("Java");
    });
  });

  describe("analyze - シンボル抽出", () => {
    it("クラス宣言とメソッド・フィールドを抽出", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "MyClass.java",
        content: `/**
 * A sample class with documentation
 */
public class MyClass {
    private String property;

    public MyClass(String value) {
        this.property = value;
    }

    public String myMethod() {
        return property;
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

      // Field
      expect(result.symbols[1]).toMatchObject({
        symbolId: 2,
        name: "property",
        kind: "field",
      });

      // Constructor
      expect(result.symbols[2]).toMatchObject({
        symbolId: 3,
        name: "MyClass",
        kind: "constructor",
      });

      // Method
      expect(result.symbols[3]).toMatchObject({
        symbolId: 4,
        name: "myMethod",
        kind: "method",
      });
    });

    it("interface 宣言を抽出", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "MyInterface.java",
        content: `/**
 * Sample interface
 */
public interface MyInterface {
    void myMethod();
    String anotherMethod(int param);
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(3);
      expect(result.symbols[0]).toMatchObject({
        name: "MyInterface",
        kind: "interface",
        doc: "Sample interface",
      });
      expect(result.symbols[1]).toMatchObject({
        name: "myMethod",
        kind: "method",
      });
      expect(result.symbols[2]).toMatchObject({
        name: "anotherMethod",
        kind: "method",
      });
    });

    it("enum 宣言を抽出", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "Direction.java",
        content: `public enum Direction {
    NORTH,
    SOUTH,
    EAST,
    WEST
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

    it("annotation 宣言を抽出", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "MyAnnotation.java",
        content: `/**
 * Custom annotation
 */
public @interface MyAnnotation {
    String value() default "";
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(2);
      expect(result.symbols[0]).toMatchObject({
        name: "MyAnnotation",
        kind: "annotation",
        doc: "Custom annotation",
      });
      expect(result.symbols[1]).toMatchObject({
        name: "value",
        kind: "method",
      });
    });

    it("ネストされたクラスを処理", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "OuterClass.java",
        content: `public class OuterClass {
    public static class InnerClass {
        private int value;
    }

    public void outerMethod() {}
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(4);
      expect(result.symbols.map((s) => s.name)).toContain("OuterClass");
      expect(result.symbols.map((s) => s.name)).toContain("InnerClass");
      expect(result.symbols.map((s) => s.name)).toContain("value");
      expect(result.symbols.map((s) => s.name)).toContain("outerMethod");
    });

    it("空のファイルは空の結果を返す", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "Empty.java",
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
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "MyClass.java",
        content: `public class MyClass {
    public void method1() {}
    public void method2() {}
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.snippets).toHaveLength(3);
      expect(result.snippets[0]?.symbolId).toBe(1); // MyClass
      expect(result.snippets[1]?.symbolId).toBe(2); // method1
      expect(result.snippets[2]?.symbolId).toBe(3); // method2
    });
  });

  describe("analyze - 依存関係解析", () => {
    it("import 文をパッケージ依存として検出", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "MyClass.java",
        content: `import java.util.List;
import java.util.ArrayList;

public class MyClass {}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(2);
      expect(result.dependencies[0]).toMatchObject({
        dstKind: "package",
        dst: "java.util.List",
        rel: "import",
      });
      expect(result.dependencies[1]).toMatchObject({
        dstKind: "package",
        dst: "java.util.ArrayList",
        rel: "import",
      });
    });

    it("ワイルドカード import を処理", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "MyClass.java",
        content: `import java.util.*;

public class MyClass {}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(1);
      expect(result.dependencies[0]).toMatchObject({
        dstKind: "package",
        dst: "java.util.*",
        rel: "import",
      });
    });

    it("ローカルファイル import をパス依存として検出", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "src/main/java/com/example/MyClass.java",
        content: `import com.example.util.Helper;

public class MyClass {}`,
        fileSet: new Set(["src/main/java/com/example/util/Helper.java"]),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(1);
      expect(result.dependencies[0]).toMatchObject({
        dstKind: "path",
        dst: "com.example.util.Helper",
        rel: "import",
      });
    });

    it("複数の import 文を処理", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "MyClass.java",
        content: `import java.io.File;
import java.io.IOException;
import java.util.List;`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(3);
    });
  });

  describe("analyze - シグネチャ", () => {
    it("シグネチャを200文字に切り詰め", async () => {
      const analyzer = new JavaAnalyzer();
      const longName = "a".repeat(250);
      const context: AnalysisContext = {
        pathInRepo: "MyClass.java",
        content: `public class MyClass {
    public void ${longName}() {}
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(2);
      const methodSymbol = result.symbols.find((s) => s.kind === "method");
      expect(methodSymbol?.signature).toBeTruthy();
      expect(methodSymbol!.signature!.length).toBeLessThanOrEqual(200);
    });

    it("シグネチャからメソッド本体を除外", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "MyClass.java",
        content: `public class MyClass {
    public int myMethod() {
        int x = 42;
        return x;
    }
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      const methodSymbol = result.symbols.find((s) => s.kind === "method");
      expect(methodSymbol?.signature).not.toContain("int x = 42");
      expect(methodSymbol?.signature).not.toContain("return x");
    });

    it("複数行のシグネチャを1行に正規化", async () => {
      const analyzer = new JavaAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "MyClass.java",
        content: `public class MyClass {
    public void myMethod(
            String param1,
            int param2
    ) {
    }
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      const methodSymbol = result.symbols.find((s) => s.kind === "method");
      expect(methodSymbol?.signature).toBeTruthy();
      // 改行が空白に置き換えられているはず
      expect(methodSymbol?.signature).not.toContain("\n");
      expect(methodSymbol?.signature).toContain("param1");
      expect(methodSymbol?.signature).toContain("param2");
    });
  });

  describe("createJavaAnalyzer", () => {
    it("ファクトリ関数で JavaAnalyzer を生成", () => {
      const analyzer = createJavaAnalyzer();

      expect(analyzer).toBeInstanceOf(JavaAnalyzer);
      expect(analyzer.language).toBe("Java");
    });
  });
});
