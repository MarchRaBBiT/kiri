/**
 * PHP Analyzer テスト
 *
 * PHPAnalyzer クラスの単体テスト
 */

import { describe, it, expect } from "vitest";

import { PHPAnalyzer, createPHPAnalyzer } from "../../../../src/indexer/codeintel/php/analyzer.js";
import type { AnalysisContext } from "../../../../src/indexer/codeintel/types.js";

describe("PHPAnalyzer", () => {
  describe("language property", () => {
    it("言語識別子は 'PHP' を返す", () => {
      const analyzer = new PHPAnalyzer();
      expect(analyzer.language).toBe("PHP");
    });
  });

  describe("analyze - シンボル抽出", () => {
    it("クラス宣言とメソッド・プロパティを抽出", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
/**
 * A sample class with documentation
 */
class MyClass {
  private $property;

  public function __construct($value) {
    $this->property = $value;
  }

  public function myMethod() {
    return $this->property;
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

      // Constructor method
      expect(result.symbols[2]).toMatchObject({
        symbolId: 3,
        name: "__construct",
        kind: "method",
      });

      // Method
      expect(result.symbols[3]).toMatchObject({
        symbolId: 4,
        name: "myMethod",
        kind: "method",
      });
    });

    it("interface 宣言を抽出", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
/**
 * Sample interface
 */
interface MyInterface {
  public function myMethod();
  public function anotherMethod($param);
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

    it("trait 宣言を抽出", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
trait MyTrait {
  private $traitProperty;

  public function traitMethod() {
    return $this->traitProperty;
  }
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(3);
      expect(result.symbols[0]).toMatchObject({
        name: "MyTrait",
        kind: "trait",
      });
      expect(result.symbols[1]).toMatchObject({
        name: "traitProperty",
        kind: "property",
      });
      expect(result.symbols[2]).toMatchObject({
        name: "traitMethod",
        kind: "method",
      });
    });

    it("namespace 宣言を抽出", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
namespace App\\Services;

class MyService {}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(2);
      expect(result.symbols[0]).toMatchObject({
        name: "App\\Services",
        kind: "namespace",
      });
      expect(result.symbols[1]).toMatchObject({
        name: "MyService",
        kind: "class",
      });
    });

    it("トップレベル関数を抽出", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
/**
 * Function documentation
 */
function topLevelFunction($param) {
  return $param * 2;
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
    });

    it("クラス定数を抽出", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
class Config {
  const DEFAULT_VALUE = 42;
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(2);
      expect(result.symbols[1]).toMatchObject({
        name: "DEFAULT_VALUE",
        kind: "constant",
      });
    });

    it("空のファイルは空の結果を返す", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "empty.php",
        content: "",
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toEqual([]);
      expect(result.snippets).toEqual([]);
      expect(result.dependencies).toEqual([]);
    });
  });

  describe("analyze - PHP タイプ検出", () => {
    it("pure PHP ファイル (<?php で開始) を正しく解析", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
class PureClass {}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]?.name).toBe("PureClass");
    });

    it("HTML-mixed PHP ファイルを正しく解析", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "template.php",
        content: `<!DOCTYPE html>
<html>
<body>
<?php
class TemplateClass {}
?>
</body>
</html>`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]?.name).toBe("TemplateClass");
    });

    it("shebang 付き PHP ファイルを処理", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "script.php",
        content: `#!/usr/bin/env php
<?php
class ShebangClass {}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]?.name).toBe("ShebangClass");
    });
  });

  describe("analyze - スニペット生成", () => {
    it("シンボル境界に揃えたスニペットを生成", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
class MyClass {
  public function method1() {}
  public function method2() {}
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
    it("use 文をパッケージ依存として検出", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
use App\\Services\\UserService;
use Illuminate\\Support\\Collection;

class MyClass {}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(2);
      expect(result.dependencies[0]).toMatchObject({
        dstKind: "package",
        dst: "App\\Services\\UserService",
        rel: "import",
      });
      expect(result.dependencies[1]).toMatchObject({
        dstKind: "package",
        dst: "Illuminate\\Support\\Collection",
        rel: "import",
      });
    });

    it("グループ化された use 文を処理", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
use App\\Services\\{UserService, OrderService};

class MyClass {}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(2);
      const deps = result.dependencies.map((d) => d.dst);
      expect(deps).toContain("App\\Services\\UserService");
      expect(deps).toContain("App\\Services\\OrderService");
    });

    it("複数の use 文を処理", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
use App\\Models\\User;
use App\\Models\\Order;
use App\\Services\\PaymentService;`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.dependencies).toHaveLength(3);
    });
  });

  describe("analyze - シグネチャ", () => {
    it("シグネチャを200文字に切り詰め", async () => {
      const analyzer = new PHPAnalyzer();
      const longName = "a".repeat(250);
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
function ${longName}() {}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      const signature = result.symbols[0]?.signature;
      expect(signature).toBeTruthy();
      expect(signature!.length).toBeLessThanOrEqual(200);
    });

    it("シグネチャから関数本体を除外", async () => {
      const analyzer = new PHPAnalyzer();
      const context: AnalysisContext = {
        pathInRepo: "test.php",
        content: `<?php
function myFunction() {
  $x = 42;
  return $x;
}`,
        fileSet: new Set(),
      };

      const result = await analyzer.analyze(context);

      expect(result.symbols).toHaveLength(1);
      const signature = result.symbols[0]?.signature;
      expect(signature).not.toContain("$x = 42");
      expect(signature).not.toContain("return $x");
    });
  });

  describe("createPHPAnalyzer", () => {
    it("ファクトリ関数で PHPAnalyzer を生成", () => {
      const analyzer = createPHPAnalyzer();

      expect(analyzer).toBeInstanceOf(PHPAnalyzer);
      expect(analyzer.language).toBe("PHP");
    });
  });
});
