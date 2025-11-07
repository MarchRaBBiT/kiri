import { describe, expect, it } from "vitest";

import { analyzeSource } from "../../src/indexer/codeintel.js";

describe("Python code intelligence", () => {
  describe("symbol extraction", () => {
    it("extracts classes, methods, and functions with docstrings", () => {
      const pythonCode = `
class MyClass:
    \"\"\"Class doc\"\"\"

    def __init__(self, value):
        \"\"\"Init doc\"\"\"
        self.value = value

    async def compute(self, x: int) -> int:
        \"\"\"Compute doc\"\"\"
        return x + 1


def helper():
    \"\"\"Helper doc\"\"\"
    pass
`.trim();

      const result = analyzeSource("test.py", "Python", pythonCode, new Set());

      expect(result.symbols).toHaveLength(4);

      expect(result.symbols[0]).toMatchObject({
        symbolId: 1,
        name: "MyClass",
        kind: "class",
        rangeStartLine: 1,
        doc: "Class doc",
      });
      expect(result.symbols[0]?.signature).toContain("class MyClass");

      expect(result.symbols[1]).toMatchObject({
        symbolId: 2,
        name: "__init__",
        kind: "method",
        doc: "Init doc",
      });
      expect(result.symbols[1]?.signature).toContain("def __init__");

      expect(result.symbols[2]).toMatchObject({
        symbolId: 3,
        name: "compute",
        kind: "method",
        doc: "Compute doc",
      });
      expect(result.symbols[2]?.signature).toContain("async def compute");

      expect(result.symbols[3]).toMatchObject({
        symbolId: 4,
        name: "helper",
        kind: "function",
        doc: "Helper doc",
      });
    });

    it("handles decorated functions and records import dependencies", () => {
      const pythonCode = `
from fastapi import APIRouter

router = APIRouter()

@router.get("/items/{item_id}")
def read_item(item_id: int):
    return {"item_id": item_id}
`.trim();

      const result = analyzeSource("router.py", "Python", pythonCode, new Set());

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]).toMatchObject({
        symbolId: 1,
        name: "read_item",
        kind: "function",
        doc: null,
      });

      const dependencyNames = result.dependencies.map((d) => d.dst);
      expect(dependencyNames).toContain("fastapi");
    });
  });

  describe("docstring and signature handling", () => {
    it("normalizes multiline docstrings and truncates long signatures", () => {
      const pythonCode = `
def complex_function(
    really_long_parameter_name_that_makes_signature_exceed_limit: str,
    another_parameter: int,
    flag: bool,
    callback=lambda x: x,
):
    \"\"\"
    Summary line.

    Details with indentation.
    \"\"\"
    return callback(really_long_parameter_name_that_makes_signature_exceed_limit)
`.trim();

      const result = analyzeSource("complex.py", "Python", pythonCode, new Set());

      expect(result.symbols).toHaveLength(1);
      const symbol = result.symbols[0];
      expect(symbol?.kind).toBe("function");
      expect(symbol?.doc).toBe("Summary line.\n\nDetails with indentation.");
      expect(symbol?.signature).toBeTruthy();
      if (symbol?.signature) {
        expect(symbol.signature.length).toBeLessThanOrEqual(200);
        expect(symbol.signature).toContain("def complex_function");
        expect(symbol.signature).not.toContain("return callback");
      }
    });
  });
});
