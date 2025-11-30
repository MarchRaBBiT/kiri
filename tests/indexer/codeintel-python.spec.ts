import { describe, expect, it } from "vitest";

import { analyzeSource } from "../../src/indexer/codeintel.js";

describe("analyzeSource with Python language", () => {
  it("extracts class, methods, async functions, and docstrings", async () => {
    const code = `"""module doc"""

class Foo:
    """Class doc"""
    def __init__(self):
        \"\"\"Init doc\"\"\"
        pass

    async def run(self):
        return True

def helper():
    '''Helper doc'''
    return 1
`;

    const result = await analyzeSource(
      "pkg/sub/file.py",
      "Python",
      code,
      new Set(["pkg/sub/file.py"])
    );
    const namesAndKinds = result.symbols.map((s) => ({ name: s.name, kind: s.kind }));

    expect(namesAndKinds).toEqual(
      expect.arrayContaining([
        { name: "Foo", kind: "class" },
        { name: "__init__", kind: "method" },
        { name: "run", kind: "method" },
        { name: "helper", kind: "function" },
      ])
    );

    const classDoc = result.symbols.find((s) => s.name === "Foo");
    const helperDoc = result.symbols.find((s) => s.name === "helper");
    expect(classDoc?.doc).toBe("Class doc");
    expect(helperDoc?.doc).toBe("Helper doc");
  });

  it("collects dependencies from import statements", async () => {
    const code = `
import os
import pkg.module as mod
from . import utils
from ..core import base, extra as ex
from pkg.sub import thing
from pkg import submodule, util
`;

    const fileSet = new Set<string>([
      "pkg/sub/file.py",
      "pkg/sub/utils.py",
      "pkg/sub/__init__.py",
      "pkg/core.py",
      "pkg/module.py",
      "pkg/submodule.py",
      "pkg/util.py",
    ]);

    const result = await analyzeSource("pkg/sub/file.py", "Python", code, fileSet);

    expect(result.dependencies).toEqual(
      expect.arrayContaining([
        { dstKind: "package", dst: "os", rel: "import" },
        { dstKind: "path", dst: "pkg/module.py", rel: "import" },
        { dstKind: "path", dst: "pkg/sub/utils.py", rel: "import" },
        { dstKind: "path", dst: "pkg/core.py", rel: "import" },
        { dstKind: "path", dst: "pkg/sub/__init__.py", rel: "import" },
        { dstKind: "path", dst: "pkg/submodule.py", rel: "import" },
        { dstKind: "path", dst: "pkg/util.py", rel: "import" },
      ])
    );
  });

  it("returns empty result for empty files", async () => {
    const result = await analyzeSource("file.py", "Python", "", new Set(["file.py"]));
    expect(result).toEqual({ symbols: [], snippets: [], dependencies: [] });
  });
});
