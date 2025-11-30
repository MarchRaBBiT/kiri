import { describe, expect, it } from "vitest";

import { analyzeSource } from "../../src/indexer/codeintel.js";

describe("analyzeSource with Rust language", () => {
  it("extracts symbols and doc comments", async () => {
    const rustCode = `/// Struct doc
pub struct Foo {
    value: i32,
}

impl Foo {
    /// Adds one
    pub fn add_one(&self) {}
}

pub trait Greeter {
    fn greet(&self);
}

fn helper() {}
`;

    const result = await analyzeSource("src/lib.rs", "Rust", rustCode, new Set(["src/lib.rs"]));

    const namesAndKinds = result.symbols.map((s) => ({ name: s.name, kind: s.kind }));
    expect(namesAndKinds).toEqual(
      expect.arrayContaining([
        { name: "Foo", kind: "struct" },
        { name: "impl Foo", kind: "impl" },
        { name: "add_one", kind: "method" },
        { name: "Greeter", kind: "trait" },
        { name: "greet", kind: "method" },
        { name: "helper", kind: "function" },
      ])
    );

    const structDoc = result.symbols.find((s) => s.name === "Foo");
    expect(structDoc?.doc).toBe("Struct doc");

    expect(result.snippets).toHaveLength(result.symbols.length);
  });

  it("collects dependencies from use and mod statements", async () => {
    const rustCode = `
mod utils;

use crate::foo::{bar, nested::deep};
use std::collections::HashMap;
use crate::glob::*;
extern crate regex;
use crate::foo::Bar;
`;

    const fileSet = new Set<string>([
      "src/lib.rs",
      "src/utils.rs",
      "src/foo/bar.rs",
      "src/foo/mod.rs",
      "src/foo/nested/deep.rs",
      "src/glob/mod.rs",
      "src/foo.rs",
    ]);

    const result = await analyzeSource("src/lib.rs", "Rust", rustCode, fileSet);

    expect(result.dependencies).toEqual(
      expect.arrayContaining([
        { dstKind: "path", dst: "src/utils.rs", rel: "mod" },
        { dstKind: "path", dst: "src/foo/bar.rs", rel: "import" },
        { dstKind: "path", dst: "src/foo/nested/deep.rs", rel: "import" },
        { dstKind: "path", dst: "src/foo.rs", rel: "import" },
        { dstKind: "package", dst: "std", rel: "import" },
        { dstKind: "package", dst: "regex", rel: "extern_crate" },
        { dstKind: "path", dst: "src/glob/mod.rs", rel: "import" },
      ])
    );
  });

  it("returns empty result for empty files", async () => {
    const result = await analyzeSource("src/lib.rs", "Rust", "", new Set(["src/lib.rs"]));
    expect(result).toEqual({ symbols: [], snippets: [], dependencies: [] });
  });
});
