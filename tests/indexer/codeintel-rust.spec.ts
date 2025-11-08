import { describe, expect, it } from "vitest";

import { analyzeSource } from "../../src/indexer/codeintel.js";

describe("Rust code intelligence", () => {
  describe("symbol extraction", () => {
    it("extracts structs, impl methods, and free functions with doc comments", () => {
      const rustCode = `
#[derive(Debug)]
/// Represents a 2D point.
pub struct Point {
    pub x: i32,
    pub y: i32,
}

impl Point {
    /// Creates a new point.
    pub fn new(x: i32, y: i32) -> Self {
        Self { x, y }
    }

    /// Moves the point by the given delta.
    pub fn translate(&mut self, dx: i32, dy: i32) {
        self.x += dx;
        self.y += dy;
    }
}

/// Doubles a value.
pub fn helper(value: i32) -> i32 {
    value * 2
}
`.trim();

      const result = analyzeSource("src/lib.rs", "Rust", rustCode, new Set());

      expect(result.symbols).toHaveLength(4);
      expect(result.symbols[0]).toMatchObject({
        symbolId: 1,
        name: "Point",
        kind: "struct",
        doc: "Represents a 2D point.",
      });
      expect(result.symbols[1]).toMatchObject({
        symbolId: 2,
        name: "new",
        kind: "method",
        doc: "Creates a new point.",
      });
      expect(result.symbols[2]).toMatchObject({
        symbolId: 3,
        name: "translate",
        kind: "method",
        doc: "Moves the point by the given delta.",
      });
      expect(result.symbols[3]).toMatchObject({
        symbolId: 4,
        name: "helper",
        kind: "function",
        doc: "Doubles a value.",
      });
    });

    it("extracts enums with variants", () => {
      const rustCode = `
pub enum Mode {
    /// API server mode
    Api,
    /// Web mode with port selection
    Web { port: u16 },
}
`.trim();

      const result = analyzeSource("src/mode.rs", "Rust", rustCode, new Set());

      expect(result.symbols).toHaveLength(3);
      expect(result.symbols[0]).toMatchObject({
        symbolId: 1,
        name: "Mode",
        kind: "enum",
      });
      expect(result.symbols[1]).toMatchObject({
        symbolId: 2,
        name: "Api",
        kind: "enum_variant",
        doc: "API server mode",
      });
      expect(result.symbols[2]).toMatchObject({
        symbolId: 3,
        name: "Web",
        kind: "enum_variant",
      });
    });

    it("extracts macro_rules macros with doc comments", () => {
      const rustCode = `
/// Logs a value and returns it.
macro_rules! log_and_return {
    ($value:expr) => {{
        println!("{}", $value);
        $value
    }};
}
`.trim();

      const result = analyzeSource("src/macros.rs", "Rust", rustCode, new Set());

      expect(result.symbols).toHaveLength(1);
      expect(result.symbols[0]).toMatchObject({
        symbolId: 1,
        name: "log_and_return",
        kind: "macro",
        doc: "Logs a value and returns it.",
      });
    });
  });

  describe("dependency extraction", () => {
    it("collects crate-level dependencies from use and extern statements", () => {
      const rustCode = `
use serde::{Serialize, Deserialize};
use std::collections::HashMap;
use crate::utils::math;
extern crate regex;

pub struct Dummy(HashMap<String, String>);
`.trim();

      const result = analyzeSource("src/main.rs", "Rust", rustCode, new Set());
      const dependencies = result.dependencies.map((dependency) => dependency.dst).sort();

      expect(dependencies).toEqual(["regex", "serde", "std"]);
    });
  });
});
