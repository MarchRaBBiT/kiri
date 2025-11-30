# Rust Analyzer Implementation Plan

## Goals

- Provide AST-level symbol/snippet extraction for `.rs` files so Rust code benefits from the same MCP search precision as TypeScript/Swift (`docs/overview.md`, `README.md:801-821`).
- Avoid schema changes: reuse the current `symbols/snippets/dependencies` tables populated via `buildCodeIntel` (`src/indexer/cli.ts:1191-1280`).

## Constraints & Dependencies

- Runtime: Node.js 20, pnpm (repo standard).
- Parser stack: `tree-sitter` is already locked at `^0.22.0`; add `tree-sitter-rust` at a compatible version in `package.json`/`pnpm-lock.yaml`.
- Language routing: `detectLanguage` already maps `.rs → Rust` (`src/indexer/language.ts:1-33`), so only analyzer registration is missing.

## Work Plan

1. **Dependency wiring**
   - Add `tree-sitter-rust` dependency and run `pnpm install`.
   - Document the new parser in `README.md` “Supported Languages”.
2. **Analyzer scaffolding**
   - Create `src/indexer/codeintel/rust/analyzer.ts` and `index.ts`, mirroring the Java/Swift modules for consistency.
   - Export `RustAnalyzer`/`createRustAnalyzer`.
3. **Symbol extraction**
   - Instantiate a shared `Parser` configured with `tree-sitter-rust`.
   - Traverse the tree collecting `struct`, `enum`, `trait`, `impl`, `fn`, `mod`, `const`, `static`, `type`, macro definitions, etc.
   - Use helpers from `src/indexer/codeintel/utils.ts` (`sanitizeTreeSitterSignature`, `assignSymbolIds`, `symbolsToSnippets`, `cleanDocComment`).
   - Support both `///` and `/** */` doc comments by scanning preceding siblings (see Swift analyzer for reference).
4. **Dependency recording**
   - Reuse `createDependencyRecorder()` to capture:
     - `use`/`extern crate` paths (package vs. repo-relative resolution via `context.fileSet`).
     - `mod foo;` statements that map to sibling files (`foo.rs`, `foo/mod.rs`).
   - Normalize `crate::/self::/super::` prefixes before resolution; skip unresolved references.
5. **Registry integration**
   - Import and register `createRustAnalyzer()` in `src/indexer/codeintel.ts`.
   - Re-export from `src/indexer/codeintel/index.ts` if other modules need it.
6. **Testing**
   - Add `tests/indexer/codeintel-rust.spec.ts`, patterned after existing analyzer suites, covering:
     - Symbol extraction for each construct, doc comments, impl blocks, nested modules.
     - Dependency detection, fallback behavior on syntax errors/empty files.
   - Run `pnpm run test --filter codeintel-rust` plus `pnpm run lint`.
7. **Documentation & changelog**
   - Update `README.md` Supported Languages table.
   - Add a CHANGELOG entry describing Rust analyzer addition and any flags/env vars needed.
8. **Validation steps**
   - Rebuild the index locally (`pnpm run build` ➝ `pnpm exec tsx src/indexer/cli.ts --repo . --full`) and inspect Rust-heavy repos to ensure symbols populate DUCKDB.
   - Share the executed `pnpm run check` output in the eventual PR per repository guidelines.

## Open Questions / Follow-ups

- Need to confirm whether macro_rules! definitions should become snippets or remain full-file; decide based on observed search usefulness.
- Evaluate if we should gate the analyzer behind a feature flag initially to derisk performance regressions.
