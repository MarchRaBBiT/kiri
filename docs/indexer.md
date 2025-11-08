# 取り込みパイプライン（Indexer）

## ステップ概要

1. **ワークツリー列挙**: `git ls-files` を用いつつ ignore を尊重し、サブモジュールは別リポジトリとして扱う。
2. **メタデータ推定**: 拡張子から言語判定し、サイズ・mtime・バイナリ判定（ヌルバイト/閾値）を取得する。
3. **blob/tree 生成**: blob をハッシュで重複排除し、HEAD 時点の path→blob 対応を保持する。
4. **シンボル抽出**: TypeScript (TypeScript Compiler API)、Swift (tree-sitter)、PHP (tree-sitter) で定義・範囲・シグネチャを抽出する。
   - **TypeScript**: `class`, `interface`, `enum`, `function`, `method`
   - **Swift**: `class`, `struct`, `protocol`, `enum`, `extension`, `func`, `init`, `property`
   - **PHP**: `class`, `interface`, `trait`, `function`, `method`, `property`, `constant`, `namespace` (pure PHPおよびHTML混在PHPの両方をサポート)
5. **依存解決**: TypeScript プラグイン（`tsconfig` の paths/alias、`package.json` exports、`pnpm-workspace`）と Swift (`import` 文解析）を基準にし、他言語プラグインは後続拡張とする。
6. **snippet 切り出し**: 原則シンボル境界を用い、特定できない場合のみ 120–200 行のスライディングウィンドウを適用する。
7. **埋め込み生成（任意）**: snippet 単位で埋め込みを計算し `snippet_embedding` テーブルへ格納する。
8. **履歴・blame 更新**: 差分ファイルのみ更新し、フル再計算は週次などバッチで実施する。
9. **ステージング投入**: 小刻み書き込みを避け、ステージング→バッチマージでトランザクションをまとめる。

## 実行モード

- CLI: `kiri index --repo /path/to/repo --db /path/to/index.duckdb [--full | --since <commit>]`
- トリガ: pre-commit / post-merge hook / ファイル監視からの自動起動

## 疑似コード（TypeScript）

```ts
import { connect } from "duckdb";

export async function indexRepo(repoRoot: string, dbPath: string) {
  const db = await connect(dbPath);
  const files = await gitLsFiles(repoRoot);

  const stage: Array<[string, ...unknown[]]> = [];
  for (const filePath of files) {
    const meta = await statAndLang(filePath);
    if (meta.isBinary) continue;
    const content = await readText(filePath);
    const hash = hashContent(content);
    stage.push(["blob", hash, content.length, content.split(/\r?\n/).length, content]);
    stage.push(["file", filePath, hash, meta.ext, meta.lang, false, meta.mtime]);
  }

  await db.transaction(async (trx) => {
    await upsertBlobsAndFiles(trx, stage); // まとめて投入
    await extractSymbolsAndDeps(trx, repoRoot, files); // tree-sitter
    await cutSnippetsAndEmbeddings(trx, repoRoot); // 任意で VSS
  });
}
```

## 言語アナライザモジュール

| 言語       | モジュール                            | パーサ / サービス                    | 主なシンボル                                                             |
| ---------- | ------------------------------------- | ------------------------------------ | ------------------------------------------------------------------------ |
| TypeScript | `src/indexer/languages/typescript.ts` | TypeScript Compiler API              | class, interface, enum, function, method                                 |
| Swift      | `src/indexer/languages/swift.ts`      | tree-sitter-swift                    | class, struct, protocol, enum, extension, func, init, property           |
| PHP        | `src/indexer/languages/php.ts`        | tree-sitter-php（pure + html-mixed） | class, interface, trait, function, method, property, constant, namespace |
| Java       | `src/indexer/languages/java.ts`       | tree-sitter-java                     | class, interface, enum, annotation, method, constructor, field           |
| Dart       | `src/indexer/languages/dart.ts`       | Dart Analysis Server                 | class, mixin, enum, extension, function, method, getter, setter          |

補助ファイル:

- `src/indexer/languages/types.ts`: 共有 `SymbolRecord` / `SnippetRecord` / `DependencyRecord` / `AnalysisResult` と `buildSnippetsFromSymbols`、`buildFallbackSnippet` などのヘルパー。
- `src/indexer/languages/index.ts`: 各アナライザを `Map<string, LanguageAnalyzer>` に登録し、参照ヘルパーを公開。
- `src/indexer/codeintel.ts`: 適切なアナライザを選択するオーケストレータ（未対応言語は空結果を返す）。

### 新しい言語の追加手順

1. `src/indexer/languages/<lang>.ts` を作成して `LanguageAnalyzer` をエクスポートする。`buildSnippetsFromSymbols` を再利用し、並列実行安全のためパーサ状態はローカルに保つ。
2. `src/indexer/languages/index.ts` にアナライザを登録する。
3. 本ドキュメントと `README.md` を更新し、`tests/indexer/languages/` に対象テストを追加する。
4. `pnpm run test` と `pnpm run build` を通して CI が新アナライザを検証できる状態にする。
