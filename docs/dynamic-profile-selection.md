# 動的プロファイル選択機能

**導入日**: 2025-11-17  
**バージョン**: 0.11.0+  
**関連Issue**: [#77](https://github.com/CAPHTECH/kiri/issues/77)

---

## 概要

クエリの内容に応じて最適なブーストプロファイルを**自動選択**する機能です。

ユーザーが明示的にプロファイルを指定しなくても、クエリテキストのキーワードから適切なプロファイル（testfail, typeerror, bugfix, etc.）が選択されます。

---

## 使用方法

### MCP クライアント（Cursor, Claude Code, etc.）

#### 自動選択を有効化

```json
{
  "jsonrpc": "2.0",
  "method": "context_bundle",
  "params": {
    "goal": "test failed in LoginTest",
    "auto_select_profile": true
  }
}
```

→ 自動的に`testfail`プロファイルが選択されます

#### 明示的にプロファイルを指定（従来通り）

```json
{
  "jsonrpc": "2.0",
  "method": "context_bundle",
  "params": {
    "goal": "fix authentication bug",
    "boost_profile": "bugfix"
  }
}
```

→ 明示指定が優先されます（auto_select_profileは不要）

---

## プロファイル選択ルール

### キーワードベースマッチング

クエリテキストに含まれるキーワードに応じてプロファイルを選択します。

| プロファイル  | キーワード例                                                                        | 用途              |
| ------------- | ----------------------------------------------------------------------------------- | ----------------- |
| **testfail**  | test fail, test error, failing test, broken test, test suite                        | テスト失敗の調査  |
| **typeerror** | type error, typescript error, type mismatch, cannot assign, property does not exist | 型エラーの修正    |
| **bugfix**    | fix bug, bug fix, resolve issue, crash, error, broken, regression                   | バグ修正          |
| **debug**     | debug, debugger, console log, trace, inspect, troubleshoot                          | デバッグ作業      |
| **api**       | api, endpoint, rest, graphql, request, response, route, controller                  | API開発           |
| **editor**    | editor, ui, component, render, display, view, layout, style                         | エディター/UI作業 |
| **feature**   | add feature, new feature, implement, create, build, develop                         | 新機能開発        |

### 優先度

複数のキーワードがマッチした場合、**weightが高いパターン**が優先されます。

```typescript
// 例: "test failed with error"
// → testfail (weight=10) > bugfix (weight=8)
```

### フォールバック

キーワードが一致しない場合は`default`プロファイルを使用します。

---

## 実装例

### TypeScript (MCPクライアント)

```typescript
import { MCPClient } from "@modelcontextprotocol/client";

const client = new MCPClient(/* ... */);

// 自動選択を有効化
const result = await client.call("context_bundle", {
  goal: "type error in UserService",
  auto_select_profile: true, // 👈 これだけ！
});

// → typeerror プロファイルが自動選択される
```

### curl (テスト用)

```bash
curl -X POST http://localhost:8765 \
  -H "Content-Type: application/json" \
  -d '{
    "jsonrpc": "2.0",
    "method": "context_bundle",
    "params": {
      "goal": "test failed in authentication",
      "auto_select_profile": true
    },
    "id": 1
  }'
```

---

## テストケース

### 基本的な選択

```typescript
selectProfileFromQuery("test failed in LoginTest");
// → "testfail"

selectProfileFromQuery("type error in UserService");
// → "typeerror"

selectProfileFromQuery("fix bug in authentication");
// → "bugfix"

selectProfileFromQuery("debug login flow");
// → "debug"
```

### 複数キーワード

```typescript
selectProfileFromQuery("test case failed in test suite");
// → "testfail" (複数のキーワードがマッチしてスコアが高い)
```

### 優先度

```typescript
selectProfileFromQuery("test failed with error");
// → "testfail" (testfailの方がbugfixより優先度が高い)
```

### 大文字小文字

```typescript
selectProfileFromQuery("TEST FAILED");
// → "testfail" (大文字小文字を区別しない)
```

### フォールバック

```typescript
selectProfileFromQuery("some random query");
// → "default" (キーワードが一致しない)
```

---

## デバッグ

### 選択理由の説明

```typescript
import { explainProfileSelection } from "./src/server/profile-selector.js";

const query = "test failed in test suite";
const selected = selectProfileFromQuery(query);
const explanation = explainProfileSelection(query, selected);

console.log(explanation);
// → Selected "testfail" based on keywords: test fail, test suite
```

### 利用可能なプロファイル一覧

```typescript
import { getAvailableProfiles } from "./src/server/profile-selector.js";

const profiles = getAvailableProfiles();
console.log(profiles);
// → [
//     { profile: "testfail", keywords: ["test fail", ...] },
//     { profile: "typeerror", keywords: ["type error", ...] },
//     ...
//   ]
```

---

## パフォーマンス影響

- **オーバーヘッド**: 約0.1ms（キーワードマッチング）
- **メモリ**: 数KB（パターン定義）
- **影響**: 無視できるレベル

---

## 拡張方法

### 新しいパターンを追加

`src/server/profile-selector.ts`の`PROFILE_PATTERNS`配列に追加：

```typescript
const PROFILE_PATTERNS: ProfilePattern[] = [
  // 既存のパターン...

  // 新しいパターン
  {
    profile: "performance",
    keywords: ["slow", "performance", "optimization", "bottleneck", "latency"],
    weight: 8,
  },
];
```

### キーワードの調整

既存のパターンのキーワードを追加・削除：

```typescript
{
  profile: "testfail",
  keywords: [
    "test fail",
    "test error",
    // 新しいキーワードを追加
    "test timeout",
    "flaky test",
  ],
  weight: 10,
},
```

---

## 制限事項

1. **英語のみ対応**
   - 現在のキーワードは英語のみ
   - 日本語クエリには未対応

2. **単純なキーワードマッチング**
   - 自然言語理解（NLU）は未実装
   - 複雑な文脈理解は不可

3. **weightの手動調整**
   - 機械学習ベースの最適化は未実装
   - weightは手動でチューニング

---

## 今後の改善案

### 短期（実装容易）

1. **日本語対応**
   - 日本語キーワードの追加
   - "テスト失敗" → testfail

2. **カスタムパターン**
   - ユーザー定義パターンのサポート
   - config/profile-patterns.yml

### 中期（要設計）

3. **機械学習ベースの選択**
   - クエリとファイルの関連性を学習
   - データ駆動の最適化

4. **フィードバックループ**
   - ユーザーの選択を記録
   - パターンを自動改善

5. **文脈理解**
   - 単なるキーワードマッチングを超えた理解
   - 埋め込みベクトルの活用

---

## トラブルシューティング

### Q: 自動選択が効かない

**A**: `auto_select_profile: true`を指定していますか？

```json
{
  "goal": "test failed",
  "auto_select_profile": true // 👈 必須
}
```

### Q: 期待と異なるプロファイルが選択される

**A**: キーワードを確認してください。

```typescript
// デバッグ用
import { explainProfileSelection } from "./src/server/profile-selector.js";
const explanation = explainProfileSelection(query, selected);
console.log(explanation);
```

### Q: 明示指定と自動選択を併用できる？

**A**: 明示指定が優先されます。

```json
{
  "goal": "test failed",
  "boost_profile": "bugfix", // 👈 これが優先される
  "auto_select_profile": true // 無視される
}
```

---

## 関連ファイル

- **実装**: `src/server/profile-selector.ts`
- **統合**: `src/server/rpc.ts`
- **テスト**: `tests/server/profile-selector.spec.ts`
- **プロファイル定義**: `src/server/boost-profiles.ts`

---

## 参考資料

- Issue #77: ブーストプロファイルの系統的テスト
- 最終評価: `docs/eval-profile-optimization-final-2025-11-17.md`
- プロファイル比較: `docs/eval-profile-adjustment-comparison-2025-11-17.md`

---

## まとめ

動的プロファイル選択機能により、ユーザーは明示的にプロファイルを指定しなくても、クエリの内容に応じて最適なプロファイルが自動選択されます。

**使い方は簡単**:

```json
{
  "goal": "test failed in LoginTest",
  "auto_select_profile": true
}
```

これだけで、適切なプロファイル（この場合`testfail`）が選択され、より関連性の高い検索結果が得られます。
