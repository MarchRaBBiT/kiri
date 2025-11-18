import { describe, it, expect } from "vitest";

import {
  selectProfileFromQuery,
  explainProfileSelection,
  getAvailableProfiles,
} from "../../src/server/profile-selector.js";

describe("selectProfileFromQuery", () => {
  it("should select testfail profile for test-related queries", () => {
    expect(selectProfileFromQuery("test failed in LoginTest")).toBe("testfail");
    expect(selectProfileFromQuery("unit test is broken")).toBe("testfail");
    expect(selectProfileFromQuery("failing test case needs fix")).toBe("testfail");
  });

  it("should select typeerror profile for type error queries", () => {
    expect(selectProfileFromQuery("type error in UserService")).toBe("typeerror");
    expect(selectProfileFromQuery("typescript error: cannot assign")).toBe("typeerror");
    expect(selectProfileFromQuery("property does not exist on type")).toBe("typeerror");
  });

  it("should select bugfix profile for bug-related queries", () => {
    expect(selectProfileFromQuery("fix bug in authentication")).toBe("bugfix");
    expect(selectProfileFromQuery("resolve crash issue")).toBe("bugfix");
    expect(selectProfileFromQuery("app is broken after update")).toBe("bugfix");
  });

  it("should select debug profile for debugging queries", () => {
    expect(selectProfileFromQuery("debug login flow")).toBe("debug");
    expect(selectProfileFromQuery("add console log for tracing")).toBe("debug");
    expect(selectProfileFromQuery("troubleshoot performance issue")).toBe("debug");
  });

  it("should select api profile for API-related queries", () => {
    expect(selectProfileFromQuery("add new API endpoint")).toBe("api");
    expect(selectProfileFromQuery("REST API route handler")).toBe("api");
    expect(selectProfileFromQuery("GraphQL resolver implementation")).toBe("api");
  });

  it("should select editor profile for UI/editor queries", () => {
    expect(selectProfileFromQuery("fix editor component rendering")).toBe("editor");
    expect(selectProfileFromQuery("UI layout issue")).toBe("editor");
    expect(selectProfileFromQuery("component style adjustment")).toBe("editor");
  });

  it("should select feature profile for feature development", () => {
    expect(selectProfileFromQuery("add new feature for users")).toBe("feature");
    expect(selectProfileFromQuery("implement dark mode")).toBe("feature");
    expect(selectProfileFromQuery("create new dashboard")).toBe("feature");
  });

  it("should prioritize higher-weight patterns", () => {
    // "test failed" has higher weight than "error"
    expect(selectProfileFromQuery("test failed with error")).toBe("testfail");

    // "type error" has higher weight than "error"
    expect(selectProfileFromQuery("type error in component")).toBe("typeerror");
  });

  it("should return default profile for unrecognized queries", () => {
    expect(selectProfileFromQuery("some random query")).toBe("default");
    expect(selectProfileFromQuery("")).toBe("default");
  });

  it("should accept custom fallback profile", () => {
    expect(selectProfileFromQuery("random query", "balanced")).toBe("balanced");
  });

  it("should be case-insensitive", () => {
    expect(selectProfileFromQuery("TEST FAILED")).toBe("testfail");
    expect(selectProfileFromQuery("Type Error")).toBe("typeerror");
    expect(selectProfileFromQuery("FIX BUG")).toBe("bugfix");
  });

  it("should handle multi-keyword matches", () => {
    // Multiple keywords from same pattern should increase score
    expect(selectProfileFromQuery("test case failed in test suite")).toBe("testfail");
  });
});

describe("explainProfileSelection", () => {
  it("should explain testfail selection", () => {
    const explanation = explainProfileSelection("test failed", "testfail");
    expect(explanation).toContain("testfail");
    expect(explanation).toContain("test fail");
  });

  it("should explain typeerror selection", () => {
    const explanation = explainProfileSelection("type error in code", "typeerror");
    expect(explanation).toContain("typeerror");
    expect(explanation).toContain("type error");
  });

  it("should explain fallback selection", () => {
    const explanation = explainProfileSelection("random query", "default");
    expect(explanation).toContain("fallback");
    expect(explanation).toContain("default");
  });

  it("should list all matched keywords", () => {
    const explanation = explainProfileSelection("test failed in test suite", "testfail");
    expect(explanation).toContain("test fail");
    expect(explanation).toContain("test suite");
  });
});

describe("getAvailableProfiles", () => {
  it("should return all available profiles", () => {
    const profiles = getAvailableProfiles();
    expect(profiles.length).toBeGreaterThan(0);

    const profileNames = profiles.map((p) => p.profile);
    expect(profileNames).toContain("testfail");
    expect(profileNames).toContain("typeerror");
    expect(profileNames).toContain("bugfix");
    expect(profileNames).toContain("debug");
    expect(profileNames).toContain("api");
    expect(profileNames).toContain("editor");
    expect(profileNames).toContain("feature");
  });

  it("should include keywords for each profile", () => {
    const profiles = getAvailableProfiles();
    const testfailProfile = profiles.find((p) => p.profile === "testfail");

    expect(testfailProfile).toBeDefined();
    expect(testfailProfile?.keywords.length).toBeGreaterThan(0);
    expect(testfailProfile?.keywords).toContain("test fail");
  });
});

describe("Japanese keyword support", () => {
  it("should select testfail profile for Japanese test queries", () => {
    expect(selectProfileFromQuery("テストが失敗しています")).toBe("testfail");
    expect(selectProfileFromQuery("ユニットテストが壊れている")).toBe("testfail");
    expect(selectProfileFromQuery("テストスイートのエラー")).toBe("testfail");
    expect(selectProfileFromQuery("テストケースがタイムアウト")).toBe("testfail");
  });

  it("should select typeerror profile for Japanese type error queries", () => {
    expect(selectProfileFromQuery("型エラーが発生しています")).toBe("typeerror");
    expect(selectProfileFromQuery("TypeScript エラー: 型の不一致")).toBe("typeerror");
    expect(selectProfileFromQuery("返り値の型が一致しません")).toBe("typeerror");
    expect(selectProfileFromQuery("プロパティが存在しません")).toBe("typeerror");
  });

  it("should select bugfix profile for Japanese bug queries", () => {
    expect(selectProfileFromQuery("バグ修正が必要です")).toBe("bugfix");
    expect(selectProfileFromQuery("不具合を直してください")).toBe("bugfix");
    expect(selectProfileFromQuery("クラッシュが発生します")).toBe("bugfix");
    expect(selectProfileFromQuery("リグレッションバグ")).toBe("bugfix");
  });

  it("should select debug profile for Japanese debug queries", () => {
    expect(selectProfileFromQuery("デバッグしたい")).toBe("debug");
    expect(selectProfileFromQuery("ログ出力を追加")).toBe("debug");
    expect(selectProfileFromQuery("トラブルシューティング")).toBe("debug");
    expect(selectProfileFromQuery("診断情報が必要")).toBe("debug");
  });

  it("should select api profile for Japanese API queries", () => {
    expect(selectProfileFromQuery("APIエンドポイントの実装")).toBe("api");
    expect(selectProfileFromQuery("リクエストハンドラ")).toBe("api");
    expect(selectProfileFromQuery("レスポンス形式の変更")).toBe("api");
  });

  it("should select editor profile for Japanese UI queries", () => {
    expect(selectProfileFromQuery("コンポーネントの表示")).toBe("editor");
    expect(selectProfileFromQuery("レンダリングの問題")).toBe("editor");
    expect(selectProfileFromQuery("レイアウトの調整")).toBe("editor");
    expect(selectProfileFromQuery("UIスタイルの修正")).toBe("editor");
  });

  it("should select feature profile for Japanese feature queries", () => {
    expect(selectProfileFromQuery("新機能の実装")).toBe("feature");
    expect(selectProfileFromQuery("機能追加が必要")).toBe("feature");
    expect(selectProfileFromQuery("新しい機能を開発")).toBe("feature");
  });

  it("should select debug profile for Japanese performance queries", () => {
    expect(selectProfileFromQuery("パフォーマンスが遅い")).toBe("debug");
    expect(selectProfileFromQuery("ボトルネックの調査")).toBe("debug");
    expect(selectProfileFromQuery("最適化が必要")).toBe("debug");
  });

  it("should handle mixed Japanese and English queries", () => {
    expect(selectProfileFromQuery("テスト test failed")).toBe("testfail");
    expect(selectProfileFromQuery("型エラー type error")).toBe("typeerror");
    expect(selectProfileFromQuery("バグ bug fix")).toBe("bugfix");
  });

  it("should explain Japanese keyword matches", () => {
    const query = "テストが失敗しています";
    const selected = selectProfileFromQuery(query);
    const explanation = explainProfileSelection(query, selected);

    expect(selected).toBe("testfail");
    expect(explanation).toContain("testfail");
    // Check for keywords separately (they are stored individually)
    expect(explanation).toContain("テスト");
  });
});
