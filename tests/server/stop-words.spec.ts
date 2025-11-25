/**
 * Stop Words Service Tests
 *
 * @see Issue #48: Improve context_bundle stop word coverage and configurability
 */

import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

import {
  clearStopWordsCache,
  getLegacyStopWords,
  loadStopWords,
  StopWordsService,
} from "../../src/server/stop-words.js";

const cleanups: Array<() => Promise<void>> = [];

beforeEach(() => {
  // テスト前にキャッシュをクリア
  clearStopWordsCache();
});

afterEach(async () => {
  // テスト後にキャッシュをクリア
  clearStopWordsCache();
  for (const cleanup of cleanups.splice(0, cleanups.length)) {
    await cleanup();
  }
});

describe("StopWordsService.normalizeToken", () => {
  it("converts to lowercase", () => {
    expect(StopWordsService.normalizeToken("The")).toBe("the");
    expect(StopWordsService.normalizeToken("HELLO")).toBe("hello");
  });

  it("applies NFKC normalization (full-width to half-width)", () => {
    // 全角英数字→半角
    expect(StopWordsService.normalizeToken("ＡＢＣＤ")).toBe("abcd");
    expect(StopWordsService.normalizeToken("１２３")).toBe("123");
  });

  it("converts katakana to hiragana", () => {
    expect(StopWordsService.normalizeToken("コト")).toBe("こと");
    expect(StopWordsService.normalizeToken("ハ")).toBe("は");
    expect(StopWordsService.normalizeToken("データ")).toBe("でーた");
  });

  it("trims whitespace", () => {
    expect(StopWordsService.normalizeToken("  hello  ")).toBe("hello");
  });

  it("handles mixed content", () => {
    expect(StopWordsService.normalizeToken("　コレ　")).toBe("これ");
  });

  // 追加テストケース: エッジケース対応

  it("handles null/undefined/empty input gracefully", () => {
    // 空文字
    expect(StopWordsService.normalizeToken("")).toBe("");
    // null/undefinedは型的にはstringだが、実行時に渡される可能性に備える
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    expect(StopWordsService.normalizeToken(null as any)).toBe("");
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    expect(StopWordsService.normalizeToken(undefined as any)).toBe("");
  });

  it("preserves long vowel mark (ー) without conversion", () => {
    // 長音記号ー(U+30FC)はひらがな/カタカナ共用のため変換しない
    expect(StopWordsService.normalizeToken("サーバー")).toBe("さーばー");
    expect(StopWordsService.normalizeToken("データベース")).toBe("でーたべーす");
    expect(StopWordsService.normalizeToken("ユーザー")).toBe("ゆーざー");
    // 長音記号単体
    expect(StopWordsService.normalizeToken("ー")).toBe("ー");
  });

  it("handles extended katakana (ヴ, ヵ, ヶ)", () => {
    // ヴ(U+30F4) → ゔ(U+3094)
    expect(StopWordsService.normalizeToken("ヴァイオリン")).toBe("ゔぁいおりん");
    // ヵ(U+30F5) → ゕ(U+3095)
    expect(StopWordsService.normalizeToken("ヵ")).toBe("ゕ");
    // ヶ(U+30F6) → ゖ(U+3096)
    expect(StopWordsService.normalizeToken("ヶ")).toBe("ゖ");
  });

  it("does not convert katakana outside the conversion range (ヷ-ヺ)", () => {
    // U+30F7-U+30FA は対応ひらがなが未割当のため変換しない
    // これらの文字は実際にはほとんど使われないが、正しく処理されることを確認
    expect(StopWordsService.normalizeToken("ヷ")).toBe("ヷ"); // U+30F7
    expect(StopWordsService.normalizeToken("ヺ")).toBe("ヺ"); // U+30FA
  });
});

describe("StopWordsService", () => {
  it("uses legacy stop words when config is null", () => {
    // console.info をモック
    const infoSpy = vi.spyOn(console, "info").mockImplementation(() => {});

    const service = new StopWordsService(null);

    expect(service.legacy).toBe(true);
    expect(service.size).toBe(31); // レガシーストップワード数
    expect(service.has("the")).toBe(true);
    expect(service.has("and")).toBe(true);
    expect(service.has("fix")).toBe(true);
    expect(service.has("unknown")).toBe(false);

    // レガシーモード警告が出力されることを確認
    expect(infoSpy).toHaveBeenCalledWith(expect.stringContaining("legacy stop words"));

    infoSpy.mockRestore();
  });

  it("loads words from config with default language", () => {
    const config = {
      version: "1.0",
      default_language: "en" as const,
      languages: {
        en: { words: ["apple", "banana"] },
        ja: { words: ["りんご", "バナナ"] },
      },
      code_generic: ["null", "undefined"],
      custom: ["custom1"],
    };

    const service = new StopWordsService(config);

    expect(service.legacy).toBe(false);
    // en + code_generic + custom
    expect(service.has("apple")).toBe(true);
    expect(service.has("banana")).toBe(true);
    expect(service.has("null")).toBe(true);
    expect(service.has("undefined")).toBe(true);
    expect(service.has("custom1")).toBe(true);
    // ja words are not included when default is en
    expect(service.has("りんご")).toBe(false);
  });

  it("loads words for specified language", () => {
    const config = {
      version: "1.0",
      default_language: "en" as const,
      languages: {
        en: { words: ["apple"] },
        ja: { words: ["りんご", "バナナ"] },
      },
      code_generic: ["null"],
      custom: [],
    };

    const service = new StopWordsService(config, "ja");

    expect(service.has("りんご")).toBe(true);
    // カタカナはひらがなに正規化される
    expect(service.has("バナナ")).toBe(true);
    expect(service.has("ばなな")).toBe(true);
    expect(service.has("null")).toBe(true);
    // en words are not included
    expect(service.has("apple")).toBe(false);
  });

  it("normalizes words when checking has()", () => {
    const config = {
      version: "1.0",
      default_language: "en" as const,
      languages: {
        en: { words: ["hello"] },
      },
      code_generic: [],
      custom: [],
    };

    const service = new StopWordsService(config);

    // 大文字小文字を正規化
    expect(service.has("HELLO")).toBe(true);
    expect(service.has("Hello")).toBe(true);
    expect(service.has("hello")).toBe(true);
  });

  it("getWeight returns 0 for stop words, 1 for others", () => {
    const config = {
      version: "1.0",
      default_language: "en" as const,
      languages: {
        en: { words: ["the"] },
      },
      code_generic: [],
      custom: [],
    };

    const service = new StopWordsService(config);

    expect(service.getWeight("the")).toBe(0);
    expect(service.getWeight("programming")).toBe(1);
  });
});

describe("loadStopWords", () => {
  it("loads from YAML config file", async () => {
    const dir = await mkdtemp(join(tmpdir(), "stop-words-"));
    cleanups.push(async () => rm(dir, { recursive: true, force: true }));

    const configPath = join(dir, "stop-words.yml");
    await writeFile(
      configPath,
      `version: "1.0"
default_language: "en"
languages:
  en:
    words:
      - custom
      - test
code_generic:
  - "null"
custom: []
`
    );

    const service = loadStopWords({ configPath });

    expect(service.legacy).toBe(false);
    expect(service.has("custom")).toBe(true);
    expect(service.has("test")).toBe(true);
    expect(service.has("null")).toBe(true);
  });

  it("returns legacy service when no config file exists", async () => {
    const dir = await mkdtemp(join(tmpdir(), "stop-words-empty-"));
    cleanups.push(async () => rm(dir, { recursive: true, force: true }));

    // console.info をモック
    const infoSpy = vi.spyOn(console, "info").mockImplementation(() => {});

    const service = loadStopWords({ cwd: dir });

    expect(service.legacy).toBe(true);
    expect(service.size).toBe(31); // レガシーストップワード数

    infoSpy.mockRestore();
  });

  it("caches the service and returns same instance", async () => {
    const dir = await mkdtemp(join(tmpdir(), "stop-words-cache-"));
    cleanups.push(async () => rm(dir, { recursive: true, force: true }));

    const configPath = join(dir, "stop-words.yml");
    await writeFile(
      configPath,
      `version: "1.0"
default_language: "en"
languages:
  en:
    words:
      - cached
code_generic: []
custom: []
`
    );

    const service1 = loadStopWords({ configPath });
    const service2 = loadStopWords({ configPath });

    expect(service1).toBe(service2);
  });

  it("reloads when forceReload is true", async () => {
    const dir = await mkdtemp(join(tmpdir(), "stop-words-reload-"));
    cleanups.push(async () => rm(dir, { recursive: true, force: true }));

    const configPath = join(dir, "stop-words.yml");
    await writeFile(
      configPath,
      `version: "1.0"
default_language: "en"
languages:
  en:
    words:
      - original
code_generic: []
custom: []
`
    );

    const service1 = loadStopWords({ configPath });
    expect(service1.has("original")).toBe(true);

    // ファイルを更新
    await writeFile(
      configPath,
      `version: "1.0"
default_language: "en"
languages:
  en:
    words:
      - updated
code_generic: []
custom: []
`
    );

    // 強制リロード
    const service2 = loadStopWords({ configPath, forceReload: true });
    expect(service2).not.toBe(service1);
    expect(service2.has("updated")).toBe(true);
  });

  it("throws on invalid YAML config", async () => {
    const dir = await mkdtemp(join(tmpdir(), "stop-words-invalid-"));
    cleanups.push(async () => rm(dir, { recursive: true, force: true }));

    const configPath = join(dir, "stop-words.yml");
    await writeFile(
      configPath,
      `version: "1.0"
default_language: "invalid_lang"
languages: {}
code_generic: []
custom: []
`
    );

    expect(() => loadStopWords({ configPath })).toThrow(/Invalid stop words config/);
  });

  it("finds config in standard locations", async () => {
    const dir = await mkdtemp(join(tmpdir(), "stop-words-location-"));
    cleanups.push(async () => rm(dir, { recursive: true, force: true }));

    // config/stop-words.yml に配置
    const configDir = join(dir, "config");
    await writeFile(join(configDir, ".gitkeep"), "", { flag: "w" }).catch(() => {});
    const { mkdir } = await import("node:fs/promises");
    await mkdir(configDir, { recursive: true });
    await writeFile(
      join(configDir, "stop-words.yml"),
      `version: "1.0"
default_language: "en"
languages:
  en:
    words:
      - found
code_generic: []
custom: []
`
    );

    const service = loadStopWords({ cwd: dir });

    expect(service.legacy).toBe(false);
    expect(service.has("found")).toBe(true);
  });
});

describe("getLegacyStopWords", () => {
  it("returns the legacy stop words list", () => {
    const legacy = getLegacyStopWords();

    expect(legacy).toContain("the");
    expect(legacy).toContain("and");
    expect(legacy).toContain("fix");
    expect(legacy).toContain("test");
    expect(legacy).toContain("bug");
    expect(legacy).toContain("goal");
    expect(legacy.length).toBe(31);
  });
});

describe("Japanese stop words", () => {
  it("handles common Japanese particles and auxiliaries", async () => {
    const dir = await mkdtemp(join(tmpdir(), "stop-words-ja-"));
    cleanups.push(async () => rm(dir, { recursive: true, force: true }));

    const configPath = join(dir, "stop-words.yml");
    await writeFile(
      configPath,
      `version: "1.0"
default_language: "ja"
languages:
  ja:
    words:
      - は
      - が
      - を
      - に
      - の
      - こと
      - コト
code_generic: []
custom: []
`
    );

    const service = loadStopWords({ configPath });

    // ひらがな
    expect(service.has("は")).toBe(true);
    expect(service.has("が")).toBe(true);
    expect(service.has("こと")).toBe(true);

    // カタカナはひらがなに正規化される
    expect(service.has("コト")).toBe(true);

    // 含まれない語
    expect(service.has("データベース")).toBe(false);
  });
});
