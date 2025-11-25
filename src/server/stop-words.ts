/**
 * Stop Words Service
 *
 * ストップワード（除外語）の設定と判定を提供するサービス。
 * 多言語対応（英語・日本語）、外部設定ファイルからの読み込み、
 * シングルトンキャッシュによるパフォーマンス最適化を実装。
 *
 * @see Issue #48: Improve context_bundle stop word coverage and configurability
 */

import fs from "node:fs";
import path from "node:path";

import { parse } from "yaml";
import { z } from "zod";

// ============================================================
// 定数
// ============================================================

/**
 * カタカナ→ひらがな変換オフセット
 *
 * Unicode上でカタカナ(U+30A1-U+30F6)とひらがな(U+3041-U+3096)は
 * 0x60(96)の差で対応している。例: ア(U+30A2) - 0x60 = あ(U+3042)
 *
 * @see https://www.unicode.org/charts/PDF/U3040.pdf (Hiragana)
 * @see https://en.wikipedia.org/wiki/Katakana_(Unicode_block)
 */
const KATAKANA_HIRAGANA_OFFSET = 0x60;

/**
 * カタカナ変換対象範囲の開始 (ァ)
 * U+30A1-U+30F6 は全て -0x60 でひらがなに変換可能
 */
const KATAKANA_START = 0x30a1;

/**
 * カタカナ変換対象範囲の終了 (ヶ)
 * この範囲にはヴ(U+30F4)、ヵ(U+30F5)、ヶ(U+30F6)も含まれる
 *
 * 注意: U+30F7-U+30FA (ヷ-ヺ) は対応ひらがなが未割当のため除外
 * 注意: U+30FC (ー) は長音記号でひらがな/カタカナ共用のため変換不要
 */
const KATAKANA_END = 0x30f6;

// ============================================================
// 型定義
// ============================================================

export interface StopWordsConfig {
  version: string;
  default_language: "en" | "ja";
  languages: Record<string, { words: string[] }>;
  code_generic: string[];
  custom: string[];
}

/**
 * Phase 2用IDFプロバイダーインターフェース
 * Phase 1では使用しないが、将来の拡張に備えて定義
 */
export interface IdfProvider {
  getIdf(word: string): number;
}

// ============================================================
// Zodスキーマ
// ============================================================

const LanguageWordsSchema = z.object({
  words: z.array(z.string().trim().min(1)),
});

const StopWordsConfigSchema = z.object({
  version: z.string().default("1.0"),
  default_language: z.enum(["en", "ja"]).default("en"),
  languages: z.record(z.string(), LanguageWordsSchema).default({}),
  code_generic: z.array(z.string().trim().min(1)).default([]),
  custom: z.array(z.string().trim().min(1)).default([]),
});

// ============================================================
// レガシーデフォルト（後方互換用）
// ============================================================

const LEGACY_STOP_WORDS = [
  "the",
  "and",
  "for",
  "with",
  "from",
  "this",
  "that",
  "have",
  "has",
  "will",
  "would",
  "into",
  "about",
  "there",
  "their",
  "your",
  "fix",
  "test",
  "tests",
  "issue",
  "error",
  "bug",
  "fail",
  "failing",
  "make",
  "when",
  "where",
  "should",
  "could",
  "need",
  "goal",
];

// ============================================================
// StopWordsService クラス
// ============================================================

/**
 * ストップワードサービス
 *
 * ストップワードの判定と重み付けを提供する。
 * 設定ファイルがない場合はレガシーモードで動作し、
 * 既存の31語のストップワードを使用する。
 */
export class StopWordsService {
  private readonly words: Set<string>;
  private readonly isLegacyMode: boolean;

  constructor(config: StopWordsConfig | null, language?: string) {
    if (!config) {
      // レガシーモード: 設定ファイルなし
      this.words = new Set(LEGACY_STOP_WORDS);
      this.isLegacyMode = true;
      console.info(
        `[KIRI] Using legacy stop words (${LEGACY_STOP_WORDS.length} words). ` +
          "Consider adding config/stop-words.yml for extended support."
      );
      return;
    }

    this.isLegacyMode = false;
    const lang = language ?? config.default_language;
    const langWords = config.languages[lang]?.words ?? [];

    // マージ優先順位: code_generic < language < custom
    // 全て同じSetに追加されるため、実質的に和集合
    const merged = new Set<string>();
    for (const word of config.code_generic) {
      merged.add(StopWordsService.normalizeToken(word));
    }
    for (const word of langWords) {
      merged.add(StopWordsService.normalizeToken(word));
    }
    for (const word of config.custom) {
      merged.add(StopWordsService.normalizeToken(word));
    }

    this.words = merged;
  }

  /**
   * ストップワード判定
   *
   * @param word - 判定対象の単語
   * @returns ストップワードならtrue
   */
  has(word: string): boolean {
    return this.words.has(StopWordsService.normalizeToken(word));
  }

  /**
   * IDF重み付け取得
   *
   * ストップワードの場合は0.0を返す。
   * IdfProviderが提供された場合は、IDFベースの重みを返す。
   * それ以外の場合は1.0（ニュートラル重み）を返す。
   *
   * Phase 2実装: IdfProviderを使用して高頻度語を自動的に減衰。
   *
   * @param word - 対象単語
   * @param idfProvider - IDFプロバイダー（オプション）
   * @returns 重み（0.0〜1.0）
   */
  getWeight(word: string, idfProvider?: IdfProvider): number {
    // ストップワードは常に0.0
    if (this.has(word)) {
      return 0.0;
    }

    // IdfProviderが提供されている場合はIDF重みを使用
    if (idfProvider) {
      return idfProvider.getIdf(word);
    }

    // フォールバック: ニュートラル重み
    return 1.0;
  }

  /**
   * トークン正規化
   * - 空文字・null/undefinedの防御処理
   * - NFKC正規化（全角→半角、濁点統合等）
   * - 小文字化
   * - カタカナ→ひらがな変換（日本語用）
   *
   * @param token - 正規化対象のトークン
   * @returns 正規化されたトークン（空入力時は空文字列）
   */
  static normalizeToken(token: string): string {
    // 防御的ガード: null/undefined/空文字の場合は早期リターン
    if (!token) {
      return "";
    }

    // NFKC正規化
    let normalized = token.normalize("NFKC");

    // 小文字化
    normalized = normalized.toLowerCase();

    // カタカナ→ひらがな変換
    // 範囲: U+30A1(ァ)〜U+30F6(ヶ)
    // 長音記号ー(U+30FC)は範囲外のため変換されず、ひらがな文中でもそのまま保持される
    // codePointAtを使用してサロゲートペア対応（カタカナはBMP内だが安全のため）
    normalized = normalized.replace(
      new RegExp(`[\\u${KATAKANA_START.toString(16)}-\\u${KATAKANA_END.toString(16)}]`, "g"),
      (char) => {
        const codePoint = char.codePointAt(0);
        if (codePoint === undefined) {
          return char;
        }
        return String.fromCodePoint(codePoint - KATAKANA_HIRAGANA_OFFSET);
      }
    );

    return normalized.trim();
  }

  /**
   * デバッグ用: 現在のストップワード数を取得
   */
  get size(): number {
    return this.words.size;
  }

  /**
   * レガシーモードかどうか
   */
  get legacy(): boolean {
    return this.isLegacyMode;
  }

  /**
   * 全ストップワードを取得（デバッグ・テスト用）
   */
  getWords(): string[] {
    return Array.from(this.words);
  }
}

// ============================================================
// シングルトンキャッシュ
// ============================================================

let cachedService: StopWordsService | null = null;
let cachedConfigPath: string | null = null;
let cachedConfigMtime: number | null = null;

function getConfigMtime(configPath: string): number | null {
  try {
    return fs.statSync(configPath).mtimeMs;
  } catch {
    return null;
  }
}

// ============================================================
// ローダー関数
// ============================================================

const CONFIG_CANDIDATES = [
  ".kiri/stop-words.yml",
  ".kiri/stop-words.yaml",
  "config/stop-words.yml",
  "config/stop-words.yaml",
];

export interface LoadStopWordsOptions {
  configPath?: string;
  cwd?: string;
  language?: string;
  forceReload?: boolean;
}

/**
 * ストップワードサービスをロード
 *
 * 設定ファイルを読み込み、StopWordsServiceを初期化する。
 * シングルトンキャッシュを使用し、同一設定ファイルの再読み込みを回避。
 *
 * @param options - ロードオプション
 * @returns StopWordsServiceインスタンス
 */
export function loadStopWords(options: LoadStopWordsOptions = {}): StopWordsService {
  const cwd = options.cwd ?? process.cwd();
  const forceReload = options.forceReload ?? false;

  // 設定ファイルパスの解決
  let resolvedPath: string | null = null;

  if (options.configPath) {
    resolvedPath = path.isAbsolute(options.configPath)
      ? options.configPath
      : path.join(cwd, options.configPath);
  } else {
    for (const candidate of CONFIG_CANDIDATES) {
      const fullPath = path.join(cwd, candidate);
      if (fs.existsSync(fullPath)) {
        resolvedPath = fullPath;
        break;
      }
    }
  }

  // キャッシュ有効性チェック
  if (!forceReload && cachedService) {
    if (!resolvedPath && cachedConfigPath === null) {
      return cachedService; // 両方ともconfig無し
    }
    if (resolvedPath && resolvedPath === cachedConfigPath) {
      const currentMtime = getConfigMtime(resolvedPath);
      if (currentMtime === cachedConfigMtime) {
        return cachedService; // 同一ファイル、未変更
      }
    }
  }

  // 設定ファイル読み込み
  let config: StopWordsConfig | null = null;

  if (resolvedPath && fs.existsSync(resolvedPath)) {
    const raw = fs.readFileSync(resolvedPath, "utf8");
    const parsed = parse(raw);
    const result = StopWordsConfigSchema.safeParse(parsed);

    if (!result.success) {
      const details = result.error.issues.map((issue) => issue.message).join(", ");
      throw new Error(`Invalid stop words config in ${resolvedPath}: ${details}`);
    }

    config = result.data;
    cachedConfigPath = resolvedPath;
    cachedConfigMtime = getConfigMtime(resolvedPath);
  } else {
    cachedConfigPath = null;
    cachedConfigMtime = null;
  }

  // サービス生成＆キャッシュ
  cachedService = new StopWordsService(config, options.language);
  return cachedService;
}

/**
 * テスト用: キャッシュクリア
 */
export function clearStopWordsCache(): void {
  cachedService = null;
  cachedConfigPath = null;
  cachedConfigMtime = null;
}

/**
 * レガシーストップワードリストを取得（テスト・マイグレーション用）
 */
export function getLegacyStopWords(): readonly string[] {
  return LEGACY_STOP_WORDS;
}
