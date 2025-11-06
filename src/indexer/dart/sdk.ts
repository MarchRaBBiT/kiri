/**
 * Dart SDK detection and validation utilities
 */

import { execSync, execFileSync } from "node:child_process";
import { existsSync } from "node:fs";
import path from "node:path";

export interface DartSdkInfo {
  sdkPath: string;
  version: string;
  analysisServerPath: string;
}

/**
 * MissingToolError: Dart SDKが見つからない場合のエラー
 */
export class MissingToolError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "MissingToolError";
  }
}

/**
 * Dart SDKの検出と検証
 *
 * 検出順序:
 * 1. DART_SDK 環境変数
 * 2. PATH から dart コマンド検索
 *
 * @returns DartSdkInfo
 * @throws MissingToolError - Dart SDKが見つからない場合
 */
export function detectDartSdk(): DartSdkInfo {
  // 1. DART_SDK 環境変数をチェック
  const dartSdkEnv = process.env.DART_SDK;
  if (dartSdkEnv) {
    const snapshotPath = path.join(dartSdkEnv, "bin", "snapshots", "analysis_server.dart.snapshot");
    if (existsSync(snapshotPath)) {
      const version = getDartVersion(path.join(dartSdkEnv, "bin", "dart"));
      return {
        sdkPath: dartSdkEnv,
        version,
        analysisServerPath: snapshotPath,
      };
    }
  }

  // 2. PATH から dart コマンドを検索
  try {
    const dartPath = execSync("which dart", { encoding: "utf-8" }).trim();
    if (dartPath) {
      const version = getDartVersion(dartPath);
      // dart コマンドから SDK パスを推測
      // 通常 /path/to/dart-sdk/bin/dart なので bin の親ディレクトリ
      const sdkPath = path.dirname(path.dirname(dartPath));
      const snapshotPath = path.join(sdkPath, "bin", "snapshots", "analysis_server.dart.snapshot");

      if (existsSync(snapshotPath)) {
        return {
          sdkPath,
          version,
          analysisServerPath: snapshotPath,
        };
      }
    }
  } catch {
    // which dart が失敗した場合は次へ
  }

  // Dart SDK が見つからない
  throw new MissingToolError(
    "Dart SDK not found. Please install Dart SDK and ensure 'dart' is in PATH, or set DART_SDK environment variable. Visit https://dart.dev/get-dart for installation instructions."
  );
}

/**
 * dart --version の実行結果からバージョン文字列を取得
 *
 * @param dartExecutable - dart 実行ファイルのパス
 * @returns バージョン文字列（例: "3.2.0"）
 */
function getDartVersion(dartExecutable: string): string {
  try {
    // execFileSync を使用してコマンドインジェクションを防ぐ
    // 引数を配列で渡すことで安全に実行
    const output = execFileSync(dartExecutable, ["--version"], {
      encoding: "utf-8",
      stdio: ["pipe", "pipe", "pipe"],
    });
    // "Dart SDK version: 3.2.0 (stable) ..." のような出力から抽出
    const match = output.match(/Dart SDK version:\s+(\S+)/);
    if (match?.[1]) {
      return match[1];
    }
    return "unknown";
  } catch (error) {
    // execFileSync は stderr に出力する場合でも error.stderr で取得可能
    if (error && typeof error === "object" && "stderr" in error) {
      const stderr = String(error.stderr);
      const match = stderr.match(/Dart SDK version:\s+(\S+)/);
      if (match?.[1]) {
        return match[1];
      }
    }
    return "unknown";
  }
}

/**
 * Dart SDK が利用可能かチェック（throws しない版）
 *
 * @returns SDK が利用可能な場合 true
 */
export function isDartSdkAvailable(): boolean {
  try {
    detectDartSdk();
    return true;
  } catch {
    return false;
  }
}
