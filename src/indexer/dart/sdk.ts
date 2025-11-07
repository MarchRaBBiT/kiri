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
  dartExecutable: string; // dart 実行ファイルの絶対パス（Windows対応）
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
  // Windows判定
  const isWindows = process.platform === "win32";
  const dartExeName = isWindows ? "dart.exe" : "dart";

  // 1. DART_SDK 環境変数をチェック
  const dartSdkEnv = process.env.DART_SDK;
  if (dartSdkEnv) {
    const dartPath = path.join(dartSdkEnv, "bin", dartExeName);
    const snapshotPath = path.join(dartSdkEnv, "bin", "snapshots", "analysis_server.dart.snapshot");

    if (existsSync(snapshotPath) && existsSync(dartPath)) {
      const version = getDartVersion(dartPath);
      return {
        sdkPath: dartSdkEnv,
        version,
        analysisServerPath: snapshotPath,
        dartExecutable: dartPath,
      };
    }
  }

  // 2. PATH から dart コマンドを検索（プラットフォーム別）
  try {
    const whichCmd = isWindows ? "where" : "which";
    const dartPathOutput = execSync(`${whichCmd} dart`, { encoding: "utf-8" }).trim();
    // where は複数行返す可能性があるので最初の行を使用
    const dartPath = dartPathOutput.split("\n")[0]?.trim();

    if (dartPath && existsSync(dartPath)) {
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
          dartExecutable: dartPath,
        };
      }
    }
  } catch {
    // which/where dart が失敗した場合は次へ
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
