/**
 * Tests for Dart SDK detection (src/indexer/dart/sdk.ts)
 */

import { describe, expect, it, beforeEach, vi, afterEach } from "vitest";
import type {
  execSync as ExecSyncType,
  execFileSync as ExecFileSyncType,
} from "node:child_process";
import type { existsSync as ExistsSyncType } from "node:fs";

// Mock modules
vi.mock("node:child_process");
vi.mock("node:fs");

describe("Dart SDK detection", () => {
  let execSyncMock: ReturnType<typeof vi.fn>;
  let execFileSyncMock: ReturnType<typeof vi.fn>;
  let existsSyncMock: ReturnType<typeof vi.fn>;
  let originalEnv: NodeJS.ProcessEnv;

  beforeEach(async () => {
    originalEnv = { ...process.env };

    const childProcess = await import("node:child_process");
    const fs = await import("node:fs");

    execSyncMock = vi.fn();
    execFileSyncMock = vi.fn();
    existsSyncMock = vi.fn();

    // execSync is used for "which dart", execFileSync is used for "dart --version"
    vi.mocked(childProcess.execSync).mockImplementation(execSyncMock);
    vi.mocked(childProcess.execFileSync).mockImplementation(execFileSyncMock);
    vi.mocked(fs.existsSync).mockImplementation(existsSyncMock);
  });

  afterEach(() => {
    process.env = originalEnv;
    vi.restoreAllMocks();
  });

  describe("detectDartSdk", () => {
    it("detects SDK from DART_SDK environment variable", async () => {
      process.env.DART_SDK = "/custom/dart-sdk";
      existsSyncMock.mockReturnValue(true);
      execFileSyncMock.mockReturnValue("Dart SDK version: 3.2.0 (stable)\n");

      const { detectDartSdk } = await import("../../../src/indexer/dart/sdk.js");
      const result = detectDartSdk();

      expect(result.sdkPath).toBe("/custom/dart-sdk");
      expect(result.version).toBe("3.2.0");
      expect(result.analysisServerPath).toContain("analysis_server.dart.snapshot");
      expect(result.dartExecutable).toContain("/custom/dart-sdk/bin/dart");
    });

    it("detects SDK from PATH when DART_SDK not set", async () => {
      delete process.env.DART_SDK;
      execSyncMock.mockReturnValueOnce("/usr/local/bin/dart\n"); // which dart
      execFileSyncMock.mockReturnValueOnce("Dart SDK version: 3.1.5 (stable)\n"); // dart --version
      existsSyncMock.mockReturnValue(true);

      const { detectDartSdk } = await import("../../../src/indexer/dart/sdk.js");
      const result = detectDartSdk();

      expect(result.sdkPath).toBe("/usr/local");
      expect(result.version).toBe("3.1.5");
      expect(result.dartExecutable).toBe("/usr/local/bin/dart");
    });

    it("throws MissingToolError when SDK not found", async () => {
      delete process.env.DART_SDK;
      execSyncMock.mockImplementation(() => {
        throw new Error("command not found");
      });

      const { detectDartSdk, MissingToolError } = await import("../../../src/indexer/dart/sdk.js");
      expect(() => detectDartSdk()).toThrow(MissingToolError);
      expect(() => detectDartSdk()).toThrow(/Dart SDK not found/);
    });

    it("extracts version from stderr when dart --version outputs to stderr", async () => {
      delete process.env.DART_SDK;
      execSyncMock.mockReturnValueOnce("/opt/dart/bin/dart\n"); // which dart
      execFileSyncMock.mockImplementationOnce(() => {
        const error: any = new Error("stderr output");
        error.stderr = Buffer.from("Dart SDK version: 3.3.0 (stable)\n");
        throw error;
      });
      existsSyncMock.mockReturnValue(true);

      const { detectDartSdk } = await import("../../../src/indexer/dart/sdk.js");
      const result = detectDartSdk();

      expect(result.version).toBe("3.3.0");
    });

    it("returns 'unknown' version when version extraction fails", async () => {
      process.env.DART_SDK = "/custom/dart-sdk";
      existsSyncMock.mockReturnValue(true);
      execFileSyncMock.mockReturnValue("Invalid output\n");

      const { detectDartSdk } = await import("../../../src/indexer/dart/sdk.js");
      const result = detectDartSdk();

      expect(result.version).toBe("unknown");
    });
  });

  describe("isDartSdkAvailable", () => {
    it("returns true when SDK is available", async () => {
      process.env.DART_SDK = "/custom/dart-sdk";
      existsSyncMock.mockReturnValue(true);
      execFileSyncMock.mockReturnValue("Dart SDK version: 3.2.0\n");

      const { isDartSdkAvailable } = await import("../../../src/indexer/dart/sdk.js");
      expect(isDartSdkAvailable()).toBe(true);
    });

    it("returns false when SDK is not available", async () => {
      delete process.env.DART_SDK;
      execSyncMock.mockImplementation(() => {
        throw new Error("not found");
      });

      const { isDartSdkAvailable } = await import("../../../src/indexer/dart/sdk.js");
      expect(isDartSdkAvailable()).toBe(false);
    });
  });
});
