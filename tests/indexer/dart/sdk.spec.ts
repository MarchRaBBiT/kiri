/**
 * Tests for Dart SDK detection (src/indexer/dart/sdk.ts)
 */

import { describe, expect, it, beforeEach, vi, afterEach } from "vitest";
import {
  detectDartSdk,
  MissingToolError,
  isDartSdkAvailable,
} from "../../../src/indexer/dart/sdk.js";

// Mock modules
vi.mock("node:child_process");
vi.mock("node:fs");

describe("Dart SDK detection", () => {
  let execSyncMock: ReturnType<typeof vi.fn>;
  let existsSyncMock: ReturnType<typeof vi.fn>;
  let originalEnv: NodeJS.ProcessEnv;

  beforeEach(async () => {
    originalEnv = { ...process.env };
    vi.resetModules();

    const childProcess = await import("node:child_process");
    const fs = await import("node:fs");

    execSyncMock = vi.fn();
    existsSyncMock = vi.fn();

    vi.mocked(childProcess.execSync).mockImplementation(execSyncMock);
    vi.mocked(fs.existsSync).mockImplementation(existsSyncMock);
  });

  afterEach(() => {
    process.env = originalEnv;
    vi.restoreAllMocks();
  });

  describe("detectDartSdk", () => {
    it("detects SDK from DART_SDK environment variable", () => {
      process.env.DART_SDK = "/custom/dart-sdk";
      existsSyncMock.mockReturnValue(true);
      execSyncMock.mockReturnValue("Dart SDK version: 3.2.0 (stable)\n");

      const result = detectDartSdk();

      expect(result.sdkPath).toBe("/custom/dart-sdk");
      expect(result.version).toBe("3.2.0");
      expect(result.analysisServerPath).toContain("analysis_server.dart.snapshot");
    });

    it("detects SDK from PATH when DART_SDK not set", () => {
      delete process.env.DART_SDK;
      execSyncMock
        .mockReturnValueOnce("/usr/local/bin/dart\n") // which dart
        .mockReturnValueOnce("Dart SDK version: 3.1.5 (stable)\n"); // dart --version
      existsSyncMock.mockReturnValue(true);

      const result = detectDartSdk();

      expect(result.sdkPath).toBe("/usr/local");
      expect(result.version).toBe("3.1.5");
    });

    it("throws MissingToolError when SDK not found", () => {
      delete process.env.DART_SDK;
      execSyncMock.mockImplementation(() => {
        throw new Error("command not found");
      });

      expect(() => detectDartSdk()).toThrow(MissingToolError);
      expect(() => detectDartSdk()).toThrow(/Dart SDK not found/);
    });

    it("extracts version from stderr when dart --version outputs to stderr", () => {
      delete process.env.DART_SDK;
      execSyncMock.mockReturnValueOnce("/opt/dart/bin/dart\n").mockImplementationOnce(() => {
        const error: any = new Error("stderr output");
        error.stderr = Buffer.from("Dart SDK version: 3.3.0 (stable)\n");
        throw error;
      });
      existsSyncMock.mockReturnValue(true);

      const result = detectDartSdk();

      expect(result.version).toBe("3.3.0");
    });

    it("returns 'unknown' version when version extraction fails", () => {
      process.env.DART_SDK = "/custom/dart-sdk";
      existsSyncMock.mockReturnValue(true);
      execSyncMock.mockReturnValue("Invalid output\n");

      const result = detectDartSdk();

      expect(result.version).toBe("unknown");
    });
  });

  describe("isDartSdkAvailable", () => {
    it("returns true when SDK is available", () => {
      process.env.DART_SDK = "/custom/dart-sdk";
      existsSyncMock.mockReturnValue(true);
      execSyncMock.mockReturnValue("Dart SDK version: 3.2.0\n");

      expect(isDartSdkAvailable()).toBe(true);
    });

    it("returns false when SDK is not available", () => {
      delete process.env.DART_SDK;
      execSyncMock.mockImplementation(() => {
        throw new Error("not found");
      });

      expect(isDartSdkAvailable()).toBe(false);
    });
  });
});
