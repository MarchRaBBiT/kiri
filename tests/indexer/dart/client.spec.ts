/**
 * Tests for DartAnalysisClient (src/indexer/dart/client.ts)
 */

import { describe, expect, it, beforeEach, vi, afterEach } from "vitest";
import { DartAnalysisClient, DAPProtocolError } from "../../../src/indexer/dart/client.js";
import { MockChildProcess, createMockSdkInfo } from "./test-helpers.js";

// Mock dependencies
vi.mock("../../../src/indexer/dart/sdk.js");
vi.mock("node:child_process");

describe("DartAnalysisClient", () => {
  let mockProcess: MockChildProcess;
  let client: DartAnalysisClient;
  let skipDisposal = false;

  beforeEach(async () => {
    skipDisposal = false;

    // Reset modules to ensure clean state
    vi.resetModules();

    // Mock SDK detection
    const sdk = await import("../../../src/indexer/dart/sdk.js");
    vi.mocked(sdk.detectDartSdk).mockReturnValue(createMockSdkInfo());

    // Mock spawn to return our MockChildProcess
    const childProcess = await import("node:child_process");
    mockProcess = new MockChildProcess();
    vi.mocked(childProcess.spawn).mockReturnValue(mockProcess as any);

    client = new DartAnalysisClient({ workspaceRoots: ["/test/workspace"] });
  });

  afterEach(async () => {
    vi.useRealTimers(); // Always restore real timers first
    if (!skipDisposal) {
      await client.dispose();
    }
    vi.restoreAllMocks();
  });

  describe("initialization", () => {
    it("spawns dart analysis server process", async () => {
      const childProcess = await import("node:child_process");

      // Simulate server.connected notification
      setTimeout(() => {
        mockProcess.sendMessage({
          event: "server.connected",
          params: { version: "1.0.0", pid: 12345 },
        });
      }, 10);

      // Respond to setSubscriptions and setAnalysisRoots
      mockProcess.stdin.write = vi.fn((chunk: any, encoding?: any, callback?: any) => {
        const msg = JSON.parse(chunk.toString());
        mockProcess.sendMessage({ id: msg.id, result: {} });
        if (typeof callback === "function") {
          callback();
        } else if (typeof encoding === "function") {
          encoding();
        }
        return true;
      });

      await client.initialize();

      expect(childProcess.spawn).toHaveBeenCalledWith(
        "/mock/dart-sdk/bin/dart", // Uses dartExecutable from SDK info
        expect.arrayContaining(["--disable-dart-dev"]),
        expect.any(Object)
      );
    });

    it("sets analysis roots during initialization", async () => {
      const messages: any[] = [];

      mockProcess.stdin.write = vi.fn((chunk: any, encoding?: any, callback?: any) => {
        const msg = JSON.parse(chunk.toString());
        messages.push(msg);
        mockProcess.sendMessage({ id: msg.id, result: {} });
        if (typeof callback === "function") {
          callback();
        } else if (typeof encoding === "function") {
          encoding();
        }
        return true;
      });

      await client.initialize();

      const setRootsMsg = messages.find((m) => m.method === "analysis.setAnalysisRoots");
      expect(setRootsMsg).toBeDefined();
      expect(setRootsMsg?.params.included).toContain("/test/workspace");
    });
  });

  describe("analyzeFile", () => {
    beforeEach(async () => {
      mockProcess.stdin.write = vi.fn((chunk: any, encoding?: any, callback?: any) => {
        const msg = JSON.parse(chunk.toString());
        mockProcess.sendMessage({ id: msg.id, result: {} });
        if (typeof callback === "function") {
          callback();
        } else if (typeof encoding === "function") {
          encoding();
        }
        return true;
      });

      await client.initialize();
    });

    it("sends updateContent and getOutline requests", async () => {
      const messages: any[] = [];

      mockProcess.stdin.write = vi.fn((chunk: any, encoding?: any, callback?: any) => {
        const msg = JSON.parse(chunk.toString());
        messages.push(msg);

        if (msg.method === "analysis.getOutline") {
          mockProcess.sendMessage({
            id: msg.id,
            result: {
              outline: {
                kind: "COMPILATION_UNIT",
                offset: 0,
                length: 10,
                element: { kind: "COMPILATION_UNIT", name: "test.dart" },
              },
            },
          });
        } else {
          mockProcess.sendMessage({ id: msg.id, result: {} });
        }
        if (typeof callback === "function") {
          callback();
        } else if (typeof encoding === "function") {
          encoding();
        }
        return true;
      });

      await client.analyzeFile("/test/file.dart", "void main() {}");

      expect(messages.some((m) => m.method === "analysis.updateContent")).toBe(true);
      expect(messages.some((m) => m.method === "analysis.getOutline")).toBe(true);
    });

    it("returns outline from analysis server", async () => {
      mockProcess.stdin.write = vi.fn((chunk: any, encoding?: any, callback?: any) => {
        const msg = JSON.parse(chunk.toString());

        if (msg.method === "analysis.getOutline") {
          mockProcess.sendMessage({
            id: msg.id,
            result: {
              outline: {
                kind: "CLASS",
                offset: 0,
                length: 20,
                element: { kind: "CLASS", name: "TestClass" },
              },
            },
          });
        } else {
          mockProcess.sendMessage({ id: msg.id, result: {} });
        }
        if (typeof callback === "function") {
          callback();
        } else if (typeof encoding === "function") {
          encoding();
        }
        return true;
      });

      const result = await client.analyzeFile("/test/file.dart", "class TestClass {}");

      expect(result.outline.element.name).toBe("TestClass");
    });
  });

  describe("error handling", () => {
    it("rejects with DAPProtocolError on server error response", async () => {
      mockProcess.stdin.write = vi.fn((chunk: any, encoding?: any, callback?: any) => {
        const msg = JSON.parse(chunk.toString());
        mockProcess.sendMessage({
          id: msg.id,
          error: { code: -1, message: "Invalid file" },
        });
        if (typeof callback === "function") {
          callback();
        } else if (typeof encoding === "function") {
          encoding();
        }
        return true;
      });

      await expect(client.initialize()).rejects.toThrow(DAPProtocolError);
    });

    it("handles timeout for unresponded requests", async () => {
      vi.useFakeTimers();
      skipDisposal = true; // Skip disposal in afterEach - client is in error state

      mockProcess.stdin.write = vi.fn((_chunk: any, encoding?: any, callback?: any) => {
        if (typeof callback === "function") {
          callback();
        } else if (typeof encoding === "function") {
          encoding();
        }
        return true;
      });

      const promise = client.initialize();

      vi.advanceTimersByTime(31000); // Advance past 30s timeout

      await expect(promise).rejects.toThrow(DAPProtocolError);
      await expect(promise).rejects.toThrow(/timeout/i);
    });
  });

  describe("cleanup", () => {
    it("sends shutdown request on dispose", async () => {
      skipDisposal = true; // We test disposal in this test
      const messages: any[] = [];

      mockProcess.stdin.write = vi.fn((chunk: any, encoding?: any, callback?: any) => {
        const msg = JSON.parse(chunk.toString());
        messages.push(msg);
        mockProcess.sendMessage({ id: msg.id, result: {} });

        // Simulate process exit after shutdown request
        if (msg.method === "server.shutdown") {
          setTimeout(() => {
            mockProcess.kill("SIGTERM");
          }, 10);
        }

        if (typeof callback === "function") {
          callback();
        } else if (typeof encoding === "function") {
          encoding();
        }
        return true;
      });

      await client.initialize();
      await client.dispose();

      expect(messages.some((m) => m.method === "server.shutdown")).toBe(true);
    });

    it("kills process after dispose", async () => {
      skipDisposal = true; // We test disposal in this test

      mockProcess.stdin.write = vi.fn((chunk: any, encoding?: any, callback?: any) => {
        const msg = JSON.parse(chunk.toString());
        mockProcess.sendMessage({ id: msg.id, result: {} });

        // Simulate process exit after shutdown request
        if (msg.method === "server.shutdown") {
          setTimeout(() => {
            mockProcess.kill("SIGTERM");
          }, 10);
        }

        if (typeof callback === "function") {
          callback();
        } else if (typeof encoding === "function") {
          encoding();
        }
        return true;
      });

      await client.initialize();
      await client.dispose();

      expect(mockProcess.killed).toBe(true);
    });
  });
});
