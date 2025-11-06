/**
 * Tests for analyzeDartSource (src/indexer/dart/analyze.ts)
 */

import { describe, expect, it, beforeEach, vi, afterEach } from "vitest";
import { analyzeDartSource, cleanup } from "../../../src/indexer/dart/analyze.js";

// Mock dependencies
vi.mock("../../../src/indexer/dart/client.js");
vi.mock("../../../src/indexer/dart/sdk.js");

describe("analyzeDartSource", () => {
  let mockClient: any;
  let isDartSdkAvailableMock: ReturnType<typeof vi.fn>;

  beforeEach(async () => {
    vi.resetModules();

    // Mock SDK availability
    const sdk = await import("../../../src/indexer/dart/sdk.js");
    isDartSdkAvailableMock = vi.fn().mockReturnValue(true);
    vi.mocked(sdk.isDartSdkAvailable).mockImplementation(isDartSdkAvailableMock);

    // Mock DartAnalysisClient
    mockClient = {
      initialize: vi.fn().mockResolvedValue(undefined),
      analyzeFile: vi.fn().mockResolvedValue({
        outline: {
          kind: "COMPILATION_UNIT",
          offset: 0,
          length: 100,
          element: { kind: "COMPILATION_UNIT", name: "test.dart" },
          children: [
            {
              kind: "CLASS",
              offset: 0,
              length: 50,
              element: { kind: "CLASS", name: "TestClass" },
            },
          ],
        },
      }),
      getLibraryDependencies: vi.fn().mockResolvedValue({
        libraries: [],
        packageMap: {},
      }),
      dispose: vi.fn().mockResolvedValue(undefined),
    };

    const clientModule = await import("../../../src/indexer/dart/client.js");
    vi.mocked(clientModule.DartAnalysisClient).mockImplementation(() => mockClient);
  });

  afterEach(async () => {
    await cleanup();
    vi.restoreAllMocks();
  });

  it("returns symbols and snippets from Analysis Server", async () => {
    const result = await analyzeDartSource("/test/file.dart", "class TestClass {}", "/test");

    expect(result.symbols).toHaveLength(1);
    expect(result.symbols[0]).toMatchObject({
      name: "TestClass",
      kind: "class",
    });
    expect(result.snippets).toHaveLength(1);
  });

  it("returns empty dependencies in MVP phase", async () => {
    const result = await analyzeDartSource("/test/file.dart", "class TestClass {}", "/test");

    expect(result.dependencies).toEqual([]);
  });

  it("reuses client for same workspace root", async () => {
    await analyzeDartSource("/test/file1.dart", "class A {}", "/test");
    await analyzeDartSource("/test/file2.dart", "class B {}", "/test");

    expect(mockClient.initialize).toHaveBeenCalledTimes(1);
    expect(mockClient.analyzeFile).toHaveBeenCalledTimes(2);
  });

  it("disposes old client when workspace root changes", async () => {
    await analyzeDartSource("/test1/file.dart", "class A {}", "/test1");
    await analyzeDartSource("/test2/file.dart", "class B {}", "/test2");

    expect(mockClient.dispose).toHaveBeenCalledTimes(1);
    expect(mockClient.initialize).toHaveBeenCalledTimes(2);
  });

  it("returns empty result when Dart SDK is not available", async () => {
    isDartSdkAvailableMock.mockReturnValue(false);

    const consoleSpy = vi.spyOn(console, "warn").mockImplementation(() => {});

    const result = await analyzeDartSource("/test/file.dart", "class TestClass {}", "/test");

    expect(result).toEqual({ symbols: [], snippets: [], dependencies: [] });
    expect(consoleSpy).toHaveBeenCalled();

    consoleSpy.mockRestore();
  });

  it("handles analysis errors gracefully", async () => {
    mockClient.analyzeFile.mockRejectedValue(new Error("Analysis failed"));

    const consoleSpy = vi.spyOn(console, "error").mockImplementation(() => {});

    const result = await analyzeDartSource("/test/file.dart", "invalid code", "/test");

    expect(result).toEqual({ symbols: [], snippets: [], dependencies: [] });
    expect(consoleSpy).toHaveBeenCalled();

    consoleSpy.mockRestore();
  });

  describe("cleanup", () => {
    it("disposes global client", async () => {
      await analyzeDartSource("/test/file.dart", "class A {}", "/test");
      await cleanup();

      expect(mockClient.dispose).toHaveBeenCalledTimes(1);

      // Verify new client is created after cleanup
      await analyzeDartSource("/test/file.dart", "class B {}", "/test");
      expect(mockClient.initialize).toHaveBeenCalledTimes(2);
    });
  });
});
