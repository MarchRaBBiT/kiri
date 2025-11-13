import { describe, expect, it, vi } from "vitest";

import { RepoRepository } from "../../../src/server/services/repo-repository.js";
import { DuckDBClient } from "../../../src/shared/duckdb.js";

describe("RepoRepository", () => {
  describe("findByPaths", () => {
    it("returns null immediately when candidates array is empty", async () => {
      const mockDb = {
        all: vi.fn(),
      } as unknown as DuckDBClient;

      const repository = new RepoRepository(mockDb);
      const result = await repository.findByPaths([]);

      expect(result).toBeNull();
      expect(mockDb.all).not.toHaveBeenCalled();
    });

    it("prioritizes direct root match over normalized_root match", async () => {
      const mockDb = {
        all: vi
          .fn()
          // First call: direct root lookup succeeds
          .mockResolvedValueOnce([{ id: 1, root: "/exact/path" }]),
      } as unknown as DuckDBClient;

      const repository = new RepoRepository(mockDb);
      const result = await repository.findByPaths(["/exact/path", "/other/path"]);

      expect(result).toEqual({ id: 1, root: "/exact/path" });
      expect(mockDb.all).toHaveBeenCalledTimes(1);
      // Should not proceed to normalized_root lookup
    });

    it("falls back to normalized_root match when direct match fails", async () => {
      const mockDb = {
        all: vi
          .fn()
          // First call: direct root lookup fails
          .mockResolvedValueOnce([])
          // Second call: column existence check succeeds
          .mockResolvedValueOnce([{ column_name: "normalized_root" }])
          // Third call: normalized_root lookup succeeds
          .mockResolvedValueOnce([{ id: 2, root: "/Users/user/project" }]),
      } as unknown as DuckDBClient;

      const repository = new RepoRepository(mockDb);
      const result = await repository.findByPaths(["/users/user/project"]);

      expect(result).toEqual({ id: 2, root: "/Users/user/project" });
      expect(mockDb.all).toHaveBeenCalledTimes(3);
    });

    it("returns null when both direct and normalized lookups fail", async () => {
      const mockDb = {
        all: vi
          .fn()
          // First call: direct root lookup fails
          .mockResolvedValueOnce([])
          // Second call: column existence check succeeds
          .mockResolvedValueOnce([{ column_name: "normalized_root" }])
          // Third call: normalized_root lookup fails
          .mockResolvedValueOnce([]),
      } as unknown as DuckDBClient;

      const repository = new RepoRepository(mockDb);
      const result = await repository.findByPaths(["/nonexistent/path"]);

      expect(result).toBeNull();
      expect(mockDb.all).toHaveBeenCalledTimes(3);
    });
  });

  describe("tableExists", () => {
    it("returns true when repo table exists", async () => {
      const mockDb = {
        all: vi.fn().mockResolvedValueOnce([{ column: "id" }]),
      } as unknown as DuckDBClient;

      const repository = new RepoRepository(mockDb);
      const result = await repository.tableExists();

      expect(result).toBe(true);
    });

    it("returns false when repo table does not exist", async () => {
      const mockDb = {
        all: vi
          .fn()
          .mockRejectedValueOnce(new Error("Catalog Error: Table with name repo does not exist")),
      } as unknown as DuckDBClient;

      const repository = new RepoRepository(mockDb);
      const result = await repository.tableExists();

      expect(result).toBe(false);
    });

    it("wraps non-repo errors with actionable message", async () => {
      const mockDb = {
        all: vi.fn().mockRejectedValueOnce(new Error("Permission denied")),
      } as unknown as DuckDBClient;

      const repository = new RepoRepository(mockDb);

      await expect(repository.tableExists()).rejects.toThrow(
        "Repo metadata check failed. Verify DuckDB permissions before retrying."
      );
    });
  });
});
