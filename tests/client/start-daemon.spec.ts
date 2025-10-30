/**
 * Tests for daemon starter utility
 */

import { afterEach, beforeEach, describe, expect, it } from "vitest";
import * as fs from "fs/promises";
import * as path from "path";
import * as os from "os";
import { isDaemonRunning } from "../../src/client/start-daemon.js";

describe("Daemon Starter", () => {
  let tmpDir: string;
  let databasePath: string;

  beforeEach(async () => {
    tmpDir = await fs.mkdtemp(path.join(os.tmpdir(), "kiri-starter-test-"));
    databasePath = path.join(tmpDir, "test.duckdb");
  });

  afterEach(async () => {
    // クリーンアップ
    try {
      await fs.rm(tmpDir, { recursive: true, force: true });
    } catch (err) {
      // Ignore cleanup errors
    }
  });

  describe("isDaemonRunning", () => {
    it("returns false when no PID file exists", async () => {
      const running = await isDaemonRunning(databasePath);
      expect(running).toBe(false);
    });

    it("returns false when PID file contains stale PID", async () => {
      const pidFilePath = `${databasePath}.daemon.pid`;

      // 存在しないPIDを書き込む
      const nonExistentPid = 999999;
      await fs.writeFile(pidFilePath, String(nonExistentPid), "utf-8");

      const running = await isDaemonRunning(databasePath);
      expect(running).toBe(false);

      // PIDファイルがクリーンアップされたことを確認
      await expect(fs.access(pidFilePath)).rejects.toThrow();
    });

    it("returns false when daemon process exists but socket is not responsive", async () => {
      const pidFilePath = `${databasePath}.daemon.pid`;

      // 現在のプロセスのPIDを書き込む（ソケットは存在しない）
      await fs.writeFile(pidFilePath, String(process.pid), "utf-8");

      const running = await isDaemonRunning(databasePath);
      expect(running).toBe(false);

      // PIDファイルがクリーンアップされたことを確認
      await expect(fs.access(pidFilePath)).rejects.toThrow();
    });

    it("cleans up stale socket file", async () => {
      const pidFilePath = `${databasePath}.daemon.pid`;
      const socketPath = `${databasePath}.sock`;

      // 存在しないPIDとソケットファイルを作成
      await fs.writeFile(pidFilePath, "999999", "utf-8");
      await fs.writeFile(socketPath, "", "utf-8"); // ダミーソケット

      const running = await isDaemonRunning(databasePath);
      expect(running).toBe(false);

      // 両方のファイルがクリーンアップされたことを確認
      await expect(fs.access(pidFilePath)).rejects.toThrow();
      await expect(fs.access(socketPath)).rejects.toThrow();
    });

    it("cleans up startup lock file", async () => {
      const pidFilePath = `${databasePath}.daemon.pid`;
      const startupLockPath = `${databasePath}.daemon.starting`;

      // 存在しないPIDとスタートアップロックを作成
      await fs.writeFile(pidFilePath, "999999", "utf-8");
      await fs.writeFile(startupLockPath, "999999", "utf-8");

      const running = await isDaemonRunning(databasePath);
      expect(running).toBe(false);

      // 両方のファイルがクリーンアップされたことを確認
      await expect(fs.access(pidFilePath)).rejects.toThrow();
      await expect(fs.access(startupLockPath)).rejects.toThrow();
    });
  });
});
