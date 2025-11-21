import { existsSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { describe, it, expect, beforeAll } from "vitest";

// external/assay-kit は private submodule。存在しなければテストを丸ごとスキップ。
const assayKitPath = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  "../../external/assay-kit/packages/assay-kit/src/index.ts"
);

if (!existsSync(assayKitPath)) {
  describe.skip("KiriSearchAdapter metadata hints (assay-kit missing)", () => {});
} else {
  describe("KiriSearchAdapter metadata hints", () => {
    type Query = {
      id: string;
      text: string;
      metadata?: { hints?: string[]; expected?: string[] };
    };

    type KiriAdapterCtor = typeof import("../../scripts/assay/kiri-adapter.js").KiriSearchAdapter;
    let KiriSearchAdapterClass: KiriAdapterCtor;

    beforeAll(async () => {
      const module = await import("../../scripts/assay/kiri-adapter.js");
      KiriSearchAdapterClass = module.KiriSearchAdapter;
    });

    function createTestAdapter() {
      const Base = KiriSearchAdapterClass;
      return new (class extends Base {
        public lastParams?: Record<string, unknown>;
        public lastMethod?: string;

        constructor() {
          super("var/index.duckdb", process.cwd(), "node");
        }

        protected override async callKiri(
          method: string,
          params: Record<string, unknown>,
          _timeoutMs: number,
          _parentSignal?: AbortSignal
        ): Promise<unknown> {
          this.lastMethod = method;
          this.lastParams = params;
          return {
            context: [
              {
                path: "src/stats/tests.ts",
              },
            ],
          };
        }
      })();
    }

    function createContext() {
      const controller = new AbortController();
      return { signal: controller.signal, options: {} };
    }

    it("passes normalized metadata.hints to context_bundle artifacts", async () => {
      const adapter = createTestAdapter();
      const query: Query = {
        id: "q-hints",
        text: "mann whitney u",
        metadata: {
          hints: [
            "  mannWhitneyU  ",
            "rank-biserial",
            "stats/tests.ts",
            "mannWhitneyU",
            "",
            " extra ",
          ],
          expected: ["src/stats/tests.ts"],
        },
      };

      await adapter.execute(query, createContext());

      expect(adapter.lastMethod).toBe("context_bundle");
      const artifacts = (adapter.lastParams?.artifacts ?? {}) as { hints?: string[] };
      expect(artifacts.hints).toEqual(["mannWhitneyU", "rank-biserial", "stats/tests.ts", "extra"]);
    });

    it("omits artifacts when no valid hints exist", async () => {
      const adapter = createTestAdapter();
      const query: Query = {
        id: "q-no-hints",
        text: "orchestrator tuning",
        metadata: {
          expected: ["src/runtime/orchestrator.ts"],
        },
      };

      await adapter.execute(query, createContext());

      expect(adapter.lastMethod).toBe("context_bundle");
      expect(adapter.lastParams?.artifacts).toBeUndefined();
    });

    it("caps metadata hints to eight entries to keep payloads bounded", async () => {
      const adapter = createTestAdapter();
      const hints = Array.from({ length: 12 }, (_, index) => `hint-${index + 1}`);
      const query: Query = {
        id: "q-many-hints",
        text: "stats query",
        metadata: {
          hints,
          expected: ["src/stats/tests.ts"],
        },
      };

      await adapter.execute(query, createContext());

      const artifacts = (adapter.lastParams?.artifacts ?? {}) as { hints?: string[] };
      expect(artifacts.hints).toEqual(hints.slice(0, 8));
    });
  });
}
