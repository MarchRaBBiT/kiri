import { describe, it, expect } from "vitest";

import type { Query } from "../../external/assay-kit/src/index.ts";
import { KiriSearchAdapter } from "../../scripts/assay/kiri-adapter.js";

class TestableKiriSearchAdapter extends KiriSearchAdapter {
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
}

function createContext() {
  const controller = new AbortController();
  return { signal: controller.signal, options: {} };
}

describe("KiriSearchAdapter metadata hints", () => {
  it("passes normalized metadata.hints to context_bundle artifacts", async () => {
    const adapter = new TestableKiriSearchAdapter();
    const query: Query<Record<string, unknown>, { hints: string[]; expected: string[] }> = {
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
    const adapter = new TestableKiriSearchAdapter();
    const query: Query<Record<string, unknown>, { expected: string[] }> = {
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
    const adapter = new TestableKiriSearchAdapter();
    const hints = Array.from({ length: 12 }, (_, index) => `hint-${index + 1}`);
    const query: Query<Record<string, unknown>, { hints: string[]; expected: string[] }> = {
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
