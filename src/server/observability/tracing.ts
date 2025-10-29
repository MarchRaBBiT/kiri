import type { Span } from "@opentelemetry/api";

let tracerPromise: Promise<{
  startActiveSpan: (name: string, fn: (span: Span) => Promise<unknown>) => Promise<unknown>;
} | null>;

async function loadTracer() {
  if (!tracerPromise) {
    tracerPromise = (async () => {
      try {
        const api = await import("@opentelemetry/api");
        return {
          startActiveSpan: async (name: string, fn: (span: Span) => Promise<unknown>) => {
            return await api.trace.getTracer("kiri").startActiveSpan(name, async (span) => {
              try {
                return await fn(span);
              } finally {
                span.end();
              }
            });
          },
        };
      } catch {
        return null;
      }
    })();
  }
  return tracerPromise;
}

export async function withSpan<T>(name: string, fn: (span: Span | null) => Promise<T>): Promise<T> {
  const tracer = await loadTracer();
  if (!tracer) {
    return await fn(null);
  }
  const result = await tracer.startActiveSpan(name, async (span) => {
    try {
      const output = await fn(span);
      // 成功時はOKステータスを設定
      span.setStatus({ code: 1 }); // SpanStatusCode.OK
      return output;
    } catch (error) {
      // エラー詳細をキャプチャしてデバッグ可能にする
      span.setStatus({
        code: 2, // SpanStatusCode.ERROR
        message: error instanceof Error ? error.message : String(error),
      });
      span.setAttribute("error", true);
      if (error instanceof Error) {
        span.setAttribute("error.type", error.constructor.name);
        span.setAttribute("error.message", error.message);
        if (error.stack) {
          span.setAttribute("error.stack", error.stack);
        }
      }
      throw error; // エラーを記録後に再スロー
    }
  });
  return result as T;
}
