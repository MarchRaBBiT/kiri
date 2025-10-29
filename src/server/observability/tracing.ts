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
    const output = await fn(span);
    return output;
  });
  return result as T;
}
