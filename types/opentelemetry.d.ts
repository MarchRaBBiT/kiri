declare module "@opentelemetry/api" {
  export interface SpanStatus {
    code: number;
    message?: string;
  }

  export interface Span {
    setAttribute(key: string, value: unknown): void;
    recordException(error: unknown): void;
    setStatus(status: SpanStatus): void;
    end(): void;
  }

  export interface Tracer {
    startActiveSpan<T>(name: string, fn: (span: Span) => Promise<T>): Promise<T>;
  }

  export const trace: {
    getTracer(name: string): Tracer;
  };
}
