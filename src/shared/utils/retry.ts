export interface RetryOptions {
  maxAttempts: number;
  delayMs: number;
  jitterMs?: number;
  isRetriable?: (error: unknown) => boolean;
}

export async function withRetry<T>(
  operation: () => Promise<T>,
  { maxAttempts, delayMs, jitterMs = 0, isRetriable }: RetryOptions
): Promise<T> {
  if (maxAttempts < 1) {
    throw new Error("maxAttempts must be >= 1");
  }

  for (let attempt = 1; attempt <= maxAttempts; attempt++) {
    try {
      return await operation();
    } catch (error) {
      const shouldRetry = attempt < maxAttempts && (isRetriable ? isRetriable(error) : true);
      if (!shouldRetry) {
        throw error;
      }
      const jitter = jitterMs > 0 ? Math.random() * jitterMs : 0;
      await new Promise((resolve) => setTimeout(resolve, delayMs + jitter));
    }
  }

  throw new Error("Retry attempts exhausted");
}
