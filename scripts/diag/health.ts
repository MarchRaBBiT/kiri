import { request } from "node:http";

export interface HealthReport {
  metricsReachable: boolean;
  latencyMs: number | null;
}

export async function checkHealth(
  url = process.env.KIRI_METRICS_URL ?? "http://127.0.0.1:8765/metrics"
): Promise<HealthReport> {
  const started = Date.now();
  return await new Promise<HealthReport>((resolve) => {
    const req = request(url, (res) => {
      res.resume();
      res.on("end", () => {
        resolve({ metricsReachable: res.statusCode === 200, latencyMs: Date.now() - started });
      });
    });
    req.on("error", () => {
      resolve({ metricsReachable: false, latencyMs: null });
    });
    req.end();
  });
}
