import { ServerResponse } from "node:http";

export interface MetricSnapshot {
  httpRequestsTotal: number;
  maskAppliedTotal: number;
  denylistHitsTotal: number;
  requestDurationMs: number;
}

export class MetricsRegistry {
  private httpRequestsTotal = 0;
  private maskAppliedTotal = 0;
  private denylistHitsTotal = 0;
  private requestDurationMs = 0;

  recordRequest(durationMs: number): void {
    this.httpRequestsTotal += 1;
    this.requestDurationMs += durationMs;
  }

  recordMask(applied: number): void {
    this.maskAppliedTotal += applied;
  }

  recordDenylistHit(count: number): void {
    this.denylistHitsTotal += count;
  }

  /**
   * メトリクスをリセット（テスト用、またはメトリクスローテーション用）
   */
  reset(): void {
    this.httpRequestsTotal = 0;
    this.maskAppliedTotal = 0;
    this.denylistHitsTotal = 0;
    this.requestDurationMs = 0;
  }

  snapshot(): MetricSnapshot {
    return {
      httpRequestsTotal: this.httpRequestsTotal,
      maskAppliedTotal: this.maskAppliedTotal,
      denylistHitsTotal: this.denylistHitsTotal,
      requestDurationMs: this.requestDurationMs,
    };
  }

  toPrometheus(): string {
    const snapshot = this.snapshot();
    return [
      "# HELP kiri_http_requests_total Total number of JSON-RPC requests handled",
      "# TYPE kiri_http_requests_total counter",
      `kiri_http_requests_total ${snapshot.httpRequestsTotal}`,
      "# HELP kiri_mask_applied_total Number of sensitive values masked",
      "# TYPE kiri_mask_applied_total counter",
      `kiri_mask_applied_total ${snapshot.maskAppliedTotal}`,
      "# HELP kiri_denylist_hits_total Number of paths excluded via denylist",
      "# TYPE kiri_denylist_hits_total counter",
      `kiri_denylist_hits_total ${snapshot.denylistHitsTotal}`,
      "# HELP kiri_request_duration_ms Accumulated request duration in milliseconds",
      "# TYPE kiri_request_duration_ms counter",
      `kiri_request_duration_ms ${snapshot.requestDurationMs}`,
    ].join("\n");
  }
}

export function writeMetricsResponse(res: ServerResponse, registry: MetricsRegistry): void {
  res.statusCode = 200;
  res.setHeader("Content-Type", "text/plain; version=0.0.4");
  res.end(`${registry.toPrometheus()}\n`);
}
