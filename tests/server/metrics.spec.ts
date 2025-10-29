import { afterEach, describe, expect, it } from "vitest";

import { MetricsRegistry, writeMetricsResponse } from "../../src/server/observability/metrics.js";

describe("MetricsRegistry", () => {
  let registry: MetricsRegistry;

  afterEach(() => {
    registry?.reset();
  });

  it("records HTTP requests with duration", () => {
    registry = new MetricsRegistry();
    registry.recordRequest(100);
    registry.recordRequest(200);

    const snapshot = registry.snapshot();
    expect(snapshot.httpRequestsTotal).toBe(2);
    expect(snapshot.requestDurationMs).toBe(300);
  });

  it("records mask applications", () => {
    registry = new MetricsRegistry();
    registry.recordMask(5);
    registry.recordMask(3);

    const snapshot = registry.snapshot();
    expect(snapshot.maskAppliedTotal).toBe(8);
  });

  it("records denylist hits", () => {
    registry = new MetricsRegistry();
    registry.recordDenylistHit(10);
    registry.recordDenylistHit(5);

    const snapshot = registry.snapshot();
    expect(snapshot.denylistHitsTotal).toBe(15);
  });

  it("resets all metrics to zero", () => {
    registry = new MetricsRegistry();
    registry.recordRequest(100);
    registry.recordMask(5);
    registry.recordDenylistHit(10);

    registry.reset();

    const snapshot = registry.snapshot();
    expect(snapshot.httpRequestsTotal).toBe(0);
    expect(snapshot.maskAppliedTotal).toBe(0);
    expect(snapshot.denylistHitsTotal).toBe(0);
    expect(snapshot.requestDurationMs).toBe(0);
  });

  it("exports Prometheus text format correctly", () => {
    registry = new MetricsRegistry();
    registry.recordRequest(150);
    registry.recordMask(3);
    registry.recordDenylistHit(7);

    const output = registry.toPrometheus();

    expect(output).toContain("# HELP kiri_http_requests_total");
    expect(output).toContain("# TYPE kiri_http_requests_total counter");
    expect(output).toContain("kiri_http_requests_total 1");
    expect(output).toContain("kiri_mask_applied_total 3");
    expect(output).toContain("kiri_denylist_hits_total 7");
    expect(output).toContain("kiri_request_duration_ms 150");
  });

  it("provides isolated snapshots without modifying state", () => {
    registry = new MetricsRegistry();
    registry.recordRequest(100);

    const snapshot1 = registry.snapshot();
    const snapshot2 = registry.snapshot();

    expect(snapshot1).toEqual(snapshot2);
    expect(snapshot1).not.toBe(snapshot2); // Different object instances
  });
});

describe("writeMetricsResponse", () => {
  it("writes Prometheus metrics to HTTP response", () => {
    const registry = new MetricsRegistry();
    registry.recordRequest(200);
    registry.recordMask(5);

    const mockResponse = {
      statusCode: 0,
      headers: {} as Record<string, string>,
      ended: false,
      body: "",
      setHeader(key: string, value: string) {
        this.headers[key] = value;
      },
      end(data: string) {
        this.body = data;
        this.ended = true;
      },
    };

    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    writeMetricsResponse(mockResponse as any, registry);

    expect(mockResponse.statusCode).toBe(200);
    expect(mockResponse.headers["Content-Type"]).toBe("text/plain; version=0.0.4");
    expect(mockResponse.ended).toBe(true);
    expect(mockResponse.body).toContain("kiri_http_requests_total 1");
    expect(mockResponse.body).toContain("kiri_mask_applied_total 5");
    expect(mockResponse.body).toContain("kiri_request_duration_ms 200");
  });
});
