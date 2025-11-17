# KIRI Golden Set Evaluation - 2025-11-17

**Version**: 0.10.0 (77d4dbb)
**Dataset**: v2025-11-docs-plain
**K**: 10

## Overall Metrics

| Metric              | Value  | Threshold | Status |
| ------------------- | ------ | --------- | ------ |
| P@10                | 0.286  | ≥0.7      | ❌     |
| Avg TFFU            | 1ms    | ≤1000ms   | ✅     |
| Avg Token Savings   | 89.5%  | ≥40%      | ✅     |
| Avg Hint Coverage   | 14.1%  | -         | -      |
| Metadata Pass       | 50.0%  | ≥100%     | ❌     |
| Inbound Link Pass   | 50.0%  | ≥100%     | ❌     |
| Avg Bundle Tokens   | 42462  | -         | -      |
| Avg Baseline Tokens | 457694 | -         | -      |
| Total Queries       | 22     | -         | -      |
| Successful          | 17     | -         | -      |
| Failed              | 5      | -         | -      |

## By Category

| Category   | P@10  | Avg TFFU | Avg Token Savings | Avg Hint Coverage | Metadata Pass | Inbound Pass | Count |
| ---------- | ----- | -------- | ----------------- | ----------------- | ------------- | ------------ | ----- |
| editor     | 0.200 | 0ms      | 98.1%             | 30.0%             | N/A           | N/A          | 2     |
| api        | 0.133 | 0ms      | 87.9%             | 16.7%             | N/A           | N/A          | 3     |
| debug      | 0.150 | 0ms      | 81.0%             | 15.0%             | N/A           | N/A          | 2     |
| feature    | 0.125 | 0ms      | 98.6%             | 17.5%             | N/A           | N/A          | 4     |
| infra      | 0.200 | 0ms      | 62.7%             | 30.0%             | N/A           | N/A          | 1     |
| docs       | 0.900 | 4ms      | 88.5%             | 0.0%              | 100.0%        | 100.0%       | 5     |
| docs-plain | 0.000 | 0ms      | N/A               | N/A               | 0.0%          | 0.0%         | 5     |

## Category Δ Metrics

| Baseline | Variant    | ΔP@10  | ΔMetadata Pass | ΔInbound Pass |
| -------- | ---------- | ------ | -------------- | ------------- |
| docs     | docs-plain | -0.900 | -1.000         | -1.000        |

## Failed Queries

| ID                                       | Status | Error |
| ---------------------------------------- | ------ | ----- |
| kiri-docs-runbook-degrade-plain          | empty  | N/A   |
| kiri-docs-security-windows-plain         | empty  | N/A   |
| kiri-docs-search-ranking-profile-plain   | empty  | N/A   |
| kiri-docs-operations-observability-plain | empty  | N/A   |
| kiri-docs-testing-golden-plain           | empty  | N/A   |
