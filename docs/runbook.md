# 運用 Runbook

## Degrade 発生時の復旧手順

1. `/metrics` を確認し、`kiri_http_requests_total` の伸びと 503 レスポンスが増えていないかを確認する。
2. 監査ログ (`var/audit/*.json`) を開き、直近の `degrade` イベントと対象リポジトリを確認する。
3. `pnpm exec tsx src/client/cli.ts security verify` を実行し、セキュリティロックに改ざんがないことを確認する。
4. DuckDB/VSS プロセスのヘルスチェックを行い、必要であれば再起動する。
5. 復旧が完了したらサーバーを `--allow-degrade` なしで再起動する。復旧完了後に `/metrics` のレスポンスから `degrade: true`
   が含まれないことを確認する。

## 観測項目

- `kiri_mask_applied_total`: 機密データのマスキング件数。急増した場合は流出を疑い監査を実施する。
- `kiri_denylist_hits_total`: インデックス除外の件数。設定値と `.gitignore` の差分がないか `pnpm exec tsx scripts/diag.ts check-denylist`
  で確認する。
- `kiri_request_duration_ms`: JSON-RPC リクエストの合計遅延。急増時は DuckDB/VSS の負荷を調査する。
