import { DuckDBClient } from "../shared/duckdb";

export interface ServerContext {
  db: DuckDBClient;
  repoId: number;
}
