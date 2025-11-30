#!/usr/bin/env bash
set -euo pipefail

# Setup script for golden-set evaluation.
# - Clones VS Code repo to external/vscode (shallow) if missing.
# - Builds DuckDB index (.kiri/index.duckdb).
# - Generates security lock file for the DB.
#
# Prerequisites: pnpm, Node 20, tsx available (pnpm install済み想定)。

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_PATH="$ROOT_DIR/external/vscode"
DB_PATH="$REPO_PATH/.kiri/index.duckdb"
LOCK_PATH="$REPO_PATH/.kiri/security.lock"

if [[ ! -d "$REPO_PATH/.git" ]]; then
  echo "[setup-golden] Cloning vscode..."
  git clone --depth 1 https://github.com/microsoft/vscode.git "$REPO_PATH"
else
  echo "[setup-golden] vscode repo already present. Skipping clone."
fi

mkdir -p "$REPO_PATH/.kiri"

echo "[setup-golden] Building DuckDB index at $DB_PATH ..."
pnpm exec tsx src/indexer/cli.ts --repo "$REPO_PATH" --db "$DB_PATH" --full

echo "[setup-golden] Generating security lock ..."
pnpm exec tsx src/client/cli.ts security verify --db "$DB_PATH" --security-lock "$LOCK_PATH" --write-lock

echo "[setup-golden] Done. You can now run: pnpm run eval:golden"
