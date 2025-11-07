#!/usr/bin/env bash
set -euo pipefail

command="${1:-server}"
if [[ $# -gt 0 ]]; then
  shift
fi

normalize_bool() {
  local value="${1:-false}"
  case "${value,,}" in
    1|true|yes|on) echo "true" ;;
    *) echo "false" ;;
  esac
}

if [[ "${command}" == "server" || "${command}" == "mcp" ]]; then
  port="${KIRI_PORT:-8765}"
  repo_root="${KIRI_REPO_ROOT:-/data/repo}"
  db_path="${KIRI_DB_PATH:-/app/var/index.duckdb}"
  security_config="${KIRI_SECURITY_CONFIG:-}"
  security_lock="${KIRI_SECURITY_LOCK:-}"
  allow_degrade="$(normalize_bool "${KIRI_ALLOW_DEGRADE:-false}")"
  force_reindex="$(normalize_bool "${KIRI_FORCE_REINDEX:-false}")"
  watch_mode="$(normalize_bool "${KIRI_WATCH:-false}")"
  debounce_ms="${KIRI_DEBOUNCE_MS:-500}"

  db_dir="$(dirname "${db_path}")"
  mkdir -p "${db_dir}"
  if [[ ! -d "${repo_root}" ]]; then
    echo "WARNING: KIRI_REPO_ROOT (${repo_root}) does not exist inside the container." >&2
  else
    if command -v git >/dev/null 2>&1; then
      git config --global --add safe.directory "${repo_root}" >/dev/null 2>&1 || true
    fi
  fi

  args=(
    "--repo" "${repo_root}"
    "--db" "${db_path}"
    "--port" "${port}"
  )

  if [[ "${allow_degrade}" == "true" ]]; then
    args+=("--allow-degrade")
  fi
  if [[ "${force_reindex}" == "true" ]]; then
    args+=("--reindex")
  fi
  if [[ "${watch_mode}" == "true" ]]; then
    args+=("--watch" "--debounce" "${debounce_ms}")
  fi
  if [[ -n "${security_config}" ]]; then
    args+=("--security-config" "${security_config}")
  fi
  if [[ -n "${security_lock}" ]]; then
    lock_dir="$(dirname "${security_lock}")"
    mkdir -p "${lock_dir}"
    args+=("--security-lock" "${security_lock}")
  fi

  exec node dist/src/server/main.js "${args[@]}" "$@"
fi

exec "${command}" "$@"
