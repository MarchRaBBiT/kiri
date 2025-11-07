# Containerized KIRI MCP Server

This directory contains everything required to build and run the KIRI MCP server inside Docker. The container bundles a production build of the server, installs the native dependencies needed for DuckDB and tree-sitter, and exposes the HTTP JSON-RPC interface on port `8765`.

## What’s Included

- `Dockerfile` – Multi-stage build that compiles the TypeScript sources and ships only the runtime artifacts.
- `entrypoint.sh` – Translates environment variables into CLI flags for `dist/src/server/main.js`.
- `docker-compose.example.yml` – Reference stack that mounts your repository, configuration, and DuckDB volume.

## Build the Image

Run the following from the repository root:

```bash
docker build -f container/Dockerfile -t kiri-mcp:latest .
```

The build installs dependencies with `pnpm`, compiles to `dist/`, prunes dev dependencies, and produces a runtime layer that only keeps the compiled server plus production dependencies.

## Run the Container Directly

Mount a repository (read-only) and a writable DuckDB volume, then expose the port:

```bash
docker run --rm \
  -p 8765:8765 \
  -e KIRI_REPO_ROOT=/data/repo \
  -e KIRI_DB_PATH=/app/var/index.duckdb \
  -v "$(pwd)/config:/app/config:ro" \
  -v "$(pwd)/var:/app/var" \
  -v /path/to/your/repo:/data/repo:ro \
  kiri-mcp:latest
```

The server boots, ensures the DuckDB index exists (creating it in `/app/var/index.duckdb`), and begins serving JSON-RPC requests on `localhost:8765`.

## docker-compose Example

Copy `container/docker-compose.example.yml` or reference it directly:

```bash
docker compose -f container/docker-compose.example.yml up --build
```

Update the `/absolute/path/to/your/repository` volume so the container can scan the codebase you want to expose via MCP. The compose file maps the default config and `var/` directories, enables watch mode, and restarts the service if it exits unexpectedly.

## Runtime Environment Variables

| Variable               | Default                 | Description                                                                                                  |
| ---------------------- | ----------------------- | ------------------------------------------------------------------------------------------------------------ |
| `KIRI_PORT`            | `8765`                  | Port that the HTTP JSON-RPC server listens on (also used by the health check).                               |
| `KIRI_REPO_ROOT`       | `/data/repo`            | Path **inside** the container that points to the repository being indexed. Mount your repo at this location. |
| `KIRI_DB_PATH`         | `/app/var/index.duckdb` | Location for the DuckDB database file. Mount `/app/var` to keep indexes between restarts.                    |
| `KIRI_ALLOW_DEGRADE`   | `false`                 | When `true`, enables degrade mode if scoring profiles fail to load.                                          |
| `KIRI_FORCE_REINDEX`   | `false`                 | Forces a full reindex on startup (equivalent to `--reindex`).                                                |
| `KIRI_WATCH`           | `false`                 | Enables file watch + incremental reindexing. Requires the repo mount to support inotify (bind mounts do).    |
| `KIRI_DEBOUNCE_MS`     | `500`                   | Debounce duration (milliseconds) applied when watch mode is enabled.                                         |
| `KIRI_SECURITY_CONFIG` | _(unset)_               | Absolute path to `config/security.yml` inside the container. Set if you need stricter ACL enforcement.       |
| `KIRI_SECURITY_LOCK`   | _(unset)_               | Optional path for the generated security lock file. Mount it if you need to persist lock state.              |

Any extra arguments passed to `docker run ... kiri-mcp:latest <args>` are forwarded to the server. For example, `docker run ... kiri-mcp:latest server --allow-degrade` is equivalent to setting `KIRI_ALLOW_DEGRADE=true`.

## Tips

- The container runs as the `node` user (UID 1000). Ensure host volumes grant that UID read access to the repo mount and write access to `/app/var` (e.g., `chown -R 1000:1000 var`).
- Health checks hit `http://127.0.0.1:8765/metrics`. If you change `KIRI_PORT`, update your orchestration health-check port accordingly.
- Keep `config/` mounted read-only so security policies, deny lists, and scoring profiles stay versioned alongside your source.

For deeper customization (e.g., publishing to a registry, adding diagnostics stages), extend `container/Dockerfile` or add new compose overlays in this directory.
