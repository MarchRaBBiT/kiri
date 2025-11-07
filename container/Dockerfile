# syntax=docker/dockerfile:1.6

ARG NODE_VERSION=20-bookworm

FROM node:${NODE_VERSION} AS base
ENV PNPM_HOME=/pnpm
ENV PATH="${PNPM_HOME}:${PATH}"
RUN corepack enable

FROM base AS deps
WORKDIR /app
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    ca-certificates \
    git \
    python3 \
    make \
    g++ \
  && rm -rf /var/lib/apt/lists/*
COPY package.json pnpm-lock.yaml ./
RUN pnpm install --frozen-lockfile

FROM deps AS builder
COPY tsconfig.json tsconfig.build.json ./
COPY src ./src
COPY scripts ./scripts
COPY config ./config
COPY sql ./sql
COPY types ./types
RUN pnpm run build
RUN pnpm prune --prod

FROM node:${NODE_VERSION} AS runtime
ENV NODE_ENV=production \
    KIRI_PORT=8765 \
    KIRI_REPO_ROOT=/data/repo \
    KIRI_DB_PATH=/app/var/index.duckdb \
    KIRI_ALLOW_DEGRADE=false \
    KIRI_FORCE_REINDEX=false \
    KIRI_WATCH=false \
    KIRI_DEBOUNCE_MS=500
WORKDIR /app
RUN apt-get update \
  && apt-get install -y --no-install-recommends curl ca-certificates git \
  && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/node_modules ./node_modules
COPY --from=builder /app/dist ./dist
COPY --from=builder /app/config ./config
COPY --from=builder /app/sql ./sql
COPY package.json ./package.json
COPY container/entrypoint.sh /entrypoint.sh
RUN chmod +x /entrypoint.sh \
  && mkdir -p /app/var /data/repo \
  && chown -R node:node /app /data
USER node
VOLUME ["/app/var", "/data/repo"]
EXPOSE 8765
HEALTHCHECK --interval=30s --timeout=5s --start-period=45s --retries=3 CMD curl -fsS http://127.0.0.1:8765/metrics || exit 1
ENTRYPOINT ["/entrypoint.sh"]
CMD ["server"]
