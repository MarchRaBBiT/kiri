import type { AssayConfig } from "external/assay-kit/src/config/types.ts";

const config: AssayConfig = {
  baseline: {
    providers: {
      localGit: {
        module: "builtin:git",
        trusted: true,
        options: {
          repoPath: ".",
          storagePath: "baselines",
          maxVersions: 20,
        },
      },
    },
    targets: {
      "vscode-golden": {
        provider: "localGit",
        scope: {
          dataset: "vscode",
          type: "golden",
        },
        defaultThresholdProfileId: "vscode-tight",
      },
    },
    thresholds: {
      "vscode-tight": {
        rules: [
          {
            metric: "precision",
            direction: "higher",
            strategy: "relative",
            limit: 0.05,
            label: "Precision P@10",
          },
          {
            metric: "latencyMs",
            direction: "lower",
            strategy: "relative",
            limit: 0.1,
            label: "Avg latency",
          },
          {
            metric: "timeToFirstUseful",
            direction: "lower",
            strategy: "absolute",
            limit: 0.5,
            label: "TTFU (s)",
          },
        ],
        fallback: "fail",
      },
    },
  },
};

export default config;
