#!/usr/bin/env ts-node
import { loadServerConfig } from "../src/server/config.js";

function main(): void {
  try {
    const cfg = loadServerConfig();
    // Already validated in loadServerConfig; reaching here means OK.
    console.log("adaptiveK config OK", {
      enabled: cfg.adaptiveK.enabled,
      allowedSet: cfg.adaptiveK.allowedSet,
      kMin: cfg.adaptiveK.kMin,
      kMax: cfg.adaptiveK.kMax,
      kDefault: cfg.adaptiveK.kDefault,
      kWhenDisabled: cfg.adaptiveK.kWhenDisabled,
    });
    process.exit(0);
  } catch (error) {
    console.error("adaptiveK config validation failed", error);
    process.exit(1);
  }
}

main();
