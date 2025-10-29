import {
  assertSecurityBaseline,
  evaluateSecurityStatus,
  updateSecurityLock,
} from "../shared/security/config.js";

export interface BootstrapOptions {
  securityConfigPath?: string;
  securityLockPath?: string;
  allowWriteLock?: boolean;
}

export interface BootstrapReport {
  security: ReturnType<typeof evaluateSecurityStatus>;
}

export function bootstrapServer(options: BootstrapOptions = {}): BootstrapReport {
  const security = evaluateSecurityStatus(options.securityConfigPath, options.securityLockPath);
  if (!security.matches) {
    if (!security.lockHash && options.allowWriteLock) {
      updateSecurityLock(security.hash, options.securityLockPath);
      return {
        security: {
          ...security,
          lockHash: security.hash,
          matches: true,
        },
      };
    }
    assertSecurityBaseline(options.securityConfigPath, options.securityLockPath);
  }
  return { security };
}
