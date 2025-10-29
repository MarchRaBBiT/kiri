import { readFileSync, readdirSync, statSync } from "node:fs";
import { join, relative as relativePath, resolve } from "node:path";

export interface DegradeState {
  active: boolean;
  reason: string | null;
  since: Date | null;
}

export interface DegradeSearchResult {
  path: string;
  preview: string;
  matchLine: number;
}

export class DegradeController {
  private state: DegradeState = { active: false, reason: null, since: null };
  private readonly repoRoot: string;

  constructor(repoRoot: string) {
    this.repoRoot = resolve(repoRoot);
  }

  get current(): DegradeState {
    return this.state;
  }

  enable(reason: string): void {
    if (this.state.active) {
      return;
    }
    this.state = { active: true, reason, since: new Date() };
  }

  disable(): void {
    this.state = { active: false, reason: null, since: null };
  }

  async withResource<T>(operation: () => Promise<T>, reason: string): Promise<T> {
    if (this.state.active) {
      throw new Error(
        `Server is running in degrade mode: ${this.state.reason ?? "unknown"}. Only files.search is available.`
      );
    }
    try {
      const result = await operation();
      return result;
    } catch (error) {
      this.enable(reason);
      throw error;
    }
  }

  search(query: string, limit = 20): DegradeSearchResult[] {
    const tokens = query.split(/\s+/).filter((token) => token.length > 0);
    if (tokens.length === 0) {
      return [];
    }
    const results: DegradeSearchResult[] = [];
    this.walkFiles(this.repoRoot, (absolutePath, relativeFile) => {
      if (results.length >= limit) {
        return;
      }
      const content = readFileSync(absolutePath, "utf8");
      const lines = content.split(/\r?\n/);
      const matchIndex = lines.findIndex((line) => tokens.every((token) => line.includes(token)));
      if (matchIndex >= 0) {
        const preview = lines.slice(matchIndex, matchIndex + 3).join("\n");
        results.push({ path: relativeFile, preview, matchLine: matchIndex + 1 });
      }
    });
    return results;
  }

  private walkFiles(root: string, visitor: (absolute: string, relative: string) => void): void {
    const entries = readdirSync(root);
    for (const entry of entries) {
      const absolute = join(root, entry);
      const relative = relativePath(this.repoRoot, absolute);
      const stats = statSync(absolute);
      if (stats.isDirectory()) {
        this.walkFiles(absolute, visitor);
      } else if (stats.isFile()) {
        visitor(absolute, relative);
      }
    }
  }
}
