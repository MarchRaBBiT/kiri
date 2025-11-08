import { getLanguageAnalyzer } from "./languages/index.js";
import type { AnalysisResult } from "./languages/types.js";

export type { SymbolRecord, SnippetRecord, DependencyRecord } from "./languages/types.js";
export { buildFallbackSnippet } from "./languages/types.js";

export async function analyzeSource(
  pathInRepo: string,
  lang: string | null,
  content: string,
  fileSet: Set<string>,
  workspaceRoot?: string
): Promise<AnalysisResult> {
  const analyzer = getLanguageAnalyzer(lang ?? "");
  if (!analyzer) {
    return { symbols: [], snippets: [], dependencies: [] };
  }

  return await analyzer.analyze({
    pathInRepo,
    content,
    fileSet,
    language: lang,
    workspaceRoot,
  });
}
