import { analyzeDartSource } from "../dart/analyze.js";

import {
  type AnalysisResult,
  type LanguageAnalyzer,
  type LanguageAnalyzerParams,
} from "./types.js";

export const dartAnalyzer: LanguageAnalyzer = {
  async analyze({
    pathInRepo,
    content,
    workspaceRoot,
  }: LanguageAnalyzerParams): Promise<AnalysisResult> {
    if (!workspaceRoot) {
      console.warn(
        `[analyzeSource] workspaceRoot required for Dart analysis, skipping ${pathInRepo}`
      );
      return { symbols: [], snippets: [], dependencies: [] };
    }

    return await analyzeDartSource(pathInRepo, content, workspaceRoot);
  },
};
