export interface SymbolRecord {
  symbolId: number;
  name: string;
  kind: string;
  rangeStartLine: number;
  rangeEndLine: number;
  signature: string | null;
  doc: string | null;
}

export interface SnippetRecord {
  startLine: number;
  endLine: number;
  symbolId: number | null;
}

export interface DependencyRecord {
  dstKind: "path" | "package";
  dst: string;
  rel: string;
}

export interface AnalysisResult {
  symbols: SymbolRecord[];
  snippets: SnippetRecord[];
  dependencies: DependencyRecord[];
}

export interface LanguageAnalyzerParams {
  pathInRepo: string;
  content: string;
  fileSet: Set<string>;
  language?: string | null | undefined;
  workspaceRoot?: string | undefined;
}

export interface LanguageAnalyzer {
  analyze(params: LanguageAnalyzerParams): Promise<AnalysisResult>;
}

export function buildSnippetsFromSymbols(symbols: SymbolRecord[]): SnippetRecord[] {
  return symbols.map((symbol) => ({
    startLine: symbol.rangeStartLine,
    endLine: symbol.rangeEndLine,
    symbolId: symbol.symbolId,
  }));
}

export function buildFallbackSnippet(totalLines: number): SnippetRecord {
  return { startLine: 1, endLine: totalLines, symbolId: null };
}
