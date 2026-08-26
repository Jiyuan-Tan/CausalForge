import { appendFile, readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";

export interface ModelTokenUsage {
  input_tokens: number;
  cached_input_tokens: number;
  cache_creation_input_tokens: number;
  output_tokens: number;
  reasoning_output_tokens: number;
  total_tokens: number;
}

export interface TokenUsageRecord {
  timestamp: string;
  provider: "codex" | "claude";
  model: string;
  stage: string;
  duration_ms: number;
  success: boolean;
  usage: ModelTokenUsage | null;
}

export interface ProviderTokenSummary extends ModelTokenUsage {
  calls: number;
  calls_missing_usage: number;
}

export interface PaperTokenUsageSummary {
  complete: boolean;
  orchestrator_tokens: number | null;
  pipeline_codex: ProviderTokenSummary;
  pipeline_claude: ProviderTokenSummary;
  total_tokens_consumed: number | null;
}

export const TOKEN_USAGE_LEDGER = "token_usage.jsonl";
export const TOKEN_USAGE_SUMMARY = "token_usage_summary.json";
export const TOKEN_USAGE_INCOMPLETE = "token_usage_incomplete";

const zeroProvider = (): ProviderTokenSummary => ({
  calls: 0,
  calls_missing_usage: 0,
  input_tokens: 0,
  cached_input_tokens: 0,
  cache_creation_input_tokens: 0,
  output_tokens: 0,
  reasoning_output_tokens: 0,
  total_tokens: 0,
});

export async function appendTokenUsageRecord(runDir: string, record: TokenUsageRecord): Promise<void> {
  await appendFile(path.join(runDir, TOKEN_USAGE_LEDGER), `${JSON.stringify(record)}\n`, "utf8");
}

export async function markTokenUsageIncomplete(runDir: string, reason: string): Promise<void> {
  await appendFile(
    path.join(runDir, TOKEN_USAGE_INCOMPLETE),
    `${new Date().toISOString()} ${reason}\n`,
    "utf8",
  );
}

export async function summarizeTokenUsage(
  runDir: string,
  orchestratorTokens?: number,
): Promise<PaperTokenUsageSummary> {
  const ledger = path.join(runDir, TOKEN_USAGE_LEDGER);
  const codex = zeroProvider();
  const claude = zeroProvider();
  if (existsSync(ledger)) {
    const lines = (await readFile(ledger, "utf8")).split(/\r?\n/).filter((line) => line.trim());
    for (const line of lines) {
      const record = JSON.parse(line) as TokenUsageRecord;
      const target = record.provider === "codex" ? codex : claude;
      target.calls += 1;
      if (!record.usage) {
        target.calls_missing_usage += 1;
        continue;
      }
      for (const key of [
        "input_tokens",
        "cached_input_tokens",
        "cache_creation_input_tokens",
        "output_tokens",
        "reasoning_output_tokens",
        "total_tokens",
      ] as const) target[key] += record.usage[key];
    }
  }
  const orch = orchestratorTokens === undefined ? null : orchestratorTokens;
  const complete = existsSync(ledger) && !existsSync(path.join(runDir, TOKEN_USAGE_INCOMPLETE)) && orch !== null &&
    codex.calls_missing_usage === 0 && claude.calls_missing_usage === 0;
  return {
    complete,
    orchestrator_tokens: orch,
    pipeline_codex: codex,
    pipeline_claude: claude,
    total_tokens_consumed: complete
      ? orch! + codex.total_tokens + claude.total_tokens
      : null,
  };
}

export async function writeTokenUsageSummary(runDir: string, summary: PaperTokenUsageSummary): Promise<void> {
  await writeFile(
    path.join(runDir, TOKEN_USAGE_SUMMARY),
    `${JSON.stringify(summary, null, 2)}\n`,
    "utf8",
  );
}

export function tokenUsageYaml(summary: PaperTokenUsageSummary): string {
  const value = (n: number | null) => n === null ? "null" : String(n);
  return [
    "token_usage:",
    `  complete: ${summary.complete}`,
    `  orchestrator_tokens: ${value(summary.orchestrator_tokens)}`,
    `  pipeline_codex_tokens: ${summary.pipeline_codex.total_tokens}`,
    `  pipeline_claude_tokens: ${summary.pipeline_claude.total_tokens}`,
    `  total_tokens_consumed: ${value(summary.total_tokens_consumed)}`,
  ].join("\n");
}

export async function patchReadmeTokenUsage(
  readmePath: string,
  summary: PaperTokenUsageSummary,
): Promise<void> {
  const text = await readFile(readmePath, "utf8");
  const block = `${tokenUsageYaml(summary)}\n`;
  const pattern = /^token_usage:\n(?:  .*\n)*/m;
  const next = pattern.test(text)
    ? text.replace(pattern, block)
    : text.replace(/^banked_on:/m, `${block}banked_on:`);
  await writeFile(readmePath, next, "utf8");
}
