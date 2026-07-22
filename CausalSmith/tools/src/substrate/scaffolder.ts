// CausalSmith/tools/src/substrate/scaffolder.ts
import { runCodex as realRunCodex } from "../shared/codex.js";
import { MODELS } from "../models.js";
import { expectStringJsonOutput } from "../shared/codex_json.js";
import { logAgentCall } from "./log.js";
import { buildScaffolderPrompt } from "./prompts.js";
import { parseScaffolderOutput, type ScaffolderOutput, type RoundReport, type ReviewVerdict } from "./types.js";

export interface ScaffolderArgs {
  repoRoot: string; runDir: string; slug: string; requirement: string; leanDir: string; modulePrefix: string;
  planMarkdown: string | null; lastReport: RoundReport | null; lastReview: ReviewVerdict | null;
  buildRounds: number; buildCap: number;
}
export interface ScaffolderDeps { runCodex: typeof realRunCodex }

export async function runScaffolder(
  args: ScaffolderArgs,
  deps: ScaffolderDeps = { runCodex: realRunCodex },
): Promise<ScaffolderOutput> {
  const prompt = buildScaffolderPrompt(args);
  const t0 = Date.now();
  let stdout = "";
  let parsed: ScaffolderOutput | undefined;
  let parseError: string | undefined;
  try {
    const result = await deps.runCodex({
      prompt,
      model: MODELS.codexKernel,
      reasoningEffort: "high",
      cwd: args.repoRoot,
    });
    stdout = result.stdout;
    parsed = parseScaffolderOutput(expectStringJsonOutput(stdout));
    return parsed;
  } catch (err) {
    parseError = err instanceof Error ? err.message : String(err);
    throw err;
  } finally {
    await logAgentCall(args.runDir, {
      agent: "scaffolder", round: args.buildRounds + 1, callId: "main", model: MODELS.codexKernel,
      prompt, promptBytes: Buffer.byteLength(prompt), rawOutput: stdout,
      parsed, parseError, ok: parseError === undefined, durationMs: Date.now() - t0,
    });
  }
}
