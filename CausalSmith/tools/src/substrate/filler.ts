// CausalSmith/tools/src/substrate/filler.ts
import { runCodex as realRunCodex } from "../shared/codex.js";
import { MODELS } from "../models.js";
import { mapLimit } from "../presentation/gates.js";
import { logAgentCall } from "./log.js";
import { buildFillerPrompt } from "./prompts.js";
import type { CodexPrompt, FillerReport } from "./types.js";

export interface FillerArgs { repoRoot: string; runDir: string; round: number; leanDir: string; modulePrefix: string; prompts: CodexPrompt[]; concurrency: number }
export interface FillerDeps { runCodex: typeof realRunCodex }

export async function runFillers(
  args: FillerArgs,
  deps: FillerDeps = { runCodex: realRunCodex },
): Promise<FillerReport[]> {
  return mapLimit(args.prompts, args.concurrency, async (p): Promise<FillerReport> => {
    const prompt = buildFillerPrompt({ leanDir: args.leanDir, modulePrefix: args.modulePrefix, prompt: p });
    const t0 = Date.now();
    let stdout = "";
    let ok = false;
    let errMsg: string | undefined;
    try {
      const res = await deps.runCodex({
        prompt,
        model: MODELS.codexKernel,
        reasoningEffort: "medium",
        cwd: args.repoRoot,
      });
      stdout = res.stdout;
      ok = true;
    } catch (err) {
      errMsg = err instanceof Error ? err.message : String(err);
    }
    await logAgentCall(args.runDir, {
      agent: "filler", round: args.round, callId: p.id, model: MODELS.codexKernel,
      prompt, promptBytes: Buffer.byteLength(prompt), rawOutput: stdout,
      parseError: errMsg, ok, durationMs: Date.now() - t0,
    });
    return { id: p.id, ok, summary: ok ? stdout.trim().slice(-600) : errMsg ?? "failed" };
  });
}
