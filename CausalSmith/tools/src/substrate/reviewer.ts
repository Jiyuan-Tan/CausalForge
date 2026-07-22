// CausalSmith/tools/src/substrate/reviewer.ts
import { runCodex as realRunCodex } from "../shared/codex.js";
import { expectStringJsonOutput } from "../shared/codex_json.js";
import { logAgentCall } from "./log.js";
import { buildReviewerPrompt } from "./prompts.js";
import { parseReviewVerdict, type ReviewVerdict } from "./types.js";

export interface ReviewerArgs { repoRoot: string; runDir: string; round: number; slug: string; requirement: string; leanDir: string; modulePrefix: string }
export interface ReviewerDeps { runCodex: typeof realRunCodex }

export async function runReviewer(
  args: ReviewerArgs,
  deps: ReviewerDeps = { runCodex: realRunCodex },
): Promise<ReviewVerdict> {
  const prompt = buildReviewerPrompt(args);
  const t0 = Date.now();
  let stdout = "";
  let parsed: ReviewVerdict | undefined;
  let parseError: string | undefined;
  try {
    const res = await deps.runCodex({ prompt, cwd: args.repoRoot });
    stdout = res.stdout;
    parsed = parseReviewVerdict(expectStringJsonOutput(stdout));
    return parsed;
  } catch (err) {
    parseError = err instanceof Error ? err.message : String(err);
    throw err;
  } finally {
    await logAgentCall(args.runDir, {
      agent: "reviewer", round: args.round, callId: "main", model: "codex",
      prompt, promptBytes: Buffer.byteLength(prompt), rawOutput: stdout,
      parsed, parseError, ok: parseError === undefined, durationMs: Date.now() - t0,
    });
  }
}
