// Formalization Codex review helpers. Extracted from pipeline_stages.ts in Step 2.3 of the three-submodules refactor.

import { existsSync } from "node:fs";
import { MODEL_PLAN } from "../constants.js";
import { type ReviewResult } from "../judgment.js";
import { coreJsonPath } from "../discovery/stages/d0_core.js";
import type { PipelineContext, StateJson } from "../types.js";
import {
  artifactPaths,
  baseBrief,
  bookkeepingPolicyBlock,
  parseReview,
  readIfExists,
  readRequired,
  readPrompt,
  type StageDeps,
} from "../pipeline_support.js";
import { dispatchAgent } from "../framework/agent_dispatch.js";

const REVIEW_MODEL_PLAN: Record<"1.5" | "2.5", { model: string; effort: "medium" | "high" | "xhigh" }> = {
  "1.5": { model: MODEL_PLAN.stage1_5.model, effort: MODEL_PLAN.stage1_5.effort },
  "2.5": { model: MODEL_PLAN.stage2_5.model, effort: MODEL_PLAN.stage2_5.effort },
};

export async function reviewWithCodex(
  args: { ctx: PipelineContext; state: StateJson; deps: StageDeps },
  promptName: string,
  stageLabel: "1.5" | "2.5",
  instruction: string,
): Promise<ReviewResult> {
  const paths = artifactPaths(args.ctx, args.state);
  // F1.5 reviews the formalization PLAN against the typed core (reuse-soundness) —
  // both are REQUIRED (fail loud; see readRequired). F2.5 reviews the note; the .md
  // is OPTIONAL by design (retired upstream of F3 on modern runs) and injected only
  // when present.
  const contextBlock =
    stageLabel === "1.5"
      ? `Formalization plan (plan.json — the subject of review):\n${await readRequired(paths.plan, "F1.5 review")}\n\nTyped core JSON (the structural ground truth):\n${await readRequired(coreJsonPath(args.ctx), "F1.5 review")}\n`
      : existsSync(paths.md)
        ? `Markdown:\n${await readIfExists(paths.md)}\n`
        : "";
  // The prose .tex is irrelevant to the F1.5 reuse-soundness review (structure
  // comes from the core); suppress it there to save tokens. 2.5 keeps it (required).
  const texBlock = stageLabel === "1.5" ? "" : `TeX:\n${await readRequired(paths.tex, "F2.5 review")}`;
  const noveltyHeader = args.ctx.noveltyTarget
    ? `novelty_target: ${args.ctx.noveltyTarget}\n`
    : "";
  // Surface loop counters that the prompt's relaxation rules consult — currently
  // `scaffold_redirects` (read by stage 2.5 H.G to relax G.ii/G.iii on post-Stage-3
  // rewrites where the scaffolder may have carried over a real proof body).
  const loopCounters =
    stageLabel === "2.5"
      ? `Loop counters: scaffold_redirects=${args.state.flags.scaffold_redirect_count ?? 0}\n`
      : "";
  // Formalization gates (1.5/2.5) consult the shared bookkeeping policy so a
  // regularity side-condition added by F1/F2 is NOT mis-flagged as illegitimate
  // assumption-strengthening.
  const bookkeepingBlock =
    stageLabel === "1.5" || stageLabel === "2.5" ? `\n${bookkeepingPolicyBlock()}\n` : "";
  const prompt = [
    (await readPrompt(args.ctx, promptName)) + bookkeepingBlock,
    "",
    baseBrief(args.ctx, args.state),
    "",
    noveltyHeader + instruction,
    "",
    loopCounters,
    texBlock,
    "",
    contextBlock,
    "Lean files are under the Lean artifact directory; read them as needed.",
    "RETURN ONLY ReviewResult JSON.",
  ].join("\n");
  const plan = REVIEW_MODEL_PLAN[stageLabel];
  // lean-lsp is default-ON for every codex call (see shared/codex.ts) so the
  // reviewer's `lean_multi_attempt` vacuity probes are actually available.
  const out = await dispatchAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: stageLabel,
    label: `F${stageLabel} review (${promptName})`,
    prompt,
    promptSources:
      stageLabel === "1.5"
        ? [promptName, "baseBrief", paths.plan, coreJsonPath(args.ctx)]
        : [promptName, "baseBrief", ...(existsSync(paths.md) ? [paths.md] : []), paths.tex],
    model: plan.model,
    reasoningEffort: plan.effort,
  });
  return parseReview(out.stdout);
}
