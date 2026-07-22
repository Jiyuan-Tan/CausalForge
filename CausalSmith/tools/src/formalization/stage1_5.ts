// Discovery Stage 1.5 (F1.5) — the REUSE-SOUNDNESS review boundary.
//
// The deterministic plan gate (plan_gate.ts) owns one-to-one coverage / kind /
// member / hyp-closure / reuse-existence / module checks — it replaces the prose-
// faithfulness checks (F/Q/N/L/P) the old F1.5 ran against the .tex. F1.5 now runs
// that gate as a pre-lint (a violation routes straight back to F1, no LLM spent),
// then an LLM reviews only the genuinely hard judgment: does each chosen reuse decl
// actually type-fit at the right abstraction level, and is each define-local
// justified. See CausalSmith/doc/research/F1_F2_PLAN_REDESIGN.md §9.

import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import type { PipelineContext, StageResult, StateJson } from "../types.js";
import type { ReviewResult } from "../judgment.js";
import { type StageDeps, artifactPaths, readRequired } from "../pipeline_support.js";
import { reviewWithCodex } from "../pipeline_stages.js";
import { runReviewBoundary } from "../shared/intervention_routing.js";
import { runStage1 } from "./stage1.js";
import { propagateTheoremReview } from "./theorem_review.js";
import { coreJsonPath } from "../discovery/stages/d0_core.js";
import { CoreSchema } from "../discovery/core/schema.js";
import { runPlanGate } from "../formalization/plan/plan_gate.js";
import { createRetrieval } from "../formalization/reuse_retrieval.js";

/** Run the deterministic plan gate over the just-written plan. Returns a synthetic
 *  `revise` verdict (routing F1 to fix the mechanical violations) when it fails, or
 *  `null` when the plan is gate-clean. core.json is REQUIRED (throws via
 *  readRequired if missing/unparseable); a missing plan.json still routes back to
 *  F1 as a synthetic revise. */
export async function planGatePrelint(
  args: { ctx: PipelineContext; state: StateJson },
  planPath: string,
): Promise<ReviewResult | null> {
  const corePath = coreJsonPath(args.ctx);
  // The deterministic plan gate is the structural hard-fail; silently skipping it
  // when core.json is missing/unparseable let a plan advance ungated. Fail loud.
  const coreText = await readRequired(corePath, "F1.5 plan gate");
  let core;
  try {
    core = CoreSchema.parse(JSON.parse(coreText));
  } catch (err) {
    throw new Error(
      `F1.5 plan gate: core.json at ${corePath} failed to parse/validate: ${err instanceof Error ? err.message : String(err)} (legacy pre-typed-core run? re-run discovery (D0) to regenerate core.json)`,
    );
  }
  // A core exists but F1 wrote no plan → route back to F1 to author it.
  if (!existsSync(planPath)) {
    return {
      status: "revise",
      classification: "plan-gate",
      perItemFindings: [{ label: "plan.json", verdict: "FLAG-missing", one_line: `F1 did not write a plan at ${planPath}` }],
      verbatim_critique: `No plan.json found at ${planPath}. Author the formalization plan — one node entry per core node (assumptions ∪ definitions ∪ statements), plus the env S-block(s).`,
    };
  }
  let planObj: unknown;
  try {
    planObj = JSON.parse(await readFile(planPath, "utf8"));
  } catch (err) {
    return {
      status: "revise",
      classification: "plan-gate",
      perItemFindings: [{ label: "plan.json", verdict: "FLAG-parse", one_line: String(err) }],
      verbatim_critique: "plan.json is not valid JSON; re-emit it as a single well-formed object.",
    };
  }
  let knownDecls: Set<string> | undefined;
  try {
    const lib = createRetrieval(args.ctx.repoRoot).library;
    if (lib) knownDecls = new Set(lib.entries.map((e) => e.name));
  } catch {
    knownDecls = undefined;
  }
  if (!knownDecls) {
    console.warn(
      "[causalsmith] library index unavailable (doc/library_index.json missing/unreadable) — the P5 reuse-existence check is SKIPPED this pass; hallucinated reuse decls will surface only at compile. Run `lake build && lake exe library_index`.",
    );
  }
  const gate = runPlanGate(planObj, core, { knownDecls });
  if (gate.ok) return null;
  const shown = gate.violations.slice(0, 40);
  return {
    status: "revise",
    classification: "plan-gate",
    perItemFindings: shown.map((v) => ({ label: v.where, verdict: `FLAG-${v.code}`, one_line: v.message })),
    verbatim_critique:
      "The plan failed the deterministic gate (one-to-one coverage / kind / member / hyp-closure / reuse-existence / module). Fix these mechanical violations in plan.json, keeping every core node mapped exactly once:\n  - " +
      shown.map((v) => `${v.code} @ ${v.where}: ${v.message}`).join("\n  - "),
  };
}

export async function runStage1_5(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  return runReviewBoundary({
    ctx: args.ctx,
    state: args.state,
    deps: args.deps,
    boundary: "stage_1.5_to_1",
    stage: "1.5",
    cap: 3,
    // The F1 plan + F1.5 reuse-soundness review settle into ONE consolidated
    // CKPT 1: a PASS halts here for the orchestrator's DEPTH + REUSE + fidelity
    // audit, rather than flowing straight into F2 scaffolding.
    checkpointOnPass:
      "CONSOLIDATED CKPT 1 (F1 plan + F1.5 reuse-soundness passed). Audit DEPTH + REUSE + statement-vs-math fidelity before --resume into F2.",
    heuristic:
      "plan_gate violations + reuse-fit / abstraction-level flags route to stage_1 (re-plan the flagged nodes); a defect rooted in the core's math routes to stage_0; unresolved ambiguity routes to user.",
    producer: (prior, attempt, intervention) =>
      runStage1({ ...args, priorReview: prior, attempt, intervention }),
    reviewer: async () => {
      const paths = artifactPaths(args.ctx, args.state);
      // 1. Deterministic gate pre-lint — must pass before the LLM runs.
      const gateReview = await planGatePrelint(args, paths.plan);
      if (gateReview) {
        propagateTheoremReview(args.state, gateReview, "1.5");
        return gateReview;
      }
      // 2. LLM reuse-soundness review over the gate-clean plan.
      const review = await reviewWithCodex(
        args,
        "stage1_5_reuse_soundness.txt",
        "1.5",
        "Review the plan's per-node reuse decisions for type-fit and abstraction level; the deterministic gate has already passed (coverage/kind/member/hyp/reuse-existence/module are settled — do NOT re-litigate them).",
      );
      propagateTheoremReview(args.state, review, "1.5");
      return review;
    },
  });
}
