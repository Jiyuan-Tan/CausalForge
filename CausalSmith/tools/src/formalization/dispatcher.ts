// Formalization dispatcher. The graph-driven proof-review loop is the sole proof path:
// it runs in the F2.5 slot and owns the statement gate, proof fill, unused-hyp lint, and
// dual-model convergence. It logs F2.5/F3/F3.5/F4 at their real phase boundaries and advances
// directly to F5; the legacy handlers remain only for old/manual stage pointers.
// The legacy split-stage system was retired.

import type { PipelineContext, Stage, StageResult, StateJson } from "../types.js";
import { artifactPaths, type StageDeps } from "../pipeline_support.js";
import { coreJsonPath } from "../discovery/stages/d0_core.js";
import { runProofReviewLoop, writeRunBarrel, type LoopOutcome } from "./proof_review_loop.js";
import { startSharedLeanLsp } from "../shared/lean_lsp_server.js";
import { runStage1 } from "./stage1.js";
import { runStage1_5 } from "./stage1_5.js";
import { runStage2 } from "./stage2.js";
import { runStage5 } from "./stage5.js";
import { applyInterventionRoute, resetFormalizationLoopCounters } from "../shared/intervention_routing.js";
import type { Intervention } from "../judgment.js";

/** Per-node cap on F3→D0 rewinds: after this many witnessed bounces of the SAME node, stop
 *  auto-rewinding and checkpoint for orchestrator approval (a node that keeps coming back is not
 *  self-resolving). Mirrors the stage1_rewinds / theorem_splits caps. */
const REDO_MATH_MAX = 3;

const PROOF_REVIEW_BYPASS_STAGES = new Set<Stage>(["3", "3.5", "4", "5"]);

/**
 * Persist the proof-review boundary outcome on the shared state object. An
 * escalation immediately rewinds the durable completion cursor to F2; only a
 * genuine loop completion clears the unresolved marker.
 */
export function recordProofReviewOutcome(state: StateJson, outcome: LoopOutcome): void {
  if (outcome.status === "escalate") {
    state.flags.proof_review_escalation_pending = {
      route: outcome.route,
      reason: outcome.reason,
    };
    state.stage_completed = "2";
    return;
  }
  state.flags.proof_review_escalation_pending = null;
}

/**
 * Fail closed against stale/manual stage pointers after a proof-review
 * escalation. `advance:false` is essential for F5: it prevents pipeline.ts
 * from treating this checkpoint as a completed F5 and firing the post-F5 hook.
 */
export function unresolvedProofReviewGuard(state: StateJson, stage: Stage): StageResult | null {
  const pending = state.flags.proof_review_escalation_pending;
  if (!pending || !PROOF_REVIEW_BYPASS_STAGES.has(stage)) return null;
  state.stage_completed = "2";
  return {
    stage,
    status: "checkpoint",
    advance: false,
    completedStage: "2",
    message:
      `PROOF-REVIEW ESCALATION UNRESOLVED [${pending.route}]: cannot enter F${stage}; ` +
      `rewound to completedStage F2 so resume re-enters F2.5. ${pending.reason}`,
  };
}

export async function runFormalizationStage(args: {
  ctx: PipelineContext;
  state: StateJson;
  stage: Stage;
  deps: StageDeps;
}): Promise<StageResult | null> {
  const proofReviewGuard = unresolvedProofReviewGuard(args.state, args.stage);
  if (proofReviewGuard) return proofReviewGuard;
  switch (args.stage) {
    case "1":
      return runStage1({ ctx: args.ctx, state: args.state, deps: args.deps });
    case "1.5":
      return runStage1_5({ ctx: args.ctx, state: args.state, deps: args.deps });
    case "2":
      return runStage2({ ctx: args.ctx, state: args.state, deps: args.deps });
    case "2.5":
      // The proof-review loop runs here and owns the entire proof/review path.
      return runProofReviewLoopStage(args);
    case "3":
    case "3.5":
    case "4":
      return {
        stage: args.stage,
        status: "skipped",
        message: "legacy pass-through: this phase is executed and logged inside the combined proof-review loop",
      };
    case "5":
      return runStage5({ ctx: args.ctx, state: args.state, deps: args.deps });
    default:
      return null;
  }
}

/** A pre-set `flags.scaffold_redirect` (hand-injected, or left by an interrupted run)
 *  must be consumed by an F2 pass BEFORE the proof-review loop reviews the stale
 *  scaffold — a plain `--resume` at stage_completed="2" otherwise never applies it.
 *  Returns null to proceed into the loop, or the non-completed F2 result (fail closed).
 *  `scaffoldFn` is injectable for tests. */
export async function consumePendingScaffoldRedirect(
  args: { ctx: PipelineContext; state: StateJson; deps: StageDeps },
  scaffoldFn: typeof runStage2 = runStage2,
): Promise<StageResult | null> {
  if (!args.state.flags.scaffold_redirect) return null;
  console.warn("[F] pending flags.scaffold_redirect found at F2.5 entry — running an F2 pass to consume it before the review loop.");
  const result = await scaffoldFn({ ctx: args.ctx, state: args.state, deps: args.deps });
  if (result.status !== "completed") return result;
  return null; // runStage2 self-clears the flag on completion
}

/**
 * Run the graph-driven proof-review loop in the F2.5 slot. On convergence it completes through
 * stage "4" (so the pipeline advances directly to F5); on escalation it checkpoints with the route +
 * reason for the Claude meta-orchestrator to intervene (build-substrate / hint / fix-source /
 * bank-partial / abandon) and `--resume`.
 */
async function runProofReviewLoopStage(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  const pendingRedirect = await consumePendingScaffoldRedirect(args);
  if (pendingRedirect) return pendingRedirect;
  const paths = artifactPaths(args.ctx, args.state);
  // Boot ONE shared streamable-HTTP `lean-lsp-mcp` (= one `lake serve`) for the whole proof
  // loop so the reviewer + per-target fillers reuse a single WARM server instead of each codex
  // call cold-starting its own stdio lean-lsp. On a loaded host a fresh per-call cold-start
  // re-elaborates the import closure for minutes, blows past codex's lean-lsp MCP timeout, and
  // the per-call servers proliferate — the bare `--resume` path used to hit exactly this wedge
  // (`f3_loop.ts` already boots a shared one; this brings `--resume` to parity). Only boot when a
  // launcher hasn't already exported a URL; non-fatal on failure (falls back to per-process stdio
  // lean-lsp — correct, just slower). `leanLspCodexFlags` (codex.ts) reads the env var per call.
  let shared: Awaited<ReturnType<typeof startSharedLeanLsp>> | null = null;
  const ownsSharedLeanLsp = !process.env.CAUSALSMITH_SHARED_LEAN_LSP_URL?.trim();
  if (ownsSharedLeanLsp) {
    try {
      shared = await startSharedLeanLsp(args.ctx.repoRoot);
      process.env.CAUSALSMITH_SHARED_LEAN_LSP_URL = shared.url;
    } catch {
      shared = null;
    }
  }
  try {
  // Refresh the per-run barrel at F-stage entry so the whole run stays ONE buildable target.
  // Research modules are unreachable from the top-level CausalSmith.lean barrel, so the DEFAULT
  // lake target skips them and reports green on stale oleans. Best-effort — never sink a run.
  try {
    const barrel = await writeRunBarrel(args.ctx.repoRoot, paths.leanDir);
    if (barrel) console.warn(`[F] run barrel refreshed: ${barrel}`);
  } catch (e) {
    console.warn(`[F] run-barrel refresh failed (non-fatal): ${e instanceof Error ? e.message : String(e)}`);
  }

  const outcome = await runProofReviewLoop({
    ctx: { repoRoot: args.ctx.repoRoot, qid: args.ctx.qid, specialization: args.ctx.specialization },
    deps: { runCodex: args.deps.runCodex, runClaude: args.deps.runClaude },
    // The SHARED state object. `pipeline.ts` loads state once and re-saves this same object after
    // the stage, so the loop must mutate IT — a disk-only write is clobbered (last-writer-wins),
    // which silently made the iteration caps inert and left `cited_checks: []`.
    state: args.state,
    formalizationDir: paths.formalizationDir,
    leanDir: paths.leanDir,
    texPath: paths.tex,
    // Advisory context the filler/reviewer read for per-node proof_tex + statements.
    // The .md is retired upstream of F3; point this at the typed core instead (it
    // carries each statement's proof_tex). The load-bearing graph comes from graph.json.
    corePath: coreJsonPath(args.ctx),
    // Phase-B proof-fill directive: a load-bearing PROOF hint the orchestrator injects on
    // `--resume` (via bin/f3_directive.ts) when the fill loop is stuck. Persists on state.flags
    // until the orchestrator clears it, so it steers every filler call this run.
    fillerDirective: args.state.flags.f3_filler_directive ?? null,
    // Phase-A re-scaffold seam: drive F2 in revise-mode via a scaffold_redirect directive (it
    // patches the named decls in place, preserving proofs via carry-over and self-clears the flag).
    scaffold: async ({ redirect, targets }) => {
      args.state.flags.scaffold_redirect = [
        redirect,
        targets.length ? `Declarations to edit (JSON obj_id array): ${JSON.stringify(targets)}` : "",
      ].filter(Boolean).join("\n\n");
      const result = await runStage2({ ctx: args.ctx, state: args.state, deps: args.deps });
      if (result.status !== "completed") {
        // why: a failed F2 scaffold redirect must reject so the proof-review loop blocks fail-closed.
        throw new Error(`Stage 2 scaffold redirect did not complete (${result.status}): ${result.message}`);
      }
    },
  });
  recordProofReviewOutcome(args.state, outcome);
  // F3→D0 rewind: a witnessed `statement-wrong`. Adjudicate here (state.flags is in scope) — the loop
  // only proposed it. Per-node durable cap mirrors stage1_rewinds; any already-PROVEN dependent makes
  // this the expensive case → checkpoint for orchestrator approval rather than an auto-rewind.
  if (outcome.status === "escalate" && outcome.route === "redo-math" && outcome.redoMath) {
    const rm = outcome.redoMath;
    const seen = args.state.flags.redo_math_rewinds ?? {};
    const nth = (seen[rm.obj_id] ?? 0) + 1;
    args.state.flags.redo_math_rewinds = { ...seen, [rm.obj_id]: nth };
    const w = `witness[${rm.witness.type}]: ${rm.witness.detail}`;
    if (rm.touchesProven || nth > REDO_MATH_MAX) {
      return {
        stage: "2.5", status: "checkpoint", completedStage: "2",
        message: `PROOF-REVIEW LOOP → D0 REWIND NEEDS APPROVAL [${rm.obj_id}] `
          + `(${rm.touchesProven ? "invalidates PROVEN dependents" : `cap ${REDO_MATH_MAX} hit`}; `
          + `dependents: ${rm.dependents.join(", ") || "none"}; ${w}): ${outcome.reason}`,
      };
    }
    // Auto-rewind: witnessed, no proven dependents, under cap. Re-enter D0-solve and let it CONSUME
    // the witness (re-derive obj_id + dependents only — never from scratch). Reset the per-attempt
    // laundering counters, exactly as the propose-mode stage_0 route does.
    if (args.state.proposed_from) {
      applyInterventionRoute(args.state, {
        route: "stage_0", action_kind: "re_derive",
        reason: `F3 witnessed ${rm.obj_id} ${w}`, proposed_action: rm.witness.detail,
      } as Intervention);
    } else {
      args.state.stage_completed = "-0.5";           // nextStage("-0.5") = "0" → re-run typed D0-SOLVE
      resetFormalizationLoopCounters(args.state);
    }
    args.state.flags.redo_math_witness = {           // D0-solve reads this to scope + constrain the re-solve
      obj_id: rm.obj_id, type: rm.witness.type, detail: rm.witness.detail, dependents: rm.dependents,
    };
    return {
      stage: "2.5", status: "rewound", advance: false,
      message: `PROOF-REVIEW LOOP → AUTO D0 REWIND [${rm.obj_id}] (${w}): ${outcome.reason}`,
    };
  }
  if (outcome.status === "completed") {
    return {
      stage: "2.5",
      status: "completed",
      completedStage: "4",
      message: "proof-review loop converged (statement gate, proof fill, lint, and convergence review)",
    };
  }
  return {
    // The combined loop enters through F2.5 but may halt in F3/F3.5/F4. Preserve that
    // logical origin so pipeline.jsonl does not mislabel every escalation as F2.5.
    stage: outcome.phase ?? "2.5",
    status: "checkpoint",
    // The loop did NOT complete (it escalated). Record `completedStage: "2"` so a later
    // `--resume` RE-ENTERS the proof-review loop (next stage after "2" is "2.5") instead of
    // skipping it: with no `completedStage`, `pipeline.ts` would set `stage_completed = "2.5"`,
    // and resume would treat the loop as done — running 3/3.5/4 as no-ops straight to F5,
    // so the orchestrator's post-escalation fix never gets re-proved. "2" does NOT re-run F2
    // (STAGE_ORDER: … "2", "2.5", …); Phase A re-review is incremental (cached-matched).
    completedStage: "2",
    message: `PROOF-REVIEW LOOP ESCALATION [${outcome.route}]: ${outcome.reason}`,
  };
  } finally {
    // Tear down the shared server we booted (a launcher-provided one is owned by the launcher).
    if (ownsSharedLeanLsp && shared) {
      try {
        await shared.stop();
      } catch {
        /* best-effort teardown */
      }
      delete process.env.CAUSALSMITH_SHARED_LEAN_LSP_URL;
    }
  }
}
