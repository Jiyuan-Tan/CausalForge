import { mkdir, writeFile } from "node:fs/promises";
import { MODELS } from "../models.js";
import path from "node:path";
import { type Intervention, type ReviewResult } from "../judgment.js";
import { appendReviewLog, type ReviewLogEntry } from "../log.js";
import { formalizationDir } from "../paths.js";
import {
  appendReview,
  baseBrief,
  getLastClaudeDiagnostic,
  parseIntervention,
  readPrompt,
  synthesizeInterventionFromReviews,
  type StageDeps,
} from "../pipeline_support.js";
import type { PipelineContext, Stage, StageResult, StateJson } from "../types.js";
// Known smell from Step 2.4: routing owns these legacy proposer-loop caps,
// but the constants still live with Stage -1.2 until a neutral caps module exists.
import { NEG1_PIVOT_BUDGET, NEG1_REVISE_CAP } from "../discovery/stages/neg1_2.js";
import { STAGE2_REDIRECT_MAX } from "../formalization/loop_limits.js";

export async function runReviewBoundary(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  boundary: string;
  stage: Stage;
  cap: number;
  heuristic: string;
  producer: (
    prior: ReviewResult | null,
    attempt: number,
    intervention: Intervention | null,
  ) => Promise<StageResult>;
  reviewer: (attempt: number) => Promise<ReviewResult>;
  /**
   * When set, a PASS/ACCEPT verdict HALTS at a user checkpoint (advance: false)
   * instead of flowing on to the next stage. Used by F1.5 so the F1 plan +
   * F1.5 reuse-soundness review settle into ONE consolidated CKPT 1 the
   * orchestrator audits before F2 scaffolds. The string is the checkpoint
   * message.
   */
  checkpointOnPass?: string;
}): Promise<StageResult> {
  const reviews: ReviewResult[] = [];
  const producerOutputs: string[] = [];
  let prior: ReviewResult | null = null;
  let rejected = false;
  for (let attempt = 1; attempt <= args.cap; attempt++) {
    if (attempt > 1 || prior) {
      const producerResult = await args.producer(prior, attempt, null);
      producerOutputs.push(producerResult.message);
      if (producerResult.status === "blocked") return producerResult;
    }
    const review = await args.reviewer(attempt);
    await appendReview(args.ctx, args.boundary, attempt, review);
    reviews.push(review);
    // Deterministic halt channel: a reviewer that judges the work unsalvageable
    // (currently only D0.5.G's cold-referee below-floor-not-salvageable verdict)
    // attaches `halt_reason`. Short-circuit to a clean checkpoint BEFORE any
    // producer retry or the LLM intervention judge — neither could help, and the
    // judge might re-route (pivot/re-derive) instead of stopping.
    const haltReason = (review as { halt_reason?: string }).halt_reason;
    if (haltReason) {
      args.state.flags.general_review_halt = haltReason;
      return {
        stage: args.stage,
        status: "checkpoint",
        advance: false,
        message: `Review boundary ${args.boundary} halted (below novelty floor, not salvageable): ${haltReason}`,
      };
    }
    if (review.status === "pass" || review.status === "accept") {
      if (args.checkpointOnPass) {
        return {
          stage: args.stage,
          status: "checkpoint",
          advance: true,
          message: args.checkpointOnPass,
        };
      }
      return {
        stage: args.stage,
        status: "completed",
        message: `Review boundary ${args.boundary} passed`,
      };
    }
    prior = review;
    // Fast-path: a "reject" verdict, an `escalate_to_proposer` signal, OR a
    // fix-locus `escalate_route` (Stage 2.5 rooted the defect in F1/F0, not the
    // Lean scaffold) means another producer retry cannot help — skip remaining
    // attempts and route now. "revise" without escalation still consumes the cap.
    if (
      review.status === "reject" ||
      (review as { escalate_to_proposer?: boolean }).escalate_to_proposer === true ||
      (review as { escalate_route?: string }).escalate_route !== undefined
    ) {
      rejected = review.status === "reject";
      break;
    }
  }

  // Deterministic escalation short-circuit. When a review flagged a finding as
  // not fixable by a D0 re-solve (`escalate_to_proposer`), route via the
  // deterministic synth (→ stage_neg1 / proposer redraft) and DO NOT consult the
  // LLM intervention judge — the judge has no concept of this flag and could
  // override the routing. Persist the reason so the intent survives a --resume.
  // Fix-locus triage (Stage 2.5): a review carrying `escalate_route` was rooted
  // upstream of F2 by the reviewer. Route there DETERMINISTICALLY — no LLM judge
  // (the routing decision is already made) and no synth (which only targets the
  // proposer). Takes precedence over the proposer-escalation and judge paths.
  const locusReview = reviews.find(
    (r) => (r as { escalate_route?: "stage_0" | "stage_1" }).escalate_route !== undefined,
  );
  const escalateReview = reviews.find(
    (r) => (r as { escalate_to_proposer?: boolean }).escalate_to_proposer === true,
  );
  const intervention = locusReview
    ? (() => {
        const er = locusReview as {
          escalate_route: "stage_0" | "stage_1";
          escalate_locus_reason?: string;
        };
        const reason =
          er.escalate_locus_reason ?? `Stage 2.5 fix-locus triage routed upstream to ${er.escalate_route}.`;
        return {
          route: er.escalate_route,
          reason,
          proposed_action: reason,
          cite: undefined,
          action_kind: "re_derive",
        } as Intervention;
      })()
    : escalateReview
    ? (() => {
        const synth = synthesizeInterventionFromReviews([escalateReview], args.boundary);
        args.state.flags.escalate_to_proposer =
          (escalateReview as { escalate_reason?: string }).escalate_reason || synth.reason;
        return {
          route: synth.route,
          reason: synth.reason,
          proposed_action: synth.proposed_action,
          cite: undefined,
          action_kind: synth.action_kind,
        } as Intervention;
      })()
    : await runIntervention({
        ctx: args.ctx,
        deps: args.deps,
        state: args.state,
        boundary: args.boundary,
        heuristic: args.heuristic,
        originalBrief: baseBrief(args.ctx, args.state),
        reviews,
        producerOutputs,
      });
  const rewound = applyInterventionRoute(args.state, intervention);
  const trigger = rejected ? "reject fast-path" : locusReview ? "fix-locus triage" : "cap exhausted";
  // Only mark "rewound" when the route actually mutated state.stage_completed.
  // No-op fallbacks (route=user, stage_neg1 with exhausted pivot budget, etc.)
  // must return "checkpoint" — otherwise the pipeline loop will re-enter the
  // same boundary stage forever from `nextStage(state.stage_completed)`.
  const status: "rewound" | "checkpoint" = rewound ? "rewound" : "checkpoint";
  return {
    stage: args.stage,
    status,
    advance: false,
    message: `Review boundary ${args.boundary} routed to ${intervention.route} (${trigger}): ${intervention.reason}`,
  };
}

export function interventionBlock(intervention: Intervention | null | undefined): string {
  if (!intervention) return "";
  return [
    "=== OPUS INTERVENTION DIRECTIVE ===",
    `Route: ${intervention.route}`,
    `Diagnosis: ${intervention.reason}`,
    `Cite: ${intervention.cite ?? "none"}`,
    `Required action: ${intervention.proposed_action ?? ""}`,
    "=== END OPUS INTERVENTION DIRECTIVE ===",
    "",
  ].join("\n");
}

/**
 * Apply the route action embedded in an intervention. Returns `true` iff the
 * route actually mutated `state.stage_completed` (i.e. a genuine rewind
 * happened). Returns `false` when the route was a no-op fallback (route=user,
 * or stage_neg1 with no propose-mode / exhausted pivot budget). Callers MUST
 * branch on this flag when deciding between `status: "rewound"` (auto-flow
 * back into the rewound stage) and `status: "checkpoint"` (halt for user
 * inspection) — otherwise a no-op fallback drives the loop to re-enter the
 * same stage forever.
 */
/**
 * F3/F4 in-stage loop budgets (`assumption_review_count`, `f4_localpatch_rounds`)
 * are PER-FORMALIZATION-ATTEMPT. An upstream rewind (to stage_0/1/2 or a pivot)
 * starts a fresh attempt — fresh math, fresh scaffold, fresh premises — so the
 * budgets must reset when an upstream rewind starts a fresh attempt.
 * Without this they are increment-only and leak across rewinds: a re-entered F3
 * inherits an exhausted `assumption_review_count` and routes its new added
 * premises straight to the F4 backstop (`assumption_review_cap_hit`) unaudited —
 * a silent laundering escape. Call on every successful upstream rewind.
 */
export function resetFormalizationLoopCounters(state: StateJson): void {
  state.flags.assumption_review_count = 0;
  state.flags.f4_localpatch_rounds = 0;
  delete state.flags.assumption_review_cap_hit;
}

export function applyInterventionRoute(state: StateJson, intervention: Intervention): boolean {
  if (intervention.route === "stage_neg1") {
    // Abandon the current angle and pivot to a new one. Only meaningful in
    // propose-mode (proposed_from must exist and have spare pivot budget).
    // If preconditions fail, downgrade to a user-facing checkpoint by leaving
    // stage_completed untouched and recording the fallback reason.
    const pf = state.proposed_from;
    if (!pf) {
      state.flags.stage_neg1_fallback = `stage_neg1 requested without propose-mode: ${intervention.reason}`;
      return false;
    }
    const currentAngle = pf.current_angle_index ?? 0;
    const nextAngle = currentAngle + 1;
    if (nextAngle >= NEG1_PIVOT_BUDGET) {
      state.flags.stage_neg1_fallback = `stage_neg1 requested but pivot budget exhausted (NEG1_PIVOT_BUDGET=${NEG1_PIVOT_BUDGET}): ${intervention.reason}`;
      return false;
    }
    pf.exhausted_angles = pf.exhausted_angles ?? [];
    if (!pf.exhausted_angles.includes(currentAngle)) {
      pf.exhausted_angles.push(currentAngle);
    }
    pf.current_angle_index = nextAngle;
    pf.current_version = 0;
    pf.current_mode = "pivot";
    pf.last_reviewer_verdict = "";
    delete pf.last_draft_handoff;
    delete pf.last_draft_status;
    state.stage_completed = "-1.2";
    state.flags.rewound_from_stage0_5_pivot = intervention.reason;
    state.pending_sorries = [];
    resetFormalizationLoopCounters(state);
    return true;
  }
  if (intervention.route === "stage_0") {
    // Downgrade to user checkpoint if theorem_split budget is exhausted.
    if (
      intervention.action_kind === "theorem_split" &&
      (state.flags.theorem_splits ?? 0) >= 3
    ) {
      state.flags.theorem_splits_cap_hit = `theorem_split cap reached (${state.flags.theorem_splits ?? 0}): ${intervention.reason}`;
      return false;
    }
    // Downgrade to user checkpoint when Stage -0.5 budget is fully exhausted —
    // the rewind would re-enter Stage -0.5 only to checkpoint immediately, which
    // burns one intervention call for nothing.
    const pf0 = state.proposed_from;
    if (pf0) {
      const angleExhausted = (pf0.current_angle_index ?? 0) >= NEG1_PIVOT_BUDGET - 1;
      const versionExhausted = (pf0.current_version ?? 0) >= NEG1_REVISE_CAP;
      if (angleExhausted && versionExhausted) {
        state.flags.stage0_budget_exhausted = `stage_0 route requested but -0.5 budget exhausted: ${intervention.reason}`;
        return false;
      }
    }
    // stage_completed = "-1.2" so nextStage = "-0.5" (proposal re-review). Then
    // Stage -0.5's resume-aware producer-first guard fires only when the last
    // draft handoff is empty AND a prior reviewer verdict exists. We clear
    // last_draft_handoff and pin current_mode = "revise" to guarantee that on
    // resume, the producer runs once before the reviewer re-judges — that way
    // the Stage 0.5 rejection context is woven into a fresh v(N+1) draft
    // rather than the reviewer re-accepting the same already-judged .tex.
    state.stage_completed = "-1.2";
    state.flags.rewound_from_stage0 = intervention.reason;
    state.pending_sorries = [];
    resetFormalizationLoopCounters(state);
    recordAutoBucketAAssumption(state, intervention);
    if (intervention.action_kind === "theorem_split") {
      state.flags.theorem_splits = (state.flags.theorem_splits ?? 0) + 1;
    }
    if (intervention.action_kind === "statement_correction" && intervention.proposed_restatement) {
      const r = intervention.proposed_restatement;
      state.flags.statement_correction_directive = r.rationale
        ? `${r.statement}\n\nWhy this is a correction (not a weakening): ${r.rationale}`
        : r.statement;
    }
    const pf = state.proposed_from;
    if (pf) {
      pf.last_draft_handoff = undefined;
      pf.last_draft_status = undefined;
      pf.current_mode = "revise";
    }
    return true;
  }
  if (intervention.route === "stage_1") {
    // Code-level cap: after 3 stage_1 rewinds the intervention judge should
    // have routed to "user"; if it keeps routing here, force a checkpoint.
    const rewindCount = (state.flags.stage1_rewinds ?? 0) + 1;
    if (rewindCount > 3) {
      state.flags.stage1_rewinds_cap_hit = `stage_1 rewind cap reached (${rewindCount - 1}): ${intervention.reason}`;
      return false;
    }
    state.flags.stage1_rewinds = rewindCount;
    state.stage_completed = "0.5";
    state.flags.local_fix_from_4d = true;
    // Park the rewind reason so the rewound F1 (dispatched with no priorReview)
    // knows WHAT to fix and patches in place instead of blind-regenerating. Set
    // for any stage_1 route; F2.5 fix-locus carries the `nl-plan` critique here.
    state.flags.f1_revise_directive = intervention.proposed_action ?? intervention.reason;
    state.pending_sorries = [];
    resetFormalizationLoopCounters(state);
    return true;
  }
  if (intervention.route === "stage_2") {
    // Encoding-drift redirect: rewind to before Stage 2 (nextStage("1.5") = "2")
    // and surface the verbatim directive on state.flags.scaffold_redirect.
    // Hard cap: bounded redirects per run; the next one escalates to user via no-op.
    const count = (state.flags.scaffold_redirect_count ?? 0) + 1;
    if (count > STAGE2_REDIRECT_MAX) {
      state.flags.scaffold_redirect_cap_hit =
        `stage_2 redirect cap reached (${count - 1}): ${intervention.reason}`;
      return false;
    }
    state.stage_completed = "1.5";
    state.flags.scaffold_redirect_count = count;
    state.flags.scaffold_redirect =
      intervention.proposed_action ?? intervention.reason;
    state.pending_sorries = [];
    resetFormalizationLoopCounters(state);
    return true;
  }
  if (intervention.route === "stage_4d") {
    // stage_4d is only meaningful at Stage 4, where it is intercepted before
    // applyInterventionRoute is called. Reaching here means it was routed from
    // a non-Stage-4 boundary — degrade to user checkpoint and record the event.
    state.flags.stage4d_misrouted = `stage_4d received at non-stage-4 boundary: ${intervention.reason}`;
    return false;
  }
  if (intervention.route === "stage_3_local") {
    // stage_3_local is only meaningful at Stage 3 escalation boundaries, where
    // stage3.ts intercepts it before applyInterventionRoute is called. At any
    // other boundary, degrade to user checkpoint and record the event.
    // why: distinguish Stage-3 local misroutes from true Stage-4D misroutes.
    (state.flags as typeof state.flags & { stage3_local_misrouted?: string }).stage3_local_misrouted =
      `stage_3_local received at non-stage-3 boundary: ${intervention.reason}`;
    return false;
  }
  // route="user" or any unrecognized route: no-op, halt for user inspection.
  return false;
}

export async function runIntervention(args: {
  ctx: PipelineContext;
  deps: StageDeps;
  state: StateJson;
  boundary: string;
  heuristic: string;
  originalBrief: string;
  reviews: ReviewResult[];
  producerOutputs: string[];
}): Promise<Intervention> {
  const base = await readPrompt(args.ctx, "intervention.txt");
  const loopCounters = {
    theorem_splits: args.state.flags.theorem_splits ?? 0,
    scaffold_redirects: args.state.flags.scaffold_redirect_count ?? 0,
  };
  const prompt = [
    base,
    "",
    `Boundary: ${args.boundary}`,
    `Per-boundary heuristic: ${args.heuristic}`,
    "",
    "Loop counters:",
    JSON.stringify(loopCounters, null, 2),
    "",
    "Original brief:",
    args.originalBrief,
    "",
    "Review reports:",
    JSON.stringify(args.reviews, null, 2),
    "",
    "Producer outputs:",
    args.producerOutputs.join("\n\n---\n\n"),
    "",
    "RETURN ONLY THE JSON OBJECT MATCHING THE SCHEMA.",
  ].join("\n");
  const jsonSchema = {
    type: "object",
    properties: {
      // Keep these enums in sync with `interventionSchema` (judgment.ts) —
      // this schema is enforced via constrained generation, so a route/kind
      // missing here is one the judge physically cannot emit even when the
      // prompt and the downstream handlers support it (stage_3_local was
      // silently unreachable for that reason).
      route: {
        enum: ["user", "stage_0", "stage_1", "stage_2", "stage_3_local", "stage_4d", "stage_neg1"],
      },
      reason: { type: "string" },
      proposed_action: { type: "string" },
      cite: { type: "string" },
      action_kind: {
        enum: [
          "theorem_split",
          "statement_correction",
          "re_derive",
          "patch",
          "local_patch",
          "split_collapsed",
          "loop_guard",
          "user_required",
          "redraft_proposal",
        ],
      },
      proposed_restatement: {
        type: "object",
        properties: {
          statement: { type: "string" },
          rationale: { type: "string" },
        },
        required: ["statement"],
        additionalProperties: false,
      },
      assumption_classifications: {
        type: "array",
        items: {
          type: "object",
          properties: {
            label: { type: "string" },
            classification: { enum: ["latent", "caveat", "regime_defining"] },
            one_line: { type: "string" },
          },
          required: ["label", "classification", "one_line"],
          additionalProperties: false,
        },
      },
      proposed_assumption: {
        type: "object",
        properties: {
          label: { type: "string" },
          statement: { type: "string" },
          source: { type: "string" },
        },
        required: ["label", "statement"],
        additionalProperties: false,
      },
    },
    required: ["route", "reason"],
    additionalProperties: false,
  };

  // Try the judge up to 3 times. Empty stdout from the judge (observed
  // intermittently — see PIPELINE_NOTES) and other transient parse failures
  // burn the run otherwise; cheap retries are cheaper than surrendering
  // the whole boundary to a user fallback, especially since the synth path
  // is intentionally neutral and can't recommend a stage_0 re-derive.
  const MAX_INTERVENTION_ATTEMPTS = 3;
  let intervention: Intervention | null = null;
  let lastReason = "";
  let lastOut = "";
  for (let attempt = 1; attempt <= MAX_INTERVENTION_ATTEMPTS; attempt++) {
    const retryNote =
      attempt > 1
        ? "\n\n(Previous judge call returned an empty or unparseable response; this is a retry. Emit only the JSON object specified by the schema, with no surrounding prose or duplicates.)"
        : "";
    lastOut = await args.deps.runClaude({
      prompt: prompt + retryNote,
      model: MODELS.claudeMain,
      cwd: args.ctx.repoRoot,
      jsonSchema,
    });
    try {
      intervention = parseIntervention(lastOut);
      break;
    } catch (err) {
      lastReason = err instanceof Error ? err.message : String(err);
      console.warn(
        `[causalsmith] intervention parse failed (attempt ${attempt}/${MAX_INTERVENTION_ATTEMPTS}: ${lastReason}); ` +
          (attempt < MAX_INTERVENTION_ATTEMPTS ? "retrying once." : "falling back to route=user."),
      );
    }
  }
  if (!intervention) {
    // Dump full diagnostics: parsed text (often empty) + raw stdout + raw
    // stderr from the last claude invocation. Stderr is the key visibility
    // gap that turns the empty-output mystery into a debuggable signal.
    const diag = getLastClaudeDiagnostic();
    const dumpPath = path.join(
      formalizationDir(args.ctx.repoRoot, args.ctx.qid),
      `intervention_raw_${Date.now()}.txt`,
    );
    await mkdir(path.dirname(dumpPath), { recursive: true });
    const dumpBody = [
      "=== parsed text (what runIntervention received) ===",
      lastOut ?? "",
      "",
      "=== raw stdout (last claude invocation) ===",
      diag?.rawStdout ?? "(no diagnostic captured)",
      "",
      "=== raw stderr (last claude invocation) ===",
      diag?.rawStderr ?? "(no diagnostic captured)",
    ].join("\n");
    await writeFile(dumpPath, dumpBody, "utf8");

    // Deterministic synthesis from the latest review verdict. The pipeline
    // has all the information needed to checkpoint cleanly even when the
    // intervention judge silently fails — there is no need to surrender
    // with a content-free PARSE_FAILED message.
    const synth = synthesizeInterventionFromReviews(args.reviews, args.boundary);
    intervention = {
      route: synth.route,
      reason:
        `Intervention judge returned no parseable output after ${MAX_INTERVENTION_ATTEMPTS} attempts ` +
        `(${lastReason}); diagnostics dumped to ${dumpPath}. ` +
        `Synthesized intervention deterministically from latest review: ${synth.reason}`,
      proposed_action: synth.proposed_action,
      cite: undefined,
      action_kind: synth.action_kind,
    };
  }
  const entry: Omit<Extract<ReviewLogEntry, { kind: "intervention" }>, "timestamp"> = {
    kind: "intervention",
    stage: args.boundary,
    route: intervention.route,
    reason: intervention.reason,
    proposed_action: intervention.proposed_action,
    cite: intervention.cite,
    intervention,
  };
  await appendReviewLog(args.ctx, entry);
  return intervention;
}

export function bucketAApprovedBlock(state: StateJson): string {
  const approved = state.added_assumptions.filter((a) => a.user_approved === true);
  if (approved.length === 0) return "";
  const rows = approved
    .map((a) => `- [${a.label}] ${a.statement}${a.source ? `  (source: ${a.source})` : ""}`)
    .join("\n");
  const rewind = state.flags.rewound_from_stage0 ?? "(none)";
  return [
    "=== USER-APPROVED BUCKET A DIRECTIVE (load-bearing) ===",
    "The user has approved the following labelled assumptions for inclusion in §7 (Assumptions).",
    "Integrate each VERBATIM under a new Assumption label in §7 of the .tex; treat them as locked-",
    "parameter additions (not silent strengthenings). Invoke them by label wherever the proof of",
    "Theorem 1 (or any downstream lemma) requires the missing hypothesis. Do NOT add OTHER new",
    "assumptions: any further unstated premise is still a Hard Rule 2 violation.",
    "",
    `Rewind reason: ${rewind}`,
    "User-approved assumptions:",
    rows,
    "=== END USER-APPROVED BUCKET A DIRECTIVE ===",
    "",
  ].join("\n");
}

/**
 * Persist an Opus-authored Bucket A assumption into the shared assumption
 * ledger so that `bucketAApprovedBlock` surfaces it verbatim on the rewound
 * Stage 0. Idempotent on the (label) key so retries do not duplicate rows.
 */
export function recordAutoBucketAAssumption(state: StateJson, intervention: Intervention): void {
  const proposed = intervention.proposed_assumption;
  if (!proposed) return;
  const existing = state.added_assumptions.find((a) => a.label === proposed.label);
  if (existing) {
    existing.statement = proposed.statement;
    existing.user_approved = true;
    existing.source = proposed.source ?? existing.source ?? "opus-intervention-auto-bucket-a";
    return;
  }
  state.added_assumptions.push({
    label: proposed.label,
    statement: proposed.statement,
    user_approved: true,
    source: proposed.source ?? "opus-intervention-auto-bucket-a",
  });
}
