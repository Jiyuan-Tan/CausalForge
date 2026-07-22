import type { STAGE_ORDER } from "./constants.js";
import type { DraftRunner } from "./workers/draftAdapter.js";
import type { NoveltyTarget } from "./novelty.js";

export type Stage = (typeof STAGE_ORDER)[number];

export const UPGRADE_AXES = ["computation", "estimation", "generalization", "mechanism"] as const;
export type UpgradeAxis = (typeof UPGRADE_AXES)[number];

export const UPGRADE_PARENT_TIERS = ["accepted", "downgraded"] as const;

export interface UpgradeFrom {
  parent_qid: string;
  parent_spec: string;
  parent_tier: (typeof UPGRADE_PARENT_TIERS)[number];
  upgrade_axis: UpgradeAxis;
}

export interface PendingSorry {
  file: string;
  line: number;
  label?: string;
  goal?: string;
  suggestions?: string[];
  bucket?: "1" | "2" | "3" | "4" | null;
  attempts?: number;
  codex_diagnosis?: string;
  // Per-sorry convergence memory (Stage 3 state-machine). Persisted so the
  // committed remediation track and progress survive rewind/resume — without
  // this the classifier re-rolls the bucket from scratch on every resume.
  /** Committed remediation track (bucket family). */
  track?: "1" | "2" | "3" | "4" | "5" | null;
  /** Goal hash at last sighting — a change means proof progress. */
  last_goal_hash?: string | null;
  /** Times escalated one rung (telemetry). */
  escalations?: number;
  /** Whether the Bucket-4 decomposition burst already fired. */
  bursted?: boolean;
}

export interface AddedAssumption {
  label: string;
  statement: string;
  user_approved?: boolean;
  source?: string;
  /** `.tex`/`.md` anchor the premise is claimed to match (F3-localPatch adds). */
  anchor?: string;
  /**
   * Faithfulness class of the premise, on the invariant-#10 crux-vs-gate axis:
   *  - `faithful-refinement`: the .tex already states/implies it in this setting.
   *  - `regularity-bookkeeping`: a measurability/integrability/finiteness side-condition.
   *  - `substrate-gate`: a genuinely classical, dischargeable fact (must be built before banking).
   */
  classification?: "faithful-refinement" | "regularity-bookkeeping" | "substrate-gate";
  /**
   * For automated F3-localPatch adds: whether the F2.5 delta re-review has cleared
   * this premise. `false` (or absent) after a localPatch add → triggers the rewind.
   */
  reviewed?: boolean;
}

export interface MissingItem {
  kind: string;
  name_suggestion: string;
  purpose: string;
  why_substantial: string;
  nl_artifact_reference?: string;
  suggested_location?: string;
}

/**
 * Loop tag (Phase 2 study-pipeline addition).
 *
 *   - `"research"`: the existing /causalsmith pipeline (Stages -1.2 → 5). This is
 *     the default for any state file that does not declare `loop`.
 *   - `"study"`: the retired study pipeline (Stages S-1 → S3). Its
 *     compatibility runs use a separate state file under `doc/study/runs/<run_id>/state.json` and a
 *     distinct shape (`StudyStateJson` in `study/state.ts`); the field is
 *     declared on `StateJson` only to keep loop dispatch uniform when
 *     pipeline.ts inspects a generic state blob.
 */
export type Loop = "research" | "study";

/** Phase 2 lineage marker shared by every pipeline. */
export interface StateLineage {
  parent_run_id?: string;
  parent_kind?: Loop;
}

/**
 * Step 2.1 namespacing — `StateJson` is split into three conceptual
 * interfaces:
 *
 *   • `SharedState` — fields read or written by both phases (orchestrator
 *     bookkeeping, paper-batching coordinates, loop tag, lineage).
 *   • `DiscoveryState` — fields owned by Stages −1.1 … 1.5 (gap intake,
 *     proposer state, from-question wiring, OpenQuestion close hook).
 *   • `FormalizationState` — fields owned by Stages 2 … 5 (pending sorries,
 *     design decisions, added assumptions).
 *
 * The on-disk JSON shape is unchanged; `StateJson` is the intersection. Step 2
 * code lives under `src/discovery/` and `src/formalization/`, each consuming
 * its namespaced half via `StateJson` (the union remains the canonical type
 * for I/O — see `src/state.ts::stateSchema`).
 *
 * The `flags` object is similarly split into `SharedFlags`, `DiscoveryFlags`,
 * `FormalizationFlags` and intersected on `StateJson.flags`.
 */

/** Flag fields read or written by both phases (paper batching). */
export interface SharedFlags {
  theorem_splits?: number;
  theorem_splits_cap_hit?: string;
}

/** One built substrate decl, recorded by the meta-orchestrator on the
 *  `substrate_built` channel for F1 to discharge against. */
export interface SubstrateBuiltDecl {
  /** The plan/core gate node id this decl discharges (e.g. `ass:vc-localized-envelope`). */
  gate_id: string;
  /** Fully-qualified Lean name of the built theorem (e.g.
   *  `Causalean.Stat.Concentration.localized_uniform_deviation_expectation`). */
  decl_name: string;
  /** Module path hosting the decl (for the plan's reuse `module`/import). */
  module: string;
  /** One-line NL statement of what was proven (so F1 can confirm type-fit before reuse). */
  nl_statement: string;
}

/** Flag fields owned by the discovery half (Stages −1.1 … 1.5). */
export interface DiscoveryFlags {
  rewound_from_stage0?: string | null;
  rewound_from_stage0_5_pivot?: string | null;
  stage_neg1_fallback?: string | null;
  stage0_budget_exhausted?: string;
  stage1_rewinds?: number;
  stage1_rewinds_cap_hit?: string;
  /**
   * Set by `runReviewBoundary` when the D0.5.G cold general referee judges the
   * accepted note below the novelty floor AND not salvageable. Carries the
   * referee's critique; the run halts at a checkpoint with this reason.
   */
  general_review_halt?: string | null;
  /**
   * Substrate-build seam. Set by F1 (stage1) when the plan's feasibility verdict
   * is `needs-new-infrastructure` with Defer-items; F1 self-halts here (a halt
   * distinct from the F1.5 CKPT 1). Carries an infra-item summary, and BLOCKS
   * `--resume` (via a resume gate) until the orchestrator deals with it. The
   * model: dispatch BACKGROUND builder subagents for the Defer-items, then CLEAR
   * this flag and resume so the run proceeds with the gates ASSUMED (does not
   * stall). Each landed build is discharged later (at the next checkpoint) by
   * codex wiring the lemma into the theorem's Lean and a rewind to F2.5 to
   * re-review — NOT a rewind to F1, since the plan and scaffold are unchanged.
   * (The `substrate_built` → F1 re-plan channel below, or consciously clearing
   * to gate/defer, remain alternatives.)
   */
  substrate_build_required?: string | null;
  /**
   * Substrate-built channel (the build→F1 communication seam, the dual of
   * `substrate_build_required`). After the meta-orchestrator builds a Defer-item's
   * crux substrate 0-sorry in Causalean, it records the new decl(s) HERE and reruns
   * F1. F1 reads this manifest as a directive: each listed gate node is now PROVEN
   * upstream, so F1 must DISCHARGE it — reclassify the matching `ass:*`/gate node to
   * `lean_kind:"lemma"`, `disposition:"reuse"` from `decl_name`, and drop it from
   * `hyps` — instead of re-deferring or re-assuming it. Cleared once F1 has consumed
   * it (the rerun produced a plan with no remaining matching Defer-item). This is
   * the F1-RE-PLAN discharge alternative; the PREFERRED discharge wires the lemma
   * into the Lean directly and rewinds to F2.5 (no re-plan). Either way the
   * discharge changes the proof, so the chain re-runs through F4 and MUST re-pass
   * F4 before banking.
   */
  substrate_built?: SubstrateBuiltDecl[] | null;
  /**
   * D0.5.G directed-reroute counter. Incremented each time a below-floor note is
   * sent back to D0 with a bounded improvement directive (better estimator / derive
   * an assumed condition / tighten a bound) instead of halting. Capped (2) so a
   * genuinely-stuck topic still halts deterministically for the operator.
   */
  general_reroute_count?: number;
  /**
   * D0.R loop state. `d0r_human_directive`: an optional operator/orchestrator
   * injection consumed by the next D0.R round (the strategic flip the reviewer
   * can't generate), cleared after use. `d0r_flagship_rounds`: flagship-upside
   * attempts used (cap 2) after a field accept with flagship potential.
   * `d0r_best_tier`/`d0r_best_note_path`: the highest-tier accepted note seen
   * across rounds/runs — the deliverable is the BEST, not the last (guards the
   * round-5→round-6 framing regression).
   */
  d0r_human_directive?: string | null;
  d0r_flagship_rounds?: number;
  d0r_best_tier?: string | null;
  d0r_best_note_path?: string | null;
  /**
   * Set by the intervention router on an `action_kind: "statement_correction"`
   * stage_0 rewind. Carries the corrected, standard-form restatement of the
   * over-precise headline object (e.g. closure / inf-sup form where the draft
   * over-claimed pointwise extremum attainment). The rewound proposer reads it
   * via `buildStage0_5RejectionContext` and must restate the SAME focal object
   * in this form WITHOUT demoting to a conjecture or adding an assumption
   * (distinguishes a true over-precision fix from a regime-defining split).
   * Cleared when runStage0 (D0) next starts.
   */
  statement_correction_directive?: string | null;
  /**
   * F3 phase-B proof-fill directive. An optional load-bearing PROOF hint the
   * orchestrator injects for the filler agent (lemma names / tactic strategy /
   * Mathlib API) when the proof-fill loop is stuck. Loop-wide and persistent:
   * injected into EVERY filler call for the rest of phase B until the orchestrator
   * clears it (unlike the one-shot correction directives, it is NOT auto-cleared).
   * Mirrors the D0 escalation-log directive channel. It is a proof hint ONLY — the
   * per-iteration anti-laundering + assumption/def gates still reject any use that
   * changes a statement, adds an unsanctioned hypothesis, or axiomatizes a goal.
   */
  f3_filler_directive?: string | null;
  /** Persistent orchestrator F2 scaffold directive (analogue of `f3_filler_directive`):
   *  read on every scaffold/revise pass as a top-priority faithfulness constraint,
   *  persists across resumes until cleared via `bin/f2_directive.ts`. */
  f2_scaffold_directive?: string | null;
  /**
   * Set by the Stage 0.5 boundary when a review marked a finding as not fixable
   * by a D0 re-solve (needs a proposal restructure / new math). Persists the
   * proposer-redraft reason so the escalation intent survives a --resume (the
   * `escalate_to_proposer` flag lives only on the in-memory ReviewResult).
   */
  escalate_to_proposer?: string | null;
  /** Set when proposal §8 has more than the 4-conjecture cap; surfaced to the user. */
  stage0_too_many_conjectures?: string;
  /** Set when the post-stitch validator (Stage 0.M) cannot trace §9 to per-conjecture verdicts. */
  stage0_stitch_invariant_violated?: string;
}

/**
 * One drift verdict for a definition/assumption clause inside a CrosswalkEntry.
 * `src` is the .md signature clause; `lean` is how the Lean def encodes it (or
 * "absent"); `v` is the per-clause verdict from the same vocabulary as the
 * entry verdict.
 */
export interface CrosswalkClause {
  src: string;
  lean: string;
  v: CrosswalkVerdict;
}

/**
 * Drift verdict vocabulary, shared with the H.1 hypothesis matrix. `exact` /
 * `equivalent` pass; everything else is a blocking drift the F2.5 gate folds
 * into its findings.
 */
export type CrosswalkVerdict =
  | "exact"
  | "equivalent"
  | "stronger-in-Lean"
  | "weaker-in-Lean"
  | "missing-in-Lean"
  | "extra-in-Lean"
  | "encoding-drift"
  | "drift"
  | "unmatched"; // skeleton-only placeholder before the reviewer assigns a verdict

/**
 * One object in the F2.5 tex↔Lean crosswalk. The deterministic skeleton builder
 * fills every field EXCEPT `verdict`/`clauses[].v`/`note`/`fix_locus` (left as
 * `unmatched`/empty); the codex reviewer fills those, keyed by `obj_id`. Durable
 * anchors are `obj_id` (.md/.tex side) and `(lean.file, lean.decl)` (Lean side);
 * `lean.line` and `tex.line_range` are convenience and re-derivable.
 */
export interface CrosswalkEntry {
  obj_id: string;
  kind: "definition" | "assumption" | "theorem" | "lemma" | "proposition";
  title: string;
  tex: { label: string; line_range: string };
  lean: { file: string; decl: string; decl_kind: string; line: number } | null;
  verdict: CrosswalkVerdict;
  clauses?: CrosswalkClause[];
  fix_locus?: "lean-scaffold" | "nl-plan" | "math-source";
  note?: string;
}

/** Flag fields owned by the formalization half (Stages 2 … 5). */
export interface FormalizationFlags {
  rewound_from_stage4d?: string | null;
  local_fix_from_4d: boolean;
  missing_architecture: boolean;
  missing_architecture_items?: MissingItem[];
  stage4d_misrouted?: string;
  /** Verbatim directive from the intervention judge when route=stage_2; consumed by runStage2 then cleared on success. */
  scaffold_redirect?: string | null;
  /** Loop guard counter; accumulates across the run. */
  scaffold_redirect_count?: number;
  /** Mirrors `theorem_splits_cap_hit`: populated when the legacy stage_2 redirect cap is exceeded. */
  scaffold_redirect_cap_hit?: string;
  /** The proof-review loop's iteration budgets, PERSISTED across resumes. These used to be
   * in-process locals, so every `--resume` silently handed the loop a fresh budget — an
   * orchestrator could re-roll the (non-deterministic) reviewer indefinitely with no flag, no
   * audit trail, and no gate. Persisting them makes a cap a real circuit breaker. */
  proof_loop_counters?: {
    iters: number;
    scaffold_rounds: number;
    stale: number;
    tag_reroutes: number;
    node_strikes: Record<string, number>;
    /** Hash-keyed counts of identical F2.5 target+diagnostic signatures. */
    review_error_strikes: Record<string, number>;
    /** Hash of the last red `lake build` diagnostic, so the identically-red no-progress
     * cap survives a `--resume` instead of resetting `stale` on every re-entry. */
    last_build_error_sig?: string;
  };
  /** Set when any `proof_loop_counters` budget is exhausted. BLOCKS `--resume` until cleared via
   * `--clear-gate proof_loop_cap_hit`. Only MAIN may clear it (a sub never resets its own cap). */
  proof_loop_cap_hit?: string;
  /** D-phase loop budgets, persisted for the same reason as `proof_loop_counters`: the D0
   *  solve loop and the D0.5 revise loop were plain in-process `for` bounds, so a plain
   *  `--resume` handed each a FRESH budget — 15 more multi-unit solve rounds, 3 more
   *  (3-referee panel + D0.R) rounds — unbounded and unaudited. `consistency_heals`
   *  migrated here from `design_decisions` so a cap gate can reset it. */
  d0_loop_counters?: {
    solve_rounds: number;
    revise_rounds: number;
    consistency_heals: number;
  };
  /** Set when any `d0_loop_counters` budget is exhausted. BLOCKS `--resume` until cleared
   *  via `--clear-gate d0_loop_cap_hit`. */
  d0_loop_cap_hit?: string;
  /** D-0.5 producer env-failure retries, persisted for the same reason as the D0 counters:
   *  a process-local counter meant every resume re-granted the full retry budget while
   *  `last_draft_status` stayed "env-failure", looping forever. Reset by the
   *  `stage_neg1_fallback` gate. */
  neg1_env_failure_retries?: number;
  /**
   * Durable fail-closed record that the combined F2.5 proof-review loop returned
   * an escalation without converging. While present, the dispatcher must not
   * enter the retired F3/F3.5/F4 pass-through slots or F5. It is cleared only
   * after a genuine `runProofReviewLoop` completion.
   */
  proof_review_escalation_pending?: {
    route: string;
    reason: string;
  } | null;
  /** F4 localized-repair rounds used (cap `F4_LOCALPATCH_CAP`). Each round runs the
   * flavor-(e) localPatch+codex lane on the F4 reject flags (fix the statement toward the
   * `.tex` + re-prove in place) instead of a full stage_2 re-scaffold, then rewinds to F3.5
   * to re-verify. A residual `BLOCKER: needs-substrate` sorry or an exhausted budget
   * escalates to the orchestrator. */
  f4_localpatch_rounds?: number;
  /** Verbatim F2.5 fix-locus critique when an `nl-plan` finding routes to stage_1 (F1); consumed by runStage1's revise mode then cleared. Carries the upstream reason across the cross-stage rewind (priorReview is absent on a rewind dispatch). */
  f1_revise_directive?: string | null;
  /** F3→D0 rewind counter, keyed by the broken node's obj_id (cap `REDO_MATH_MAX`). Bumped each time
   * a witnessed `statement-wrong` bounces that node back to D0-solve; a node exceeding the cap (or one
   * whose re-solve would invalidate already-PROVEN dependents) checkpoints for orchestrator approval
   * instead of auto-rewinding. Persists across `--resume` so the cap bounds total ping-pong. */
  redo_math_rewinds?: Record<string, number>;
  /** The witness + blast-radius parked for the rewound D0-SOLVE to CONSUME: re-derive `obj_id` and its
   * `dependents` (never from scratch) treating the obstruction as a hard constraint, so the re-solve
   * cannot regenerate the same refuted claim. Cleared by D0-solve once consumed. */
  redo_math_witness?: { obj_id: string; type: string; detail: string; dependents: string[] };
  /** Stage 3.5: human-readable lines describing advisory unused-hypothesis findings forwarded to Stage 4. */
  stage3_5_advisory_unused?: string[];
  /** Stage 3.5: stamped when Codex pruning broke `lake build` and the edits were reverted. */
  stage3_5_build_failed?: string;
  /**
   * F2.5 tex↔Lean crosswalk PASS snapshot: the merged crosswalk entries
   * (obj_id → anchors + drift verdict) captured at the last F2.5 PASS. This is
   * the authoritative correspondence backbone the future paper↔Lean linked view
   * consumes; on a non-PASS outcome the on-disk crosswalk is still written but
   * not snapshotted here.
   */
  f25_crosswalk?: CrosswalkEntry[];
  /**
   * F3→F2.5 assumption delta re-review counter (cap `MAX_ASSUMPTION_REVIEWS`).
   * Bumped each time an F3 localPatch adds a premise and rewinds to F2.5 to
   * re-audit it. Kept SEPARATE from `scaffold_redirect_count` so an assumption
   * re-review never consumes the encoding-drift redirect budget; folded into the
   * reported `scaffold_redirects` only so the G.ii/G.iii relaxation fires over the
   * F3-filled proofs being re-reviewed.
   */
  assumption_review_count?: number;
  /** Populated when `MAX_ASSUMPTION_REVIEWS` is exceeded; the residual premises fall through to the F4 backstop. */
  assumption_review_cap_hit?: string;
  /**
   * Verbatim directive surfaced to the F2.5 reviewer when a localPatch added a
   * premise: the new premise labels to audit on the crux-vs-gate axis. Set on the
   * rewind, consumed (and the premises marked `reviewed`) on re-entry to F3.
   */
  assumption_delta_review?: string | null;
  /** Authoritative, orchestrator-recorded incremental source correction.  While
   * `status === "applied"`, F2 must invalidate exactly `dirty_nodes` even when
   * their Lean signature/hidden-definition hashes already changed before the
   * revise snapshot.  After persisting that invalidation F2 advances the receipt
   * to `f2_revised`; the graph then carries the delta through F2.5. */
  source_rewind?: {
    status: string;
    command_ts?: string;
    target?: string;
    subtype?: string;
    reentry_stage?: string;
    reentry_mode?: string;
    dirty_nodes: string[];
    review_scope?: string;
    f2_revised_at?: string;
  };
}

/**
 * Cross-phase fields: stage cursor, target Lean directory, loop tag, lineage,
 * paper-batching coordinates. Touched by orchestrator and both submodules.
 */
export interface SharedState {
  stage_completed: Stage;
  lean_subdir: string;
  /**
   * Self-identifying run coordinates. Stamped on every save (see `saveState`)
   * so the qid/spec survive the causalsmith-style bare `state.json` filename
   * that no longer encodes the spec. Optional for back-compat with pre-rename
   * state files (whose spec is still recoverable from their prefixed filename).
   */
  qid?: string;
  specialization?: string;
  /**
   * Loop tag — `"research"` for /causalsmith. Defaulted to `"research"` on load
   * for backward compatibility with state files written before Phase 2.
   */
  loop?: Loop;
  /**
   * Auto mode — set by `--auto` (cold start or any `--resume`). When true the
   * meta-orchestrator makes every checkpoint decision itself per the skill and
   * `--resume`s WITHOUT asking the user; it stops only on a terminal failure or
   * at CKPT 2 (F5 bank/promote/commit, which always waits). Persisted so a run
   * stays autonomous across resumes even if a later `--resume` omits `--auto`,
   * and re-surfaced on every checkpoint line (`checkpointGuidance` banner) so
   * the orchestrator does not forget it is autonomous and revert to asking.
   */
  auto_mode?: boolean;
  /** `"pending_checkpoint" | "user_chose:<command>" | null`. */
  next_action?: string | null;
  lineage?: StateLineage | null;
  /**
   * Phase-A (paper batching) — per-theorem sub-states for runs dispatched
   * from the study pipeline with multiple Theorems. Absent on legacy single-theorem
   * runs; the pipeline treats `theorems === undefined` as "act as if there is
   * one implicit theorem corresponding to the qid root."
   */
  theorems?: import("./shared/paper_batch_types.js").TheoremEntry[];
  /**
   * Phase-A (paper batching) — index into `theorems` for the per-theorem
   * stage currently running. Used by Stages 0, 0.5, 1, 1.5, 3, 4 to resume
   * after a checkpoint or failure. Paper-wide stages (2, 5) do not consult
   * this. Absent iff `theorems` is absent.
   */
  current_theorem_index?: number;
}

/**
 * Discovery-phase fields (Stages −1.1 … 1.5): literature gaps, proposer
 * state, from-question wiring, OpenQuestion close hook.
 */
export interface DiscoveryState {
  /**
   * Phase 3 — set by `/causalsmith --from-question <oq_id>` to wire the research
   * loop into the idea-map graph. When non-null the Stage -1.2 driver splices
   * the rendered OpenQuestion bundle into the proposer prompt, the Stage -0.5
   * driver scopes its novelty corpus to `bankedTheoremsForMethod(method_id)`,
   * and `pipeline.ts` fires the post-Stage-5 `close_open_question` hook.
   * Existing state files load as `null` (backward-compatible).
   */
  from_question_oq_id?: string | null;
  /**
   * Phase 3 — the seed Method id for the from-question OpenQuestion, captured
   * during the Stage -1.2 bundle resolution so Stage -0.5 can scope its
   * novelty corpus without re-walking the graph.
   */
  method_id?: string | null;
  /**
   * Phase 3 — populated by the post-Stage-5 close hook after a successful
   * `closeOpenQuestion`. Downstream tooling (and the Phase 4 CHECKPOINT_NEXT)
   * inspects this to confirm the OpenQuestion was minted into a
   * BankedTheorem.
   */
  closed_oq?: {
    oq_id: string;
    bt_id: string;
  } | null;
  /**
   * OpenQuestion ids banked by the Stage 0 short-circuit (zero Conjectures
   * + ≥1 load-bearing Open Question in the D-1.2 proposal §8). Present iff
   * the run terminated via that path. Each id corresponds to a node at
   * `<graph_root>/nodes/open_question/<oq_id>.json` (see
   * `mint_proposal_oq.ts`). A future `--from-question <oq_id>` dispatch
   * can claim/close any of these once a candidate construction is proposed.
   */
  banked_open_ended_question_ids?: string[];
  /**
   * Open-problem substrate produced by Stage -1.1 (literature scout). Populated
   * before Stage -1.2 (proposer) runs, so the proposer's seed-generation step
   * can anchor every seed to either a published paper or a prior CausalSmith
   * proposal/reviewer signal listed here. Absent until Stage -1.1 succeeds; in
   * non-propose mode, never populated.
   */
  gaps?: {
    /** Absolute or repo-relative path to the gaps.json artifact on disk. */
    gaps_path: string;
    /** Number of open problems recorded; must be ≥ 3 when status is "completed". */
    n_open_problems: number;
    /**
     * "completed" → advance to Stage -1.2.
     * "needs-pivot" → quantity bar failed (<3 problems after G1–G5) OR the
     * scout returned an unrecognized verdict; orchestrator halts so the user
     * can broaden/replace the topic. (A separate "rejected" R1–R4 verdict was
     * documented here historically but never implemented — the prompt, zod
     * schema, and handler only know completed|needs-pivot. Do not write
     * "rejected" into state: the schema refuses it on load.)
     */
    status: "completed" | "needs-pivot";
  };
  proposed_from?: {
    topic: string;
    novelty_target: NoveltyTarget;
    pivot_budget_used: number;
    final_verdict: string | null;
    proposal_path: string;
    novelty_justification: string;
    chosen_qid: string;
    chosen_specialization: string;
    cluster?: "panel" | "exactid" | "partialid" | "stat" | "experimentation" | "scm";
    /**
     * Scope caveats the D-0.5 proposal review ACCEPTED as conditional claims
     * ("sharp UNDER the saturation convention"). Persisted from the D-0.5 review
     * and surfaced to the Stage 0.5 derivation reviewer so it treats them as
     * settled scope rather than relitigating them as fresh correctness defects.
     */
    accepted_scope_caveats?: Array<{ label: string; caveat: string; bound_claim: string }>;
    seed_list?: string[];
    seed_details?: Array<Record<string, unknown>>;
    literature_map?: string;
    current_angle_index?: number;
    current_version?: number;
    current_mode?: "cold-start" | "revise" | "draft-rebuild" | "kernel-replace" | "pivot";
    /** Per-angle revision ceilings persisted by the angle-action CLI. Keys are
     * decimal angle indices. This replaces one-off environment-variable cap
     * bumps, so retries remain reproducible across resumes. */
    revision_cap_by_angle?: Record<string, number>;
    /** Halt written after a D-0.5 review and before another proposer starts.
     * `revise` lets the D-orchestrator persist a directive before continuing;
     * `angle-boundary` requires an explicit switch/retry/give-up decision. */
    angle_checkpoint?: {
      kind: "revise" | "angle-boundary";
      angle: number;
      version: number;
      verdict: string;
      reason: string;
      revise_cap: number;
      next_angle?: number;
    };
    kernel_replace_used_angles?: number[];
    draft_rebuild_used_angles?: number[];
    last_draft_handoff?: string;
    last_draft_status?: "completed" | "needs-pivot" | "invalid-draft" | "env-failure";
    exhausted_angles?: number[];
    last_reviewer_verdict?: string;
    iterations?: Array<{
      angle: number;
      version: number;
      mode: string;
      verdict: string;
      tier?: string;
      clean_substance?: boolean;
    }>;
    archived_proposals?: string[];
    upgrade_from?: UpgradeFrom;
  };
}

/**
 * Formalization-phase fields (Stages 2 … 5): scaffold/proof bookkeeping,
 * assumption accumulation, free-form design notes. `design_decisions` is
 * formally cross-phase but in practice every writer lives in formalization
 * code paths, so it is owned here.
 */
/** One cited node's persisted F4 source-match verdict. See {@link FormalizationState.cited_checks}. */
export interface CitedCheck {
  name: string;
  check_status: string;
  cite_id?: string;
  locator?: string;
  reviewer?: "codex" | "claude";
}

/** Durable, source-bound proof that one F4 peer checked a delivered cited node.
 * Unlike the compatibility `cited_checks` summary, this preserves peer identity and locator. */
export interface CitedReviewReceipt {
  node_id: string;
  reviewer: "codex" | "claude";
  check_status: string;
  cite_id: string;
  locator: string;
  evidence_hash: string;
}

/** Durable proof that each F4 peer independently accepted one disclosed omission.
 * The evidence hash binds the receipt to the current plan/graph contribution evidence,
 * so changing a role, reason, or dependency closure invalidates an old receipt. */
export interface DeliveryReviewReceipt {
  node_id: string;
  reviewer: "codex" | "claude";
  verdict: "matched" | "drift";
  evidence_hash: string;
  note?: string;
}

export interface FormalizationState {
  pending_sorries: PendingSorry[];
  design_decisions: Record<string, string>;
  added_assumptions: AddedAssumption[];
  /**
   * The F4 reviewer's CITED source-match verdicts. `cited-mismatch` / `cited-underspecified`
   * hard-block banking; persisting them lets `bankEntry` enforce that outside the review loop,
   * where the check previously lived only in memory.
   *
   * Optional for backward compatibility: every state written before this field existed omits it,
   * and the Zod schema defaults it to `[]` on parse. Absent ⇒ no cited nodes ⇒ nothing to block.
   */
  cited_checks?: CitedCheck[];
  cited_review_receipts?: CitedReviewReceipt[];
  delivery_review_receipts?: DeliveryReviewReceipt[];
}

export interface StateJson
  extends SharedState,
    DiscoveryState,
    FormalizationState {
  flags: SharedFlags & DiscoveryFlags & FormalizationFlags;
}

export interface PipelineContext {
  repoRoot: string;
  qid: string;
  specialization: string;
  dryRun: boolean;
  resume: boolean;
  /** `--auto`: drive the run autonomously (see `SharedState.auto_mode`). Persisted onto state. */
  auto?: boolean;
  proposeTopic?: string;
  noveltyTarget?: NoveltyTarget;
  upgradeFrom?: UpgradeFrom;
  /**
   * Optional override for Stage -1.2's draft runner. Selects between the
   * Codex (default) and Claude transports declared in
   * MODEL_PLAN.stageNeg1_2_draft. Both consume the same prompt text. Other
   * stages are unaffected.
   */
  proposerOverride?: DraftRunner;
  /**
   * Phase 3 — `/causalsmith --from-question <oq_id>` flag. On cold start the
   * pipeline atomically claims the OpenQuestion (status: in_progress) under
   * `withGraphWriteLock`, resolves its radius-1 neighborhood, and persists
   * `from_question_oq_id` on the run state. On clean Stage 5 completion the
   * close hook mints a BankedTheorem and flips status to closed_by:<bt_id>.
   * Mutually exclusive with `--propose`, `--upgrade`, `--upgrade-axis` (per
   * spec §7.1/7.2 the form is alone-standing).
   */
  fromQuestionOqId?: string;
}

export interface StageResult {
  stage: Stage;
  /**
   * Loop-control semantics:
   *  - `completed` / `skipped`: pipeline advances to `nextStage(stage)`.
   *  - `checkpoint`: pipeline halts; user must `--resume`. Use when human input is needed before the next stage can run (genuine CKPTs, NO-PASS-with-user-action, route=user interventions).
   *  - `blocked`: pipeline halts; `state.flags` carries the block reason. Used for missing-architecture and pre-Stage-(-1) gates.
   *  - `rewound`: handler programmatically reset `state.stage_completed` to an earlier marker; pipeline continues from `nextStage(state.stage_completed)`. Use when an intervention/escalation routes back to an earlier stage WITHOUT needing user input. `advance: false` MUST be set so the loop does not overwrite the handler's reset.
   */
  status: "completed" | "checkpoint" | "blocked" | "skipped" | "rewound";
  message: string;
  artifacts?: string[];
  advance?: boolean;
  completedStage?: Stage;
}

export interface PipelineLogEntry {
  timestamp: string;
  stage: Stage | "resume" | "init";
  model?: string;
  input_digest?: string;
  output_digest?: string;
  status: string;
  duration_ms: number;
  message?: string;
  /**
   * Condensed orchestrator reminder for a checkpoint/blocked halt: what to do
   * at this checkpoint + what the next phase is, with a pointer to the canonical
   * SKILL section. Populated by `checkpointGuidance`; absent on ordinary
   * `completed` transitions. The causalsmith-main skill tells the meta-orchestrator
   * to read this on the last pipeline.jsonl line so it re-grounds after a long run.
   */
  next_step_guidance?: string;
}
