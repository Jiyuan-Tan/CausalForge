/**
 * Types for paper-scoped causalsmith dispatch.
 *
 * A paper-wide causalsmith run covers multiple Theorems extracted from the same
 * Insight in a single spawn. `TheoremEntry` tracks per-theorem stage progress
 * within that run; `PaperBatch` is the dispatcher input that describes what
 * causalsmith should prove.
 *
 * `TheoremEntry` is persisted in the causalsmith state JSON (one per theorem in
 * the batch) so that stages can record progress for each theorem independently.
 * On success (Stage 5), a `TheoremEntry` becomes a `BankedTheorem` in the graph.
 * On failure, it becomes a failure-Note.
 */
import type { Stage } from "../types.js";

/**
 * Per-theorem entry inside a paper-scoped causalsmith run. One TheoremEntry maps
 * 1:1 to one BankedTheorem on success and to one failure-Note on Stage 5
 * failure. `theorem_local_id` is the suffix after stripping `<insight_id>_`
 * from `origin_theorem_id`; it is the stable handle stages refer to.
 */
export interface TheoremEntry {
  /** Stable per-paper handle, e.g. "t1". Used in Lean filenames. */
  theorem_local_id: string;
  /** Source study-pipeline Theorem.theorem_id, e.g. "ins1_t1". */
  origin_theorem_id: string;
  /** Full statement copied from the source Theorem. */
  statement: string;
  /** Proof sketch from study-pipeline S0; null falls back to placeholder. */
  proof_sketch: string | null;
  /** Per-theorem lifecycle within the paper run. */
  status: "pending" | "in_progress" | "completed" | "stuck" | "failed";
  /**
   * Last stage that completed for THIS theorem. `null` until stage 0 first
   * touches the theorem. Paper-wide stages (e.g. `2` scaffold of Common)
   * update every entry to the same value.
   */
  stage_completed: Stage | null;
  /**
   * Relative path under the lean_subdir, e.g. "Theorem_t1.lean". `null` until
   * stage 2 writes the per-theorem file.
   */
  lean_file_relpath: string | null;
  /** Optional human-readable diagnosis when status is "stuck" | "failed". */
  failure_reason?: string;
  /** Lean declaration name for THIS theorem inside the paper module
   * (e.g. `"t1_thm"`). Set by Stage 2 scaffold. Stage 5 uses this to
   * derive BankedTheorem IDs and Lean import paths. */
  lean_decl_name?: string;
  /**
   * BankedTheorem id written by `closeOpenQuestion` after Stage 5 completes.
   * Format: `<insight_id>_<theorem_local_id>_<spec>`, e.g. `"ins1_t1_v1"`.
   * Absent until the post-Stage-5 close hook runs successfully.
   * Used by study-pipeline S5 to look up the BankedTheorem file for reconciliation.
   */
  bt_id?: string;
  /**
   * OpenQuestion id minted by `mintFailedTheoremOpenQuestion` at bank time for
   * a failed theorem that cleared Stage 0.5. Mirror of `bt_id` on the failure
   * side. Format: `oq_failed_<qid>_<spec>_<theorem_local_id>`. Absent on
   * completed/stuck entries or on failures gated below Stage 0.5.
   */
  minted_oq_id?: string;
}

/**
 * Dispatcher input. One PaperBatch produces one causalsmith spawn.
 *
 * `shared_setup` is the paper-wide preamble (random-variable definitions,
 * notation) that appears once at the top of the seed `.tex` and is referenced
 * by every theorem. Per-theorem `setup` text is folded into this when the
 * paper has only one Theorem (degenerate case).
 */
export interface PaperBatch {
  insight_id: string;
  shared_setup: string;
  /**
   * Lean substrate hint for this paper. Used by `paper_dispatcher` to stamp
   * `state.lean_subdir` since insight-id qids do not encode substrate. S4
   * resolves this from the parent Insight node (heuristic from `instantiates`
   * / topic, or an explicit `substrate` field on the Insight schema if set).
   * When absent the dispatcher defaults to `"Panel"`.
   */
  lean_substrate?: "Panel" | "ExactID" | "PartialID";
  theorems: Array<{
    theorem_local_id: string;
    statement: string;
    proof_sketch: string | null;
  }>;
}
