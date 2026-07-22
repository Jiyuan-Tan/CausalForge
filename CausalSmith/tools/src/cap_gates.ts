import type { StateJson } from "./types.js";

type StateFlags = StateJson["flags"];

/**
 * A cap / halt flag that BLOCKS `--resume` until the orchestrator deliberately
 * clears it. This registry is the single source of truth shared by:
 *
 *  - `resolveResumeGates` (pipeline.ts) — reads `flags[flag]`; if truthy it refuses
 *    the resume and surfaces `guidance`.
 *  - the `--clear-gate <flag>` CLI surface (cli.ts) — calls `clear(flags)` as part of
 *    the resume, so the orchestrator NEVER hand-edits `state.json`. Hand-editing risks a
 *    Zod-invalid state that fails the NEXT resume; routing every flag flip through the CLI
 *    keeps the state schema-valid and the action auditable.
 *
 * Each `clear` nulls/undefines the blocking flag AND resets any paired counter (so the
 * cap does not immediately re-trip on the next pass).
 */
export interface CapGate {
  /** The flag key on `state.flags` that blocks resume while truthy. */
  flag: string;
  /** Clear the flag (+ reset any paired counter). */
  clear: (flags: StateFlags) => void;
  /** Halt-message guidance shown when the gate blocks a resume. */
  guidance: string;
}

export const CAP_GATES: CapGate[] = [
  {
    flag: "stage_neg1_fallback",
    clear: (f) => {
      f.stage_neg1_fallback = null;
      f.neg1_env_failure_retries = 0;
    },
    guidance:
      "bank the run (`bank_entry.ts --tier downgraded|failed`), or — after an out-of-band proposal revision — resume with `--clear-gate stage_neg1_fallback`",
  },
  {
    flag: "general_review_halt",
    clear: (f) => {
      f.general_review_halt = null;
    },
    guidance:
      "revise the proposal out-of-band, then resume with `--clear-gate general_review_halt`; or bank the run",
  },
  {
    flag: "substrate_build_required",
    clear: (f) => {
      f.substrate_build_required = null;
    },
    guidance:
      "build the Defer-item gates (cheapest route that unblocks), then resume with `--clear-gate substrate_build_required` to proceed with the gates assumed (discharge each landed build at the next checkpoint: wire the lemma into the Lean and rewind to F2.5 to re-review — NOT F1, since the plan/scaffold are unchanged — re-passing F4 before banking); OR clear it to proceed with the deferral as-is",
  },
  {
    flag: "theorem_splits_cap_hit",
    clear: (f) => {
      f.theorem_splits_cap_hit = undefined;
    },
    guidance:
      "decide split-vs-bank (review flags.theorem_splits), then resume with `--clear-gate theorem_splits_cap_hit`",
  },
  {
    flag: "stage0_budget_exhausted",
    clear: (f) => {
      f.stage0_budget_exhausted = undefined;
    },
    guidance:
      "grant more budget, then resume with `--clear-gate stage0_budget_exhausted`; or bank the run",
  },
  {
    flag: "stage1_rewinds_cap_hit",
    clear: (f) => {
      f.stage1_rewinds_cap_hit = undefined;
      f.stage1_rewinds = 0;
    },
    guidance:
      "fix the root cause, then resume with `--clear-gate stage1_rewinds_cap_hit` (also resets flags.stage1_rewinds)",
  },
  {
    flag: "scaffold_redirect_cap_hit",
    clear: (f) => {
      f.scaffold_redirect_cap_hit = undefined;
      f.scaffold_redirect_count = 0;
    },
    guidance:
      "fix the root cause, then resume with `--clear-gate scaffold_redirect_cap_hit` (also resets flags.scaffold_redirect_count — grants more in-place F2.5 reroute attempts)",
  },
  {
    // Covers EVERY proof-review-loop iteration budget: total iters, Phase-A scaffold-reroute
    // rounds, per-node strikes, tag reroutes, and the no-progress bound. These were in-process
    // locals, so a plain `--resume` reset them all silently — unbounded, unaudited re-rolls of a
    // non-deterministic reviewer (laundering by resampling). Now persisted; only MAIN clears.
    flag: "proof_loop_cap_hit",
    clear: (f) => {
      f.proof_loop_cap_hit = undefined;
      f.proof_loop_counters = {
        iters: 0,
        scaffold_rounds: 0,
        stale: 0,
        tag_reroutes: 0,
        node_strikes: {},
        review_error_strikes: {},
      };
    },
    guidance:
      "a proof-loop iteration budget is exhausted. Do NOT simply re-resume — that is a re-roll, not a retry, and the reviewer is non-deterministic. Diagnose the ROOT cause first (scaffolder drifting → `bin/f2_directive.ts`; reviewer wrong → fix the reviewer PROMPT as a pipeline-bug; plan wrong → rewind). Only once something at the root has CHANGED, resume with `--clear-gate proof_loop_cap_hit` (resets all loop counters). MAIN's authority only — a sub-orchestrator never resets its own cap.",
  },
  {
    // The D-phase analogue of `proof_loop_cap_hit`. D0_SOLVE_CAP (15 rounds) and
    // D0_REVISE_CAP (3 rounds) were in-process `for` bounds with no persisted counterpart,
    // so every plain `--resume` granted a fresh budget — the identical re-sampling defect
    // the proof-loop gate above was written to eliminate. `consistency_heals` is included
    // because it was previously wedge-only: capped at 1, persisted in `design_decisions`,
    // and absent from this registry, so once tripped there was NO CLI escape at all and
    // the run could only be freed by hand-editing state.json.
    flag: "d0_loop_cap_hit",
    clear: (f) => {
      f.d0_loop_cap_hit = undefined;
      f.d0_loop_counters = { solve_rounds: 0, revise_rounds: 0, consistency_heals: 0 };
    },
    guidance:
      "a D-phase loop budget is exhausted (D0 solve rounds, D0.5 revise rounds, or the D0 consistency self-heal). Do NOT simply re-resume — the solver and referees are non-deterministic, so that is a re-roll rather than a retry. Diagnose the root cause first (solver stuck → `bin/d0_directive.ts` with an exact construction; a proposal needs adjudicating → `bin/d0_apply_change.ts`; the math is wrong → rewind to D-1.2). Once something at the root has CHANGED, resume with `--clear-gate d0_loop_cap_hit` (resets all D-phase loop counters).",
  },
];

/** All clearable cap-gate flag names, for CLI validation + usage text. */
export const CAP_GATE_FLAGS: string[] = CAP_GATES.map((g) => g.flag);

/**
 * Clear a cap gate by flag name (mutates `flags`). Throws on an unknown name so the CLI
 * reports the valid set instead of silently no-op'ing. Returns the matched gate.
 */
export function clearCapGate(flags: StateFlags, name: string): CapGate {
  const gate = CAP_GATES.find((g) => g.flag === name);
  if (!gate) {
    throw new Error(
      `--clear-gate: unknown gate '${name}'. Known gates: ${CAP_GATE_FLAGS.join(", ")}`,
    );
  }
  gate.clear(flags);
  return gate;
}
