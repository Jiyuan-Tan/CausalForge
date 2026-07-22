---
qid: pid_continuous_iv_no_monotonicity
spec: v1
topic: "Sharp partial identification of the local average treatment effect under a continuous instrument when the Imbens-Angrist monotonicity restriction is relaxed to a calibrated bounded-violation regime — the share of the population whose first-stage response is non-monotonic in the instrument is bounded above by a known propensity-derivative envelope — characterizing the sharp identified set of LATE as a function of the violation budget and the observed propensity-derivative function, recovering Heckman-Vytlacil MTE point identification at the trivial bound, and proving a strict-gap structural separation theorem against the standard quasi-monotone IV identifying formula"
novelty_target: flagship
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - 'Theorem sharp-pasting / Section 7: The theorem defines the shadow set by existence of a full-data law in the original feasible set, then proves sharpness by unpacking that definition, so the flagship equality is not an independent characterization.'
  - 'Proof of Conjecture 1: Endpoint attainment relies on unproved compactness and closedness claims for full-data laws, full-P matching for every z, absolute-continuity constraints, and a positive denominator bounded away from zero.'
  - 'Finite mesh linear-fractional program: The finite program is only sketched and its convergence to the continuous sharp endpoints is asserted, not stated as a precise optimization theorem with explicit approximation hypotheses.'
  - 'Theorem strict-separation: The witness is explicit and arithmetically plausible, but it is a hand-built tagged-cell example rather than a generic-class obstruction against a named published estimator/workflow using the refuted quasi-monotone formula.'
  - 'Novelty tier floor: Assessed tier is at most subfield, below novelty_target=flagship, because the main sharp-set theorem is definitional and the negative result lacks the published-target and generic-class structure required for flagship status.'
  - 'Conjecture 1 verdict (angle 0): Lines 424-434 explicitly leave endpoint attainment and compactness/closedness unproved, so the flagship sharpness claim is not delivered.'
  - 'Conjecture 2 verdict (angle 0): Lines 486-493 explicitly leave the nonempty open-set witness and endpoint-map continuity unproved, replacing the flagship separation theorem with a conditional certificate.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The run attempted to characterize the sharp identified set for LATE under a continuous instrument when monotonicity is relaxed to a calibrated bounded negative-response-density envelope, pivoting after angle 0 collapsed to a derivative-process feasibility framing (K_b^proj as the closure of a linear projection system). The local signed-measure equations and zero-envelope Heckman-Vytlacil reduction held, but the flagship Conjecture 1 (sharp pasting / support-function iff certificate) was rejected at Stage 0 as tautological by construction — the shadow set was defined via existence of a feasible full-data law, so sharpness was a change-of-variables, not an independent characterization — and the finite-mesh LP structure was unproved. Conjecture 2 produced an internally consistent arithmetic witness but lacked generic-class obstruction against a named published estimator, leaving the negative-result novelty below flagship floor.
banked_on: "2026-05-21"
---

# pid_continuous_iv_no_monotonicity / v1 — Failed

**Topic.** Sharp partial identification of the local average treatment effect under a continuous instrument when the Imbens-Angrist monotonicity restriction is relaxed to a calibrated bounded-violation regime — the share of the population whose first-stage response is non-monotonic in the instrument is bounded above by a known propensity-derivative envelope — characterizing the sharp identified set of LATE as a function of the violation budget and the observed propensity-derivative function, recovering Heckman-Vytlacil MTE point identification at the trivial bound, and proving a strict-gap structural separation theorem against the standard quasi-monotone IV identifying formula

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0 re-test (post D0-solver upgrade) on prior kernel_substituted parent: First post-restore D0.5 on the original proposal returned REJECT@flagship - Theorem sharp-pasting / Section 7 correctness, Proof of Conjecture 1 correctness, Finite mesh linear-fractional program structure. New D0 produced a derivation whose headline sharp-pasting theorem has proof correctness gaps and the finite-mesh LP structure is broken. Intervention routing reason: case 6b - reject on conjecture-level grounds (kernel_substituted, definitional flagship, no generic-class obstruction), headline theorem tautological by construction. Pipeline pivoted to angle 1 v3 but run was stopped mid-pivot per user direction. Apples-to-apples verdict on original kernel: new D0 still produces a derivation with headline-theorem correctness gaps; kernel_substituted persists.

## Key files

- `pid_continuous_iv_no_monotonicity_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_continuous_iv_no_monotonicity_v1_proposal.tex` — final proposal version.
- `pid_continuous_iv_no_monotonicity_v1.tex` — derivation note (if Stage 0 ran).
- `pid_continuous_iv_no_monotonicity_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_continuous_iv_no_monotonicity_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
