---
qid: panel_jackknife_signflip_phase
spec: v1
topic: "Leave-one-cluster sign-flip phase for two-way fixed-effect event-study ATT estimates. Pre-anchor: closest published anchors are Goodman-Bacon and de Chaisemartin-D'Haultfoeuille negative-weight decompositions, Sun-Abraham event-study contamination, and cluster jackknife influence diagnostics; closest banked proposals are q1_spectral_phase_transition_p1_markov and eid_bjs_if_contrast_frontier_v1. Our theorem is not that because it is not another negative-weight decomposition or standard influence-function statement: it gives an exact finite leverage table where the full TWFE/event-study contrast is positive but the leave-one-cluster jackknife contrast is negative, and derives the sharp threshold in the residualized cluster leverage h_g and signed cohort-time contrast s_g. Why non-trivial: the sign flip occurs without changing treatment effects, only by deleting one cluster and recomputing residualized weights. Why promising: the concrete object is a hand-specified 4 cluster by 4 period adoption table with residualized treatment column, cluster deletion Sherman-Morrison update, and a threshold inequality s_g h_g greater than the full contrast margin. Reject if the delta reduces to ordinary negative weights, support coverage, constrained-gradient geometry, or routine jackknife algebra without the finite witness table."
novelty_target: flagship
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "constructive_object_missing"
reusable: unknown
reraise_status: retry
gap_reasons:
  - "Angle 0 v1: D-0.5 REJECT at not-publishable tier; Conjecture 1 / Theorem 2 had N-promissory-object because Exhibit 9.1 substituted declared beta,h_2,s_2,ell_2 values without computing them from an explicit residualized 4x4 table."
  - "Angle 0 v1: reviewer flagged C-tautological-iff and C-definitional-unfold: once Assumption sm states beta_-g=(beta-J_g)/(1-ell_g), the sign frontier is immediate algebra rather than an independently derived object."
  - "Angle 0 v1: Theorem 2 claimed a nondegenerate four-cluster design, but the proposal contained only substituted coordinates, not the raw design/table realizing them."
  - "Angle 1 v1: D-0.5 REJECT at letter tier; Theorem 1 was already-known because BJS, Sun-Abraham, and Callaway-Sant'Anna already target cohort-time ATT under maintained support/common-effect conditions."
  - "Angle 1 v1: Conjecture 1 remained N-promissory-object: N, Q, h_A, s_A, and q_A were stipulated as residualized primitives rather than derived from a raw four-cluster outcome table."
  - "Angle 1 v1: reviewer found N-no-concrete-witness for flagship novelty: a single finite four-cluster witness plus minimality is not a generic-class obstruction or estimator frontier."
  - "Angle 1 v1: soundness issue in the no-refit corollary; the proposal displayed s_A=0.090 > N=0.080 but no separate fixed-residual deleted score."
reusable_artifacts:
  - "panel_jackknife_signflip_phase_v1_gaps.json: useful literature map for TWFE negative weights, event-study contamination, cluster leverage diagnostics, and the closest banked panel proposals."
  - "panel_jackknife_signflip_phase_v1_proposal_angle0_rejected.tex: negative example of a LOCO frontier that assumes its deletion update instead of deriving it from raw panel primitives."
  - "panel_jackknife_signflip_phase_v1_proposal_angle1_rejected.tex: finite equal-target TWFE deletion witness attempt; useful only as a checklist of what must be computed from raw outcomes before retrying."
  - "panel_jackknife_signflip_phase_v1_reviews/angle0_v1.json and angle1_v1.json: precise reviewer failure modes and strengthening paths."
seeds_burned: []
proof_attempt_summary: |
  This run tried to make a flagship panel/estimation-geometry result: a leave-one-cluster TWFE event-study sign flip with full-sample contrast positive, deleted-cluster refit negative, and modern ATT estimators remaining positive. The first angle collapsed because the LOCO frontier was tautological under an assumed deletion formula and the finite witness values were not computed from a displayed residualized table; the pivot improved the witness framing but still stipulated residualized primitives and reached only letter tier. A future retry needs a raw 4-by-4 outcome/adoption table with FWL residuals, N/Q/h/s/q, and all leave-one coefficients computed directly, plus an open-class theorem rather than a single cautionary finite example.
banked_on: "2026-05-25"
---

# panel_jackknife_signflip_phase / v1 — Failed

**Topic.** Leave-one-cluster sign-flip phase for two-way fixed-effect event-study ATT estimates. Pre-anchor: closest published anchors are Goodman-Bacon and de Chaisemartin-D'Haultfoeuille negative-weight decompositions, Sun-Abraham event-study contamination, and cluster jackknife influence diagnostics; closest banked proposals are q1_spectral_phase_transition_p1_markov and eid_bjs_if_contrast_frontier_v1. Our theorem is not that because it is not another negative-weight decomposition or standard influence-function statement: it gives an exact finite leverage table where the full TWFE/event-study contrast is positive but the leave-one-cluster jackknife contrast is negative, and derives the sharp threshold in the residualized cluster leverage h_g and signed cohort-time contrast s_g. Why non-trivial: the sign flip occurs without changing treatment effects, only by deleting one cluster and recomputing residualized weights. Why promising: the concrete object is a hand-specified 4 cluster by 4 period adoption table with residualized treatment column, cluster deletion Sherman-Morrison update, and a threshold inequality s_g h_g greater than the full contrast margin. Reject if the delta reduces to ordinary negative weights, support coverage, constrained-gradient geometry, or routine jackknife algebra without the finite witness table.

**Novelty target.** flagship

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped early after D-0.5 rejected two panel leave-one-cluster sign-flip angles: angle 0 was not-publishable because the LOCO frontier/witness was assumed rather than computed, and angle 1 stayed below flagship/letter tier as a finite TWFE deletion witness around routine negative-weight and jackknife algebra.

## Key files

- `panel_jackknife_signflip_phase_v1_state.json` — pipeline state at banking (`banked: true`).
- `panel_jackknife_signflip_phase_v1_proposal.tex` — final proposal version.
- `panel_jackknife_signflip_phase_v1.tex` — derivation note (if Stage 0 ran).
- `panel_jackknife_signflip_phase_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `panel_jackknife_signflip_phase_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

Do not relaunch this topic as a flagship seed unless the finite witness is hand-computed from raw panel primitives before D-1. The reviewer gave a concrete repair path: replace the residualized-coordinate exhibit by a raw 4-by-4 outcome table, compute FWL residuals and deletion coefficients directly, then lift the example to a nonempty region/open-class diagnostic.
