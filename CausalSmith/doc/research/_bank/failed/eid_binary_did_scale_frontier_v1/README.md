---
qid: eid_binary_did_scale_frontier
spec: v1
topic: "Additive parallel-trends DiD versus odds-ratio equi-confounding DiD for binary outcomes; finite observed 2x2x2 table frontier for additive, OREC/UDiD, and corrected scale-transport ATT maps."
novelty_target: flagship
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "angle0_v1: Theorem 1 / Conjecture 1 were incoherently phrased as simultaneous additive parallel trends and OREC assumptions; off the frontier they must be alternative transport maps."
  - "angle0_v1: Theorem 1 was flagged C-definitional-unfold: solve OREC, define Delta_OR-add=q_L-q_A, and factor q_L=q_A."
  - "angle0_v1: Conjecture 1 promised an open-cell finite SWIG witness family but only set conditional means p11=q_A or p11=q_L, not a full finite observed/latent law."
  - "angle0_v1: Conjecture 2's scale-link exhibit was false as written; the proposed probit value on the symmetric branch did not separate from q_A."
  - "angle0_v2: still field-tier under flagship target. Reviewer called Theorem 1 a direct finite-table algebraic corollary of OREC/UDiD and said flagship would require an observable test statistic, asymptotic distribution, or decision rule."
  - "angle0_v2: Conjecture 2 remained under-anchored against Roth-Sant'Anna functional-form sensitivity and Wooldridge nonlinear DiD."
reusable_artifacts:
  - "eid_binary_did_scale_frontier_v1_gaps.json: literature map and seed list for additive-vs-OREC binary DiD scale conflicts."
  - "eid_binary_did_scale_frontier_v1_reviews/angle0_v1.json: useful defect list for incoherent simultaneous assumptions, missing full-law witness, and false scale-link exhibit."
  - "eid_binary_did_scale_frontier_v1_reviews/angle0_v2.json: decisive flagship-ceiling review; use as a stop anchor for future algebraic Delta_OR-add variants."
  - "eid_binary_did_scale_frontier_v1_proposal.tex: contains observed algebra q_A, q_L, Delta_OR-add and numeric witness sketches; reusable only as a field-tier diagnostic scaffold."
seeds_burned:
  - "Finite binary additive-vs-OREC equality frontier."
  - "Open-cell SWIG non-nesting witness without full finite law."
  - "Scale-link invariance frontier around additive/logit/probit transports."
proof_attempt_summary: |
  Attempted to turn binary additive DiD versus OREC/UDiD into a flagship finite-table equality frontier with Delta_OR-add and non-nesting witnesses. The reviewer accepted that the repo axis was clear, but twice kept the proposal at field tier because the main theorem was routine logit/OREC algebra and the witness/scale-invariance claims lacked a full finite law or close comparator anchors. Do not revive this as another equality-frontier proposal unless the core object becomes a named estimator or inference geometry with a decision rule beyond definition unfolding.
banked_on: "2026-05-25"
---

# eid_binary_did_scale_frontier / v1 - Failed

**Topic.** Additive parallel-trends DiD versus odds-ratio equi-confounding DiD for binary outcomes, targeting a finite observed table frontier between additive risk transport, OREC/UDiD logit transport, and corrected scale transport.

**Novelty target.** flagship

**Stage -0.5 verdict.** REVISE / field at angle0 v1 and angle0 v2.

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped at D-0.5 after angle0 v2 remained field-tier under the flagship target. The main theorem was still routine Delta_OR-add=q_L-q_A algebra, and the reviewer said a flagship upgrade would require a named estimator/frontier package with an observable statistic, asymptotic distribution, or decision rule rather than another equality-frontier revision.

## Key Files

- `eid_binary_did_scale_frontier_v1_state.json` - pipeline state at banking.
- `eid_binary_did_scale_frontier_v1_gaps.json` - harvested literature and seed list.
- `eid_binary_did_scale_frontier_v1_proposal.tex` - final proposal version.
- `eid_binary_did_scale_frontier_v1_reviews.jsonl` - per-round reviewer log.
- `eid_binary_did_scale_frontier_v1_reviews/angle0_v1.json` - first D-0.5 review.
- `eid_binary_did_scale_frontier_v1_reviews/angle0_v2.json` - decisive second D-0.5 review.

## Reflection

Failure cause: topic/proposal strength, not reviewer strictness or D0 solver weakness. The proposal did repair some coherence issues between v1 and v2, but the remaining mathematical core was a finite-table algebraic corollary of OREC/UDiD rather than a nonroutine flagship object. Future binary-DiD topics should start from estimator geometry, inference, or a full finite-law witness class; do not spend more attempts on Delta_OR-add equality-frontier variants alone.
