---
qid: eid_proximal_did_bridge_frontier
spec: v1
topic: "New flagship topic: proximal difference-in-differences bridge frontier with negative controls. Pre-anchor check: closest published anchors are Miao-Geng-Tchetgen proximal causal inference, Tchetgen-Tchetgen negative-control bridge work, standard two-period and staggered DiD identification, and recent papers on difference-in-differences with negative controls. Our theorem is not those because the focal object is a finite pretrend-proxy bridge operator that sharply separates three regimes: ordinary parallel-trends DiD identifies ATT, proximal negative-control DiD identifies ATT even when parallel trends fails, and neither identifies ATT. Require a concrete nonroutine object: an explicit 2-group x 3-period x binary-proxy witness with observed negative-control outcome and exposure, a bridge-rank condition computed from pre-period moments, and a non-equivalence theorem showing the proximal bridge and parallel-trends restrictions are neither nested nor equivalent. If the proposal reduces to generic proximal completeness, ordinary DiD placebo tests, support coverage, or a definition-unfold rank condition without a worked witness and non-equivalence class, pivot or stop early."
novelty_target: flagship
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Angle 0 v1: the advertised constructive frontier was only moment rows, not a full finite observed/latent law computing every object from primitives."
  - "Angle 0 v1: Assumption 6 already encoded the iff frontier, so Conjecture 1 partly unfolded an assumption."
  - "Angle 0 v2: Theorem 1 was already the proximal null-annihilator point-identification criterion from eid_proximal_phase_v1 plus the standard DiD decomposition."
  - "Angle 0 v2: Conjecture 1 remained a finite bridge-fiber well-definedness criterion, not a strict named NC-DiD estimator frontier."
  - "Angle 0 v2: the proposal still had a W/Z proxy-role convention mismatch and missing proximal-panel comparator anchors."
reusable_artifacts:
  - "eid_proximal_did_bridge_frontier_v1_gaps.json: useful literature map for negative-control DiD, proximal bridges, single-proxy controls, and multiple-preperiod panel bridge comparators."
  - "eid_proximal_did_bridge_frontier_v1_reviews/angle0_v1.json: reviewer diagnosis requiring full finite latent laws rather than moment rows."
  - "eid_proximal_did_bridge_frontier_v1_reviews/angle0_v2.json: concise final diagnosis that the kernel is the existing null-annihilator bridge criterion specialized to DiD."
  - "eid_proximal_did_bridge_frontier_v1_proposal.tex: revised field-tier proposal with a concrete binary-proxy table, useful only as setup for a future estimator-frontier theorem."
seeds_burned: []
proof_attempt_summary: |
  Attempted a finite proximal DiD bridge frontier separating parallel-trends-only, proximal-only, and nonidentified regimes. The witness idea was concrete, but the theorem-level object did not clear flagship: it reduced to the known bridge-fiber/null-loading criterion from proximal identification plus standard DiD decomposition. Reuse the literature map and binary table only if a future proposal targets a named NC-DiD estimator or proximal-panel bridge formula and proves a strict extension/non-equivalence result.
banked_on: "2026-05-25"
---

# eid_proximal_did_bridge_frontier / v1 - Failed

**Topic.** New flagship topic: proximal difference-in-differences bridge frontier with negative controls. Pre-anchor check: closest published anchors are Miao-Geng-Tchetgen proximal causal inference, Tchetgen-Tchetgen negative-control bridge work, standard two-period and staggered DiD identification, and recent papers on difference-in-differences with negative controls. Our theorem is not those because the focal object is a finite pretrend-proxy bridge operator that sharply separates three regimes: ordinary parallel-trends DiD identifies ATT, proximal negative-control DiD identifies ATT even when parallel trends fails, and neither identifies ATT. Require a concrete nonroutine object: an explicit 2-group x 3-period x binary-proxy witness with observed negative-control outcome and exposure, a bridge-rank condition computed from pre-period moments, and a non-equivalence theorem showing the proximal bridge and parallel-trends restrictions are neither nested nor equivalent. If the proposal reduces to generic proximal completeness, ordinary DiD placebo tests, support coverage, or a definition-unfold rank condition without a worked witness and non-equivalence class, pivot or stop early.

**Novelty target.** flagship

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped after two D-0.5 REVISE@field reviews under flagship target: the finite bridge-rank frontier remained a proximal null-annihilator/bridge-fiber definition specialized to DiD, with no named NC-DiD estimator frontier or strict extension beyond existing proximal panel bridge results.

## Key files

- `eid_proximal_did_bridge_frontier_v1_state.json` - pipeline state at banking (`banked: true`).
- `eid_proximal_did_bridge_frontier_v1_proposal.tex` - final proposal version.
- `eid_proximal_did_bridge_frontier_v1_reviews.jsonl` - per-round reviewer log.
- `eid_proximal_did_bridge_frontier_v1_reviews/` - per-version reviewer JSON files.

## Notes

Reflection: this was a topic/proposal-strength failure. The proposer found a plausible field-tier finite witness but did not create a new flagship object; the reviewer was correct to demand a strict comparator theorem against named negative-control DiD or proximal panel estimators. Not a pipeline bug and not a D0 solver issue.
