---
qid: pid_tv_pretrend_atet
spec: v1
topic: "Sharp partial identification of the average treatment effect on the treated (ATET) in staggered-adoption panel data under a total-variation (TV) bound on the pre-trend discrepancy — replacing the sup-norm / Lipschitz smoothness relaxations of Rambachan & Roth (2023). Establish a closed-form sharp width in terms of the TV-discrepancy bound and the pre-treatment outcome dispersion, characterise the critical-TV-discrepancy frontier separating sign-identification from vacuity, and exhibit when the closed form strictly tightens the sup-norm bound."
novelty_target: flagship
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: unknown
reraise_status: retry
gap_reasons:
  - 'Theorem 1: C-coherence — B is alternately an ATET support radius, an outcome-range cap, and a bias cap |omega''u|<=B; the theorem and assumptions do not use the same restriction.'
  - 'Theorem 2: C-sanity — The sign-loss frontier ignores the range cap: if |hat theta| > B, zero never enters the capped interval, but the formula gives a finite kappa_sign.'
  - 'Theorem 2 (angle1_v3): C-sanity — The proof uses ||Mz||_1 <= ||z||_1 from nonnegative row sums at most one, which is false; l1 contraction needs column-sum control.'
  - 'Theorem 1 (angle2): C-sanity — The support formula incorrectly scales the anchor term by kappa: the true support is d_{tau,-1} sum_h omega_h + kappa D_pre max_h |C_h|, not kappa times the unit-radius support.'
  - 'Conjecture 3: C-wellposed — The displayed row-space equality is dimensionally unclear: row(D_agg), row(A), and row(A D_coh) are not defined in compatible ambient spaces under the stated maps.'
  - 'Theorem 1 (angle3): N-pub — The sharp support-interval theorem is the finite-dimensional specialization of published Honest-DiD partial-ID support geometry, not a new kernel.'
  - 'Conjecture 1 (angle3): C-wellposed — Multiplying a set-valued interval by 1{varphi=0}, and the coverage/expected-length convention when the diagnostic rejects, are undefined.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The proposal attempted to derive a joint anchored-TV support body for a finite family of staggered-adoption ATT aggregates, with Theorem 1 claiming a closed-form dual norm Gamma_TV and Theorem 2 projecting scalar sign-loss frontiers from that body. The underlying TV dual-norm derivation via Abel summation and l1-duality is sound in outline, but every angle collapsed on the same algebra fault: the anchored TV support formula either conflated the anchor constant (d_{tau,-1} sum omega_h) with the TV slope, used a false l1-contraction step (||Mz||_1 <= ||z||_1 requires column-substochasticity, not nonnegative row sums), or produced a sign-loss frontier that ignored the outcome-range cap B. Conjecture 3 (generic non-rectangularity of the joint TV body versus the coordinatewise Rambachan-Roth rectangle) was never reached because the supporting theorems were not soundly established; the underlying geometric claim — that the TV body can be a strict non-rectangular subset of the coordinatewise rectangle — has a valid exhibit (Exhibit 9.1 at a=(1,-1)) and may be worth retrying once the algebra is fixed.
banked_on: "2026-05-24"
---

# pid_tv_pretrend_atet / v1 — Failed

**Topic.** Sharp partial identification of the average treatment effect on the treated (ATET) in staggered-adoption panel data under a total-variation (TV) bound on the pre-trend discrepancy — replacing the sup-norm / Lipschitz smoothness relaxations of Rambachan & Roth (2023). Establish a closed-form sharp width in terms of the TV-discrepancy bound and the pre-treatment outcome dispersion, characterise the critical-TV-discrepancy frontier separating sign-identification from vacuity, and exhibit when the closed form strictly tightens the sup-norm bound.

**Novelty target.** flagship

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Discovery stalled after 4 exhausted angles (best tier=letter at angle 3); angle 4 draft done but run died before review; blocking: N-pub on Theorems 1/2 (Honest-DiD specialization), B-algebra C-coherence, promissory Conjecture 1 without concrete witness.

## Key files

- `pid_tv_pretrend_atet_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_tv_pretrend_atet_v1_proposal.tex` — final proposal version.
- `pid_tv_pretrend_atet_v1.tex` — derivation note (if Stage 0 ran).
- `pid_tv_pretrend_atet_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_tv_pretrend_atet_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
