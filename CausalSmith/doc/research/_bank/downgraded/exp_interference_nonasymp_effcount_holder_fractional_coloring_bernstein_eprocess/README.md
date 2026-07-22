---
qid: exp_interference_nonasymp_effcount
spec: holder_fractional_coloring_bernstein_eprocess
topic: "Exponential-tail, dependency-adaptive nonasymptotic confidence interval for a design-based causal exposure effect under general network interference: for the Horvitz-Thompson exposure estimator theta_hat of an exposure contrast theta=(1/n)sum_i[Y_i(a)-Y_i(b)] under KNOWN Bernoulli assignment with a neighborhood-dependent exposure mapping c_i=g(Z_{N(i)}) and known exposure propensities pi_i(.)>=pi_exp, construct a Holder-normalized fractional-coloring Bernstein e-value over an exact b-fold coloring of the exposure-dependency graph D (i~j iff N(i) cap N(j) nonempty), giving a finite-sample CI |theta_hat-theta| <= sqrt(2 chi_f(D) Vbar log(2/alpha)/n) + chi_f(D) log(2/alpha)/(3 n pi_exp) with observable propensity-only envelope Vbar=n^{-1}sum_i[1/pi_i(a)+1/pi_i(b)], whose half-width tracks the effective independent-exposure count n/chi_f(D) with log(1/alpha) tails -- the first exponential-tail, chi_f-adaptive, general-network finite-sample CI for exposure-HT inference (improving Aronow-Samii's Chebyshev CI), the network-interference lift of the negative-dependence effective-sample-size idea of Sandoval-Balakrishnan-Feller-Jordan-Waudby-Smith 2601.11744"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "Novelty tier: subfield < requested field floor."
  - "The general fractional-color Bernstein interval is established supporting machinery, not the novelty claim."
  - "Unequal-block/conventional-alpha salvage requires genuinely new heterogeneous interval and weighted lower-bound research absent from the live package."
reusable_artifacts:
  - "discovery/core.json — validated mathematical core containing the design-unbiased exposure-HT result, fractional-color Bernstein interval, and clique-block same-class confidence-length sandwich."
  - "discovery/writeup.tex — pdflatex-verified derivation note."
  - "discovery/semantic_manifest.json — fail-closed contract for the canonical theorem and dependency-ownership interfaces."
  - "discovery/gaps.json — harvested literature and research gaps."
  - "orchestrator/decision_log.jsonl — complete mathematical, novelty, recovery, and terminal receipts."
seeds_burned:
  - index: 0
    one_liner: "Clique-block minimax frontier: determine whether n/chi_f(D_n) is the unavoidable finite-population effective exposure count for all design-valid intervals."
    reason: "The canonical clique-block same-class sandwich is sound but only subfield-level; field-tier salvage requires a genuinely new heterogeneous interval and weighted lower-bound argument."
proof_attempt_summary: |
  The run proved the finite-sample exposure-HT concentration result and a
  moderate-deviation clique-block same-class confidence-length sandwich whose
  effective count is n/(r 2^r). Independent math and positioning reviews passed,
  but novelty review placed the contribution at subfield rather than the requested
  field tier because the general upper interval is established substrate. A
  field-tier successor would need a genuinely new heterogeneous-network interval
  and matching weighted lower bound, rather than another refinement of this block witness.
banked_on: "2026-07-16"
---

# exp_interference_nonasymp_effcount / holder_fractional_coloring_bernstein_eprocess — Downgraded

**Topic.** Exponential-tail, dependency-adaptive nonasymptotic confidence interval for a design-based causal exposure effect under general network interference: for the Horvitz-Thompson exposure estimator theta_hat of an exposure contrast theta=(1/n)sum_i[Y_i(a)-Y_i(b)] under KNOWN Bernoulli assignment with a neighborhood-dependent exposure mapping c_i=g(Z_{N(i)}) and known exposure propensities pi_i(.)>=pi_exp, construct a Holder-normalized fractional-coloring Bernstein e-value over an exact b-fold coloring of the exposure-dependency graph D (i~j iff N(i) cap N(j) nonempty), giving a finite-sample CI |theta_hat-theta| <= sqrt(2 chi_f(D) Vbar log(2/alpha)/n) + chi_f(D) log(2/alpha)/(3 n pi_exp) with observable propensity-only envelope Vbar=n^{-1}sum_i[1/pi_i(a)+1/pi_i(b)], whose half-width tracks the effective independent-exposure count n/chi_f(D) with log(1/alpha) tails -- the first exponential-tail, chi_f-adaptive, general-network finite-sample CI for exposure-HT inference (improving Aronow-Samii's Chebyshev CI), the network-interference lift of the negative-dependence effective-sample-size idea of Sandoval-Balakrishnan-Feller-Jordan-Waudby-Smith 2601.11744

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** Math review PASS and positioning review PASS, but the independent novelty tier was subfield below the requested field floor.

## Key files

- `exp_interference_nonasymp_effcount_holder_fractional_coloring_bernstein_eprocess_state.json` — pipeline state at banking (`banked: true`).
- `exp_interference_nonasymp_effcount_holder_fractional_coloring_bernstein_eprocess_proposal.tex` — final proposal version.
- `exp_interference_nonasymp_effcount_holder_fractional_coloring_bernstein_eprocess.tex` — derivation note (if Stage 0 ran).
- `exp_interference_nonasymp_effcount_holder_fractional_coloring_bernstein_eprocess_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `exp_interference_nonasymp_effcount_holder_fractional_coloring_bernstein_eprocess_reviews/` — per-version reviewer JSON files (if present).

## Notes

The package was banked at the discovery boundary and did not enter Lean
formalization. The mathematical core is sound and useful as a benchmark, but the
current angle is burned for a field-tier claim. Reuse the verified concentration
and witness machinery only as substrate for a materially broader heterogeneous
construction.
