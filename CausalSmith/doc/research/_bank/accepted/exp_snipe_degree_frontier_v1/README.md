---
qid: exp_snipe_degree_frontier
spec: v1
topic: "Exact degree dependence of the minimax MSE for total-treatment-effect estimation under beta-order neighborhood interference and unit-randomized Bernoulli design: prove the matched frontier R* asymp d*binom(d,k*)/n over the bounded-coefficient bounded-degree class, where k*(beta,p) is the exposed order max{k<=beta: (1-p)^k-(-p)^k != 0}, delivering both the least-favourable family and the attaining estimator, and showing that BOTH bounds of Cortez-Rodriguez, Eichhorn and Yu (JCI 2023, arXiv:2208.05553) are loose -- their d-free Theorem 2 lower bound by d^(k*+1) and their Theorem 1 d^(beta+2) variance bound by a factor d -- contrary to their printed diagnosis; verified block witness at beta=1, p=1/2 gives Theta(d^2/n) two-sidedly with no observation noise"
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  # NONE — accepted with no gap. F4 dual-model convergence passed on all 29/29 delivered
  # plan nodes and 43/43 symbols, with ZERO gated and ZERO cited dependencies and
  # added_assumptions == []. D0.5 review_general: tier `field`, meets_floor true,
  # flagged_conjecture_labels [], improvement_directive null. Verbatim: "no conjecture or
  # assumed crux carries the headline".
  # Recorded scope narrowing (NOT a gap in the delivered result): the topic's original pitch
  # that BOTH bounds of Cortez-Rodriguez, Eichhorn & Yu (JCI 2023) are loose was RETIRED during
  # discovery — their Theorem 2 uses unbounded Gaussian priors, so it is not a converse on this
  # class, and the class-inclusion rescue is vacuous (unrestricted minimax risk is infinite as
  # B -> infinity). What is claimed and proved is the upper-bound half: their STATED worst-case
  # variance bound is tightened by a factor d, with d^beta replaced by binom(d,k*).
  # collapsed and why. Source: exp_snipe_degree_frontier_v1_reviews.jsonl and any
  # *_oneshot_stage0_5_*.txt files in this directory.
reusable_artifacts:
  # F7 substrate promotion (2026-07-28): the paper-independent parts of this run's
  # Le Cam machinery now live in Causalean and should be imported, not re-derived.
  - Causalean/Stat/Minimax/HellingerAffinity.lean   # densityAffinity, hellingerSqDensity,
      # hellingerSqDensity_eq_two_mul_one_sub_affinity, tvDist_le_sqrt_two_mul_one_sub_affinity,
      # one_sub_prod_le_sum, densityAffinity_pi (generalized to any finite product of
      # sigma-finite measure spaces).  Two-tilt common-density route to a TV bound.
  - Causalean/Stat/Minimax/MinimaxRisk.lean         # integral_le_sSup_range_of_isProbabilityMeasure
      # (Bayes risk <= worst-case risk), promoted from this run's Helpers/BayesRisk.lean.
  # Still run-coupled (deliberately NOT promoted): the cosine-squared prior computation
  # (Helpers/HellingerAffinity.lean), LocalLinearCompleteBlocks, LeastFavourableProperties,
  # SnipeVariance, BlockRepresenter*, BernoulliFourier, BlockScore, OverlapCount.
seeds_burned: []
proof_attempt_summary: |
  Delivered in full: the matched two-sided minimax frontier R* asymp B^2 * min{1, d*binom(d,k*)/n}
  for total-treatment-effect estimation under beta-order neighborhood interference and a
  Bernoulli(p) unit-randomized design, proved SIMULTANEOUSLY over the l1 coefficient-mass class
  and the strictly larger uniformly-bounded-outcome class (inclusion plus a ModelClassStrict
  witness, proved rather than assumed) and attained by CLIPPED SNIPE on the saturated branches;
  plus the exact local-linear minimax constant with its representer characterization. The degree
  order d^(k*+1) is set by the exposed order k*(beta,p) = max{k <= beta : (1-p)^k - (-p)^k != 0},
  i.e. by what the DESIGN exposes rather than by the model order (k* = beta except at p = 1/2 with
  beta even, where k* = beta - 1).
  Nothing collapsed mathematically. Discovery corrected itself four times under codex challenge —
  most consequentially, plain UNCLIPPED SNIPE does not satisfy the saturated B^2 branch (caught
  after two review rounds had missed it), and a discrete-shift Rademacher construction was
  unusable in a noiseless model and replaced by a bounded continuous baseline with finite Fisher
  energy. One F4 statement-vs-note gap was closed by STRENGTHENING the Lean (the PerturbFeasible
  attainment conjunct), never by weakening a claim.
  Remaining/open: inference theory (no CLT or confidence procedure), a fixed common propensity and
  fixed interaction order, and a known graph — the limitations that hold this at field rather than
  flagship tier. Verification at bank time: full lake build exit 0 (2899 jobs), source grep clean
  of sorry/admit/native_decide/axiom, and all six core statements axiom-clean
  [propext, Classical.choice, Quot.sound] under `lake env lean`.
banked_on: "2026-07-28"
paper_score: 7.8
paper_score_rationale: "The verified mathematical core delivers a sharp and useful minimax calibration, while the manuscript needs targeted prose repairs for comparison scope, cross-reference hygiene, and a few stale or confusing exposition points."
---

# exp_snipe_degree_frontier / v1 — Accepted

**Topic.** Exact degree dependence of the minimax MSE for total-treatment-effect estimation under beta-order neighborhood interference and unit-randomized Bernoulli design: prove the matched frontier R* asymp d*binom(d,k*)/n over the bounded-coefficient bounded-degree class, where k*(beta,p) is the exposed order max{k<=beta: (1-p)^k-(-p)^k != 0}, delivering both the least-favourable family and the attaining estimator, and showing that BOTH bounds of Cortez-Rodriguez, Eichhorn and Yu (JCI 2023, arXiv:2208.05553) are loose -- their d-free Theorem 2 lower bound by d^(k*+1) and their Theorem 1 d^(beta+2) variance bound by a factor d -- contrary to their printed diagnosis; verified block witness at beta=1, p=1/2 gives Theta(d^2/n) two-sidedly with no observation noise

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Matched two-sided minimax frontier R* asymp B^2*min{1, d*binom(d,k*)/n} for TTE estimation under beta-order neighborhood interference with a Bernoulli(p) unit-randomized design, proved SIMULTANEOUSLY over the l1 coefficient-mass class and the strictly larger uniformly-bounded-outcome class, attained by CLIPPED SNIPE; plus the exact local-linear minimax constant with representer characterization. Degree order is d^(k*+1) where k*(beta,p)=max{k<=beta:(1-p)^k-(-p)^k != 0} is the order the DESIGN exposes, not the model order (k*=beta except p=1/2 with beta even, where k*=beta-1). Tightens the stated worst-case variance bound of Cortez-Rodriguez, Eichhorn and Yu (JCI 2023) by a factor d and replaces d^beta with binom(d,k*). D0.5 tier field, meets_floor true, zero flagged conjectures. Fully proved: full lake build exit 0 (2899 jobs), source grep clean, all six core statements axiom-clean [propext, Classical.choice, Quot.sound] via lake env lean, 29/29 delivered plan nodes matched, 43/43 symbols matched, ZERO gated and ZERO cited dependencies, added_assumptions empty.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
