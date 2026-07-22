---
qid: exp_ego_cluster_exposure_clt
spec: ego_cluster_polynomial_clt
topic: "Design-based Wald inference for ego-cluster network experiments via exposure-incidence polynomials: finite-population HT exposure contrasts, closed first/joint exposure probabilities, and a dependency-graph CLT under bounded ego-overlap"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  # Verbatim D0.5.G cold-tier referee (reviews/stage_0.5.G_attempt2.json) — math PANEL passed; the TIER did not clear field.
  - "The advertised CLT is therefore not a new limit theorem or sharper rate; it is an application of Chin's theorem after elementary support bookkeeping."
  - "The feasible variance result is completion-sharp only because Vbar_n is defined as the supremum over all bounded completions, so the sharpness is tautological within that envelope class and does not establish estimator-class optimality or practical tightness."
  - "It does not yet provide a field-level new rate, primitive characterization, or broadly reusable inference method."
  # codex tier adjudication (honest-subfield): none of the three field-lift paths is reachable under the same assumptions —
  - "(a) converse/necessity: o(n^(1/4)) is a sufficient Stein-bound artifact, not shown necessary; would need new lower-bound machinery."
  - "(b) estimator-class optimality: Vbar_n is a completion supremum, not minimal over quadratic-form variance estimators (HMS, arXiv:2112.01709)."
  - "(c) primitive iff: CLT validity cannot be characterized by overlap primitives alone (variance structure, outcome cancellations, distributional degeneracies)."
reusable_artifacts:
  # The proved kernel is SOUND and internally consistent (zero dangling refs) — lift it for a re-raise rather than re-derive.
  - "discovery/core.json — exact inclusion-exclusion algebra for first/joint signed-incidence target-exposure probabilities (prop:incidence-probabilities) + ego-overlap dependency-degree screen Delta_n <= b_n(omega_n-1) <= 2 q_n kappa_n(omega_n-1) (prop:dependency-degree)."
  - "discovery/core.json — feasible completion-envelope Vbar_n = max_{y in F_n^obs} Q_n(y) with the four proved supporting lemmas (lem:variance-envelope-{dominates,computable-attained,sharp}, lem:uniform-oracle-wald-coverage)."
  - "discovery/proto_core.json — frozen skeleton with the weakened consumed-rate assumption Delta_n=o(n^(1/4)) and the honest positioning vs Aronow-Samii / Chin / Harshaw-Middleton-Savje."
seeds_burned: []
proof_attempt_summary: |
  A complete, sound, panel-passing design-based inference kernel for ego-cluster network experiments:
  exact signed-incidence exposure-probability algebra + an ego-overlap dependency-degree screen feeding a
  cited dependency-graph Stein CLT (oracle + feasible conservative Wald under growing degree Delta_n=o(n^(1/4))),
  plus a computable completion-sharp variance envelope. The math is correct and useful, but the cold tier
  referee and an independent codex adjudication both rate it SUBFIELD, not field: the CLT is Chin's theorem
  after exposure bookkeeping and the envelope sharpness is tautological-within-class, so it delivers no
  field-level new rate, necessity result, estimator-class optimum, or primitive iff. Re-raise path: re-anchor
  the SAME sound kernel at a genuine field headline (a Berry-Esseen / necessity rate for the ego-polynomial
  class, or HMS-style estimator-class optimality of Vbar_n) rather than the application-level CLT framing.
banked_on: "2026-06-30"
---

# exp_ego_cluster_exposure_clt / ego_cluster_polynomial_clt — Downgraded

**Topic.** Design-based Wald inference for ego-cluster network experiments via exposure-incidence polynomials: finite-population HT exposure contrasts, closed first/joint exposure probabilities, and a dependency-graph CLT under bounded ego-overlap

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5.G tier=subfield < field floor: the HT CLT is an application of Chin's dependency-graph Stein CLT after exact ego-incidence exposure-probability bookkeeping, and the feasible-Wald sharpness is tautological within the completion-envelope class — sound and useful infrastructure but not a field-level new rate, necessity theorem, estimator-class optimum, or primitive characterization.

## Key files

- `exp_ego_cluster_exposure_clt_ego_cluster_polynomial_clt_state.json` — pipeline state at banking (`banked: true`).
- `exp_ego_cluster_exposure_clt_ego_cluster_polynomial_clt_proposal.tex` — final proposal version.
- `exp_ego_cluster_exposure_clt_ego_cluster_polynomial_clt.tex` — derivation note (if Stage 0 ran).
- `exp_ego_cluster_exposure_clt_ego_cluster_polynomial_clt_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `exp_ego_cluster_exposure_clt_ego_cluster_polynomial_clt_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
