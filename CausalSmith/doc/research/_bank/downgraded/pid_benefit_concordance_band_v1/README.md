---
qid: pid_benefit_concordance_band
spec: v1
topic: "Continuous-outcome nonparametric sharp bounds on the proportion who benefit from treatment, Pr(Y1 > Y0), under a rank-concordance band — Spearman's rho of the potential-outcome copula constrained to [rho_minus, rho_plus] rather than a fixed copula family — with the critical concordance rho* at which the benefit-majority sign (Pr > 1/2 vs < 1/2) becomes data-undetermined; plug-in endpoint estimators and Imbens-Manski/Stoye inference over the partially-identified interval. Differentiate from arXiv:2605.11415 (ordinal latent-threshold, single-family envelope) and Fan-Park Makarov (marginals-only, copula free)."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: ACCEPT
proposal_promise_gap: "constructive_object_missing"
reusable: unknown  # solver NOT blocked and artifacts ARE concretely reusable (LP/transport setup, weak-duality dual certificate, checkerboard estimator, bootstrap endpoint law); valid set has no positive "reusable" value, so unknown is the residual — see reusable_artifacts
reraise_status: retry
gap_reasons:
  # Final-round reviewer phrases (pid_benefit_concordance_band_v1_reviews.jsonl,
  # stage_0.5_to_0 attempts 1-2; conj verdict JSONs). Math NOT refuted — the
  # downgrade is a promise gap: the SHARP claim collapsed to an OUTER envelope.
  - "The original sharp identified interval claim in Conjecture 1 is not confirmed; the result establishes only an outer-envelope dual representation, not sharpness or closed endpoint attainability."  # attempt 1, k-sharp-dual-confirmed:correctness
  - "The theorem proves only pointwise no-gap dual endpoint values L_x(P)=D_x(h_x), U_x(P)=-D_x(-h_x), and explicitly disclaims endpoint attainment, measurable argmax selectors, and Theta_I(P)=[L_rho(P),U_rho(P)]."  # attempt 1
  - "The reverse inequality is not reproduced: ... Kellerer marginal duality alone does not add the uv-moment constraint ... the no-gap endpoint formula ... is unproved as stated; the theorem needs an explicit moment-constrained bounded-Borel transport duality theorem or a new proof."  # attempt 2, reverse strong-duality step
  - "delivered an exact dual representation + delta-method/bootstrap inference for an OUTER Spearman-band endpoint under strong regularity, not the sharp identified-set equality / sign-indeterminacy result the headline promised — a sound subfield partial-ID contribution, below the field target."  # D0.5.G cold-referee banking reason
  # NOTE: novelty was NOT the blocker — final round (stage_0.5_to_0 attempt 3)
  # records novelty:pass and correctness:pass for the WEAKENED kernel. The bank
  # is a tier/promise downgrade (field→subfield), not a novelty rejection.
reusable_artifacts:
  - pid_benefit_concordance_band_setup.json  # locked PartialID tuple, named assumptions (sampling/regular/band/stable-dual/finite-cell), conjecture + supporting-theorem registry
  - pid_benefit_concordance_band_conj_1_fragment.tex  # weak Spearman-band dual certificate D_x(g) (computable outer bound) + finite two-strata refutation search
  - pid_benefit_concordance_band_conj_2_fragment.tex  # confirmed bootstrap/delta-method endpoint inference (checkerboard LP, directional Hadamard expansion)
  - pid_benefit_concordance_band_v1.tex  # full derivation note (Theorem 1 closure envelope, Theorem 2 outer-envelope diagnostic, Conjecture 1 no-gap duality, Theorem inference)
  - pid_benefit_concordance_band_v1_gaps.json  # Stage -1.1 literature/open-problem harvest (Makarov/Fan-Park/Kellerer/Spearman-band comparators)
seeds_burned: []
proof_attempt_summary: |
  Attempted sharp nonparametric Spearman-band identified set for Pr(Y1>Y0) with a
  majority-sign critical-rho* indeterminacy result and Imbens-Manski/Stoye endpoint
  inference. Reviewers accepted the math in WEAKENED form — a computable weak-duality
  OUTER envelope (Theorem 1), an outer-envelope majority-sign DIAGNOSTIC (Theorem 2),
  and a confirmed bootstrap/delta-method endpoint limit law (inference, confirmed) —
  with no defect found in that scoped package. What collapsed is the headline: the
  no-gap (primal=dual) strong-duality EQUALITY that makes the interval sharp was
  demoted to unproved Conjecture 1 (Kellerer marginal duality does not supply the
  uv-Spearman-moment constraint), and "indeterminacy" softened to an outer-bound
  diagnostic. Parked on tier/promise (field→subfield), not novelty: the cold referee
  judged the delivered outer-bound contribution sound but below the field target.
banked_on: "2026-06-09"
---

# pid_benefit_concordance_band / v1 — Downgraded

**Topic.** Continuous-outcome nonparametric sharp bounds on the proportion who benefit from treatment, Pr(Y1 > Y0), under a rank-concordance band — Spearman's rho of the potential-outcome copula constrained to [rho_minus, rho_plus] rather than a fixed copula family — with the critical concordance rho* at which the benefit-majority sign (Pr > 1/2 vs < 1/2) becomes data-undetermined; plug-in endpoint estimators and Imbens-Manski/Stoye inference over the partially-identified interval. Differentiate from arXiv:2605.11415 (ordinal latent-threshold, single-family envelope) and Fan-Park Makarov (marginals-only, copula free).

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** ACCEPT

**Banking reason.** D0.5.G cold referee: delivered an exact dual representation + delta-method/bootstrap inference for an OUTER Spearman-band endpoint under strong regularity, not the sharp identified-set equality / sign-indeterminacy result the headline promised — a sound subfield partial-ID contribution, below the field target.

## Key files

- `pid_benefit_concordance_band_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_benefit_concordance_band_v1_proposal.tex` — final proposal version.
- `pid_benefit_concordance_band_v1.tex` — derivation note (if Stage 0 ran).
- `pid_benefit_concordance_band_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_benefit_concordance_band_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
