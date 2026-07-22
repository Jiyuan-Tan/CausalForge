---
qid: pid_synth_control_factor_misspec
spec: v1
topic: "Sharp partial identification of synthetic-control treatment effects when the latent factor model generating donor and treated outcomes is misspecified by a bounded sup-norm or interactive fixed-effect approximation error, characterizing the sharp interval of treatment effects compatible with the observed pre-period donor-treated gap and the misspecification budget, recovering Abadie-Diamond-Hainmueller point identification under exact factor-model fit at the trivial bound"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  # Verbatim/near-verbatim reviewer phrases (D0.5 novelty objection, repeated across all 3 rounds).
  # Source: pid_synth_control_factor_misspec_v1_reviews.jsonl.
  - "The blocking issue is novelty relative to novelty_target=field."
  - "For a negative-result flagship, the note also fails to name a published estimator/workflow that actually uses the refuted scalar sharp-calibration method; Abadie2021 and FirpoPossebom2018 are explicitly described as reporting/inference comparators, not as asserting sharp deterministic factor-misspecification identification from RMSPE."
  - "The main sharp interval, while correct, is a standard finite-dimensional support/projection calculation for a polyhedral Chebyshev tube."
  - "The scalar lower bound is a clean witness, but under the prompt's negative-result rule it must name a specific published paper, estimator, or workflow that uses the refuted method... it also means the negative result lacks the required published target."
  - "The generic scalar theorem is also not field-level as written because Assumption ass:anisotropic already assumes the decisive endpoint variation along a q-level tangent; the proof then mainly packages first-order calculus."
  - "The endpoint-sufficiency result... is a necessary-statistic restatement once validity, sharpness, and dependence through S are assumed."
  - "assessed tier=subfield below novelty_target=field, so ACCEPT is not allowed by the floor directive."
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Proposed a negative-result flagship: a sharp Chebyshev-tube partial-ID interval for
  the synthetic-control post-period effect plus a two-law scalar (RMSPE) nonsharpness
  witness and a generic q-anisotropic nonsharpness theorem. All three D0.5 reviews passed
  structure and correctness but blocked on novelty against the field floor: the sharp
  interval is a standard support/projection calculation over a polyhedral Chebyshev tube,
  endpoint-sufficiency is necessary-statistic bookkeeping, and the generic theorem assumes
  its decisive anisotropic condition. The fatal defect is positioning, not math — the
  negative-result rule requires a named published method that asserts the refuted scalar
  sharp identification, but the note explicitly concedes Abadie2021 and FirpoPossebom2018
  do not make that claim, leaving the refutation aimed at a hypothetical target.
banked_on: "2026-05-15"
---

# pid_synth_control_factor_misspec / v1 — Downgraded

**Topic.** Sharp partial identification of synthetic-control treatment effects when the latent factor model generating donor and treated outcomes is misspecified by a bounded sup-norm or interactive fixed-effect approximation error, characterizing the sharp interval of treatment effects compatible with the observed pre-period donor-treated gap and the misspecification budget, recovering Abadie-Diamond-Hainmueller point identification under exact factor-model fit at the trivial bound

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** REVISE

**Banking reason.** D-0.5 ACCEPT, D0.5 REVISE x3 on novelty: scalar-calibration sharp-bound + generic-scalar no-go lacked a named published target — reviewer flagged Abadie2021 and FirpoPossebom2018 do not make the refuted claim. Conjecture-level positioning defect; math sound.

## Key files

- `pid_synth_control_factor_misspec_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_synth_control_factor_misspec_v1_proposal.tex` — final proposal version.
- `pid_synth_control_factor_misspec_v1.tex` — derivation note (if D0 ran).
- `pid_synth_control_factor_misspec_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_synth_control_factor_misspec_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
