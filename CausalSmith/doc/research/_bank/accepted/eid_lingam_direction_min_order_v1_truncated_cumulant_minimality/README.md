---
qid: eid_lingam_direction_min_order_v1
spec: truncated_cumulant_minimality
topic: "Chen et al.'s (arXiv:2510.22711, 2025) order-(2m+3) higher-cumulant rank-deficiency test for the causal DIRECTION between two variables X,Y under m non-collinear latent confounders is NOT minimal: the direction is GENERICALLY identifiable from the joint cumulant tensor TRUNCATED at order 2m+2 (one order lower). Kernel: reading the stacked truncated cumulant tensor T_{2m+2}(X,Y) as two axis-conditioned graded cumulant-image varieties (a simultaneous binary-form / Sylvester decomposition), prove (I) [strict lower-order sufficiency] the two opposite-arrow cumulant-image varieties GENERICALLY SEPARATE at K=2m+2, so the arrow is recovered off a proper subvariety via the simultaneous-binary-form recovery map — strictly improving the anchor's order-2m+3 requirement (minimal order K*(m)=2m+2, pinned by the DOF balance p=nK-1 vs q with n=m+2); and (II) [exact exceptional non-ID locus] the two varieties INTERSECT in an explicit CODIMENSION-m exceptional variety E_m (the axis-conditioned Waring-alternative compatibility system) on which an opposite-arrow twin shares T_{2m+2}, so identification fails exactly on E_m — give E_m's defining equations and prove codim E_m = m. Deliver worked m=1 (order-4 truncation, E_1 codim-1) and m=2 (order-6, E_2 codim-2) instances then the general dichotomy. Motif M18 (structure identification: recover the arrow up to the direction indeterminacy via cumulant asymmetry; recovery map + exceptional locus are the indeterminacy characterization). ExactID structure-ID; distinct from coefficient-identification (pins the minimal cumulant ORDER and the exceptional locus of ARROW identifiability, not a coefficient's value)."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  - "The original codimension-m conjecture was corrected: the exceptional locus has codimension one."
  - "The proposed all-m identity K*(m)=2m+2 was refuted; the proved improvement is K*(m) <= 2m+1 for m >= 3, leaving only the small-m frontier open."
  - "The single-G_m-orbit strengthening was refuted by direction-preserving source swaps and low-order weight-kernel fibers."
  - "The exact real CAD atlas remains undelivered after citation-instantiation overflow; F4 independently verified it is secondary, not headline-support, and has no delivered consumer."
reusable_artifacts:
  - "Causalean/Mathlib/AlgebraicGeometry/PolynomialImageDimension/ (affine polynomial-map, closure, irreducibility, chain-dimension, coordinate-ring, transcendence, Jacobian, dense-image, affine-subspace, and retract substrate)"
  - "Causalean/Mathlib/AlgebraicGeometry/PolynomialImageDimension/IrreducibleFiniteRange.lean (finite-valued coordinate rigidity on irreducible affine sets)"
  - "Causalean/Mathlib/AlgebraicGeometry/PolynomialImageDimension/CodimensionOne.lean (irreducible components, endpoint-fixed affine codimension, and principal height-one certificates)"
  - "Causalean/Mathlib/LinearAlgebra/ConfluentVandermonde.lean (ordinary and pinned Hermite-evaluation nonsingularity)"
  - "Causalean/Mathlib/LinearAlgebra/VandermondeSynthesis.lean (endpoint-augmented Vandermonde synthesis and exact kernel dimension)"
  - "Causalean/Mathlib/LinearAlgebra/StackedVandermonde.lean (constructive injectivity for stacked weighted Vandermonde systems)"
seeds_burned: []
proof_attempt_summary: |
  D0 proved generic arrow recovery with the same-arrow fiber obstruction, exact codimension one of the exceptional locus, and the improved real information-order bound for m >= 3. F2-F4 formalized all three unconditionally and both F4 reviewers converged with zero proof holes. The exact real exceptional atlas required a large paper-specific CAD/elimination instantiation; after an honest attempt it was classified secondary and undelivered, with its statement retained only as a disclosed presentation remark.
banked_on: "2026-07-15"
paper_score: 5.8
paper_score_rationale: "The verified mathematical core appears correct and carefully scoped, but the manuscript as written is too narrow, hard to interpret economically, and insufficiently positioned to merit publication in a leading econometrics journal without substantial revision."
---

# eid_lingam_direction_min_order_v1 / truncated_cumulant_minimality — Accepted

**Topic.** Chen et al.'s (arXiv:2510.22711, 2025) order-(2m+3) higher-cumulant rank-deficiency test for the causal DIRECTION between two variables X,Y under m non-collinear latent confounders is NOT minimal: the direction is GENERICALLY identifiable from the joint cumulant tensor TRUNCATED at order 2m+2 (one order lower). Kernel: reading the stacked truncated cumulant tensor T_{2m+2}(X,Y) as two axis-conditioned graded cumulant-image varieties (a simultaneous binary-form / Sylvester decomposition), prove (I) [strict lower-order sufficiency] the two opposite-arrow cumulant-image varieties GENERICALLY SEPARATE at K=2m+2, so the arrow is recovered off a proper subvariety via the simultaneous-binary-form recovery map — strictly improving the anchor's order-2m+3 requirement (minimal order K*(m)=2m+2, pinned by the DOF balance p=nK-1 vs q with n=m+2); and (II) [exact exceptional non-ID locus] the two varieties INTERSECT in an explicit CODIMENSION-m exceptional variety E_m (the axis-conditioned Waring-alternative compatibility system) on which an opposite-arrow twin shares T_{2m+2}, so identification fails exactly on E_m — give E_m's defining equations and prove codim E_m = m. Deliver worked m=1 (order-4 truncation, E_1 codim-1) and m=2 (order-6, E_2 codim-2) instances then the general dichotomy. Motif M18 (structure identification: recover the arrow up to the direction indeterminacy via cumulant asymmetry; recovery map + exceptional locus are the indeterminacy characterization). ExactID structure-ID; distinct from coefficient-identification (pins the minimal cumulant ORDER and the exceptional locus of ARROW identifiability, not a coefficient's value).

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** F4 dual reviewers converged: three salvaged headline results are unconditional and proved; the exact-real atlas is independently verified secondary, unconsumed, and disclosed as an undelivered remark.

## Key files

- `eid_lingam_direction_min_order_v1_truncated_cumulant_minimality_state.json` — pipeline state at banking (`banked: true`).
- `eid_lingam_direction_min_order_v1_truncated_cumulant_minimality_proposal.tex` — final proposal version.
- `eid_lingam_direction_min_order_v1_truncated_cumulant_minimality.tex` — derivation note (if Stage 0 ran).
- `eid_lingam_direction_min_order_v1_truncated_cumulant_minimality_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_lingam_direction_min_order_v1_truncated_cumulant_minimality_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
