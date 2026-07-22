# tex↔Lean crosswalk

Definition/assumption/theorem (and, in the F5 complete table, lemma)
correspondence. Durable anchors: `obj_id` (.md/.tex side) and `(file, decl)`
(Lean side). Line numbers are convenience and re-derivable.

**Guarantee boundary (read this).** The Lean column is machine-verified at the
STATEMENT level: a sorry-free theorem/lemma certifies its *statement* is true.
The `.tex` PROOFS are NOT Lean-verified at the proof level — they are human
narratives refereed once at D0.5 and reconciled to the Lean *statements* at
F3.7/F4. A `.tex` proof step can therefore be wrong while the (true) statement
is Lean-certified; where the two disagree, the Lean proof is the ground truth.

| obj_id | kind | Lean (file:decl) | .tex anchor | verdict | note |
|---|---|---|---|---|---|
| P-1 | definition | `Basic.lean:twoBlockGraph (L0)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:BlockElliptopeMem (L0)` | P-2 | equivalent |  |
| P-3 | definition | `Basic.lean:BalancedDesignClass (L0)` | P-3 | equivalent |  |
| P-4 | definition | `Basic.lean:blockExchangeableDesignClass (L0)` | P-4 | equivalent |  |
| P-5 | definition | `Basic.lean:implementableCovarianceClass (L0)` | P-5 | equivalent |  |
| P-6 | definition | `Basic.lean:designObjective (L0)` | P-6 | equivalent |  |
| P-7 | definition | `Basic.lean:implementabilityGap (L0)` | P-7 | equivalent |  |
| P-8 | definition | `Basic.lean:blockSumHandle (L0)` | P-8 | equivalent |  |
| T-1 | theorem | `Tcut.lean:cut_corner_exactness (L0)` | T-1 | equivalent |  |
| T-2 | theorem | `Trobust.lean:robust_corner_exactness (L0)` | T-2 | equivalent |  |
| T-3 | theorem | `Tgap.lean:gap_window (L0)` | T-3 | equivalent |  |
| T-4 | theorem | `Tsharp.lean:sharp_rho_star (L0)` | T-4 | equivalent |  |
| L-1 | lemma | `Helpers/SymmetryReduction.lean:symmetry_reduction (L0)` | L-1 | equivalent |  |
| L-2 | lemma | `Helpers/SpectralCoordinates.lean:block_spectral_coordinates (L0)` | L-2 | equivalent |  |
| L-3 | lemma | `Helpers/VertexCertificates.lean:cut_vertex_certificate (L0)` | L-3 | equivalent |  |
| L-4 | lemma | `Helpers/VertexCertificates.lean:spread_vertex_certificate (L0)` | L-4 | equivalent |  |
| L-5 | lemma | `Helpers/FrobeniusCenter.lean:frobenius_center_certificate (L0)` | L-5 | equivalent |  |
| L-6 | lemma | `Helpers/ParitySlice.lean:pm_reduced_slice_characterization (L0)` | L-6 | equivalent |  |
| L-7 | lemma | `Helpers/SimplexActiveSet.lean:weighted_simplex_active_set (L0)` | L-7 | equivalent |  |
| L-8 | lemma | `Helpers/SimplexTruncation.lean:weighted_simplex_truncation (L0)` | L-8 | equivalent |  |
| L-9 | lemma | `Helpers/GapReduction.lean:rounding_gap_reduction (L0)` | L-9 | equivalent |  |
| A-1 | assumption | `Basic.lean:TwoBlockHomophily (L0)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:BalancedSignDesign (L0)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:LowScaleTwoBlock (L0)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:OddCommunitySize (L0)` | A-4 | equivalent |  |
| sym:r_star | definition | `Basic.lean:IsSharpExactnessBoundary (L0)` | sym:r_star | equivalent |  |
| a_cut_vertex_kappa_nonneg | assumption | `Helpers/VertexCertificates.lean:cut_vertex_certificate (L0)` | a_cut_vertex_kappa_nonneg | equivalent |  |
| a_spread_vertex_kappa_nonneg | assumption | `Helpers/VertexCertificates.lean:spread_vertex_certificate (L0)` | a_spread_vertex_kappa_nonneg | equivalent |  |
| spreadObjectiveDiff_mul_sqrt | lemma | `Helpers/VertexCertificates.lean:spreadObjectiveDiff_mul_sqrt (L0)` | spreadObjectiveDiff_mul_sqrt | unmatched |  |
| frobeniusCenterTangentXY_deriv | lemma | `Helpers/FrobeniusCenter.lean:frobeniusCenterTangentXY_deriv (L0)` | frobeniusCenterTangentXY_deriv | unmatched |  |
| frobeniusCenterTangentYZ_deriv | lemma | `Helpers/FrobeniusCenter.lean:frobeniusCenterTangentYZ_deriv (L0)` | frobeniusCenterTangentYZ_deriv | unmatched |  |
| sym:kappa_iid | definition | `Basic.lean:IsIidExactnessFrontier (L0)` | sym:kappa_iid | equivalent |  |
| cutDesign_eq_cutVDesign | lemma | `Tcut.lean:cutDesign_eq_cutVDesign (L0)` | cutDesign_eq_cutVDesign | unmatched |  |
| sInf_image_eq_of_minimizer | lemma | `Tcut.lean:sInf_image_eq_of_minimizer (L0)` | sInf_image_eq_of_minimizer | unmatched |  |
| sum_if_eq_else_self_real | lemma | `Helpers/BlockPairSums.lean:sum_if_eq_else_self_real (L0)` | sum_if_eq_else_self_real | unmatched |  |
| block_pair_sum | lemma | `Helpers/BlockPairSums.lean:block_pair_sum (L0)` | block_pair_sum | unmatched |  |
| block_signed_pair_sum | lemma | `Helpers/BlockPairSums.lean:block_signed_pair_sum (L0)` | block_signed_pair_sum | unmatched |  |
| blockSymMatrix_mem_blockElliptope_iff_reducedTriangle | lemma | `Helpers/SpectralMembership.lean:blockSymMatrix_mem_blockElliptope_iff_reducedTriangle (L0)` | blockSymMatrix_mem_blockElliptope_iff_reducedTriangle | unmatched |  |
| roundingLossCertificate_nonneg | lemma | `Basic.lean:roundingLossCertificate_nonneg (L0)` | roundingLossCertificate_nonneg | unmatched |  |
| implementabilityGap_nonneg | lemma | `Helpers/GapReduction.lean:implementabilityGap_nonneg (L0)` | implementabilityGap_nonneg | unmatched |  |
| reducedTriangle_to_simplex | lemma | `Helpers/ReducedSimplexBridge.lean:reducedTriangle_to_simplex (L0)` | reducedTriangle_to_simplex | unmatched |  |
| simplex_to_reducedTriangle | lemma | `Helpers/ReducedSimplexBridge.lean:simplex_to_reducedTriangle (L0)` | simplex_to_reducedTriangle | unmatched |  |
| reducedObjective_eq_wsObj | lemma | `Helpers/ReducedSimplexBridge.lean:reducedObjective_eq_wsObj (L0)` | reducedObjective_eq_wsObj | unmatched |  |
| wsObj_eq_reducedObjective | lemma | `Helpers/ReducedSimplexBridge.lean:wsObj_eq_reducedObjective (L0)` | wsObj_eq_reducedObjective | unmatched |  |
| spread_certificate_relaxed_minimizer_and_gap | lemma | `Helpers/SpreadGap.lean:spread_certificate_relaxed_minimizer_and_gap (L0)` | spread_certificate_relaxed_minimizer_and_gap | unmatched |  |
| sharp_reduced_active_set_and_unique | lemma | `Helpers/SharpActive.lean:sharp_reduced_active_set_and_unique (L0)` | sharp_reduced_active_set_and_unique | unmatched |  |
| sharp_truncation_value_of_no_reduced_argmin_in_slice | lemma | `Helpers/SharpTrunc.lean:sharp_truncation_value_of_no_reduced_argmin_in_slice (L0)` | sharp_truncation_value_of_no_reduced_argmin_in_slice | unmatched |  |
| sharp_roundingLoss_zero_of_even | lemma | `Helpers/SharpTrunc.lean:sharp_roundingLoss_zero_of_even (L0)` | sharp_roundingLoss_zero_of_even | unmatched |  |
| sharp_roundingLoss_zero_iff_argmin_meets_slice | lemma | `Helpers/SharpZero.lean:sharp_roundingLoss_zero_iff_argmin_meets_slice (L0)` | sharp_roundingLoss_zero_iff_argmin_meets_slice | unmatched |  |
| sharp_roundingLoss_zero_iff_unique_argmin_subset_slice | lemma | `Helpers/SharpZero.lean:sharp_roundingLoss_zero_iff_unique_argmin_subset_slice (L0)` | sharp_roundingLoss_zero_iff_unique_argmin_subset_slice | unmatched |  |
| sharp_kappa_zero_reduced_min_iff | lemma | `Helpers/SharpZero.lean:sharp_kappa_zero_reduced_min_iff (L0)` | sharp_kappa_zero_reduced_min_iff | unmatched |  |
| reduced_norm_sq_block_coords | lemma | `Helpers/RobustConvergence.lean:reduced_norm_sq_block_coords (L0)` | reduced_norm_sq_block_coords | unmatched |  |
| robust_minimizers_tendsto_identity_entries | lemma | `Helpers/RobustConvergence.lean:robust_minimizers_tendsto_identity_entries (L0)` | robust_minimizers_tendsto_identity_entries | unmatched |  |
| iidDesign_sign_pair_sum_zero | lemma | `Helpers/RobustCorner.lean:iidDesign_sign_pair_sum_zero (L0)` | iidDesign_sign_pair_sum_zero | unmatched |  |
| iidDesign_secondMoment | lemma | `Helpers/RobustCorner.lean:iidDesign_secondMoment (L0)` | iidDesign_secondMoment | unmatched |  |
| identity_mem_blockElliptope | lemma | `Helpers/RobustCorner.lean:identity_mem_blockElliptope (L0)` | identity_mem_blockElliptope | unmatched |  |
| robust_coeff_r_eq_of_center | lemma | `Helpers/RobustCorner.lean:robust_coeff_r_eq_of_center (L0)` | robust_coeff_r_eq_of_center | unmatched |  |
| robust_locus_of_center_coeffs | lemma | `Helpers/RobustCorner.lean:robust_locus_of_center_coeffs (L0)` | robust_locus_of_center_coeffs | unmatched |  |
| robust_center_coeffs_of_locus | lemma | `Helpers/RobustCorner.lean:robust_center_coeffs_of_locus (L0)` | robust_center_coeffs_of_locus | unmatched |  |
| reduced_coord_inverse | lemma | `Helpers/RobustCorner.lean:reduced_coord_inverse (L0)` | reduced_coord_inverse | unmatched |  |
| identity_objective_eq_reduced_center | lemma | `Helpers/RobustCorner.lean:identity_objective_eq_reduced_center (L0)` | identity_objective_eq_reduced_center | unmatched |  |
| center_coeffs_of_identity_relaxed_min | lemma | `Helpers/RobustCorner.lean:center_coeffs_of_identity_relaxed_min (L0)` | center_coeffs_of_identity_relaxed_min | unmatched |  |
| identity_strict_relaxed_min_of_locus | lemma | `Helpers/RobustCorner.lean:identity_strict_relaxed_min_of_locus (L0)` | identity_strict_relaxed_min_of_locus | unmatched |  |
