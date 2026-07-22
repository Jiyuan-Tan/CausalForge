# tex↔Lean crosswalk

Definition/assumption/theorem (and, in the F5 complete table, lemma)
correspondence. Durable anchors: `obj_id` (.md/.tex side) and `(file, decl)`
(Lean side). Line numbers are convenience and re-derivable.

**Guarantee boundary (read this).** The Lean column is machine-verified at the
STATEMENT level: a sorry-free theorem/lemma certifies its *statement* is true.
The `.tex` PROOFS are NOT Lean-verified at the proof level — they are human
narratives refereed once at D0.5 and reconciled to the Lean *statements* by
the proof-review loop. A `.tex` proof step can therefore be wrong while the (true) statement
is Lean-certified; where the two disagree, the Lean proof is the ground truth.

| obj_id | kind | Lean (file:decl) | .tex anchor | verdict | note |
|---|---|---|---|---|---|
| P-1 | definition | `Basic.lean:CausalSmith.Stat.DpCateMinimax.HolderCateClass (L359)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:CausalSmith.Stat.DpCateMinimax.dpMinimaxRisk (L477)` | P-2 | equivalent |  |
| P-3 | definition | `Basic.lean:CausalSmith.Stat.DpCateMinimax.nonprivateCateRate (L493)` | P-3 | equivalent |  |
| P-4 | definition | `Basic.lean:CausalSmith.Stat.DpCateMinimax.privateRegressionCalibration (L501)` | P-4 | equivalent |  |
| P-5 | definition | `Basic.lean:CausalSmith.Stat.DpCateMinimax.causalPrivateFrontierHandle (L699)` | P-5 | equivalent |  |
| P-6 | definition | `Basic.lean:CausalSmith.Stat.DpCateMinimax.CausalDpFrontierQuestion (L840)` | P-6 | equivalent |  |
| T-1 | theorem | `T_CausalDpTwoPointBarrier.lean:CausalSmith.Stat.DpCateMinimax.causal_dp_two_point_barrier (L84)` | T-1 | equivalent |  |
| L-1 | lemma | `Helpers/DpContraction.lean:CausalSmith.Stat.DpCateMinimax.dp_output_tv_contraction (L27)` | L-1 | equivalent |  |
| L-2 | lemma | `Helpers/PrivateUpperEndpoint.lean:CausalSmith.Stat.DpCateMinimax.private_local_polynomial_upper_bound (L77)` | L-2 | equivalent |  |
| L-3 | lemma | `Helpers/RateAlgebra.lean:CausalSmith.Stat.DpCateMinimax.private_regression_calibration_algebra (L27)` | L-3 | equivalent |  |
| L-4 | definition | `Helpers/HolderInterpolation.lean:CausalSmith.Stat.DpCateMinimax.holder_point_l1_interpolation (L99)` | L-4 | equivalent |  |
| L-5 | lemma | `Helpers/Bracket.lean:CausalSmith.Stat.DpCateMinimax.certified_private_cate_bracket (L39)` | L-5 | equivalent |  |
| L-6 | lemma | `Helpers/Bracket.lean:CausalSmith.Stat.DpCateMinimax.equal_smoothness_sharp_private_rate (L81)` | L-6 | equivalent |  |
| L-7 | lemma | `Helpers/CausalLowerBound.lean:CausalSmith.Stat.DpCateMinimax.causal_oracle_private_lower_bound (L455)` | L-7 | equivalent |  |
| L-8 | lemma | `Helpers/Bracket.lean:CausalSmith.Stat.DpCateMinimax.equal_smoothness_regression_inheritance (L166)` | L-8 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.Stat.DpCateMinimax.IidSampling (L218)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.Stat.DpCateMinimax.Consistency (L239)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.Stat.DpCateMinimax.CondExchangeability (L251)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:CausalSmith.Stat.DpCateMinimax.StrongOverlap (L262)` | A-4 | equivalent |  |
| A-5 | assumption | `Basic.lean:CausalSmith.Stat.DpCateMinimax.PiHolder (L268)` | A-5 | equivalent |  |
| A-6 | assumption | `Basic.lean:CausalSmith.Stat.DpCateMinimax.MuHolder (L274)` | A-6 | equivalent |  |
| A-7 | assumption | `Basic.lean:CausalSmith.Stat.DpCateMinimax.TauHolder (L281)` | A-7 | equivalent |  |
| A-8 | assumption | `Basic.lean:CausalSmith.Stat.DpCateMinimax.SmoothnessOrder (L287)` | A-8 | equivalent |  |
| A-9 | assumption | `Basic.lean:CausalSmith.Stat.DpCateMinimax.LocalDensity (L296)` | A-9 | equivalent |  |
| A-10 | assumption | `Basic.lean:CausalSmith.Stat.DpCateMinimax.CentralDP (L426)` | A-10 | equivalent |  |
| A-11 | assumption | `Basic.lean:CausalSmith.Stat.DpCateMinimax.ModelNonempty (L381)` | A-11 | unmatched |  |
| private_regression_privacy_bandwidth_identities | lemma | `Helpers/RegressionCalibrationBounds.lean:CausalSmith.Stat.DpCateMinimax.private_regression_privacy_bandwidth_identities (L18)` | private_regression_privacy_bandwidth_identities | unmatched |  |
| private_regression_sampling_bandwidth_identities | lemma | `Helpers/RegressionCalibrationBounds.lean:CausalSmith.Stat.DpCateMinimax.private_regression_sampling_bandwidth_identities (L49)` | private_regression_sampling_bandwidth_identities | unmatched |  |
| private_regression_sampling_objective_lower | lemma | `Helpers/RegressionCalibrationBounds.lean:CausalSmith.Stat.DpCateMinimax.private_regression_sampling_objective_lower (L75)` | private_regression_sampling_objective_lower | unmatched |  |
| private_regression_privacy_objective_lower | lemma | `Helpers/RegressionCalibrationBounds.lean:CausalSmith.Stat.DpCateMinimax.private_regression_privacy_objective_lower (L102)` | private_regression_privacy_objective_lower | unmatched |  |
| private_regression_max_bandwidth_bound | lemma | `Helpers/RegressionCalibrationBounds.lean:CausalSmith.Stat.DpCateMinimax.private_regression_max_bandwidth_bound (L127)` | private_regression_max_bandwidth_bound | unmatched |  |
| nonprivateCateRate_equal_smoothness | lemma | `Helpers/EqualSmoothnessAlgebra.lean:CausalSmith.Stat.DpCateMinimax.nonprivateCateRate_equal_smoothness (L14)` | nonprivateCateRate_equal_smoothness | unmatched |  |
| equal_smoothness_rate_boundary | lemma | `Helpers/EqualSmoothnessAlgebra.lean:CausalSmith.Stat.DpCateMinimax.equal_smoothness_rate_boundary (L41)` | equal_smoothness_rate_boundary | unmatched |  |
| heps | assumption | `Helpers/DpContraction.lean:CausalSmith.Stat.DpCateMinimax.dp_output_tv_contraction (L27)` | heps | equivalent |  |
| tvDist_integral_range | lemma | `Helpers/DpContractionAux.lean:CausalSmith.Stat.DpCateMinimax.tvDist_integral_range (L16)` | tvDist_integral_range | unmatched |  |
| pairwise_range_of_abs_sub_le | lemma | `Helpers/DpContractionAux.lean:CausalSmith.Stat.DpCateMinimax.pairwise_range_of_abs_sub_le (L92)` | pairwise_range_of_abs_sub_le | unmatched |  |
| pi_integral_one_coordinate_tv_bound | lemma | `Helpers/DpContractionAux.lean:CausalSmith.Stat.DpCateMinimax.pi_integral_one_coordinate_tv_bound (L119)` | pi_integral_one_coordinate_tv_bound | unmatched |  |
| pi_integral_hybrid_tv_bound | lemma | `Helpers/DpContractionAux.lean:CausalSmith.Stat.DpCateMinimax.pi_integral_hybrid_tv_bound (L202)` | pi_integral_hybrid_tv_bound | unmatched |  |
| measureReal_bind_eq_integral | lemma | `Helpers/DpContractionAux.lean:CausalSmith.Stat.DpCateMinimax.measureReal_bind_eq_integral (L270)` | measureReal_bind_eq_integral | unmatched |  |
| lem:arm-disintegration-tv-lower | definition | `(none)` | lem:arm-disintegration-tv-lower | unmatched |  |
| measurableSet_cube | lemma | `(none)` | measurableSet_cube | unmatched |  |
| holderBallStd_const | lemma | `(none)` | holderBallStd_const | unmatched |  |
| causalNullLaw | lemma | `Helpers/CausalNullLaw.lean:CausalSmith.Stat.DpCateMinimax.causalNullLaw (L22)` | causalNullLaw | unmatched |  |
| lem:explicit-private-local-poly-witness | definition | `(none)` | lem:explicit-private-local-poly-witness | unmatched |  |
| regToTreated | definition | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.regToTreated (L26)` | regToTreated | unmatched |  |
| regToTreated_Y | lemma | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.regToTreated_Y (L31)` | regToTreated_Y | unmatched |  |
| regToTreated_A | lemma | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.regToTreated_A (L36)` | regToTreated_A | unmatched |  |
| regToTreated_X | lemma | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.regToTreated_X (L41)` | regToTreated_X | unmatched |  |
| measurable_regToTreated | lemma | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.measurable_regToTreated (L47)` | measurable_regToTreated | unmatched |  |
| regToTreated_replacementAdjacent | lemma | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.regToTreated_replacementAdjacent (L52)` | regToTreated_replacementAdjacent | unmatched |  |
| cateWitnessRegressionLaw | definition | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.cateWitnessRegressionLaw (L61)` | cateWitnessRegressionLaw | unmatched |  |
| cateWitnessControlLaw | definition | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.cateWitnessControlLaw (L67)` | cateWitnessControlLaw | unmatched |  |
| cateWitnessRegressionLaw_isProbabilityMeasure | lemma | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.cateWitnessRegressionLaw_isProbabilityMeasure (L105)` | cateWitnessRegressionLaw_isProbabilityMeasure | unmatched |  |
| cateWitnessControlLaw_isProbabilityMeasure | lemma | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.cateWitnessControlLaw_isProbabilityMeasure (L119)` | cateWitnessControlLaw_isProbabilityMeasure | unmatched |  |
| cateWitnessControlLaw_support | lemma | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.cateWitnessControlLaw_support (L134)` | cateWitnessControlLaw_support | unmatched |  |
| cateWitnessRegressionLaw_map_fst | lemma | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.cateWitnessRegressionLaw_map_fst (L155)` | cateWitnessRegressionLaw_map_fst | unmatched |  |
| IsRegressionFn | definition | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.IsRegressionFn (L188)` | IsRegressionFn | unmatched |  |
| cateWitnessRegressionLaw_isRegressionFn | lemma | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.cateWitnessRegressionLaw_isRegressionFn (L298)` | cateWitnessRegressionLaw_isRegressionFn | unmatched |  |
| cateWitnessLaw_dataMeasure_mixture | lemma | `Helpers/RegressionEmbedding.lean:CausalSmith.Stat.DpCateMinimax.cateWitnessLaw_dataMeasure_mixture (L367)` | cateWitnessLaw_dataMeasure_mixture | unmatched |  |
