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
| P-1 | definition | `Basic.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.ExperimentClass (L238)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.overlapCone (L260)` | P-2 | equivalent |  |
| P-3 | definition | `Basic.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellPhiOnCone (L275)` | P-3 | equivalent |  |
| P-4 | definition | `Basic.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional (L284)` | P-4 | equivalent |  |
| P-5 | definition | `Helpers/Estimator.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.hybridEstimator (L266)` | P-5 | equivalent |  |
| P-6 | definition | `Basic.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRisk (L364)` | P-6 | equivalent |  |
| P-7 | definition | `Basic.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.twoCategoryWitness (L463)` | P-7 | equivalent |  |
| T-1 | theorem | `T_TwoCategoryConfounding.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.two_category_confounding (L12)` | T-1 | equivalent |  |
| T-2 | theorem | `T_SharpMinimaxFixedInterior.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.sharp_minimax_fixed_interior (L166)` | T-2 | equivalent |  |
| T-3 | theorem | `T_OverlapAdaptiveUniversalHybrid.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.overlap_adaptive_universal_hybrid (L88)` | T-3 | equivalent |  |
| L-1 | lemma | `Helpers/LightCell.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.light_cell_polynomial (L562)` | L-1 | equivalent |  |
| L-2 | lemma | `Helpers/PilotSandwich.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.pilot_sandwich (L317)` | L-2 | equivalent |  |
| L-3 | lemma | `Helpers/HeavyCell.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.universal_heavy_cell_rate (L1293)` | L-3 | equivalent |  |
| L-4 | lemma | `Helpers/LowerBound.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.ate_lower_bound_transfer (L159)` | L-4 | equivalent |  |
| L-5 | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.near_randomization_linear_upper (L272)` | L-5 | equivalent |  |
| L-6 | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.one_category_bernoulli_lower (L453)` | L-6 | equivalent |  |
| L-7 | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.randomized_endpoint_minimax (L578)` | L-7 | equivalent |  |
| L-8 | lemma | `Helpers/CombinedEnvelope.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.combined_upper_envelope (L16)` | L-8 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.IidSampling (L187)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap (L193)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.Consistency (L213)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.ConditionalExchangeability (L226)` | A-4 | equivalent |  |
| aux_centeredEstimator | definition | `Helpers/Estimator.lean:centeredEstimator (L336)` | aux_centeredEstimator | unmatched |  |
| aux_ControlZeroClass | definition | `Helpers/LowerBound.lean:ControlZeroClass (L8)` | aux_ControlZeroClass | unmatched |  |
| aux_DiscreteLaw | definition | `Basic.lean:DiscreteLaw (L31)` | aux_DiscreteLaw | unmatched |  |
| aux_minimaxRate | definition | `Helpers/LightCell.lean:minimaxRate (L18)` | aux_minimaxRate | unmatched |  |
| aux_mse | definition | `Basic.lean:mse (L345)` | aux_mse | unmatched |  |
| aux_Obs | definition | `Basic.lean:Obs (L28)` | aux_Obs | unmatched |  |
| aux_worstCaseMSE | definition | `Basic.lean:worstCaseMSE (L357)` | aux_worstCaseMSE | unmatched |  |
| aux_selectedEstimator | definition | `Helpers/CombinedEnvelope.lean:selectedEstimator (L8)` | aux_selectedEstimator | unmatched |  |
| aux_HybridEstimatorComputable | definition | `Helpers/Estimator.lean:HybridEstimatorComputable (L329)` | aux_HybridEstimatorComputable | unmatched |  |
| centeredUnitScore | definition | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredUnitScore (L17)` | centeredUnitScore | unmatched |  |
| centeredUnitScore_sq | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredUnitScore_sq (L21)` | centeredUnitScore_sq | unmatched |  |
| centeredEstimator_eq_scoreMean | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredEstimator_eq_scoreMean (L27)` | centeredEstimator_eq_scoreMean | unmatched |  |
| centeredUnitScore_mean | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredUnitScore_mean (L32)` | centeredUnitScore_mean | unmatched |  |
| centeredScore_category_identity | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredScore_category_identity (L47)` | centeredScore_category_identity | unmatched |  |
| jointMass_eq_zero_of_cellMass_eq_zero | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass_eq_zero_of_cellMass_eq_zero (L93)` | jointMass_eq_zero_of_cellMass_eq_zero | unmatched |  |
| cellMass_sum | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass_sum (L103)` | cellMass_sum | unmatched |  |
| centeredUnitScore_bias_identity | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredUnitScore_bias_identity (L113)` | centeredUnitScore_bias_identity | unmatched |  |
| centeredUnitScore_bias_bound | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredUnitScore_bias_bound (L135)` | centeredUnitScore_bias_bound | unmatched |  |
| centeredEstimator_mean | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredEstimator_mean (L184)` | centeredEstimator_mean | unmatched |  |
| centeredUnitScore_variance_le_one | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredUnitScore_variance_le_one (L197)` | centeredUnitScore_variance_le_one | unmatched |  |
| centeredEstimator_variance_le | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredEstimator_variance_le (L208)` | centeredEstimator_variance_le | unmatched |  |
| mse_eq_variance_add_sq_bias | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse_eq_variance_add_sq_bias (L241)` | mse_eq_variance_add_sq_bias | unmatched |  |
| mse_le_estimator_abs_sum_bound | lemma | `Helpers/LowerBound.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse_le_estimator_abs_sum_bound (L31)` | mse_le_estimator_abs_sum_bound | unmatched |  |
| oneArmMinimaxRisk_le_minimaxRisk | lemma | `Helpers/LowerBound.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.oneArmMinimaxRisk_le_minimaxRisk (L87)` | oneArmMinimaxRisk_le_minimaxRisk | unmatched |  |
| endpointParametricLaw | definition | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw (L301)` | endpointParametricLaw | unmatched |  |
| endpointParametricPertLaw | definition | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw (L308)` | endpointParametricPertLaw | unmatched |  |
| endpointParametricLaw_jointMass | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw_jointMass (L315)` | endpointParametricLaw_jointMass | unmatched |  |
| endpointParametricPertLaw_jointMass | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw_jointMass (L330)` | endpointParametricPertLaw_jointMass | unmatched |  |
| endpointParametricLaw_overlap | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw_overlap (L345)` | endpointParametricLaw_overlap | unmatched |  |
| endpointParametricPertLaw_overlap | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw_overlap (L373)` | endpointParametricPertLaw_overlap | unmatched |  |
| endpointParametricLaw_ate | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw_ate (L400)` | endpointParametricLaw_ate | unmatched |  |
| endpointParametricPertLaw_ate | lemma | `Helpers/Endpoint.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw_ate (L421)` | endpointParametricPertLaw_ate | unmatched |  |
| categoryIndicator | definition | `Helpers/PilotSandwich.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.categoryIndicator (L15)` | categoryIndicator | unmatched |  |
| categoryIndicator_mean | lemma | `Helpers/PilotSandwich.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.categoryIndicator_mean (L19)` | categoryIndicator_mean | unmatched |  |
| pilot_count_eq_bernoulliCount | lemma | `Helpers/PilotSandwich.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.pilot_count_eq_bernoulliCount (L31)` | pilot_count_eq_bernoulliCount | unmatched |  |
| pilotCategory_upper_tail | lemma | `Helpers/PilotSandwich.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.pilotCategory_upper_tail (L65)` | pilotCategory_upper_tail | unmatched |  |
| pilotCategory_lower_tail | lemma | `Helpers/PilotSandwich.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.pilotCategory_lower_tail (L90)` | pilotCategory_lower_tail | unmatched |  |
| pilotBadEvent_subset_cellwise | lemma | `Helpers/PilotSandwich.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.pilotBadEvent_subset_cellwise (L128)` | pilotBadEvent_subset_cellwise | unmatched |  |
| pilotBadEvent_probability | lemma | `Helpers/PilotSandwich.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.pilotBadEvent_probability (L161)` | pilotBadEvent_probability | unmatched |  |
| exp_neg_mul_logScale | lemma | `Helpers/PilotSandwich.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.exp_neg_mul_logScale (L228)` | exp_neg_mul_logScale | unmatched |  |
| pilot_decay_bound | lemma | `Helpers/PilotSandwich.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.pilot_decay_bound (L240)` | pilot_decay_bound | unmatched |  |
| clamp_sq_error_le | lemma | `T_SharpMinimaxFixedInterior.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.clamp_sq_error_le (L11)` | clamp_sq_error_le | unmatched |  |
| targetHeavy_add_targetLight | lemma | `T_SharpMinimaxFixedInterior.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.targetHeavy_add_targetLight (L26)` | targetHeavy_add_targetLight | unmatched |  |
| hybrid_mse_le_component_errors | lemma | `T_SharpMinimaxFixedInterior.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.hybrid_mse_le_component_errors (L40)` | hybrid_mse_le_component_errors | unmatched |  |
| canonicalClassLaw | definition | `T_SharpMinimaxFixedInterior.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.canonicalClassLaw (L78)` | canonicalClassLaw | unmatched |  |
| hybrid_upper_fixed_interior | lemma | `T_SharpMinimaxFixedInterior.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.hybrid_upper_fixed_interior (L93)` | hybrid_upper_fixed_interior | unmatched |  |
| factorial_normalization | lemma | `Helpers/FactorialMoments.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.factorial_normalization (L122)` | factorial_normalization | unmatched |  |
| overlap_adaptive_universal_hybrid_statistical | lemma | `T_OverlapAdaptiveUniversalHybrid.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.overlap_adaptive_universal_hybrid_statistical (L19)` | overlap_adaptive_universal_hybrid_statistical | unmatched |  |
| lightCells_eq_pilotHeavyAt_compl_of_cutoff_le | lemma | `Helpers/LightCell.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.lightCells_eq_pilotHeavyAt_compl_of_cutoff_le (L22)` | lightCells_eq_pilotHeavyAt_compl_of_cutoff_le | unmatched |  |
| selected_light_mass_le_bandwidth_quarter | lemma | `Helpers/LightCell.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.selected_light_mass_le_bandwidth_quarter (L34)` | selected_light_mass_le_bandwidth_quarter | unmatched |  |
| selected_light_approximation_bias | lemma | `Helpers/LightCell.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.selected_light_approximation_bias (L88)` | selected_light_approximation_bias | unmatched |  |
| integrable_factorialPolynomialContribution_trunc | lemma | `Helpers/LightCell.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.integrable_factorialPolynomialContribution_trunc (L160)` | integrable_factorialPolynomialContribution_trunc | unmatched |  |
| integral_factorialPolynomialContribution_trunc | lemma | `Helpers/LightCell.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.integral_factorialPolynomialContribution_trunc (L186)` | integral_factorialPolynomialContribution_trunc | unmatched |  |
| iidSample_shift | definition | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.iidSampleShift (L14)` | iidSample_shift | unmatched |  |
| iidSample_map | definition | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.iidSampleMap (L26)` | iidSample_map | unmatched |  |
| categoryCellLabel | definition | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.categoryCellLabel (L38)` | categoryCellLabel | unmatched |  |
| categoryCellLabel_measurable | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.categoryCellLabel_measurable (L44)` | categoryCellLabel_measurable | unmatched |  |
| optionCellExponent | definition | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.optionCellExponent (L48)` | optionCellExponent | unmatched |  |
| exponentDegree_optionCellExponent | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.exponentDegree_optionCellExponent (L53)` | exponentDegree_optionCellExponent | unmatched |  |
| categoryCellLabel_atom_mass | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.categoryCellLabel_atom_mass (L59)` | categoryCellLabel_atom_mass | unmatched |  |
| splitSize_zero_eq | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.splitSize_zero_eq (L82)` | splitSize_zero_eq | unmatched |  |
| splitSize_one_eq | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.splitSize_one_eq (L87)` | splitSize_one_eq | unmatched |  |
| estimationTailIndex | definition | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.estimationTailIndex (L101)` | estimationTailIndex | unmatched |  |
| splitCellCount_eq_tail_count | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.splitCellCount_eq_tail_count (L110)` | splitCellCount_eq_tail_count | unmatched |  |
| categoryCellLabel_fiber_card | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.categoryCellLabel_fiber_card (L164)` | categoryCellLabel_fiber_card | unmatched |  |
| estimationLabelSample | definition | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.estimationLabelSample (L188)` | estimationLabelSample | unmatched |  |
| multinomialFactorialCount_estimationLabelSample | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.multinomialFactorialCount_estimationLabelSample (L193)` | multinomialFactorialCount_estimationLabelSample | unmatched |  |
| factorialMonomial_eq_normalized_multinomialCount | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.factorialMonomial_eq_normalized_multinomialCount (L211)` | factorialMonomial_eq_normalized_multinomialCount | unmatched |  |
| lightCellEstimationIID | definition | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.lightCellEstimationIID (L223)` | lightCellEstimationIID | unmatched |  |
| factorialMonomial_trunc_eq_iidCount | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.factorialMonomial_trunc_eq_iidCount (L232)` | factorialMonomial_trunc_eq_iidCount | unmatched |  |
| integrable_factorialMonomial_trunc | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.integrable_factorialMonomial_trunc (L244)` | integrable_factorialMonomial_trunc | unmatched |  |
| integral_factorialMonomial_trunc | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.integral_factorialMonomial_trunc (L257)` | integral_factorialMonomial_trunc | unmatched |  |
| integral_factorialMonomial_mul_trunc_le | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.integral_factorialMonomial_mul_trunc_le (L278)` | integral_factorialMonomial_mul_trunc_le | unmatched |  |
| integrable_factorialMonomial_mul_trunc | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.integrable_factorialMonomial_mul_trunc (L302)` | integrable_factorialMonomial_mul_trunc | unmatched |  |
| observationExponent | definition | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.observationExponent (L336)` | observationExponent | unmatched |  |
| exponentDegree_observationExponent | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.exponentDegree_observationExponent (L341)` | exponentDegree_observationExponent | unmatched |  |
| estimationTail_fiber_card | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.estimationTail_fiber_card (L354)` | estimationTail_fiber_card | unmatched |  |
| observationExponent_fiber_count | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.observationExponent_fiber_count (L365)` | observationExponent_fiber_count | unmatched |  |
| multinomialFactorialCount_observationExponent | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.multinomialFactorialCount_observationExponent (L387)` | multinomialFactorialCount_observationExponent | unmatched |  |
| factorialMonomial_eq_normalized_observationCount | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.factorialMonomial_eq_normalized_observationCount (L405)` | factorialMonomial_eq_normalized_observationCount | unmatched |  |
| factorialMonomial_trunc_eq_observationCount | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.factorialMonomial_trunc_eq_observationCount (L417)` | factorialMonomial_trunc_eq_observationCount | unmatched |  |
| obsLaw_real_cellAtom | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw_real_cellAtom (L429)` | obsLaw_real_cellAtom | unmatched |  |
| observationExponent_mass_prod | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.observationExponent_mass_prod (L443)` | observationExponent_mass_prod | unmatched |  |
| integral_factorialMonomial_cross_trunc | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.integral_factorialMonomial_cross_trunc (L464)` | integral_factorialMonomial_cross_trunc | unmatched |  |
| vectorMass_cellVector | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.vectorMass_cellVector (L506)` | vectorMass_cellVector | unmatched |  |
| vectorArmMass_cellVector | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.vectorArmMass_cellVector (L512)` | vectorArmMass_cellVector | unmatched |  |
| obsLaw_real_singleton | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw_real_singleton (L520)` | obsLaw_real_singleton | unmatched |  |
| obsLaw_real_atom | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw_real_atom (L527)` | obsLaw_real_atom | unmatched |  |
| cellVector_mem_overlapCone | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellVector_mem_overlapCone (L533)` | cellVector_mem_overlapCone | unmatched |  |
| abs_cellPhi_cellVector_le_mass | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.abs_cellPhi_cellVector_le_mass (L576)` | abs_cellPhi_cellVector_le_mass | unmatched |  |
| multiDegree_factorialExpansionIndex | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.multiDegree_factorialExpansionIndex (L598)` | multiDegree_factorialExpansionIndex | unmatched |  |
| factorialExpansionIndex_prod | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.factorialExpansionIndex_prod (L607)` | factorialExpansionIndex_prod | unmatched |  |
| factorialExpansionIndex_binomial_sum | lemma | `Helpers/LightCellAssembly.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.factorialExpansionIndex_binomial_sum (L618)` | factorialExpansionIndex_binomial_sum | unmatched |  |
| sparseArmEnvelope_eq | lemma | `Helpers/LightCellVariance.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.sparseArmEnvelope_eq (L16)` | sparseArmEnvelope_eq | unmatched |  |
| sparseArmEnvelope_le | lemma | `Helpers/LightCellVariance.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.sparseArmEnvelope_le (L67)` | sparseArmEnvelope_le | unmatched |  |
| multiMonomial_mono | lemma | `Helpers/LightCellVariance.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.multiMonomial_mono (L104)` | multiMonomial_mono | unmatched |  |
| integral_factorialMonomial_mul_shift_le | lemma | `Helpers/LightCellVariance.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.integral_factorialMonomial_mul_shift_le (L124)` | integral_factorialMonomial_mul_shift_le | unmatched |  |
| integral_sparse_terms_mul_shift_le | lemma | `Helpers/LightCellVariance.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.integral_sparse_terms_mul_shift_le (L273)` | integral_sparse_terms_mul_shift_le | unmatched |  |
| factorialMonomial_cross_covariance_le | lemma | `Helpers/LightCellVariance.lean:CausalSmith.Stat.DiscreteAteMinimaxLoggap.factorialMonomial_cross_covariance_le (L356)` | factorialMonomial_cross_covariance_le | unmatched |  |
