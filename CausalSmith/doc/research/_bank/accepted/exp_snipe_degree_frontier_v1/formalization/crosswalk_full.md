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
| P-1 | definition | `Basic.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.kStar (L76)` | P-1 | equivalent |  |
| P-2 | definition | `Helpers/BlockScore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.ZeroDegreeConventions (L135)` | P-2 | equivalent |  |
| P-3 | definition | `Basic.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.GraphClass (L142)` | P-3 | equivalent |  |
| P-4 | definition | `Basic.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.CoeffClass (L150)` | P-4 | equivalent |  |
| P-5 | definition | `Basic.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.ModelClass (L159)` | P-5 | equivalent |  |
| P-6 | definition | `Estimator.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.snipeScore (L47)` | P-6 | equivalent |  |
| P-7 | definition | `Estimator.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.snipeEstimatorBundle (L74)` | P-7 | equivalent |  |
| P-8 | definition | `Estimator.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.minimaxRisk (L104)` | P-8 | equivalent |  |
| P-9 | definition | `Helpers/BlockScore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockScoreEnergyBundle (L67)` | P-9 | equivalent |  |
| P-10 | definition | `Helpers/LeastFavourable.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockFamilyBundle (L206)` | P-10 | equivalent |  |
| P-11 | definition | `Helpers/BlockScore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.perturbProg (L106)` | P-11 | equivalent |  |
| P-12 | definition | `Helpers/BlockScore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.weightProg (L125)` | P-12 | equivalent |  |
| P-13 | definition | `Helpers/LocalLinearClass.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.LocLinSchedClass (L30)` | P-13 | equivalent |  |
| P-14 | definition | `Helpers/LocalLinearClass.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.locLinEstimatorClass (L75)` | P-14 | equivalent |  |
| P-15 | definition | `Helpers/LocalLinearClass.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.locLinMinimaxRisk (L104)` | P-15 | equivalent |  |
| P-16 | definition | `Basic.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.BddOutcomeCoeffClass (L198)` | P-16 | equivalent |  |
| P-17 | definition | `Basic.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.BddOutcomeModelClass (L207)` | P-17 | equivalent |  |
| P-18 | definition | `Estimator.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.twoClassMinimaxRisks (L153)` | P-18 | equivalent |  |
| P-19 | definition | `Estimator.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.snipeClippedBdd (L161)` | P-19 | equivalent |  |
| T-1 | theorem | `T_degree_frontier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.degree_frontier (L165)` | T-1 | equivalent |  |
| T-2 | theorem | `T_sharp_local_linear.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.sharp_local_linear_constant_and_representers (L562)` | T-2 | equivalent |  |
| T-3 | theorem | `T_bounded_outcome_frontier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.bounded_outcome_degree_frontier (L735)` | T-3 | equivalent |  |
| T-4 | theorem | `T_fair_coin_frontier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.fair_coin_energy_frontier (L96)` | T-4 | equivalent |  |
| L-1 | lemma | `Helpers/BlockRepresenter.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockEnergy_representer (L307)` | L-1 | equivalent |  |
| L-2 | lemma | `Helpers/OverlapCount.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.overlap_count_le (L25)` | L-2 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.IsProductBernoulli (L85)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.BoundedDegree (L96)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.LowOrder (L102)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.BoundedCoeffMass (L109)` | A-4 | equivalent |  |
| aux_activeShare | definition | `Helpers/LeastFavourable.lean:activeShare (L34)` | aux_activeShare | unmatched |  |
| aux_bernoulliContrast | definition | `Basic.lean:bernoulliContrast (L49)` | aux_bernoulliContrast | unmatched |  |
| aux_blockCount | definition | `Helpers/LeastFavourable.lean:blockCount (L26)` | aux_blockCount | unmatched |  |
| aux_blockDominatingMeasure | definition | `Helpers/LeastFavourable.lean:blockDominatingMeasure (L247)` | aux_blockDominatingMeasure | unmatched |  |
| aux_blockEnergy | definition | `Helpers/BlockScore.lean:blockEnergy (L36)` | aux_blockEnergy | unmatched |  |
| aux_blockExtremal | definition | `Helpers/LocalLinearClass.lean:blockExtremal (L114)` | aux_blockExtremal | unmatched |  |
| aux_blockGraph | definition | `Helpers/LeastFavourable.lean:blockGraph (L40)` | aux_blockGraph | unmatched |  |
| aux_blockPriorDensity | definition | `Helpers/LeastFavourable.lean:blockPriorDensity (L236)` | aux_blockPriorDensity | unmatched |  |
| aux_blockSchedule | definition | `Helpers/LeastFavourable.lean:blockSchedule (L170)` | aux_blockSchedule | unmatched |  |
| aux_blockUnits | definition | `T_sharp_local_linear.lean:blockUnits (L23)` | aux_blockUnits | unmatched |  |
| aux_edgeFn | definition | `Estimator.lean:edgeFn (L28)` | aux_edgeFn | unmatched |  |
| aux_edgeFnBdd | definition | `Estimator.lean:edgeFnBdd (L32)` | aux_edgeFnBdd | unmatched |  |
| aux_effBeta | definition | `Basic.lean:effBeta (L54)` | aux_effBeta | unmatched |  |
| aux_Hbound | definition | `(none)` | aux_Hbound | unmatched |  |
| aux_hellingerSqDensity | definition | `Helpers/HellingerAffinity.lean:hellingerSqDensity (L31)` | aux_hellingerSqDensity | unmatched |  |
| aux_largestOddLE | definition | `T_fair_coin_frontier.lean:largestOddLE (L16)` | aux_largestOddLE | unmatched |  |
| aux_localEnergy | definition | `Helpers/SnipeVariance.lean:localEnergy (L304)` | aux_localEnergy | unmatched |  |
| aux_locLinMinimaxRisk | definition | `Helpers/LocalLinearClass.lean:locLinMinimaxRisk (L104)` | aux_locLinMinimaxRisk | unmatched |  |
| aux_locLinRiskRatio | definition | `T_sharp_local_linear.lean:locLinRiskRatio (L36)` | aux_locLinRiskRatio | unmatched |  |
| aux_LocLinWeights | definition | `Helpers/LocalLinearClass.lean:LocLinWeights (L43)` | aux_LocLinWeights | unmatched |  |
| aux_locLinWorstRisk | definition | `Helpers/LocalLinearClass.lean:locLinWorstRisk (L95)` | aux_locLinWorstRisk | unmatched |  |
| aux_minimaxRiskL1 | definition | `Estimator.lean:minimaxRiskL1 (L136)` | aux_minimaxRiskL1 | unmatched |  |
| aux_ModelClassIncluded | definition | `T_bounded_outcome_frontier.lean:ModelClassIncluded (L27)` | aux_ModelClassIncluded | unmatched |  |
| aux_ModelClassStrict | definition | `T_bounded_outcome_frontier.lean:ModelClassStrict (L35)` | aux_ModelClassStrict | unmatched |  |
| aux_normalizedBlockExcess | definition | `T_sharp_local_linear.lean:normalizedBlockExcess (L43)` | aux_normalizedBlockExcess | unmatched |  |
| aux_normalizedWeightDistance | definition | `T_sharp_local_linear.lean:normalizedWeightDistance (L52)` | aux_normalizedWeightDistance | unmatched |  |
| aux_normalizedWeightDistanceRelabeled | definition | `T_sharp_local_linear.lean:normalizedWeightDistanceRelabeled (L62)` | aux_normalizedWeightDistanceRelabeled | unmatched |  |
| aux_obsOutcome | definition | `Basic.lean:obsOutcome (L125)` | aux_obsOutcome | unmatched |  |
| aux_OutcomeMeasurable | definition | `Estimator.lean:OutcomeMeasurable (L42)` | aux_OutcomeMeasurable | unmatched |  |
| aux_snipeClipped | definition | `Estimator.lean:snipeClipped (L67)` | aux_snipeClipped | unmatched |  |
| aux_tiltAmplitude | definition | `Helpers/LeastFavourable.lean:tiltAmplitude (L155)` | aux_tiltAmplitude | unmatched |  |
| aux_tte | definition | `Basic.lean:tte (L132)` | aux_tte | unmatched |  |
| aux_worstRisk | definition | `Estimator.lean:worstRisk (L87)` | aux_worstRisk | unmatched |  |
| aux_worstRiskBdd | definition | `Estimator.lean:worstRiskBdd (L121)` | aux_worstRiskBdd | unmatched |  |
| aux_worstRiskBddFixedGraph | definition | `T_bounded_outcome_frontier.lean:worstRiskBddFixedGraph (L88)` | aux_worstRiskBddFixedGraph | unmatched |  |
| aux_worstRiskFixedGraph | definition | `T_bounded_outcome_frontier.lean:worstRiskFixedGraph (L80)` | aux_worstRiskFixedGraph | unmatched |  |
| aux_AdmissibleEstimator | definition | `Estimator.lean:AdmissibleEstimator (L95)` | aux_AdmissibleEstimator | unmatched |  |
| aux_AdmissibleEstimatorBdd | definition | `Estimator.lean:AdmissibleEstimatorBdd (L128)` | aux_AdmissibleEstimatorBdd | unmatched |  |
| aux_containingNeighborhoods | definition | `Helpers/OverlapCount.lean:containingNeighborhoods (L19)` | aux_containingNeighborhoods | unmatched |  |
| aux_DegreeIndex | definition | `Basic.lean:DegreeIndex (L59)` | aux_DegreeIndex | unmatched |  |
| aux_minimaxRiskBddOutcome | definition | `Estimator.lean:minimaxRiskBddOutcome (L143)` | aux_minimaxRiskBddOutcome | unmatched |  |
| aux_nbhd | definition | `Basic.lean:nbhd (L35)` | aux_nbhd | unmatched |  |
| aux_snipeEstimator | definition | `Estimator.lean:snipeEstimator (L60)` | aux_snipeEstimator | unmatched |  |
| fairCoinContrast | lemma | `T_fair_coin_frontier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.fairCoinContrast (L21)` | fairCoinContrast | unmatched |  |
| fairCoinEnergy | lemma | `T_fair_coin_frontier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.fairCoinEnergy (L41)` | fairCoinEnergy | unmatched |  |
| fairCoinKStar | lemma | `T_fair_coin_frontier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.fairCoinKStar (L76)` | fairCoinKStar | unmatched |  |
| E_coordinate_prod | lemma | `Helpers/BernoulliFourier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.E_coordinate_prod (L26)` | E_coordinate_prod | unmatched |  |
| one_sub_prod_le_sum | lemma | `Helpers/HellingerAffinity.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.one_sub_prod_le_sum (L249)` | one_sub_prod_le_sum | unmatched |  |
| potentialOutcome_abs_le_of_mem_modelClass | lemma | `T_degree_frontier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.potentialOutcome_abs_le_of_mem_modelClass (L16)` | potentialOutcome_abs_le_of_mem_modelClass | unmatched |  |
| tte_abs_le_two_mul_of_mem_modelClass | lemma | `T_degree_frontier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.tte_abs_le_two_mul_of_mem_modelClass (L41)` | tte_abs_le_two_mul_of_mem_modelClass | unmatched |  |
| snipeClipped_admissible | lemma | `T_degree_frontier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.snipeClipped_admissible (L79)` | snipeClipped_admissible | unmatched |  |
| minimaxRisk_le_worstRisk_of_admissible | lemma | `T_degree_frontier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.minimaxRisk_le_worstRisk_of_admissible (L140)` | minimaxRisk_le_worstRisk_of_admissible | unmatched |  |
| blockRepresenter_contrast_energy | assumption | `(none)` | blockRepresenter_contrast_energy | unmatched |  |
| blockScore_contrast | lemma | `Helpers/BlockRepresenterCore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockScore_contrast (L354)` | blockScore_contrast | unmatched |  |
| blockEnergy_pos | lemma | `Helpers/BlockRepresenterCore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockEnergy_pos (L395)` | blockEnergy_pos | unmatched |  |
| localEnergy_le_blockEnergy | lemma | `Helpers/SnipeVariance.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.localEnergy_le_blockEnergy (L373)` | localEnergy_le_blockEnergy | unmatched |  |
| blockContrast_binomial | lemma | `Helpers/BlockRepresenterCore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockContrast_binomial (L28)` | blockContrast_binomial | unmatched |  |
| blockScore_raw_moment | lemma | `Helpers/BlockRepresenterCore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockScore_raw_moment (L69)` | blockScore_raw_moment | unmatched |  |
| blockScore_mean_zero | lemma | `Helpers/BlockRepresenterCore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockScore_mean_zero (L163)` | blockScore_mean_zero | unmatched |  |
| centeredMonomial_raw_expansion | lemma | `Helpers/BlockRepresenterCore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.centeredMonomial_raw_expansion (L442)` | centeredMonomial_raw_expansion | unmatched |  |
| sum_powerset_subset_exchange | lemma | `Helpers/BlockRepresenterCore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.sum_powerset_subset_exchange (L460)` | sum_powerset_subset_exchange | unmatched |  |
| nbhdB_edgeFn_eq_nbhd | lemma | `Helpers/SnipeVariance.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.nbhdB_edgeFn_eq_nbhd (L26)` | nbhdB_edgeFn_eq_nbhd | unmatched |  |
| nbhdB_edgeFnBdd_eq_nbhd | lemma | `Helpers/SnipeVariance.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.nbhdB_edgeFnBdd_eq_nbhd (L32)` | nbhdB_edgeFnBdd_eq_nbhd | unmatched |  |
| E_global_coordinate_prod | lemma | `Helpers/SnipeVariance.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.E_global_coordinate_prod (L38)` | E_global_coordinate_prod | unmatched |  |
| snipeScore_raw_moment | lemma | `Helpers/SnipeVariance.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.snipeScore_raw_moment (L51)` | snipeScore_raw_moment | unmatched |  |
| snipeScore_mean_zero | lemma | `Helpers/SnipeVariance.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.snipeScore_mean_zero (L197)` | snipeScore_mean_zero | unmatched |  |
| snipeScore_potentialOutcome_moment | lemma | `Helpers/SnipeVariance.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.snipeScore_potentialOutcome_moment (L242)` | snipeScore_potentialOutcome_moment | unmatched |  |
| blockScore_weightFeasibleAt | lemma | `Helpers/BlockRepresenterCore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockScore_weightFeasibleAt (L196)` | blockScore_weightFeasibleAt | unmatched |  |
| weightProg_le_blockEnergy | lemma | `Helpers/BlockRepresenterCore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.weightProg_le_blockEnergy (L338)` | weightProg_le_blockEnergy | unmatched |  |
| kStar_mem_exposedOrder | lemma | `Helpers/BlockRepresenterCore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.kStar_mem_exposedOrder (L547)` | kStar_mem_exposedOrder | unmatched |  |
| blockEnergy_topExposed_le | lemma | `Helpers/BlockRepresenterCore.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockEnergy_topExposed_le (L567)` | blockEnergy_topExposed_le | unmatched |  |
| blockDesign_sq_eq_zero_iff | lemma | `Helpers/BlockRepresenter.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockDesign_sq_eq_zero_iff (L19)` | blockDesign_sq_eq_zero_iff | unmatched |  |
| blockScore_mem_polySpace | lemma | `Helpers/BlockRepresenter.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockScore_mem_polySpace (L50)` | blockScore_mem_polySpace | unmatched |  |
| weightFeasibleAt_represents | lemma | `Helpers/BlockRepresenter.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.weightFeasibleAt_represents (L103)` | weightFeasibleAt_represents | unmatched |  |
| perturbFeasible_energy_unique | lemma | `Helpers/BlockRepresenter.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.perturbFeasible_energy_unique (L143)` | perturbFeasible_energy_unique | unmatched |  |
| weightFeasibleAt_energy_unique | lemma | `Helpers/BlockRepresenter.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.weightFeasibleAt_energy_unique (L201)` | weightFeasibleAt_energy_unique | unmatched |  |
| blockPrograms_exact | lemma | `Helpers/BlockRepresenter.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockPrograms_exact (L265)` | blockPrograms_exact | unmatched |  |
| choose_le_pow_mul_choose | lemma | `Helpers/BlockRepresenterUniform.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.choose_le_pow_mul_choose (L43)` | choose_le_pow_mul_choose | unmatched |  |
| eligibleOrder_le_kStar | lemma | `Helpers/BlockRepresenterUniform.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.eligibleOrder_le_kStar (L62)` | eligibleOrder_le_kStar | unmatched |  |
| blockLowerConst_spec | lemma | `Helpers/BlockRepresenterUniform.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockLowerConst_spec (L82)` | blockLowerConst_spec | unmatched |  |
| blockEnergy_uniform_compare | lemma | `Helpers/BlockRepresenterUniform.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockEnergy_uniform_compare (L107)` | blockEnergy_uniform_compare | unmatched |  |
| blockRawCoef_mass_estimate | lemma | `Helpers/BlockRepresenterUniform.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockRawCoef_mass_estimate (L184)` | blockRawCoef_mass_estimate | unmatched |  |
| blockRawCoef_mass_uniform | lemma | `Helpers/BlockRepresenterUniform.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.blockRawCoef_mass_uniform (L274)` | blockRawCoef_mass_uniform | unmatched |  |
| modelClassIncluded_of_coeffMass | lemma | `T_bounded_outcome_frontier.lean:CausalSmith.Experimentation.SnipeDegreeFrontier.modelClassIncluded_of_coeffMass (L44)` | modelClassIncluded_of_coeffMass | unmatched |  |
