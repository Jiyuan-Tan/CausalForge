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
| P-1 | definition | `Basic.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.betaNStar (L315)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.collapsedPopulationProjection (L239)` | P-2 | equivalent |  |
| P-3 | definition | `Basic.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.hatBetaN (L356)` | P-3 | equivalent |  |
| P-4 | definition | `Helpers/WeightedFWL.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.weightedFWLResidual (L92)` | P-4 | equivalent |  |
| P-5 | definition | `Helpers/Frontier.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.signReversalRegion (L52)` | P-5 | equivalent |  |
| P-6 | definition | `Helpers/Frontier.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.fourCohortWitness (L122)` | P-6 | equivalent |  |
| P-7 | definition | `Helpers/Frontier.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierEliminationHandle (L162)` | P-7 | equivalent |  |
| T-1 | theorem | `ForbiddenSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.sharp_ppml_forbidden_sign (L98)` | T-1 | equivalent |  |
| T-2 | theorem | `FourCohort.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.four_cohort_sign_reversal (L738)` | T-2 | equivalent |  |
| T-3 | theorem | `Homogeneous.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.homogeneous_effect_reduction (L9)` | T-3 | equivalent |  |
| T-4 | theorem | `PrimitiveFrontier.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.primitive_global_frontier (L56)` | T-4 | equivalent |  |
| L-1 | lemma | `Collapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.unit_fe_collapse (L19)` | L-1 | equivalent |  |
| L-2 | lemma | `Projection.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.pseudo_true_ppml_projection (L55)` | L-2 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.CohortShareLimit (L370)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.UnitUntreatedExponentialMean (L380)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.WithinCohortBaselineLimit (L389)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.ProportionalEffects (L395)` | A-4 | equivalent |  |
| A-5 | assumption | `Basic.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.CollapsedDesignRank (L403)` | A-5 | equivalent |  |
| A-6 | assumption | `Basic.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.MulticohortFrontierScope (L409)` | A-6 | equivalent |  |
| A-7 | assumption | `Basic.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.StrictPositiveEffects (L416)` | A-7 | equivalent |  |
| poissonCell_linear_coercive_bound | lemma | `Helpers/PoissonProjection.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.poissonCell_linear_coercive_bound (L19)` | poissonCell_linear_coercive_bound | unmatched |  |
| poissonCell_strictConcave_midpoint | lemma | `Helpers/PoissonProjection.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.poissonCell_strictConcave_midpoint (L39)` | poissonCell_strictConcave_midpoint | unmatched |  |
| finitePoissonObjective | definition | `Helpers/PoissonProjection.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finitePoissonObjective (L57)` | finitePoissonObjective | unmatched |  |
| finitePoissonObjective_continuous | lemma | `Helpers/PoissonProjection.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finitePoissonObjective_continuous (L62)` | finitePoissonObjective_continuous | unmatched |  |
| finitePoissonObjective_exists_unique_max | lemma | `Helpers/PoissonProjection.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finitePoissonObjective_exists_unique_max (L71)` | finitePoissonObjective_exists_unique_max | unmatched |  |
| finitePoissonObjective_score | lemma | `Helpers/PoissonProjection.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finitePoissonObjective_score (L231)` | finitePoissonObjective_score | unmatched |  |
| collapsedDesignMap | definition | `Projection.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.collapsedDesignMap (L15)` | collapsedDesignMap | unmatched |  |
| limitingCriterion_eq_finitePoissonObjective | lemma | `Projection.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.limitingCriterion_eq_finitePoissonObjective (L40)` | limitingCriterion_eq_finitePoissonObjective | unmatched |  |
| tendsto_argmax_of_eventually_mem_compact | lemma | `Helpers/ArgmaxStability.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.tendsto_argmax_of_eventually_mem_compact (L14)` | tendsto_argmax_of_eventually_mem_compact | unmatched |  |
| finitePoissonObjective_tendstoUniformlyOn | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finitePoissonObjective_tendstoUniformlyOn (L15)` | finitePoissonObjective_tendstoUniformlyOn | unmatched |  |
| finitePoissonObjective_eventually_common_compact | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finitePoissonObjective_eventually_common_compact (L54)` | finitePoissonObjective_eventually_common_compact | unmatched |  |
| finitePoissonObjective_argmax_tendsto | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finitePoissonObjective_argmax_tendsto (L183)` | finitePoissonObjective_argmax_tendsto | unmatched |  |
| finiteCollapsedCriterion_eq_finitePoissonObjective | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finiteCollapsedCriterion_eq_finitePoissonObjective (L219)` | finiteCollapsedCriterion_eq_finitePoissonObjective | unmatched |  |
| collapsedDesignMap_injective | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.collapsedDesignMap_injective (L237)` | collapsedDesignMap_injective | unmatched |  |
| finiteCollapsedCriterion_exists_unique_max | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finiteCollapsedCriterion_exists_unique_max (L263)` | finiteCollapsedCriterion_exists_unique_max | unmatched |  |
| unitLevel | definition | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.unitLevel (L305)` | unitLevel | unmatched |  |
| unitTimeLevel | definition | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.unitTimeLevel (L311)` | unitTimeLevel | unmatched |  |
| unitIndex_eq_levels | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.unitIndex_eq_levels (L315)` | unitIndex_eq_levels | unmatched |  |
| collapsedCohortLevel | definition | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.collapsedCohortLevel (L364)` | collapsedCohortLevel | unmatched |  |
| collapsedTimeLevel | definition | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.collapsedTimeLevel (L370)` | collapsedTimeLevel | unmatched |  |
| collapsedIndex_eq_levels | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.collapsedIndex_eq_levels (L375)` | collapsedIndex_eq_levels | unmatched |  |
| unitDesignMap | definition | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.unitDesignMap (L427)` | unitDesignMap | unmatched |  |
| unitDesignMap_injective | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.unitDesignMap_injective (L452)` | unitDesignMap_injective | unmatched |  |
| unitCriterion_eq_finitePoissonObjective | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.unitCriterion_eq_finitePoissonObjective (L543)` | unitCriterion_eq_finitePoissonObjective | unmatched |  |
| liftCollapsedParameter | definition | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.liftCollapsedParameter (L561)` | liftCollapsedParameter | unmatched |  |
| unitIndex_liftCollapsedParameter | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.unitIndex_liftCollapsedParameter (L575)` | unitIndex_liftCollapsedParameter | unmatched |  |
| sum_baselineRatio_within_cohort | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.sum_baselineRatio_within_cohort (L603)` | sum_baselineRatio_within_cohort | unmatched |  |
| sum_baselineRatio_fiberwise | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.sum_baselineRatio_fiberwise (L622)` | sum_baselineRatio_fiberwise | unmatched |  |
| sum_units_by_supported_cohort | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.sum_units_by_supported_cohort (L651)` | sum_units_by_supported_cohort | unmatched |  |
| aggregateUnitDirection | definition | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.aggregateUnitDirection (L669)` | aggregateUnitDirection | unmatched |  |
| collapsedIndex_aggregateUnitDirection | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.collapsedIndex_aggregateUnitDirection (L683)` | collapsedIndex_aggregateUnitDirection | unmatched |  |
| unitResidual_liftCollapsedParameter | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.unitResidual_liftCollapsedParameter (L714)` | unitResidual_liftCollapsedParameter | unmatched |  |
| unitScore_eq_collapsedScore | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.unitScore_eq_collapsedScore (L737)` | unitScore_eq_collapsedScore | unmatched |  |
| uniqueGlobalMax_maximizerOrZero | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.uniqueGlobalMax_maximizerOrZero (L845)` | uniqueGlobalMax_maximizerOrZero | unmatched |  |
| finite_unit_and_collapsed_unique_beta | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finite_unit_and_collapsed_unique_beta (L864)` | finite_unit_and_collapsed_unique_beta | unmatched |  |
| selectedFiniteCollapsed_tendsto | lemma | `Helpers/FiniteCollapse.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.selectedFiniteCollapsed_tendsto (L943)` | selectedFiniteCollapsed_tendsto | unmatched |  |
| finitePoissonObjective_isMax_of_score | lemma | `Helpers/PoissonProjection.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finitePoissonObjective_isMax_of_score (L261)` | finitePoissonObjective_isMax_of_score | unmatched |  |
| fwlEnergy_pos_of_collapsedDesignRank | lemma | `ForbiddenSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.fwlEnergy_pos_of_collapsedDesignRank (L23)` | fwlEnergy_pos_of_collapsedDesignRank | unmatched |  |
| expCellUpdatedMean | definition | `Helpers/PoissonArgmaxDerivative.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.expCellUpdatedMean (L15)` | expCellUpdatedMean | unmatched |  |
| finitePoissonObjective_expCell_argmax_snd_hasDerivAt | lemma | `Helpers/PoissonArgmaxDerivative.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finitePoissonObjective_expCell_argmax_snd_hasDerivAt (L23)` | finitePoissonObjective_expCell_argmax_snd_hasDerivAt | unmatched |  |
| betaStar_update_hasDerivAt | lemma | `Helpers/PoissonArgmaxDerivative.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.betaStar_update_hasDerivAt (L297)` | betaStar_update_hasDerivAt | unmatched |  |
| linearizedScore_snd_eq_weightedFWL | lemma | `Helpers/WeightedFWL.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.linearizedScore_snd_eq_weightedFWL (L132)` | linearizedScore_snd_eq_weightedFWL | unmatched |  |
| frontierPrimitiveH_pos | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierPrimitiveH_pos (L12)` | frontierPrimitiveH_pos | unmatched |  |
| frontierPrimitiveRow_pos | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierPrimitiveRow_pos (L22)` | frontierPrimitiveRow_pos | unmatched |  |
| frontierPrimitiveColumn_pos | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierPrimitiveColumn_pos (L33)` | frontierPrimitiveColumn_pos | unmatched |  |
| frontierPrimitiveTotal_pos | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierPrimitiveTotal_pos (L45)` | frontierPrimitiveTotal_pos | unmatched |  |
| frontierPrimitiveColumn_sum | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierPrimitiveColumn_sum (L57)` | frontierPrimitiveColumn_sum | unmatched |  |
| frontierNuisanceParameter | definition | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierNuisanceParameter (L68)` | frontierNuisanceParameter | unmatched |  |
| frontierNuisanceParameter_index | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierNuisanceParameter_index (L81)` | frontierNuisanceParameter_index | unmatched |  |
| frontierNuisanceParameter_exp | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierNuisanceParameter_exp (L119)` | frontierNuisanceParameter_exp | unmatched |  |
| frontierConditionalResidual | definition | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierConditionalResidual (L140)` | frontierConditionalResidual | unmatched |  |
| frontierConditionalResidual_eq | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierConditionalResidual_eq (L150)` | frontierConditionalResidual_eq | unmatched |  |
| frontierConditionalResidual_row_sum | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierConditionalResidual_row_sum (L167)` | frontierConditionalResidual_row_sum | unmatched |  |
| frontierConditionalResidual_column_sum | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierConditionalResidual_column_sum (L185)` | frontierConditionalResidual_column_sum | unmatched |  |
| frontierConditionalNuisanceScore | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierConditionalNuisanceScore (L220)` | frontierConditionalNuisanceScore | unmatched |  |
| frontierConditionalScalarScore | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.frontierConditionalScalarScore (L304)` | frontierConditionalScalarScore | unmatched |  |
| betaStar_sign_frontierEliminationHandle | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.betaStar_sign_frontierEliminationHandle (L401)` | betaStar_sign_frontierEliminationHandle | unmatched |  |
| primitiveLimitingCriterion_restrict | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.primitiveLimitingCriterion_restrict (L498)` | primitiveLimitingCriterion_restrict | unmatched |  |
| primitiveBetaStar_restrict | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.primitiveBetaStar_restrict (L537)` | primitiveBetaStar_restrict | unmatched |  |
| cohortShareLimit_sum_eq_one | lemma | `Helpers/FrontierSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.cohortShareLimit_sum_eq_one (L546)` | cohortShareLimit_sum_eq_one | unmatched |  |
| finitePoissonObjective_snd_sign_of_nuisance_score | lemma | `Helpers/PoissonConditionalSign.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finitePoissonObjective_snd_sign_of_nuisance_score (L13)` | finitePoissonObjective_snd_sign_of_nuisance_score | unmatched |  |
| finitePoissonObjective_argmax_continuousAt_mean | lemma | `Helpers/PoissonArgmaxContinuity.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.finitePoissonObjective_argmax_continuousAt_mean (L11)` | finitePoissonObjective_argmax_continuousAt_mean | unmatched |  |
| weightedFWLResidual_continuousAt_effects | lemma | `Helpers/WeightedFWLContinuity.lean:CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.weightedFWLResidual_continuousAt_effects (L340)` | weightedFWLResidual_continuousAt_effects | unmatched |  |
