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
| P-1 | definition | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.HolderDoseClass (L280)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.thetaFunctional (L351)` | P-2 | equivalent |  |
| P-3 | definition | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.minimaxRisk (L362)` | P-3 | equivalent |  |
| P-4 | definition | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.publishedHoifRate (L376)` | P-4 | equivalent |  |
| P-5 | definition | `Frontier.lean:CausalSmith.Stat.DoseResponseMinimax.betaFrontierHandle (L25)` | P-5 | equivalent |  |
| T-1 | theorem | `T_SharpPointwiseLowerBound.lean:CausalSmith.Stat.DoseResponseMinimax.sharp_pointwise_lower_bound (L24)` | T-1 | equivalent |  |
| T-2 | theorem | `T_OracleRegimeReduction.lean:CausalSmith.Stat.DoseResponseMinimax.oracle_regime_reduction (L25)` | T-2 | equivalent |  |
| T-3 | theorem | `T_CertifiedPartialBetaFrontier.lean:CausalSmith.Stat.DoseResponseMinimax.certifiedPartialBetaFrontier (L22)` | T-3 | equivalent |  |
| T-4 | theorem | `T_SharpMinimaxSmoothCovariate.lean:CausalSmith.Stat.DoseResponseMinimax.sharp_minimax_smooth_covariate (L24)` | T-4 | equivalent |  |
| T-5 | theorem | `T_FrontierBracketDeficient.lean:CausalSmith.Stat.DoseResponseMinimax.frontier_bracket_deficient (L25)` | T-5 | equivalent |  |
| L-1 | lemma | `Helpers/Divergence.lean:CausalSmith.Stat.DoseResponseMinimax.bernoulli_mean_channel_kl_source (L45)` | L-1 | equivalent |  |
| L-2 | lemma | `Helpers/Divergence.lean:CausalSmith.Stat.DoseResponseMinimax.le_cam_two_point_mse_source (L54)` | L-2 | equivalent |  |
| L-3 | lemma | `Helpers/RateAlgebra.lean:CausalSmith.Stat.DoseResponseMinimax.rho_oracle_regime_algebra (L21)` | L-3 | equivalent |  |
| L-4 | lemma | `Helpers/TwoPointConstruction.lean:CausalSmith.Stat.DoseResponseMinimax.oracle_dose_regression_lower_all_beta (L220)` | L-4 | equivalent |  |
| L-5 | lemma | `Helpers/RateAlgebra.lean:CausalSmith.Stat.DoseResponseMinimax.rho_deficient_regime_algebra (L55)` | L-5 | equivalent |  |
| L-6 | lemma | `Helpers/FrontierBracket.lean:CausalSmith.Stat.DoseResponseMinimax.certified_beta_frontier_bracket (L29)` | L-6 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.IidSampling (L120)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.Consistency (L134)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.NoUnmeasuredConfounding (L144)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.BoundedOutcome (L157)` | A-4 | equivalent |  |
| A-5 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.InteriorDose (L162)` | A-5 | equivalent |  |
| A-6 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.LocalPositivity (L168)` | A-6 | equivalent |  |
| A-7 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.MuTreatmentHolder (L174)` | A-7 | equivalent |  |
| A-8 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.PiTreatmentHolder (L181)` | A-8 | equivalent |  |
| A-9 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.MuCovariateHolder (L187)` | A-9 | equivalent |  |
| A-10 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.PiCovariateHolder (L193)` | A-10 | equivalent |  |
| A-11 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.PxHolder (L203)` | A-11 | equivalent |  |
| A-12 | assumption | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.BaselineSubmodelSlack (L216)` | A-12 | equivalent |  |
| ass:mu-is-regression | definition | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.MuIsRegression (L233)` | ass:mu-is-regression | unmatched |  |
| ass:px-is-x-density | definition | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.PxIsXDensity (L242)` | ass:px-is-x-density | unmatched |  |
| ass:pi-is-cond-treatment-density | definition | `Basic.lean:CausalSmith.Stat.DoseResponseMinimax.PiIsCondTreatmentDensity (L264)` | ass:pi-is-cond-treatment-density | unmatched |  |
| minimaxRisk-two-point-lower | lemma | `Helpers/TwoPointConstruction.lean:CausalSmith.Stat.DoseResponseMinimax.minimaxRisk_two_point_lower (L61)` | minimaxRisk-two-point-lower | unmatched |  |
| measurable-set-cube | lemma | `Helpers/Witness/Base.lean:CausalSmith.Stat.DoseResponseMinimax.measurableSet_cube (L28)` | measurable-set-cube | unmatched |  |
| restrict-withDensity-ofReal-isProbability | lemma | `Helpers/Witness/Base.lean:CausalSmith.Stat.DoseResponseMinimax.restrict_withDensity_ofReal_isProbabilityMeasure (L35)` | restrict-withDensity-ofReal-isProbability | unmatched |  |
| integrable-of-ae-bounded | lemma | `Helpers/Witness/Base.lean:CausalSmith.Stat.DoseResponseMinimax.integrable_of_measurable_ae_bounded (L54)` | integrable-of-ae-bounded | unmatched |  |
| doseObs-measurability | lemma | `Helpers/Witness/Base.lean:CausalSmith.Stat.DoseResponseMinimax.measurable_doseObs_tuple (L65)` | doseObs-measurability | unmatched |  |
| bump-holder-substrate-gate | lemma | `Helpers/Witness/BumpHolder.lean:CausalSmith.Stat.DoseResponseMinimax.doseBump_holder_gate (L216)` | bump-holder-substrate-gate | unmatched |  |
| dose-channel-ax | definition | `Helpers/Witness/Channel.lean:CausalSmith.Stat.DoseResponseMinimax.doseChannelAX (L30)` | dose-channel-ax | unmatched |  |
| dose-ax-probability | lemma | `Helpers/Witness/Channel.lean:CausalSmith.Stat.DoseResponseMinimax.doseAXMeasure_isProbabilityMeasure (L67)` | dose-ax-probability | unmatched |  |
| dose-data-eq-axbind | lemma | `Helpers/Witness/Channel.lean:CausalSmith.Stat.DoseResponseMinimax.doseDataMeasure_eq_AXbind (L90)` | dose-data-eq-axbind | unmatched |  |
| dose-bump | definition | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.doseContDiffBump (L22)` | dose-bump | unmatched |  |
| dose-bump-function | definition | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.doseBump (L27)` | dose-bump-function | unmatched |  |
| twoPointMean-map-doseObs-measurable | lemma | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.measurable_twoPointMean_map_doseObs (L108)` | twoPointMean-map-doseObs-measurable | unmatched |  |
| twoPointMean-map-doseObs-pair-measurable | lemma | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.measurable_twoPointMean_map_doseObs_pair (L135)` | twoPointMean-map-doseObs-pair-measurable | unmatched |  |
| dose-x-measure | definition | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.doseXMeasure (L160)` | dose-x-measure | unmatched |  |
| dose-a-measure | definition | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.doseAMeasure (L167)` | dose-a-measure | unmatched |  |
| dose-outcome-kernel-measurable | lemma | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.measurable_doseOutcomeKernel (L173)` | dose-outcome-kernel-measurable | unmatched |  |
| dose-ax-measure | definition | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.doseAXMeasure (L203)` | dose-ax-measure | unmatched |  |
| dose-data-measure | definition | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.doseDataMeasure (L212)` | dose-data-measure | unmatched |  |
| dose-potential | definition | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.dosePotential (L223)` | dose-potential | unmatched |  |
| dose-witness | definition | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness (L230)` | dose-witness | unmatched |  |
| dose-base-probability | lemma | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.doseXMeasure_isProbabilityMeasure (L243)` | dose-base-probability | unmatched |  |
| dose-witness-kl-single | lemma | `Helpers/Witness/KL.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness_kl_single_le (L282)` | dose-witness-kl-single | unmatched |  |
| dose-witness-kl-nfold | lemma | `Helpers/Witness/KL.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness_kl_nfold_le (L629)` | dose-witness-kl-nfold | unmatched |  |
| dose-data-probability | lemma | `Helpers/Witness/Measure.lean:CausalSmith.Stat.DoseResponseMinimax.doseDataMeasure_isProbabilityMeasure (L21)` | dose-data-probability | unmatched |  |
| dose-data-x-marginal | lemma | `Helpers/Witness/Measure.lean:CausalSmith.Stat.DoseResponseMinimax.doseDataMeasure_map_X (L67)` | dose-data-x-marginal | unmatched |  |
| dose-witness-px-density | lemma | `Helpers/Witness/Measure.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness_pxDens (L111)` | dose-witness-px-density | unmatched |  |
| dose-witness-consistency | lemma | `Helpers/Witness/Measure.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness_consistency (L126)` | dose-witness-consistency | unmatched |  |
| dose-data-y-support | lemma | `Helpers/Witness/Measure.lean:CausalSmith.Stat.DoseResponseMinimax.doseDataMeasure_ae_Y_mem_Icc (L136)` | dose-data-y-support | unmatched |  |
| dose-witness-bounded-outcome | lemma | `Helpers/Witness/Measure.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness_bdd (L183)` | dose-witness-bounded-outcome | unmatched |  |
| dose-witness-membership | lemma | `Helpers/Witness/Membership.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness_mem_class (L158)` | dose-witness-membership | unmatched |  |
| dose-data-ax-marginal | lemma | `Helpers/Witness/PiCond.lean:CausalSmith.Stat.DoseResponseMinimax.doseDataMeasure_map_AX (L21)` | dose-data-ax-marginal | unmatched |  |
| dose-ax-product | lemma | `Helpers/Witness/PiCond.lean:CausalSmith.Stat.DoseResponseMinimax.doseAXMeasure_eq_prod (L71)` | dose-ax-product | unmatched |  |
| dose-ax-density | lemma | `Helpers/Witness/PiCond.lean:CausalSmith.Stat.DoseResponseMinimax.doseAXMeasure_density (L96)` | dose-ax-density | unmatched |  |
| dose-witness-pi-cond | lemma | `Helpers/Witness/PiCond.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness_piCond (L131)` | dose-witness-pi-cond | unmatched |  |
| dose-witness-mu-regression | lemma | `Helpers/Witness/Regression.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness_muReg (L307)` | dose-witness-mu-regression | unmatched |  |
| dose-witness-ignorability | lemma | `Helpers/Witness/Regression.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness_ignorability (L375)` | dose-witness-ignorability | unmatched |  |
| dose-witness-theta | lemma | `Helpers/Witness/Theta.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness_theta (L19)` | dose-witness-theta | unmatched |  |
| dose-witness-theta-sep | lemma | `Helpers/Witness/Theta.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitness_theta_sep (L34)` | dose-witness-theta-sep | unmatched |  |
| map-bind-map-proj | lemma | `Helpers/Witness/Base.lean:CausalSmith.Stat.DoseResponseMinimax.map_bind_map_proj (L116)` | map-bind-map-proj | unmatched |  |
| dose-witness-mu | definition | `Helpers/Witness/Core.lean:CausalSmith.Stat.DoseResponseMinimax.doseWitnessMu (L68)` | dose-witness-mu | unmatched |  |
