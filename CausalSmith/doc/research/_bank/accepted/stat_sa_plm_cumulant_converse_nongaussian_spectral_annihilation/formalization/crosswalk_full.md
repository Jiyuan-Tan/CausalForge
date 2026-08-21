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
| P-1 | definition | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.NonGaussianClass (L307)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.GaussianClass (L322)` | P-2 | equivalent |  |
| P-3 | definition | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.JmsAceClass (L336)` | P-3 | equivalent |  |
| P-4 | definition | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.zeroInstrument (L316)` | P-4 | equivalent |  |
| P-5 | definition | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.contourFunctional (L467)` | P-5 | equivalent |  |
| P-6 | definition | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.minimaxRisks (L395)` | P-6 | equivalent |  |
| P-7 | definition | `Helpers/JmsComparator.lean:CausalSmith.Stat.SaPlmCumulantConverse.jmsEligible (L61)` | P-7 | equivalent |  |
| P-8 | definition | `Helpers/SineScore.lean:CausalSmith.Stat.SaPlmCumulantConverse.thetaHatSin (L37)` | P-8 | equivalent |  |
| P-9 | definition | `OpenQuestions.lean:CausalSmith.Stat.SaPlmCumulantConverse.candidateRecord (L94)` | P-9 | equivalent |  |
| P-10 | definition | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.AceComparisonSubclass (L352)` | P-10 | equivalent |  |
| P-11 | definition | `Helpers/BoundedCertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.complexCertifiedIntervalArithmetic (L1220)` | P-11 | equivalent |  |
| P-12 | definition | `Helpers/ContourBank.lean:CausalSmith.Stat.SaPlmCumulantConverse.contourBank (L221)` | P-12 | equivalent |  |
| P-13 | definition | `Helpers/SpectralEstimator.lean:CausalSmith.Stat.SaPlmCumulantConverse.thetaHatSpec (L2672)` | P-13 | equivalent |  |
| P-14 | definition | `OpenQuestions.lean:CausalSmith.Stat.SaPlmCumulantConverse.LocalToGaussianFrontier (L106)` | P-14 | equivalent |  |
| T-1 | theorem | `T1_KnownZeroInstrument.lean:CausalSmith.Stat.SaPlmCumulantConverse.known_zero_instrument (L16)` | T-1 | equivalent |  |
| T-2 | theorem | `T2_ExactContourIdentification.lean:CausalSmith.Stat.SaPlmCumulantConverse.exact_contour_identification (L94)` | T-2 | equivalent |  |
| T-3 | theorem | `T3_AdaptiveRootNMinimax.lean:CausalSmith.Stat.SaPlmCumulantConverse.adaptive_rootn_minimax (L158)` | T-3 | equivalent |  |
| T-4 | theorem | `T4_JmsAceAlignment.lean:CausalSmith.Stat.SaPlmCumulantConverse.jms_ace_alignment (L87)` | T-4 | equivalent |  |
| T-5 | theorem | `T5_CommonExperimentDichotomy.lean:CausalSmith.Stat.SaPlmCumulantConverse.common_experiment_dichotomy (L35)` | T-5 | equivalent |  |
| T-6 | theorem | `T6_SymmetricMixtureReduction.lean:CausalSmith.Stat.SaPlmCumulantConverse.symmetric_mixture_reduction (L222)` | T-6 | equivalent |  |
| T-7 | theorem | `T7_LocalToGaussianPartialBenchmarks.lean:CausalSmith.Stat.SaPlmCumulantConverse.local_to_gaussian_partial_benchmarks (L17)` | T-7 | equivalent |  |
| T-8 | theorem | `T8_BoundedOutcomeGaussianDegeneracy.lean:CausalSmith.Stat.SaPlmCumulantConverse.bounded_outcome_gaussian_degeneracy (L205)` | T-8 | equivalent |  |
| L-1 | lemma | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.observable_factorization (L480)` | L-1 | equivalent |  |
| L-2 | lemma | `Helpers/Cumulant.lean:CausalSmith.Stat.SaPlmCumulantConverse.zero_localization (L84)` | L-2 | equivalent |  |
| L-3 | lemma | `Helpers/ContourBank.lean:CausalSmith.Stat.SaPlmCumulantConverse.finite_contour_bank (L259)` | L-3 | equivalent |  |
| L-4 | lemma | `Helpers/HardSubmodel.lean:CausalSmith.Stat.SaPlmCumulantConverse.non_gaussian_hard_submodel (L112)` | L-4 | equivalent |  |
| L-5 | lemma | `Helpers/GaussianRademacherBenchmark.lean:CausalSmith.Stat.SaPlmCumulantConverse.gaussian_rademacher_l1_benchmark (L549)` | L-5 | equivalent |  |
| L-6 | lemma | `Helpers/EmpiricalTransformSeries.lean:CausalSmith.Stat.SaPlmCumulantConverse.empirical_transform_uniform_l2 (L484)` | L-6 | equivalent |  |
| L-7 | lemma | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.l1_nuisance_zero_free (L567)` | L-7 | equivalent |  |
| L-8 | lemma | `Helpers/ClassRelations.lean:CausalSmith.Stat.SaPlmCumulantConverse.jms_ace_class_relations (L18)` | L-8 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.IidSampling (L191)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.IndependentTreatmentNoise (L197)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.OutcomeMeanIndependence (L205)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.ThetaRange (L211)` | A-4 | equivalent |  |
| A-5 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.GRange (L215)` | A-5 | equivalent |  |
| A-6 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.QRange (L219)` | A-6 | equivalent |  |
| A-7 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.BoundedGaussianOutcome (L223)` | A-7 | equivalent |  |
| A-8 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.EtaSubGaussian (L227)` | A-8 | equivalent |  |
| A-9 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.XiSubGaussian (L233)` | A-9 | equivalent |  |
| A-10 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.CumulantSeparation (L242)` | A-10 | equivalent |  |
| A-11 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.TreatmentCodeRadiusLs (L246)` | A-11 | drift |  |
| A-12 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.OutcomeCodeRadiusLs (L257)` | A-12 | drift |  |
| A-13 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.TreatmentCodeRadiusLr (L268)` | A-13 | drift |  |
| A-14 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.OutcomeCodeRadiusLr (L279)` | A-14 | drift |  |
| A-15 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.GaussianTreatmentNoise (L290)` | A-15 | equivalent |  |
| A-16 | assumption | `Basic.lean:CausalSmith.Stat.SaPlmCumulantConverse.TreatmentCodeRadiusL1 (L295)` | A-16 | equivalent |  |
| aux_ContourBankData | definition | `Helpers/ContourBank.lean:ContourBankData (L89)` | aux_ContourBankData | unmatched |  |
| aux_contourCount | definition | `Helpers/Transforms.lean:contourCount (L461)` | aux_contourCount | unmatched |  |
| aux_covariate | definition | `Basic.lean:covariate (L99)` | aux_covariate | unmatched |  |
| aux_Estimator | definition | `Basic.lean:Estimator (L359)` | aux_Estimator | unmatched |  |
| aux_eta | definition | `Basic.lean:eta (L135)` | aux_eta | unmatched |  |
| aux_gaussianRademacherLaw | definition | `Helpers/SineScore.lean:gaussianRademacherLaw (L73)` | aux_gaussianRademacherLaw | unmatched |  |
| aux_generalizedQuantile | definition | `Basic.lean:generalizedQuantile (L376)` | aux_generalizedQuantile | unmatched |  |
| aux_JmsAceClassAt | definition | `Helpers/JmsComparator.lean:JmsAceClassAt (L75)` | aux_JmsAceClassAt | unmatched |  |
| aux_jmsBound | definition | `Helpers/JmsComparator.lean:jmsBound (L65)` | aux_jmsBound | unmatched |  |
| aux_learnedResidual | definition | `Basic.lean:learnedResidual (L149)` | aux_learnedResidual | unmatched |  |
| aux_minimaxQuantileRiskG | definition | `Basic.lean:minimaxQuantileRiskG (L421)` | aux_minimaxQuantileRiskG | unmatched |  |
| aux_minimaxRiskG | definition | `Basic.lean:minimaxRiskG (L416)` | aux_minimaxRiskG | unmatched |  |
| aux_Model | definition | `Basic.lean:Model (L68)` | aux_Model | unmatched |  |
| aux_mseRisk | definition | `Basic.lean:mseRisk (L366)` | aux_mseRisk | unmatched |  |
| aux_nuisanceMGF | definition | `Helpers/Transforms.lean:nuisanceMGF (L36)` | aux_nuisanceMGF | unmatched |  |
| aux_Obs | definition | `Basic.lean:Obs (L25)` | aux_Obs | unmatched |  |
| aux_outcome | definition | `Basic.lean:outcome (L105)` | aux_outcome | unmatched |  |
| aux_outcomeResidualTransform | definition | `Helpers/Transforms.lean:outcomeResidualTransform (L46)` | aux_outcomeResidualTransform | unmatched |  |
| aux_Parameters | definition | `Basic.lean:Parameters (L28)` | aux_Parameters | unmatched |  |
| aux_pilotAdmissible | definition | `(none)` | aux_pilotAdmissible | unmatched |  |
| aux_residualMGF | definition | `Helpers/Transforms.lean:residualMGF (L43)` | aux_residualMGF | unmatched |  |
| aux_searchRadius | definition | `(none)` | aux_searchRadius | unmatched |  |
| aux_thetaHatAt | definition | `Helpers/SineScore.lean:thetaHatAt (L27)` | aux_thetaHatAt | unmatched |  |
| aux_treatmentMGF | definition | `Helpers/Transforms.lean:treatmentMGF (L33)` | aux_treatmentMGF | unmatched |  |
| aux_CertifiedBankInputs | definition | `Helpers/ContourBank.lean:CertifiedBankInputs (L37)` | aux_CertifiedBankInputs | unmatched |  |
| aux_CertifiedContourRun | definition | `(none)` | aux_CertifiedContourRun | unmatched |  |
| aux_GaussianRademacherPathConclusion | definition | `(none)` | aux_GaussianRademacherPathConclusion | unmatched |  |
| aux_minimaxRisk | definition | `Basic.lean:minimaxRisk (L411)` | aux_minimaxRisk | unmatched |  |
| aux_AceEstimator | definition | `Helpers/JmsComparator.lean:AceEstimator (L19)` | aux_AceEstimator | unmatched |  |
| aux_CertifiedEstimatorInputs | definition | `(none)` | aux_CertifiedEstimatorInputs | unmatched |  |
| aux_JmsAceTheoremFiveFour | definition | `Helpers/JmsComparator.lean:JmsAceTheoremFiveFour (L110)` | aux_JmsAceTheoremFiveFour | unmatched |  |
| aux_TotalComputableFromCertifiedNames | definition | `(none)` | aux_TotalComputableFromCertifiedNames | unmatched |  |
| aux_CanonicalCertifiedExecution | definition | `(none)` | aux_CanonicalCertifiedExecution | unmatched |  |
| aux_minimaxRiskOn | definition | `Basic.lean:minimaxRiskOn (L371)` | aux_minimaxRiskOn | unmatched |  |
| aux_CertifiedRangeInput | definition | `Helpers/SpectralEstimator.lean:CertifiedRangeInput (L25)` | aux_CertifiedRangeInput | unmatched |  |
| aux_ComplexCertifiedIntervalArithmeticSpec | definition | `(none)` | aux_ComplexCertifiedIntervalArithmeticSpec | unmatched |  |
| aux_ExecutableCertifiedRealName | definition | `Helpers/SpectralEstimator.lean:ExecutableCertifiedRealName (L2300)` | aux_ExecutableCertifiedRealName | unmatched |  |
| aux_fixedBankInput | definition | `(none)` | aux_fixedBankInput | unmatched |  |
| aux_fixedRangeInput | definition | `(none)` | aux_fixedRangeInput | unmatched |  |
| aux_iidLaw | definition | `Basic.lean:iidLaw (L362)` | aux_iidLaw | unmatched |  |
| aux_PositiveCertifiedReal | definition | `Helpers/ContourBank.lean:PositiveCertifiedReal (L30)` | aux_PositiveCertifiedReal | unmatched |  |
| aux_RepresentedExecution | definition | `Helpers/SpectralEstimator.lean:RepresentedExecution (L2696)` | aux_RepresentedExecution | unmatched |  |
| aux_RepresentedObservation | definition | `Helpers/SpectralEstimator.lean:RepresentedObservation (L152)` | aux_RepresentedObservation | unmatched |  |
| aux_RepresentedSpectralInput | definition | `Helpers/SpectralEstimator.lean:RepresentedSpectralInput (L157)` | aux_RepresentedSpectralInput | unmatched |  |
| aux_SameFixedExperimentConstants | definition | `(none)` | aux_SameFixedExperimentConstants | unmatched |  |
| aux_SpectralExecutionTrace | definition | `Helpers/SpectralEstimator.lean:SpectralExecutionTrace (L2365)` | aux_SpectralExecutionTrace | unmatched |  |
| aux_SpectralProgramResult | definition | `Helpers/SpectralEstimator.lean:SpectralProgramResult (L2468)` | aux_SpectralProgramResult | unmatched |  |
| aux_SqrtBracket | definition | `Helpers/CertifiedComplex.lean:SqrtBracket (L50)` | aux_SqrtBracket | unmatched |  |
| aux_ComplexCertifiedIntervalArithmetic | definition | `(none)` | aux_ComplexCertifiedIntervalArithmetic | unmatched |  |
| aux_jmsEligibleAt | definition | `Helpers/JmsComparator.lean:jmsEligibleAt (L49)` | aux_jmsEligibleAt | unmatched |  |
| aux_PublishedAceHandle | definition | `Helpers/JmsComparator.lean:PublishedAceHandle (L26)` | aux_PublishedAceHandle | unmatched |  |
| gaussianClass_theta_eq_zero | lemma | `T8_BoundedOutcomeGaussianDegeneracy.lean:CausalSmith.Stat.SaPlmCumulantConverse.gaussianClass_theta_eq_zero (L19)` | gaussianClass_theta_eq_zero | unmatched |  |
| generalizedQuantile_zero | lemma | `T8_BoundedOutcomeGaussianDegeneracy.lean:CausalSmith.Stat.SaPlmCumulantConverse.generalizedQuantile_zero (L176)` | generalizedQuantile_zero | unmatched |  |
| residualMGF_analyticOn_closedBall | lemma | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.residualMGF_analyticOn_closedBall (L235)` | residualMGF_analyticOn_closedBall | unmatched |  |
| residualMGF_eq_treatmentMGF_mul_nuisanceMGF | lemma | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.residualMGF_eq_treatmentMGF_mul_nuisanceMGF (L325)` | residualMGF_eq_treatmentMGF_mul_nuisanceMGF | unmatched |  |
| contamination_weighted_factorization | lemma | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.contamination_weighted_factorization (L413)` | contamination_weighted_factorization | unmatched |  |
| eta_integrable_exp | lemma | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.eta_integrable_exp (L52)` | eta_integrable_exp | unmatched |  |
| learnedResidual_integrable_exp | lemma | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.learnedResidual_integrable_exp (L81)` | learnedResidual_integrable_exp | unmatched |  |
| xi_integrable_exp | lemma | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.xi_integrable_exp (L122)` | xi_integrable_exp | unmatched |  |
| outcomeNoise_weighted_exp_integrable | lemma | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.outcomeNoise_weighted_exp_integrable (L138)` | outcomeNoise_weighted_exp_integrable | unmatched |  |
| outcomeNoise_weighted_exp_eq_zero | lemma | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.outcomeNoise_weighted_exp_eq_zero (L168)` | outcomeNoise_weighted_exp_eq_zero | unmatched |  |
| contamination_weighted_exp_integrable | lemma | `Helpers/Transforms.lean:CausalSmith.Stat.SaPlmCumulantConverse.contamination_weighted_exp_integrable (L360)` | contamination_weighted_exp_integrable | unmatched |  |
| sqrt_div_nat_eq_scale | lemma | `T4_JmsAceAlignment.lean:CausalSmith.Stat.SaPlmCumulantConverse.sqrt_div_nat_eq_scale (L28)` | sqrt_div_nat_eq_scale | unmatched |  |
| tendsto_sqrt_div_over_of_dominates | lemma | `T4_JmsAceAlignment.lean:CausalSmith.Stat.SaPlmCumulantConverse.tendsto_sqrt_div_over_of_dominates (L39)` | tendsto_sqrt_div_over_of_dominates | unmatched |  |
| weightedTransform_differentiableAt_of_ae_bounded | lemma | `T2_ExactContourIdentification.lean:CausalSmith.Stat.SaPlmCumulantConverse.weightedTransform_differentiableAt_of_ae_bounded (L34)` | weightedTransform_differentiableAt_of_ae_bounded | unmatched |  |
| treatmentMGF_iteratedDeriv_eq_zero_of_lt_order | lemma | `Helpers/KnownZeroConditional.lean:CausalSmith.Stat.SaPlmCumulantConverse.treatmentMGF_iteratedDeriv_eq_zero_of_lt_order (L16)` | treatmentMGF_iteratedDeriv_eq_zero_of_lt_order | unmatched |  |
| zeroInstrument_integral_add_eq_zero | lemma | `Helpers/KnownZeroConditional.lean:CausalSmith.Stat.SaPlmCumulantConverse.zeroInstrument_integral_add_eq_zero (L41)` | zeroInstrument_integral_add_eq_zero | unmatched |  |
| zeroInstrument_condExp_learnedResidual_eq_zero | lemma | `Helpers/KnownZeroConditional.lean:CausalSmith.Stat.SaPlmCumulantConverse.zeroInstrument_condExp_learnedResidual_eq_zero (L99)` | zeroInstrument_condExp_learnedResidual_eq_zero | unmatched |  |
| zeroInstrument_learnedResidual_integral_eq | lemma | `Helpers/KnownZeroOrthogonality.lean:CausalSmith.Stat.SaPlmCumulantConverse.zeroInstrument_learnedResidual_integral_eq (L15)` | zeroInstrument_learnedResidual_integral_eq | unmatched |  |
| outcomeNoise_zeroInstrument_integrable_and_integral_eq_zero | lemma | `Helpers/KnownZeroOrthogonality.lean:CausalSmith.Stat.SaPlmCumulantConverse.outcomeNoise_zeroInstrument_integrable_and_integral_eq_zero (L87)` | outcomeNoise_zeroInstrument_integrable_and_integral_eq_zero | unmatched |  |
| contamination_zeroInstrument_integrable_and_integral_eq_zero | lemma | `Helpers/KnownZeroOrthogonality.lean:CausalSmith.Stat.SaPlmCumulantConverse.contamination_zeroInstrument_integrable_and_integral_eq_zero (L198)` | contamination_zeroInstrument_integrable_and_integral_eq_zero | unmatched |  |
| outcome_zeroInstrument_integral_eq_theta_mul | lemma | `Helpers/KnownZeroOrthogonality.lean:CausalSmith.Stat.SaPlmCumulantConverse.outcome_zeroInstrument_integral_eq_theta_mul (L330)` | outcome_zeroInstrument_integral_eq_theta_mul | unmatched |  |
| sqrtInitial_brackets | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.sqrtInitial_brackets (L155)` | sqrtInitial_brackets | unmatched |  |
| sqrtLoStep_brackets | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.sqrtLoStep_brackets (L173)` | sqrtLoStep_brackets | unmatched |  |
| sqrtLoIterate_brackets | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.sqrtLoIterate_brackets (L183)` | sqrtLoIterate_brackets | unmatched |  |
| sqrtLoBisect_le_sqrt | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.sqrtLoBisect_le_sqrt (L196)` | sqrtLoBisect_le_sqrt | unmatched |  |
| sqrt_le_sqrtHiBisect | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.sqrt_le_sqrtHiBisect (L202)` | sqrt_le_sqrtHiBisect | unmatched |  |
| sqLo_nonneg | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.sqLo_nonneg (L212)` | sqLo_nonneg | unmatched |  |
| cxModulus_sound | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.cxModulus_sound (L218)` | cxModulus_sound | unmatched |  |
| sqrtLoStep_width | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.sqrtLoStep_width (L268)` | sqrtLoStep_width | unmatched |  |
| sqrtHiStep_width | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.sqrtHiStep_width (L273)` | sqrtHiStep_width | unmatched |  |
| sqrtStep_iterate_width | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.sqrtStep_iterate_width (L278)` | sqrtStep_iterate_width | unmatched |  |
| sqrt_bisect_width | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.sqrt_bisect_width (L290)` | sqrt_bisect_width | unmatched |  |
| cxDivGuarded_sound | lemma | `Helpers/CertifiedComplex.lean:CausalSmith.Stat.SaPlmCumulantConverse.cxDivGuarded_sound (L297)` | cxDivGuarded_sound | unmatched |  |
| Parameters.withEps2Floor | definition | `(none)` | Parameters.withEps2Floor | unmatched |  |
| Model.reparam | definition | `(none)` | Model.reparam | unmatched |  |
| canonicalDyadic_nested | lemma | `Helpers/SpectralEstimator.lean:CausalSmith.Stat.SaPlmCumulantConverse.canonicalDyadic_nested (L58)` | canonicalDyadic_nested | unmatched |  |
| canonicalDyadic_contains | lemma | `Helpers/SpectralEstimator.lean:CausalSmith.Stat.SaPlmCumulantConverse.canonicalDyadic_contains (L99)` | canonicalDyadic_contains | unmatched |  |
| canonicalDyadic_width | lemma | `Helpers/SpectralEstimator.lean:CausalSmith.Stat.SaPlmCumulantConverse.canonicalDyadic_width (L114)` | canonicalDyadic_width | unmatched |  |
| def:blaschke-correction | definition | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.blaschkeCorrection (L61)` | def:blaschke-correction | unmatched |  |
| lem:blaschke-product-mul-correction | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.blaschkeProduct_mul_blaschkeCorrection (L66)` | lem:blaschke-product-mul-correction | unmatched |  |
| lem:blaschke-correction-analytic-zero-free | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.blaschkeCorrection_analyticOnNhd_and_ne_zero (L91)` | lem:blaschke-correction-analytic-zero-free | unmatched |  |
| lem:extract-zero-free-quotient-closed-ball | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.exists_analytic_zeroFree_factorizedRational_closedBall (L120)` | lem:extract-zero-free-quotient-closed-ball | unmatched |  |
| lem:exists-pointwise-blaschke-factorization | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.exists_pointwise_blaschke_factorization_of_divisor_enumeration (L182)` | lem:exists-pointwise-blaschke-factorization | unmatched |  |
| lem:finite-divisor-multiplicity-enumeration | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.exists_multiplicityEnumeration_of_finite_nonneg_divisor (L215)` | lem:finite-divisor-multiplicity-enumeration | unmatched |  |
| lem:exists-complete-pointwise-blaschke-factorization | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.exists_complete_pointwise_blaschke_factorization (L304)` | lem:exists-complete-pointwise-blaschke-factorization | unmatched |  |
| lem:jensen-log-counting-le | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.jensen_logCounting_divisor_le (L437)` | lem:jensen-log-counting-le | unmatched |  |
| lem:zero-count-eq-sum-orders | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.zeroMultiplicityCount_eq_sum_analyticOrderNatAt (L463)` | lem:zero-count-eq-sum-orders | unmatched |  |
| lem:zero-count-mul-log-ratio-le | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.zeroMultiplicityCount_mul_log_div_le_logCounting (L480)` | lem:zero-count-mul-log-ratio-le | unmatched |  |
| lem:jensen-zero-count-bound | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.jensen_zeroMultiplicityCount_bound (L575)` | lem:jensen-zero-count-bound | unmatched |  |
| lem:blaschke-factorization-lower-bound | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.norm_lower_of_blaschke_factorization (L587)` | lem:blaschke-factorization-lower-bound | unmatched |  |
| blaschkeFactor_eq_zero_iff | lemma | `Helpers/ComplexAnalysisLocal.lean:CausalSmith.Stat.SaPlmCumulantConverse.blaschkeFactor_eq_zero_iff (L35)` | blaschkeFactor_eq_zero_iff | unmatched |  |
| rat_le_positiveCeil | lemma | `Helpers/ContourBank.lean:CausalSmith.Stat.SaPlmCumulantConverse.rat_le_positiveCeil (L79)` | rat_le_positiveCeil | unmatched |  |
| one_le_positiveCeil | lemma | `Helpers/ContourBank.lean:CausalSmith.Stat.SaPlmCumulantConverse.one_le_positiveCeil (L84)` | one_le_positiveCeil | unmatched |  |
| rat_grid_lt_one | lemma | `Helpers/ContourBank.lean:CausalSmith.Stat.SaPlmCumulantConverse.rat_grid_lt_one (L118)` | rat_grid_lt_one | unmatched |  |
| exists_translated_grid_radius_separated | lemma | `Helpers/ContourBank.lean:CausalSmith.Stat.SaPlmCumulantConverse.exists_translated_grid_radius_separated (L131)` | exists_translated_grid_radius_separated | unmatched |  |
| dyadic_product_certificate | lemma | `Helpers/ContourBank.lean:CausalSmith.Stat.SaPlmCumulantConverse.dyadic_product_certificate (L170)` | dyadic_product_certificate | unmatched |  |
| dyadic_two_mul_le_exp_neg | lemma | `Helpers/ContourBank.lean:CausalSmith.Stat.SaPlmCumulantConverse.dyadic_two_mul_le_exp_neg (L202)` | dyadic_two_mul_le_exp_neg | unmatched |  |
| treatmentMGF_entire_normalized_bound | lemma | `Helpers/Cumulant.lean:CausalSmith.Stat.SaPlmCumulantConverse.treatmentMGF_entire_normalized_bound (L23)` | treatmentMGF_entire_normalized_bound | unmatched |  |
| zeroMultiplicityCount_eq_sum_orders_on_finset | lemma | `Helpers/JensenBlaschke.lean:CausalSmith.Stat.SaPlmCumulantConverse.zeroMultiplicityCount_eq_sum_orders_on_finset (L266)` | zeroMultiplicityCount_eq_sum_orders_on_finset | unmatched |  |
| aux_RationalComplexApproximants | definition | `Helpers/CertifiedTranscendental.lean:RationalComplexApproximants (L180)` | aux_RationalComplexApproximants | unmatched |  |
| aux_RationalRealApproximants | definition | `Helpers/CertifiedTranscendental.lean:RationalRealApproximants (L169)` | aux_RationalRealApproximants | unmatched |  |
| aux_CCIAExecutableNames | definition | `(none)` | aux_CCIAExecutableNames | unmatched |  |
| aux_CircleProgramContract | definition | `Helpers/CertifiedTranscendental.lean:CircleProgramContract (L519)` | aux_CircleProgramContract | unmatched |  |
| aux_CircleSchedule | definition | `Helpers/CertifiedTranscendental.lean:CircleSchedule (L384)` | aux_CircleSchedule | unmatched |  |
| aux_CompiledCCIAArtifact | definition | `(none)` | aux_CompiledCCIAArtifact | unmatched |  |
| aux_ComplexExpContract | definition | `Helpers/CertifiedTranscendental.lean:ComplexExpContract (L367)` | aux_ComplexExpContract | unmatched |  |
| aux_ComplexTranscendentalSchedule | definition | `Helpers/CertifiedTranscendental.lean:ComplexTranscendentalSchedule (L213)` | aux_ComplexTranscendentalSchedule | unmatched |  |
| aux_ExecutableName | definition | `(none)` | aux_ExecutableName | unmatched |  |
| aux_ExecutablePositiveRealName | definition | `Helpers/CertifiedTranscendental.lean:ExecutablePositiveRealName (L194)` | aux_ExecutablePositiveRealName | unmatched |  |
| aux_FiniteExtremaContract | definition | `(none)` | aux_FiniteExtremaContract | unmatched |  |
| aux_RealTranscendentalContract | definition | `Helpers/CertifiedTranscendental.lean:RealTranscendentalContract (L353)` | aux_RealTranscendentalContract | unmatched |  |
| aux_RealTranscendentalSchedule | definition | `Helpers/CertifiedTranscendental.lean:RealTranscendentalSchedule (L206)` | aux_RealTranscendentalSchedule | unmatched |  |
| aux_TrapezoidalEnclosureContract | definition | `Helpers/CertifiedTranscendental.lean:TrapezoidalEnclosureContract (L570)` | aux_TrapezoidalEnclosureContract | unmatched |  |
| aux_CircleOutputNestingContract | definition | `(none)` | aux_CircleOutputNestingContract | unmatched |  |
| aux_CompiledEntryPoint | definition | `(none)` | aux_CompiledEntryPoint | unmatched |  |
| aux_ComplexOutputNestingContract | definition | `(none)` | aux_ComplexOutputNestingContract | unmatched |  |
| aux_NodeEvaluationContract | definition | `Helpers/CertifiedTranscendental.lean:NodeEvaluationContract (L664)` | aux_NodeEvaluationContract | unmatched |  |
| aux_NodeEvaluationFuelContract | definition | `Helpers/CertifiedTranscendental.lean:NodeEvaluationFuelContract (L646)` | aux_NodeEvaluationFuelContract | unmatched |  |
| aux_NodeEvaluationSchedule | definition | `Helpers/CertifiedTranscendental.lean:NodeEvaluationSchedule (L607)` | aux_NodeEvaluationSchedule | unmatched |  |
| aux_RationalComplexNodeApproximants | definition | `Helpers/CertifiedTranscendental.lean:RationalComplexNodeApproximants (L590)` | aux_RationalComplexNodeApproximants | unmatched |  |
| aux_RealOutputNestingContract | definition | `(none)` | aux_RealOutputNestingContract | unmatched |  |
| aux_CCIAEntryPoints | definition | `(none)` | aux_CCIAEntryPoints | unmatched |  |
| transformSupError_eq_diskSupNorm | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.transformSupError_eq_diskSupNorm (L23)` | transformSupError_eq_diskSupNorm | unmatched |  |
| empiricalF_sub_eq_centered | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.empiricalF_sub_eq_centered (L499)` | empiricalF_sub_eq_centered | unmatched |  |
| empiricalG_sub_eq_centered | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.empiricalG_sub_eq_centered (L515)` | empiricalG_sub_eq_centered | unmatched |  |
| luxemburg_even_moment_integral_le | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.luxemburg_even_moment_integral_le (L35)` | luxemburg_even_moment_integral_le | unmatched |  |
| eta_even_moment_integral_le | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.eta_even_moment_integral_le (L85)` | eta_even_moment_integral_le | unmatched |  |
| pi_finset_centered_average_sq_lintegral_le | lemma | `Helpers/UniformDiskSeries.lean:CausalSmith.Stat.SaPlmCumulantConverse.pi_finset_centered_average_sq_lintegral_le (L166)` | pi_finset_centered_average_sq_lintegral_le | unmatched |  |
| xi_luxemburg_integral_le | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.xi_luxemburg_integral_le (L99)` | xi_luxemburg_integral_le | unmatched |  |
| learnedResidual_exp_abs_sq_lintegral_le | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.learnedResidual_exp_abs_sq_lintegral_le (L120)` | learnedResidual_exp_abs_sq_lintegral_le | unmatched |  |
| outcome_fourth_moment_le | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.outcome_fourth_moment_le (L177)` | outcome_fourth_moment_le | unmatched |  |
| outcome_exp_abs_sq_lintegral_le | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.outcome_exp_abs_sq_lintegral_le (L281)` | outcome_exp_abs_sq_lintegral_le | unmatched |  |
| weighted_exp_integral_eq_moment_tsum | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.weighted_exp_integral_eq_moment_tsum (L345)` | weighted_exp_integral_eq_moment_tsum | unmatched |  |
| factorial_coefficient_memLp_two | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.factorial_coefficient_memLp_two (L437)` | factorial_coefficient_memLp_two | unmatched |  |
| centered_real_series_diskSupNorm_sq_lintegral_le | lemma | `Helpers/EmpiricalTransform.lean:CausalSmith.Stat.SaPlmCumulantConverse.centered_real_series_diskSupNorm_sq_lintegral_le (L533)` | centered_real_series_diskSupNorm_sq_lintegral_le | unmatched |  |
| centered_factorial_empirical_disk_l2 | lemma | `Helpers/EmpiricalTransformSeries.lean:CausalSmith.Stat.SaPlmCumulantConverse.centered_factorial_empirical_disk_l2 (L19)` | centered_factorial_empirical_disk_l2 | unmatched |  |
| weighted_empirical_sub_eq_centered_factorial_series | lemma | `Helpers/EmpiricalTransformSeries.lean:CausalSmith.Stat.SaPlmCumulantConverse.weighted_empirical_sub_eq_centered_factorial_series (L167)` | weighted_empirical_sub_eq_centered_factorial_series | unmatched |  |
| aux_RepresentedNodeSpecifications | definition | `(none)` | aux_RepresentedNodeSpecifications | unmatched |  |
| aux_ordinaryPilotAdmissible | definition | `(none)` | aux_ordinaryPilotAdmissible | unmatched |  |
| aux_exactOrdinaryAdmissible | definition | `(none)` | aux_exactOrdinaryAdmissible | unmatched |  |
| aux_FixedExperimentRecords | definition | `Helpers/SpectralEstimator.lean:FixedExperimentRecords (L30)` | aux_FixedExperimentRecords | unmatched |  |
| aux_AdaptiveContourEstimator | definition | `Helpers/SpectralEstimator.lean:AdaptiveContourEstimator (L2646)` | aux_AdaptiveContourEstimator | unmatched |  |
| aux_representedExecutionContract | definition | `Helpers/SpectralEstimator.lean:representedExecutionContract (L2661)` | aux_representedExecutionContract | unmatched |  |
| aux_PilotOutcome | definition | `Helpers/SpectralEstimator.lean:PilotOutcome (L2142)` | aux_PilotOutcome | unmatched |  |
| aux_Instrumented | definition | `(none)` | aux_Instrumented | unmatched |  |
| aux_BoundedCircleEvaluator | definition | `Helpers/BoundedCertifiedComplex.lean:BoundedCircleEvaluator (L784)` | aux_BoundedCircleEvaluator | unmatched |  |
| aux_BoundedComplexMap | definition | `Helpers/BoundedCertifiedComplex.lean:BoundedComplexMap (L692)` | aux_BoundedComplexMap | unmatched |  |
| aux_ofReal | definition | `Helpers/BoundedCertifiedComplex.lean:ofReal (L48)` | aux_ofReal | unmatched |  |
| aux_CompiledBoundedSpectralAdapter | definition | `(none)` | aux_CompiledBoundedSpectralAdapter | unmatched |  |
| aux_CompiledRepresentedExecution | definition | `T5_CommonExperimentDichotomy.lean:CompiledRepresentedExecution (L22)` | aux_CompiledRepresentedExecution | unmatched |  |
| clippedRatioFromScores_mse_le | lemma | `(none)` | clippedRatioFromScores_mse_le | unmatched |  |
| gaussianRademacher_second_lintegral_le | lemma | `Helpers/GaussianRademacherBenchmark.lean:CausalSmith.Stat.SaPlmCumulantConverse.gaussianRademacher_second_lintegral_le (L22)` | gaussianRademacher_second_lintegral_le | unmatched |  |
| gaussianRademacher_sine_remainder_centered | lemma | `(none)` | gaussianRademacher_sine_remainder_centered | unmatched |  |
| shiftedInnovationKernel | definition | `Helpers/AffineGaussianKL.lean:CausalSmith.Stat.SaPlmCumulantConverse.shiftedInnovationKernel (L25)` | shiftedInnovationKernel | unmatched |  |
| shiftedInnovationKernel_apply | lemma | `Helpers/AffineGaussianKL.lean:CausalSmith.Stat.SaPlmCumulantConverse.shiftedInnovationKernel_apply (L43)` | shiftedInnovationKernel_apply | unmatched |  |
| affineGaussianLaw_eq_map_shiftedInnovation | lemma | `Helpers/AffineGaussianKL.lean:CausalSmith.Stat.SaPlmCumulantConverse.affineGaussianLaw_eq_map_shiftedInnovation (L61)` | affineGaussianLaw_eq_map_shiftedInnovation | unmatched |  |
| eta_sq_integrable | lemma | `Helpers/AffineGaussianKL.lean:CausalSmith.Stat.SaPlmCumulantConverse.eta_sq_integrable (L203)` | eta_sq_integrable | unmatched |  |
| affineGaussianLaw_kl_le | lemma | `Helpers/AffineGaussianKL.lean:CausalSmith.Stat.SaPlmCumulantConverse.affineGaussianLaw_kl_le (L235)` | affineGaussianLaw_kl_le | unmatched |  |
| affineGaussianModel_iid_kl_le | lemma | `Helpers/AffineGaussianKL.lean:CausalSmith.Stat.SaPlmCumulantConverse.affineGaussianModel_iid_kl_le (L341)` | affineGaussianModel_iid_kl_le | unmatched |  |
| hardSubmodelClip | definition | `Helpers/HardSubmodel.lean:CausalSmith.Stat.SaPlmCumulantConverse.hardSubmodelClip (L25)` | hardSubmodelClip | unmatched |  |
| hardSubmodelClip_sq_sub_le | lemma | `Helpers/HardSubmodel.lean:CausalSmith.Stat.SaPlmCumulantConverse.hardSubmodelClip_sq_sub_le (L28)` | hardSubmodelClip_sq_sub_le | unmatched |  |
| minimaxRiskOn_two_point_lower | lemma | `Helpers/HardSubmodel.lean:CausalSmith.Stat.SaPlmCumulantConverse.minimaxRiskOn_two_point_lower (L44)` | minimaxRiskOn_two_point_lower | unmatched |  |
| sine_remainder_centered_of_mgf_zero | lemma | `Helpers/GaussianRademacherBenchmark.lean:CausalSmith.Stat.SaPlmCumulantConverse.sine_remainder_centered_of_mgf_zero (L76)` | sine_remainder_centered_of_mgf_zero | unmatched |  |
| sine_score_memLp_of_eta_second_lintegral_le | lemma | `Helpers/GaussianRademacherBenchmark.lean:CausalSmith.Stat.SaPlmCumulantConverse.sine_score_memLp_of_eta_second_lintegral_le (L244)` | sine_score_memLp_of_eta_second_lintegral_le | unmatched |  |
| thetaHatAt_eq_clippedRatioFromScores | lemma | `Helpers/GaussianRademacherBenchmark.lean:CausalSmith.Stat.SaPlmCumulantConverse.thetaHatAt_eq_clippedRatioFromScores (L474)` | thetaHatAt_eq_clippedRatioFromScores | unmatched |  |
| learnedResidual_sine_denominator_identity | lemma | `Helpers/SineScore.lean:CausalSmith.Stat.SaPlmCumulantConverse.learnedResidual_sine_denominator_identity (L529)` | learnedResidual_sine_denominator_identity | unmatched |  |
| learnedResidual_sine_denominator_lower | lemma | `Helpers/SineScore.lean:CausalSmith.Stat.SaPlmCumulantConverse.learnedResidual_sine_denominator_lower (L706)` | learnedResidual_sine_denominator_lower | unmatched |  |
| symmetricGaussianMixture_second_lintegral_le | lemma | `T6_SymmetricMixtureReduction.lean:CausalSmith.Stat.SaPlmCumulantConverse.symmetricGaussianMixture_second_lintegral_le (L149)` | symmetricGaussianMixture_second_lintegral_le | unmatched |  |
| aux_CanonicalAdapterEntryPointsCompiled | definition | `Helpers/SelectorSoundness.lean:CanonicalAdapterEntryPointsCompiled (L5569)` | aux_CanonicalAdapterEntryPointsCompiled | unmatched |  |
| aux_EndpointComplete | definition | `Helpers/SelectorSoundness.lean:EndpointComplete (L38)` | aux_EndpointComplete | unmatched |  |
| aux_EvaluationEnclosureSpecification | definition | `Helpers/SelectorSoundness.lean:EvaluationEnclosureSpecification (L5321)` | aux_EvaluationEnclosureSpecification | unmatched |  |
| aux_ExactSpectralSchedule | definition | `Helpers/SelectorSoundness.lean:ExactSpectralSchedule (L52)` | aux_ExactSpectralSchedule | unmatched |  |
| aux_FullCanonicalBuildAndCompilation | definition | `Helpers/SelectorSoundness.lean:FullCanonicalBuildAndCompilation (L5589)` | aux_FullCanonicalBuildAndCompilation | unmatched |  |
| aux_GenericComplexBuildImplemented | definition | `Helpers/SelectorSoundness.lean:GenericComplexBuildImplemented (L5544)` | aux_GenericComplexBuildImplemented | unmatched |  |
| aux_PilotModulusSpecification | definition | `Helpers/SelectorSoundness.lean:PilotModulusSpecification (L5262)` | aux_PilotModulusSpecification | unmatched |  |
| aux_SpectralScheduleWitness | definition | `Helpers/SelectorSoundness.lean:SpectralScheduleWitness (L5109)` | aux_SpectralScheduleWitness | unmatched |  |
| aux_WindingEnclosureSpecification | definition | `Helpers/SelectorSoundness.lean:WindingEnclosureSpecification (L5305)` | aux_WindingEnclosureSpecification | unmatched |  |
| projectedOutputName_certified | lemma | `Helpers/ProjectedOutputCertification.lean:CausalSmith.Stat.SaPlmCumulantConverse.projectedOutputName_certified (L15)` | projectedOutputName_certified | unmatched |  |
| populationNumeratorEnvelope | definition | `Helpers/PopulationNumeratorBound.lean:CausalSmith.Stat.SaPlmCumulantConverse.populationNumeratorEnvelope (L18)` | populationNumeratorEnvelope | unmatched |  |
| outcomeResidualTransform_norm_le_populationNumeratorEnvelope | lemma | `Helpers/PopulationNumeratorBound.lean:CausalSmith.Stat.SaPlmCumulantConverse.outcomeResidualTransform_norm_le_populationNumeratorEnvelope (L27)` | outcomeResidualTransform_norm_le_populationNumeratorEnvelope | unmatched |  |
| aux_PostNormalizationWidthContract | definition | `Helpers/SelectorSoundness.lean:PostNormalizationWidthContract (L3268)` | aux_PostNormalizationWidthContract | unmatched |  |
| aux_WindingDecoderContract | definition | `Helpers/SpectralEstimator.lean:WindingDecoderContract (L2071)` | aux_WindingDecoderContract | unmatched |  |
| aux_CertifiedComplexCompilation | definition | `(none)` | aux_CertifiedComplexCompilation | unmatched |  |
| aux_CertifiedComplexOperations | definition | `Helpers/BoundedCertifiedComplex.lean:CertifiedComplexOperations (L994)` | aux_CertifiedComplexOperations | unmatched |  |
| aux_barG | definition | `Basic.lean:barG (L120)` | aux_barG | unmatched |  |
| aux_barQ | definition | `Basic.lean:barQ (L130)` | aux_barQ | unmatched |  |
| aux_clippedOutcomeCode | definition | `Basic.lean:clippedOutcomeCode (L125)` | aux_clippedOutcomeCode | unmatched |  |
| aux_clippedTreatmentCode | definition | `Basic.lean:clippedTreatmentCode (L115)` | aux_clippedTreatmentCode | unmatched |  |
| aux_OutcomeCodeRadiusLrAt | definition | `Basic.lean:OutcomeCodeRadiusLrAt (L284)` | aux_OutcomeCodeRadiusLrAt | unmatched |  |
| aux_OutcomeCodeRadiusLsAt | definition | `Basic.lean:OutcomeCodeRadiusLsAt (L262)` | aux_OutcomeCodeRadiusLsAt | unmatched |  |
| aux_TreatmentCodeRadiusLrAt | definition | `Basic.lean:TreatmentCodeRadiusLrAt (L273)` | aux_TreatmentCodeRadiusLrAt | unmatched |  |
| aux_TreatmentCodeRadiusLsAt | definition | `Basic.lean:TreatmentCodeRadiusLsAt (L251)` | aux_TreatmentCodeRadiusLsAt | unmatched |  |
| aux_SuppliedRepresentedSpectralInput | definition | `Helpers/SpectralEstimator.lean:SuppliedRepresentedSpectralInput (L2634)` | aux_SuppliedRepresentedSpectralInput | unmatched |  |
| aux_TreatmentCodeRadiusL1At | definition | `Basic.lean:TreatmentCodeRadiusL1At (L301)` | aux_TreatmentCodeRadiusL1At | unmatched |  |
