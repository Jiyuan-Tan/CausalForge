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
| P-1 | definition | `Basic/World.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.ForwardLvLiNGAM (L200)` | P-1 | equivalent |  |
| P-2 | definition | `Basic/World.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.ReverseLvLiNGAM (L217)` | P-2 | equivalent |  |
| P-3 | definition | `Basic/Cumulants.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.truncatedCumulant (L24)` | P-3 | equivalent |  |
| P-4 | definition | `Basic/Cumulants.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.forwardCumulantMap (L33)` | P-4 | equivalent |  |
| P-5 | definition | `Basic/Cumulants.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.reverseCumulantMap (L45)` | P-5 | equivalent |  |
| P-6 | definition | `Helpers/Varieties.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.cumulantImageVariety (L118)` | P-6 | equivalent |  |
| P-7 | definition | `Basic/Cumulants.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.genericParameterLocus (L66)` | P-7 | equivalent |  |
| P-8 | definition | `Basic/Cumulants.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.fiberCorrespondence (L116)` | P-8 | equivalent |  |
| P-9 | definition | `Basic/Swaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.admissibleSourceSwap (L31)` | P-9 | equivalent |  |
| P-10 | definition | `Helpers/Varieties.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.genericFullFiberCompatibilityLocus (L187)` | P-10 | equivalent |  |
| P-11 | definition | `Basic/Cumulants.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.realFeasibleRegion (L134)` | P-11 | equivalent |  |
| P-12 | definition | `Selector.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.informationOrder (L459)` | P-12 | equivalent |  |
| P-13 | definition | `Selector.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.feasibleFiberDecision (L323)` | P-13 | equivalent |  |
| P-14 | definition | `Selector.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.directionSelectorWithDecision (L385)` | P-14 | equivalent |  |
| P-15 | definition | `Selector.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.separatedModelDomain (L427)` | P-15 | equivalent |  |
| P-16 | definition | `Handles.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.workedCompatibilitySystems (L126)` | P-16 | equivalent |  |
| P-17 | definition | `Helpers/Varieties.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.separationHandle (L254)` | P-17 | equivalent |  |
| P-18 | definition | `Handles.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.realTwinConstructionHandle (L164)` | P-18 | equivalent |  |
| P-19 | definition | `Handles.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.realAtlasHandleOutput (L2420)` | P-19 | equivalent |  |
| P-20 | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.effectiveRationalGroebnerCADOutput (L1927)` | P-20 | equivalent |  |
| T-1 | theorem | `TApolar.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.generic_apolar_arrow_recovery (L56)` | T-1 | equivalent |  |
| T-2 | theorem | `TGenericSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.genericArrowRecoveryAndFiberObstruction (L30)` | T-2 | equivalent |  |
| T-3 | theorem | `TExceptionalLocus.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.exceptionalLocusCodimensionOne (L24)` | T-3 | equivalent |  |
| T-4 | theorem | `TInfoOrder.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.improvedRealInformationOrder (L20)` | T-4 | equivalent |  |
| L-1 | lemma | `TAdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.admissibleSwaps_preserve_direction (L43)` | L-1 | equivalent |  |
| A-1 | assumption | `Basic/World.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.IndependentSources (L141)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic/World.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.FiniteCumulants (L146)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic/World.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.SourceNonGaussian (L151)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic/World.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.ForwardAxisModel (L157)` | A-4 | equivalent |  |
| A-5 | assumption | `Basic/World.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.ReverseAxisModel (L164)` | A-5 | equivalent |  |
| A-6 | assumption | `Basic/World.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.ForwardNonCollinear (L171)` | A-6 | equivalent |  |
| A-7 | assumption | `Basic/World.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.ReverseNonCollinear (L176)` | A-7 | equivalent |  |
| A-8 | assumption | `Basic/World.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.ForwardNonzeroEdge (L182)` | A-8 | equivalent |  |
| A-9 | assumption | `Basic/World.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.ReverseNonzeroEdge (L187)` | A-9 | equivalent |  |
| permMiddleEquiv | definition | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.permMiddleEquiv (L18)` | permMiddleEquiv | unmatched |  |
| sum_permMiddle | lemma | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.sum_permMiddle (L34)` | sum_permMiddle | unmatched |  |
| forwardLoading_admissibleSourceSwap | lemma | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.forwardLoading_admissibleSourceSwap (L41)` | forwardLoading_admissibleSourceSwap | unmatched |  |
| reverseLoading_admissibleSourceSwap | lemma | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.reverseLoading_admissibleSourceSwap (L51)` | reverseLoading_admissibleSourceSwap | unmatched |  |
| forwardCumulantMap_admissibleSourceSwap | lemma | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.forwardCumulantMap_admissibleSourceSwap (L61)` | forwardCumulantMap_admissibleSourceSwap | unmatched |  |
| reverseCumulantMap_admissibleSourceSwap | lemma | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.reverseCumulantMap_admissibleSourceSwap (L79)` | reverseCumulantMap_admissibleSourceSwap | unmatched |  |
| permLeadingEquiv | definition | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.permLeadingEquiv (L97)` | permLeadingEquiv | unmatched |  |
| finCons_comp_perm_injective | lemma | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.finCons_comp_perm_injective (L113)` | finCons_comp_perm_injective | unmatched |  |
| realFeasibleRegion_admissibleSourceSwap | lemma | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.realFeasibleRegion_admissibleSourceSwap (L130)` | realFeasibleRegion_admissibleSourceSwap | unmatched |  |
| forwardAxisModel_admissibleSourceSwap | lemma | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.forwardAxisModel_admissibleSourceSwap (L142)` | forwardAxisModel_admissibleSourceSwap | unmatched |  |
| reverseAxisModel_admissibleSourceSwap | lemma | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.reverseAxisModel_admissibleSourceSwap (L159)` | reverseAxisModel_admissibleSourceSwap | unmatched |  |
| arrowTaggedOrbit_right_left_disjoint | lemma | `Helpers/AdmissibleSwaps.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.arrowTaggedOrbit_right_left_disjoint (L176)` | arrowTaggedOrbit_right_left_disjoint | unmatched |  |
| lowerForwardStackEquation | lemma | `Helpers/LowerOrderApolarKernel.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardStackEquation (L31)` | lowerForwardStackEquation | unmatched |  |
| lowerReverseStackEquation | lemma | `Helpers/LowerOrderApolarKernel.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseStackEquation (L57)` | lowerReverseStackEquation | unmatched |  |
| lowerForwardEvaluationsVanish | lemma | `Helpers/LowerOrderApolarKernel.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardEvaluationsVanish (L83)` | lowerForwardEvaluationsVanish | unmatched |  |
| lowerReverseEvaluationsVanish | lemma | `Helpers/LowerOrderApolarKernel.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseEvaluationsVanish (L139)` | lowerReverseEvaluationsVanish | unmatched |  |
| lowerForwardSupportAnnihilatorInKernel | lemma | `Helpers/LowerOrderApolarKernel.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardSupportAnnihilatorInKernel (L199)` | lowerForwardSupportAnnihilatorInKernel | unmatched |  |
| lowerReverseSupportAnnihilatorInKernel | lemma | `Helpers/LowerOrderApolarKernel.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseSupportAnnihilatorInKernel (L220)` | lowerReverseSupportAnnihilatorInKernel | unmatched |  |
| lowerForwardApolarKernelIdentity | lemma | `Helpers/LowerOrderApolarKernel.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardApolarKernelIdentity (L241)` | lowerForwardApolarKernelIdentity | unmatched |  |
| lowerReverseApolarKernelIdentity | lemma | `Helpers/LowerOrderApolarKernel.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseApolarKernelIdentity (L260)` | lowerReverseApolarKernelIdentity | unmatched |  |
| lowerForwardContractionMinorPolynomial | definition | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardContractionMinorPolynomial (L47)` | lowerForwardContractionMinorPolynomial | unmatched |  |
| lowerReverseContractionMinorPolynomial | definition | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseContractionMinorPolynomial (L61)` | lowerReverseContractionMinorPolynomial | unmatched |  |
| lowerForwardRealRankPolynomial | definition | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardRealRankPolynomial (L73)` | lowerForwardRealRankPolynomial | unmatched |  |
| lowerReverseRealRankPolynomial | definition | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseRealRankPolynomial (L77)` | lowerReverseRealRankPolynomial | unmatched |  |
| lowerForwardComplexRankPolynomial | definition | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardComplexRankPolynomial (L81)` | lowerForwardComplexRankPolynomial | unmatched |  |
| lowerReverseComplexRankPolynomial | definition | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseComplexRankPolynomial (L85)` | lowerReverseComplexRankPolynomial | unmatched |  |
| lowerForwardRankPolynomial_map_ofReal | lemma | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardRankPolynomial_map_ofReal (L118)` | lowerForwardRankPolynomial_map_ofReal | unmatched |  |
| lowerReverseRankPolynomial_map_ofReal | lemma | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseRankPolynomial_map_ofReal (L145)` | lowerReverseRankPolynomial_map_ofReal | unmatched |  |
| lowerForwardRankPolynomial_eval_complexify | lemma | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardRankPolynomial_eval_complexify (L172)` | lowerForwardRankPolynomial_eval_complexify | unmatched |  |
| lowerReverseRankPolynomial_eval_complexify | lemma | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseRankPolynomial_eval_complexify (L189)` | lowerReverseRankPolynomial_eval_complexify | unmatched |  |
| lowerForwardWeightedContraction | definition | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardWeightedContraction (L217)` | lowerForwardWeightedContraction | unmatched |  |
| lowerReverseWeightedContraction | definition | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseWeightedContraction (L222)` | lowerReverseWeightedContraction | unmatched |  |
| lowerForwardExplicitRankData | lemma | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardExplicitRankData (L573)` | lowerForwardExplicitRankData | unmatched |  |
| lowerReverseExplicitRankData | lemma | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseExplicitRankData (L603)` | lowerReverseExplicitRankData | unmatched |  |
| lowerForwardRealRankPolynomial_ne_zero | lemma | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardRealRankPolynomial_ne_zero (L633)` | lowerForwardRealRankPolynomial_ne_zero | unmatched |  |
| lowerReverseRealRankPolynomial_ne_zero | lemma | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseRealRankPolynomial_ne_zero (L640)` | lowerReverseRealRankPolynomial_ne_zero | unmatched |  |
| lowerForwardContractionRankWitness | lemma | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardContractionRankWitness (L647)` | lowerForwardContractionRankWitness | unmatched |  |
| lowerReverseContractionRankWitness | lemma | `Helpers/LowerOrderApolarRank.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseContractionRankWitness (L679)` | lowerReverseContractionRankWitness | unmatched |  |
| lowerSlopeProductPolynomial | definition | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerSlopeProductPolynomial (L25)` | lowerSlopeProductPolynomial | unmatched |  |
| lowerForwardRealExceptionalPolynomial | definition | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardRealExceptionalPolynomial (L30)` | lowerForwardRealExceptionalPolynomial | unmatched |  |
| lowerReverseRealExceptionalPolynomial | definition | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseRealExceptionalPolynomial (L35)` | lowerReverseRealExceptionalPolynomial | unmatched |  |
| lowerForwardComplexExceptionalPolynomial | definition | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardComplexExceptionalPolynomial (L40)` | lowerForwardComplexExceptionalPolynomial | unmatched |  |
| lowerReverseComplexExceptionalPolynomial | definition | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseComplexExceptionalPolynomial (L45)` | lowerReverseComplexExceptionalPolynomial | unmatched |  |
| lowerSlopeProductPolynomial_ne_zero | lemma | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerSlopeProductPolynomial_ne_zero (L50)` | lowerSlopeProductPolynomial_ne_zero | unmatched |  |
| lowerForwardRealExceptionalPolynomial_ne_zero | lemma | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardRealExceptionalPolynomial_ne_zero (L57)` | lowerForwardRealExceptionalPolynomial_ne_zero | unmatched |  |
| lowerReverseRealExceptionalPolynomial_ne_zero | lemma | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseRealExceptionalPolynomial_ne_zero (L63)` | lowerReverseRealExceptionalPolynomial_ne_zero | unmatched |  |
| lowerForwardExceptional_eval_complexify | lemma | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardExceptional_eval_complexify (L69)` | lowerForwardExceptional_eval_complexify | unmatched |  |
| lowerReverseExceptional_eval_complexify | lemma | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseExceptional_eval_complexify (L80)` | lowerReverseExceptional_eval_complexify | unmatched |  |
| forwardSlopesInjective_of_realFeasible | lemma | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.forwardSlopesInjective_of_realFeasible (L91)` | forwardSlopesInjective_of_realFeasible | unmatched |  |
| reverseSlopesInjective_of_realFeasible | lemma | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.reverseSlopesInjective_of_realFeasible (L127)` | reverseSlopesInjective_of_realFeasible | unmatched |  |
| forwardCumulantMap_complexify | lemma | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.forwardCumulantMap_complexify (L162)` | forwardCumulantMap_complexify | unmatched |  |
| reverseCumulantMap_complexify | lemma | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.reverseCumulantMap_complexify (L189)` | reverseCumulantMap_complexify | unmatched |  |
| lowerOrderApolarSeparation | lemma | `Helpers/LowerOrderApolarSeparation.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerOrderApolarSeparation (L218)` | lowerOrderApolarSeparation | unmatched |  |
| lowerForwardReverseImpossible | lemma | `Helpers/LowerOrderEmptyFiber.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerForwardReverseImpossible (L16)` | lowerForwardReverseImpossible | unmatched |  |
| lowerReverseForwardImpossible | lemma | `Helpers/LowerOrderEmptyFiber.lean:CausalSmith.ExactID.EID_LingamDirectionMinOrderV1.lowerReverseForwardImpossible (L66)` | lowerReverseForwardImpossible | unmatched |  |
| effectiveRealAtlasOutputOfPresentation | lemma | `(none)` | effectiveRealAtlasOutputOfPresentation | unmatched |  |
| exactAtlasIncidencePresentation | lemma | `(none)` | exactAtlasIncidencePresentation | unmatched |  |
| atlas_restrict_eval_of_bandSupported | lemma | `(none)` | atlas_restrict_eval_of_bandSupported | unmatched |  |
| complexified_mem_genericCompatibilityClosure_iff_generators | lemma | `(none)` | complexified_mem_genericCompatibilityClosure_iff_generators | unmatched |  |
| complexPolynomial_eval_real_imag | lemma | `(none)` | complexPolynomial_eval_real_imag | unmatched |  |
| atlasExceptionalClosureEquations_exact | lemma | `(none)` | atlasExceptionalClosureEquations_exact | unmatched |  |
| atlasAtomicPolynomialConditions_exact | lemma | `(none)` | atlasAtomicPolynomialConditions_exact | unmatched |  |
| atlasLoadingPositive_exact | lemma | `(none)` | atlasLoadingPositive_exact | unmatched |  |
| atlasCumulantMapEquations_exact | lemma | `(none)` | atlasCumulantMapEquations_exact | unmatched |  |
| aux_AdaptedCADConstruction | definition | `Helpers/CADInterface.lean:AdaptedCADConstruction (L620)` | aux_AdaptedCADConstruction | unmatched |  |
| aux_admissibleOrbit | definition | `Helpers/Varieties.lean:admissibleOrbit (L198)` | aux_admissibleOrbit | unmatched |  |
| aux_ApolarFiberDecisionCertificate | definition | `Selector.lean:ApolarFiberDecisionCertificate (L260)` | aux_ApolarFiberDecisionCertificate | unmatched |  |
| aux_AtlasComplexityCertificate | definition | `Handles.lean:AtlasComplexityCertificate (L1860)` | aux_AtlasComplexityCertificate | unmatched |  |
| aux_AtlasMachineExecution | definition | `Handles.lean:AtlasMachineExecution (L1687)` | aux_AtlasMachineExecution | unmatched |  |
| aux_AtlasPolynomialCode | definition | `Handles.lean:AtlasPolynomialCode (L1522)` | aux_AtlasPolynomialCode | unmatched |  |
| aux_AtlasSignOracleProgram | definition | `Handles.lean:AtlasSignOracleProgram (L509)` | aux_AtlasSignOracleProgram | unmatched |  |
| aux_AtlasSignOracleRow | definition | `Handles.lean:AtlasSignOracleRow (L501)` | aux_AtlasSignOracleRow | unmatched |  |
| aux_AtlasTraceStep | definition | `Handles.lean:AtlasTraceStep (L966)` | aux_AtlasTraceStep | unmatched |  |
| aux_atomicCertificate | definition | `Selector.lean:atomicCertificate (L63)` | aux_atomicCertificate | unmatched |  |
| aux_BandSupported | definition | `Selector.lean:BandSupported (L150)` | aux_BandSupported | unmatched |  |
| aux_bandSupportedParams | definition | `Basic/Cumulants.lean:bandSupportedParams (L57)` | aux_bandSupportedParams | unmatched |  |
| aux_CertifiedAtlasConstructionTrace | definition | `Handles.lean:CertifiedAtlasConstructionTrace (L1299)` | aux_CertifiedAtlasConstructionTrace | unmatched |  |
| aux_complexifyParam | definition | `Helpers/Varieties.lean:complexifyParam (L106)` | aux_complexifyParam | unmatched |  |
| aux_ComplexPolynomialCodeFamiliesRealize | definition | `Handles.lean:ComplexPolynomialCodeFamiliesRealize (L1669)` | aux_ComplexPolynomialCodeFamiliesRealize | unmatched |  |
| aux_ComplexPolynomialCodesRealize | definition | `Handles.lean:ComplexPolynomialCodesRealize (L1655)` | aux_ComplexPolynomialCodesRealize | unmatched |  |
| aux_CumVec | definition | `Basic/World.lean:CumVec (L114)` | aux_CumVec | unmatched |  |
| aux_CylindricalCumCells | definition | `Handles.lean:CylindricalCumCells (L371)` | aux_CylindricalCumCells | unmatched |  |
| aux_DefinesAtlasBaseCellFamily | definition | `Handles.lean:DefinesAtlasBaseCellFamily (L1284)` | aux_DefinesAtlasBaseCellFamily | unmatched |  |
| aux_DefinesAtlasIncidenceEquations | definition | `Handles.lean:DefinesAtlasIncidenceEquations (L271)` | aux_DefinesAtlasIncidenceEquations | unmatched |  |
| aux_DefinesComplexGenericIncidenceEquations | definition | `Handles.lean:DefinesComplexGenericIncidenceEquations (L1056)` | aux_DefinesComplexGenericIncidenceEquations | unmatched |  |
| aux_diffApply | definition | `Helpers/ApolarDefs.lean:diffApply (L40)` | aux_diffApply | unmatched |  |
| aux_directionSelectorDecisionInterfaces | definition | `Selector.lean:directionSelectorDecisionInterfaces (L357)` | aux_directionSelectorDecisionInterfaces | unmatched |  |
| aux_dividedPowerBlock | definition | `Helpers/ApolarDefs.lean:dividedPowerBlock (L33)` | aux_dividedPowerBlock | unmatched |  |
| aux_EffectiveRealAtlasOutput | definition | `Handles.lean:EffectiveRealAtlasOutput (L1907)` | aux_EffectiveRealAtlasOutput | unmatched |  |
| aux_EncodedAtlasConstruction | definition | `Handles.lean:EncodedAtlasConstruction (L1602)` | aux_EncodedAtlasConstruction | unmatched |  |
| aux_feasibleFiberDecisionInterfaces | definition | `Selector.lean:feasibleFiberDecisionInterfaces (L287)` | aux_feasibleFiberDecisionInterfaces | unmatched |  |
| aux_feasibleFiberFormula | definition | `Selector.lean:feasibleFiberFormula (L96)` | aux_feasibleFiberFormula | unmatched |  |
| aux_forwardLoading | definition | `Basic/World.lean:forwardLoading (L119)` | aux_forwardLoading | unmatched |  |
| aux_genericCompatibilityClosure | definition | `Helpers/Varieties.lean:genericCompatibilityClosure (L145)` | aux_genericCompatibilityClosure | unmatched |  |
| aux_genericCompatibilityPreimageLeft | definition | `Helpers/Varieties.lean:genericCompatibilityPreimageLeft (L172)` | aux_genericCompatibilityPreimageLeft | unmatched |  |
| aux_genericCompatibilityPreimageRight | definition | `Helpers/Varieties.lean:genericCompatibilityPreimageRight (L167)` | aux_genericCompatibilityPreimageRight | unmatched |  |
| aux_genericFullFiberCompatibility | definition | `Helpers/Varieties.lean:genericFullFiberCompatibility (L127)` | aux_genericFullFiberCompatibility | unmatched |  |
| aux_HasCodimensionIn | definition | `Helpers/ExceptionalCodimension.lean:HasCodimensionIn (L20)` | aux_HasCodimensionIn | unmatched |  |
| aux_HasConstantSignOn | definition | `Helpers/CADInterface.lean:HasConstantSignOn (L476)` | aux_HasConstantSignOn | unmatched |  |
| aux_HasRelativeZariskiDimension | definition | `Helpers/FiberDimensionDefs.lean:HasRelativeZariskiDimension (L24)` | aux_HasRelativeZariskiDimension | unmatched |  |
| aux_IsAdaptedCAD | definition | `Helpers/CADInterface.lean:IsAdaptedCAD (L492)` | aux_IsAdaptedCAD | unmatched |  |
| aux_IsAtlasBandLimited | definition | `Handles.lean:IsAtlasBandLimited (L172)` | aux_IsAtlasBandLimited | unmatched |  |
| aux_IsAtlasIncidenceVariableOrder | definition | `Handles.lean:IsAtlasIncidenceVariableOrder (L303)` | aux_IsAtlasIncidenceVariableOrder | unmatched |  |
| aux_IsBasicSemialgebraic | definition | `Helpers/CADInterface.lean:IsBasicSemialgebraic (L94)` | aux_IsBasicSemialgebraic | unmatched |  |
| aux_IsCADAlgebraicRoot | definition | `Helpers/CADInterface.lean:IsCADAlgebraicRoot (L354)` | aux_IsCADAlgebraicRoot | unmatched |  |
| aux_IsCADLastAlgebraicRoot | definition | `Helpers/CADInterface.lean:IsCADLastAlgebraicRoot (L364)` | aux_IsCADLastAlgebraicRoot | unmatched |  |
| aux_IsCylindricallyArranged | definition | `Helpers/CADInterface.lean:IsCylindricallyArranged (L468)` | aux_IsCylindricallyArranged | unmatched |  |
| aux_IsExactAtlasSignOracle | definition | `Handles.lean:IsExactAtlasSignOracle (L527)` | aux_IsExactAtlasSignOracle | unmatched |  |
| aux_IsExactComplexObservableElimination | definition | `Handles.lean:IsExactComplexObservableElimination (L1093)` | aux_IsExactComplexObservableElimination | unmatched |  |
| aux_IsFiniteSemialgebraicFunction | definition | `Selector.lean:IsFiniteSemialgebraicFunction (L119)` | aux_IsFiniteSemialgebraicFunction | unmatched |  |
| aux_IsForwardDirectLatentSwap | definition | `Helpers/DirectLatentSwaps.lean:IsForwardDirectLatentSwap (L26)` | aux_IsForwardDirectLatentSwap | unmatched |  |
| aux_IsGeneratedCADProjectionFamily | definition | `Handles.lean:IsGeneratedCADProjectionFamily (L322)` | aux_IsGeneratedCADProjectionFamily | unmatched |  |
| aux_IsIrreducibleComponent | definition | `Helpers/ExceptionalCodimension.lean:IsIrreducibleComponent (L14)` | aux_IsIrreducibleComponent | unmatched |  |
| aux_IsIrreducibleZariskiClosed | definition | `Helpers/Varieties.lean:IsIrreducibleZariskiClosed (L99)` | aux_IsIrreducibleZariskiClosed | unmatched |  |
| aux_IsIrreducibleZariskiClosedParamIn | definition | `Helpers/FiberDimensionDefs.lean:IsIrreducibleZariskiClosedParamIn (L15)` | aux_IsIrreducibleZariskiClosedParamIn | unmatched |  |
| aux_IsOrderedFeasibleFiberCADDecision | definition | `Selector.lean:IsOrderedFeasibleFiberCADDecision (L158)` | aux_IsOrderedFeasibleFiberCADDecision | unmatched |  |
| aux_IsPolynomialRankOpen | definition | `Selector.lean:IsPolynomialRankOpen (L177)` | aux_IsPolynomialRankOpen | unmatched |  |
| aux_IsProperRealAlgebraicSubset | definition | `Selector.lean:IsProperRealAlgebraicSubset (L43)` | aux_IsProperRealAlgebraicSubset | unmatched |  |
| aux_IsRecoveredSupport | definition | `Selector.lean:IsRecoveredSupport (L209)` | aux_IsRecoveredSupport | unmatched |  |
| aux_IsReverseDirectLatentSwap | definition | `Helpers/DirectLatentSwaps.lean:IsReverseDirectLatentSwap (L35)` | aux_IsReverseDirectLatentSwap | unmatched |  |
| aux_IsSemialgebraicCumCell | definition | `Handles.lean:IsSemialgebraicCumCell (L347)` | aux_IsSemialgebraicCumCell | unmatched |  |
| aux_IsSemialgebraicSet | definition | `Helpers/CADInterface.lean:IsSemialgebraicSet (L101)` | aux_IsSemialgebraicSet | unmatched |  |
| aux_IsZariskiDenseParamIn | definition | `Helpers/Varieties.lean:IsZariskiDenseParamIn (L90)` | aux_IsZariskiDenseParamIn | unmatched |  |
| aux_IsZariskiOpenParamIn | definition | `Helpers/Varieties.lean:IsZariskiOpenParamIn (L80)` | aux_IsZariskiOpenParamIn | unmatched |  |
| aux_loadingSlopeMultiset | definition | `Helpers/DirectLatentSwaps.lean:loadingSlopeMultiset (L44)` | aux_loadingSlopeMultiset | unmatched |  |
| aux_ParamSpace | definition | `Basic/World.lean:ParamSpace (L107)` | aux_ParamSpace | unmatched |  |
| aux_PolynomialCodeFamiliesRealize | definition | `Handles.lean:PolynomialCodeFamiliesRealize (L1662)` | aux_PolynomialCodeFamiliesRealize | unmatched |  |
| aux_PolynomialCodesRealize | definition | `Handles.lean:PolynomialCodesRealize (L1640)` | aux_PolynomialCodesRealize | unmatched |  |
| aux_PrescribedFiberVariableOrder | definition | `Selector.lean:PrescribedFiberVariableOrder (L133)` | aux_PrescribedFiberVariableOrder | unmatched |  |
| aux_ProjectivelyEquivalent | definition | `Selector.lean:ProjectivelyEquivalent (L191)` | aux_ProjectivelyEquivalent | unmatched |  |
| aux_RealAtlasCADData | definition | `Handles.lean:RealAtlasCADData (L393)` | aux_RealAtlasCADData | unmatched |  |
| aux_realAtlasCADStratification | definition | `Handles.lean:realAtlasCADStratification (L2381)` | aux_realAtlasCADStratification | unmatched |  |
| aux_realAtlasForwardLabel | definition | `Handles.lean:realAtlasForwardLabel (L233)` | aux_realAtlasForwardLabel | unmatched |  |
| aux_realAtlasReverseLabel | definition | `Handles.lean:realAtlasReverseLabel (L237)` | aux_realAtlasReverseLabel | unmatched |  |
| aux_RealClosedFieldCADInterface | definition | `Helpers/CADInterface.lean:RealClosedFieldCADInterface (L645)` | aux_RealClosedFieldCADInterface | unmatched |  |
| aux_reverseLoading | definition | `Basic/World.lean:reverseLoading (L129)` | aux_reverseLoading | unmatched |  |
| aux_separatesAtOrder | definition | `Selector.lean:separatesAtOrder (L442)` | aux_separatesAtOrder | unmatched |  |
| aux_SignInvariantOn | definition | `Handles.lean:SignInvariantOn (L363)` | aux_SignInvariantOn | unmatched |  |
| aux_supportAnnihilator | definition | `Helpers/ApolarDefs.lean:supportAnnihilator (L49)` | aux_supportAnnihilator | unmatched |  |
| aux_TarskiSeidenbergProjection | definition | `Helpers/CADInterface.lean:TarskiSeidenbergProjection (L635)` | aux_TarskiSeidenbergProjection | unmatched |  |
| aux_IsAtlasObservableDecisionFamily | definition | `(none)` | aux_IsAtlasObservableDecisionFamily | unmatched |  |
| aux_IsAtlasObservableDecisionSubfamily | definition | `(none)` | aux_IsAtlasObservableDecisionSubfamily | unmatched |  |
| aux_ObservableSignInvariantOn | definition | `Handles.lean:ObservableSignInvariantOn (L1224)` | aux_ObservableSignInvariantOn | unmatched |  |
| aux_EffectivePolynomialCode | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectivePolynomialCode (L37)` | aux_EffectivePolynomialCode | unmatched |  |
| aux_EffectivePolynomialCodesRealize | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectivePolynomialCodesRealize (L82)` | aux_EffectivePolynomialCodesRealize | unmatched |  |
| aux_EffectiveRationalGroebnerCADInterface | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveRationalGroebnerCADInterface (L1873)` | aux_EffectiveRationalGroebnerCADInterface | unmatched |  |
| aux_EffectiveRationalGroebnerCADPayload | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveRationalGroebnerCADPayload (L1454)` | aux_EffectiveRationalGroebnerCADPayload | unmatched |  |
| aux_EffectiveRationalGroebnerCADResult | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveRationalGroebnerCADResult (L1504)` | aux_EffectiveRationalGroebnerCADResult | unmatched |  |
| aux_IsExactEliminationBasis | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsExactEliminationBasis (L744)` | aux_IsExactEliminationBasis | unmatched |  |
| aux_IsExactGroebnerBasis | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsExactGroebnerBasis (L726)` | aux_IsExactGroebnerBasis | unmatched |  |
| aux_IsExactIdealIntersectionBasis | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsExactIdealIntersectionBasis (L752)` | aux_IsExactIdealIntersectionBasis | unmatched |  |
| aux_IsExactSaturationBasis | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsExactSaturationBasis (L759)` | aux_IsExactSaturationBasis | unmatched |  |
| aux_SameOnEffectiveCoordinates | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:SameOnEffectiveCoordinates (L1490)` | aux_SameOnEffectiveCoordinates | unmatched |  |
| aux_UniversalEffectiveRationalGroebnerCADBound | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:UniversalEffectiveRationalGroebnerCADBound (L1866)` | aux_UniversalEffectiveRationalGroebnerCADBound | unmatched |  |
| aux_UsesOnlyEffectiveVariables | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:UsesOnlyEffectiveVariables (L695)` | aux_UsesOnlyEffectiveVariables | unmatched |  |
| aux_EffectiveAlgebraTraceStep | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveAlgebraTraceStep (L1125)` | aux_EffectiveAlgebraTraceStep | unmatched |  |
| aux_IsEffectiveEliminationVariableOrder | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsEffectiveEliminationVariableOrder (L709)` | aux_IsEffectiveEliminationVariableOrder | unmatched |  |
| aux_IsEffectiveLeadingExponent | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsEffectiveLeadingExponent (L717)` | aux_IsEffectiveLeadingExponent | unmatched |  |
| aux_EffectiveCADRetentionRow | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveCADRetentionRow (L972)` | aux_EffectiveCADRetentionRow | unmatched |  |
| aux_EffectiveCADSignQuery | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveCADSignQuery (L941)` | aux_EffectiveCADSignQuery | unmatched |  |
| aux_EffectiveCADTruthRow | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveCADTruthRow (L960)` | aux_EffectiveCADTruthRow | unmatched |  |
| aux_EffectiveCertifiedCADCell | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveCertifiedCADCell (L873)` | aux_EffectiveCertifiedCADCell | unmatched |  |
| aux_EffectiveGroebnerAlgorithmOver | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveGroebnerAlgorithmOver (L438)` | aux_EffectiveGroebnerAlgorithmOver | unmatched |  |
| aux_EffectiveGroebnerPayloadOver | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveGroebnerPayloadOver (L324)` | aux_EffectiveGroebnerPayloadOver | unmatched |  |
| aux_EffectiveGroebnerResultOver | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveGroebnerResultOver (L345)` | aux_EffectiveGroebnerResultOver | unmatched |  |
| aux_EffectivePolynomialCodeOver | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectivePolynomialCodeOver (L104)` | aux_EffectivePolynomialCodeOver | unmatched |  |
| aux_EffectivePolynomialCodesRealizeOver | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectivePolynomialCodesRealizeOver (L117)` | aux_EffectivePolynomialCodesRealizeOver | unmatched |  |
| aux_IsEffectiveEliminationMonomialOrder | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsEffectiveEliminationMonomialOrder (L148)` | aux_IsEffectiveEliminationMonomialOrder | unmatched |  |
| aux_IsExactEliminationBasisOver | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsExactEliminationBasisOver (L187)` | aux_IsExactEliminationBasisOver | unmatched |  |
| aux_IsExactGroebnerBasisForMonomialOrder | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsExactGroebnerBasisForMonomialOrder (L168)` | aux_IsExactGroebnerBasisForMonomialOrder | unmatched |  |
| aux_IsExactIdealIntersectionBasisOver | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsExactIdealIntersectionBasisOver (L196)` | aux_IsExactIdealIntersectionBasisOver | unmatched |  |
| aux_IsExactSaturationBasisOver | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsExactSaturationBasisOver (L204)` | aux_IsExactSaturationBasisOver | unmatched |  |
| aux_UsesOnlyEffectiveVariablesOver | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:UsesOnlyEffectiveVariablesOver (L141)` | aux_UsesOnlyEffectiveVariablesOver | unmatched |  |
| aux_EffectiveMonomialOrderCode | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveMonomialOrderCode (L126)` | aux_EffectiveMonomialOrderCode | unmatched |  |
| aux_EveryMonomialOrderEffectivelyPresentable | definition | `(none)` | aux_EveryMonomialOrderEffectivelyPresentable | unmatched |  |
| aux_EffectivePolynomialMachineState | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectivePolynomialMachineState (L1213)` | aux_EffectivePolynomialMachineState | unmatched |  |
| aux_AtlasCitedEffectiveExecution | definition | `Handles.lean:AtlasCitedEffectiveExecution (L618)` | aux_AtlasCitedEffectiveExecution | unmatched |  |
| aux_EffectiveDependentRationalEliminationPipeline | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveDependentRationalEliminationPipeline (L534)` | aux_EffectiveDependentRationalEliminationPipeline | unmatched |  |
| aux_EffectiveGroebnerCompletedJobOver | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveGroebnerCompletedJobOver (L500)` | aux_EffectiveGroebnerCompletedJobOver | unmatched |  |
| aux_EffectiveGroebnerJobOver | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveGroebnerJobOver (L460)` | aux_EffectiveGroebnerJobOver | unmatched |  |
| aux_EffectiveGroebnerMachineState | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveGroebnerMachineState (L227)` | aux_EffectiveGroebnerMachineState | unmatched |  |
| aux_EffectiveGroebnerTraceStep | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveGroebnerTraceStep (L268)` | aux_EffectiveGroebnerTraceStep | unmatched |  |
| aux_EffectiveRationalCADCompletedJob | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveRationalCADCompletedJob (L1788)` | aux_EffectiveRationalCADCompletedJob | unmatched |  |
| aux_EffectiveRationalCADJob | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveRationalCADJob (L1739)` | aux_EffectiveRationalCADJob | unmatched |  |
| aux_IsAtlasFiberVariableOrder | definition | `Handles.lean:IsAtlasFiberVariableOrder (L481)` | aux_IsAtlasFiberVariableOrder | unmatched |  |
| aux_IsExactComplexProjectionClosure | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsExactComplexProjectionClosure (L687)` | aux_IsExactComplexProjectionClosure | unmatched |  |
| aux_IsInjectiveOnRationalFamilyVariables | definition | `Handles.lean:IsInjectiveOnRationalFamilyVariables (L846)` | aux_IsInjectiveOnRationalFamilyVariables | unmatched |  |
| aux_RationalComplexEliminationClosureTheorem | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:RationalComplexEliminationClosureTheorem (L1805)` | aux_RationalComplexEliminationClosureTheorem | unmatched |  |
| aux_StandardFiniteBlockEliminationOrderInterface | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:StandardFiniteBlockEliminationOrderInterface (L158)` | aux_StandardFiniteBlockEliminationOrderInterface | unmatched |  |
| aux_UniversalEffectiveCombinedGroebnerCADBound | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:UniversalEffectiveCombinedGroebnerCADBound (L1820)` | aux_UniversalEffectiveCombinedGroebnerCADBound | unmatched |  |
| aux_IsCADGroundCoefficient | definition | `Helpers/CADInterface.lean:IsCADGroundCoefficient (L134)` | aux_IsCADGroundCoefficient | unmatched |  |
| aux_IsCADNonzeroGroundCoefficient | definition | `Helpers/CADInterface.lean:IsCADNonzeroGroundCoefficient (L138)` | aux_IsCADNonzeroGroundCoefficient | unmatched |  |
| aux_EffectiveCADBasicSignCondition | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveCADBasicSignCondition (L999)` | aux_EffectiveCADBasicSignCondition | unmatched |  |
| aux_EffectiveCADPrefixProjectionCertificate | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveCADPrefixProjectionCertificate (L1037)` | aux_EffectiveCADPrefixProjectionCertificate | unmatched |  |
| aux_EffectiveDependentRationalCADJob | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:EffectiveDependentRationalCADJob (L1765)` | aux_EffectiveDependentRationalCADJob | unmatched |  |
| atlasCitedExecutionOfDependentPipeline | definition | `(none)` | atlasCitedExecutionOfDependentPipeline | unmatched |  |
| atlasCitedExecutionOfDependentPipeline_symbolicOperationCount | lemma | `(none)` | atlasCitedExecutionOfDependentPipeline_symbolicOperationCount | unmatched |  |
| atlasCitedEffectiveExecution_exists | lemma | `(none)` | atlasCitedEffectiveExecution_exists | unmatched |  |
| atlasClause32ForwardEquations | definition | `(none)` | atlasClause32ForwardEquations | unmatched |  |
| atlasClause32SecondInput | definition | `(none)` | atlasClause32SecondInput | unmatched |  |
| atlasClause32_stage_family_eq | lemma | `(none)` | atlasClause32_stage_family_eq | unmatched |  |
| atlasClause32_recursively_lifted | lemma | `(none)` | atlasClause32_recursively_lifted | unmatched |  |
| aux_CADSpecializationNonzeroAt | definition | `Helpers/CADInterface.lean:CADSpecializationNonzeroAt (L312)` | aux_CADSpecializationNonzeroAt | unmatched |  |
| aux_IsJointlyPresentableSharedCoordinateRelation | definition | `Helpers/EffectiveRationalGroebnerCADInterface.lean:IsJointlyPresentableSharedCoordinateRelation (L522)` | aux_IsJointlyPresentableSharedCoordinateRelation | unmatched |  |
| atlasClause32_shared_coordinate_relation_exact_on_retained | lemma | `(none)` | atlasClause32_shared_coordinate_relation_exact_on_retained | unmatched |  |
