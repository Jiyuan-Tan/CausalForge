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
| P-1 | definition | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.TransportedIVClass (L459)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.FiniteCellClass (L2079)` | P-2 | equivalent |  |
| P-3 | definition | `Frontier.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.OracleHonest (L357)` | P-3 | equivalent |  |
| P-4 | definition | `Frontier.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.frontierRisk (L439)` | P-4 | equivalent |  |
| P-5 | definition | `Frontier.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.oracleValue (L484)` | P-5 | equivalent |  |
| P-6 | definition | `Frontier.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.finiteCellOracleValue (L498)` | P-6 | equivalent |  |
| P-7 | definition | `Frontier.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.FiniteCellHonest (L367)` | P-7 | equivalent |  |
| P-8 | definition | `Helpers/ScoreInversion.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.inversionHandle (L42)` | P-8 | equivalent |  |
| P-9 | definition | `Helpers/Witness.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.geometryHandle (L5809)` | P-9 | equivalent |  |
| P-10 | definition | `Helpers/Witness.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.leastFavorableWitness (L5750)` | P-10 | equivalent |  |
| P-11 | definition | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.AdmissibleGeometry (L2123)` | P-11 | equivalent |  |
| P-12 | definition | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.fixedGeometrySlice (L2146)` | P-12 | equivalent |  |
| P-13 | definition | `Frontier.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.FixedGeometryOracleHonest (L384)` | P-13 | equivalent |  |
| P-14 | definition | `Frontier.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.fixedGeometryValue (L513)` | P-14 | equivalent |  |
| P-15 | definition | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.RegularFiniteCellClass (L2158)` | P-15 | equivalent |  |
| P-16 | definition | `Frontier.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.RegularCellHonest (L397)` | P-16 | equivalent |  |
| T-1 | theorem | `T_CompactCausalRange.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.compact_causal_range (L312)` | T-1 | equivalent |  |
| T-2 | theorem | `T_OracleConverse.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.oracle_converse (L20)` | T-2 | equivalent |  |
| T-3 | theorem | `T_NoShiftReduction.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.no_shift_reduction (L23)` | T-3 | equivalent |  |
| T-4 | theorem | `T_OracleScoreInversionAttainment.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.oracle_score_inversion_attainment (L20)` | T-4 | equivalent |  |
| T-5 | theorem | `T_FiniteCellUnknownWeightAttainment.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.finite_cell_unknown_weight_attainment (L22)` | T-5 | equivalent |  |
| T-6 | theorem | `T_FixedGeometryFrontier.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.fixed_geometry_frontier (L24)` | T-6 | equivalent |  |
| T-7 | theorem | `T_RegularCellUnknownWeightAttainment.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.regular_cell_unknown_weight_attainment (L24)` | T-7 | equivalent |  |
| A-1 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.FullDataSupport (L264)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.PopulationPresence (L274)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.TwoSampleArray (L281)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.InstrumentOverlap (L291)` | A-4 | equivalent |  |
| A-5 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.SourceAssignmentConsistency (L304)` | A-5 | equivalent |  |
| A-6 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.IVRandomization (L346)` | A-6 | equivalent |  |
| A-7 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.IVExclusion (L356)` | A-7 | equivalent |  |
| A-8 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.IVMonotonicity (L363)` | A-8 | equivalent |  |
| A-9 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.OutcomeTransport (L371)` | A-9 | equivalent |  |
| A-10 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.ReceiptTransport (L383)` | A-10 | equivalent |  |
| A-11 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.TargetComplierPositivity (L394)` | A-11 | equivalent |  |
| A-12 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.TransportDomination (L400)` | A-12 | equivalent |  |
| A-13 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.WeightEnvelope (L405)` | A-13 | equivalent |  |
| A-14 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.WeightSecondMoment (L413)` | A-14 | equivalent |  |
| A-15 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.DegradingArray (L419)` | A-15 | equivalent |  |
| A-16 | assumption | `Basic.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.FiniteCellSource (L441)` | A-16 | equivalent |  |
| aux_feasibleFiniteCellRisk | definition | `Frontier.lean:feasibleFiniteCellRisk (L467)` | aux_feasibleFiniteCellRisk | unmatched |  |
| aux_finiteCellInversion | definition | `Helpers/CellEstimators.lean:finiteCellInversion (L61)` | aux_finiteCellInversion | unmatched |  |
| aux_FiniteCellProcedure | definition | `Frontier.lean:FiniteCellProcedure (L132)` | aux_FiniteCellProcedure | unmatched |  |
| aux_Geometry | definition | `Basic.lean:Geometry (L2109)` | aux_Geometry | unmatched |  |
| aux_OracleProcedure | definition | `Frontier.lean:OracleProcedure (L112)` | aux_OracleProcedure | unmatched |  |
| aux_regularCellInversion | definition | `Helpers/CellEstimators.lean:regularCellInversion (L50)` | aux_regularCellInversion | unmatched |  |
| aux_RegularCellProcedure | definition | `Frontier.lean:RegularCellProcedure (L162)` | aux_RegularCellProcedure | unmatched |  |
| aux_regularCellRisk | definition | `Frontier.lean:regularCellRisk (L458)` | aux_regularCellRisk | unmatched |  |
| aux_TransportedArray | definition | `Basic.lean:TransportedArray (L66)` | aux_TransportedArray | unmatched |  |
| aux_FiniteCellOracleHonest | definition | `Frontier.lean:FiniteCellOracleHonest (L378)` | aux_FiniteCellOracleHonest | unmatched |  |
| aux_FiniteCellOracleProcedure | definition | `Frontier.lean:FiniteCellOracleProcedure (L146)` | aux_FiniteCellOracleProcedure | unmatched |  |
| inverse_strength_to_frontier | lemma | `Helpers/RateAlgebra.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.inverse_strength_to_frontier (L12)` | inverse_strength_to_frontier | unmatched |  |
| aux_sourceCellMass | definition | `Frontier.lean:sourceCellMass (L278)` | aux_sourceCellMass | unmatched |  |
| aux_twoSampleLaw | definition | `Basic.lean:twoSampleLaw (L253)` | aux_twoSampleLaw | unmatched |  |
| compact_assignment_contrast_integrable | assumption | `(none)` | compact_assignment_contrast_integrable | unmatched |  |
| compact_receipt_contrast_integrable | assumption | `(none)` | compact_receipt_contrast_integrable | unmatched |  |
| measurable_observeSource | lemma | `T_CompactCausalRange.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.measurable_observeSource (L14)` | measurable_observeSource | unmatched |  |
| sourceXLaw_eq_populationXLaw_source | lemma | `T_CompactCausalRange.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.sourceXLaw_eq_populationXLaw_source (L31)` | sourceXLaw_eq_populationXLaw_source | unmatched |  |
| measure_eq_withDensity_of_toReal_setIntegral | lemma | `T_CompactCausalRange.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.measure_eq_withDensity_of_toReal_setIntegral (L46)` | measure_eq_withDensity_of_toReal_setIntegral | unmatched |  |
| ivRandomization_slice_eq_withDensity | lemma | `T_CompactCausalRange.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.ivRandomization_slice_eq_withDensity (L60)` | ivRandomization_slice_eq_withDensity | unmatched |  |
| ivRandomization_ipw_contrast | lemma | `T_CompactCausalRange.lean:CausalSmith.Stat.TransportedLateStrengthFrontier.ivRandomization_ipw_contrast (L131)` | ivRandomization_ipw_contrast | unmatched |  |
| aux_TransportedFunctionalRanges | definition | `Basic.lean:TransportedFunctionalRanges (L1377)` | aux_TransportedFunctionalRanges | unmatched |  |
| aux_SourceObservation | definition | `Basic.lean:SourceObservation (L316)` | aux_SourceObservation | unmatched |  |
| aux_ReceiptContrastRepresentation | definition | `Basic.lean:ReceiptContrastRepresentation (L162)` | aux_ReceiptContrastRepresentation | unmatched |  |
| aux_RegularCellDesign | definition | `Frontier.lean:RegularCellDesign (L88)` | aux_RegularCellDesign | unmatched |  |
| aux_RegularCellInput | definition | `Frontier.lean:RegularCellInput (L95)` | aux_RegularCellInput | unmatched |  |
| aux_regularCellInputOfClass | definition | `Frontier.lean:regularCellInputOfClass (L300)` | aux_regularCellInputOfClass | unmatched |  |
