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
| P-1 | definition | `Basic.lean:BudgetedSchedule (L0)` | P-1 | equivalent |  |
| P-2 | definition | `Basic.lean:RolloutLawClass (L0)` | P-2 | equivalent |  |
| P-3 | definition | `Basic.lean:UnbiasedWeights (L0)` | P-3 | equivalent |  |
| P-4 | definition | `Basic.lean:chebyshevSchedule (L0)` | P-4 | equivalent |  |
| P-5 | definition | `Basic.lean:minimaxAmplification (L0)` | P-5 | equivalent |  |
| P-6 | definition | `Basic.lean:exactNestedRisk (L0)` | P-6 | equivalent |  |
| P-7 | definition | `Helpers/ExactRisk.lean:exactNestedMinimaxQuestion (L0)` | P-7 | equivalent |  |
| T-1 | theorem | `T_tv_envelope_design.lean:tv_envelope_design (L0)` | T-1 | equivalent |  |
| T-2 | theorem | `T_chebyshev_minimax.lean:chebyshev_minimax (L0)` | T-2 | equivalent |  |
| L-1 | lemma | `Basic.lean:rollout_polynomial_identity (L0)` | L-1 | equivalent |  |
| L-2 | lemma | `Helpers/EqualSpacing.lean:equal_spacing_benchmark (L0)` | L-2 | equivalent |  |
| L-3 | lemma | `Helpers/NoExtrapolation.lean:no_extrapolation_boundary (L0)` | L-3 | equivalent |  |
| L-4 | lemma | `Helpers/Amplification.lean:amplification_dual_norm (L0)` | L-4 | equivalent |  |
| L-5 | lemma | `Helpers/ChebyshevExtremal.lean:chebyshev_exterior_extremal (L0)` | L-5 | equivalent |  |
| L-6 | lemma | `Helpers/EhlichZeller.lean:oversampled_chebyshev_lobatto_norming (L0)` | L-6 | equivalent |  |
| L-7 | lemma | `Helpers/ChebyshevEndpoint.lean:continuous_chebyshev_endpoint_bound (L0)` | L-7 | equivalent |  |
| L-8 | lemma | `Helpers/ChebyshevSchedule.lean:chebyshev_schedule_admissible (L0)` | L-8 | equivalent |  |
| L-9 | lemma | `Helpers/Amplification.lean:unbiased_weight_set_nonempty (L0)` | L-9 | equivalent |  |
| L-10 | lemma | `Helpers/Variance.lean:variance_envelope_sharpness (L0)` | L-10 | equivalent |  |
| L-11 | lemma | `Helpers/Variance.lean:exact_risk_envelope_upper (L0)` | L-11 | equivalent |  |
| L-12 | lemma | `Helpers/ExactRisk.lean:exact_chebyshev_rate_feasible (L0)` | L-12 | equivalent |  |
| A-1 | assumption | `Basic.lean:StaticRolloutConsistency (L0)` | A-1 | equivalent |  |
| A-2 | assumption | `Basic.lean:BetaOrderPolynomial (L0)` | A-2 | equivalent |  |
| A-3 | assumption | `Basic.lean:RoundMeanVarianceEnvelope (L0)` | A-3 | equivalent |  |
| A-4 | assumption | `Basic.lean:LowBudgetCap (L0)` | A-4 | equivalent |  |
| ass:sigma0sq-nonnegative-exact-risk-envelope-upper | assumption | `(none)` | ass:sigma0sq-nonnegative-exact-risk-envelope-upper | unmatched |  |
| ass:sigma0sq-nonnegative-exact-chebyshev-rate-feasible | assumption | `(none)` | ass:sigma0sq-nonnegative-exact-chebyshev-rate-feasible | unmatched |  |
| lagrange_endpoint_weights_unbiased | lemma | `Helpers/Amplification.lean:lagrange_endpoint_weights_unbiased (L0)` | lagrange_endpoint_weights_unbiased | unmatched |  |
| sInf_le_mul_sInf_of_forall_exists_le | lemma | `Helpers/Variance.lean:sInf_le_mul_sInf_of_forall_exists_le (L0)` | sInf_le_mul_sInf_of_forall_exists_le | unmatched |  |
| neg_one_pow_mul_le_of_abs_le_one | lemma | `Helpers/ChebyshevExtremal.lean:neg_one_pow_mul_le_of_abs_le_one (L0)` | neg_one_pow_mul_le_of_abs_le_one | unmatched |  |
| chebyshev_exterior_lagrange_coeff_nonneg | lemma | `Helpers/ChebyshevExtremal.lean:chebyshev_exterior_lagrange_coeff_nonneg (L0)` | chebyshev_exterior_lagrange_coeff_nonneg | unmatched |  |
| chebyshev_eval_eq_lambda_average | lemma | `Helpers/ChebyshevEndpoint.lean:chebyshev_eval_eq_lambda_average (L0)` | chebyshev_eval_eq_lambda_average | unmatched |  |
| endpoint_lambda_mono | lemma | `Helpers/ChebyshevEndpoint.lean:endpoint_lambda_mono (L0)` | endpoint_lambda_mono | unmatched |  |
| chebyshev_lambda_average_add_one_le | lemma | `Helpers/ChebyshevEndpoint.lean:chebyshev_lambda_average_add_one_le (L0)` | chebyshev_lambda_average_add_one_le | unmatched |  |
| chebyshev_lambda_average_sub_one_ge | lemma | `Helpers/ChebyshevEndpoint.lean:chebyshev_lambda_average_sub_one_ge (L0)` | chebyshev_lambda_average_sub_one_ge | unmatched |  |
| equalSchedule_injective | lemma | `Helpers/EqualSpacing.lean:equalSchedule_injective (L0)` | equalSchedule_injective | unmatched |  |
| equalSchedule_lagrange_basis_eval_one_le | lemma | `Helpers/EqualSpacing.lean:equalSchedule_lagrange_basis_eval_one_le (L0)` | equalSchedule_lagrange_basis_eval_one_le | unmatched |  |
| prod_Iic_erase_abs_sub_eq_factorial | lemma | `Helpers/EqualSpacingArithmetic.lean:prod_Iic_erase_abs_sub_eq_factorial (L0)` | prod_Iic_erase_abs_sub_eq_factorial | unmatched |  |
| two_pow_le_two_mul_factorial | lemma | `Helpers/EqualSpacingArithmetic.lean:two_pow_le_two_mul_factorial (L0)` | two_pow_le_two_mul_factorial | unmatched |  |
| factorial_reciprocal_sum_le_two | lemma | `Helpers/EqualSpacingArithmetic.lean:factorial_reciprocal_sum_le_two (L0)` | factorial_reciprocal_sum_le_two | unmatched |  |
| ehlichZellerMesh | lemma | `Helpers/EhlichZeller.lean:ehlichZellerMesh (L0)` | ehlichZellerMesh | unmatched |  |
| chebyshev_lambda_eq_rho_div_q | lemma | `Helpers/MinimaxAssembly.lean:chebyshev_lambda_eq_rho_div_q (L0)` | chebyshev_lambda_eq_rho_div_q | unmatched |  |
| amplification_nonneg | lemma | `Helpers/MinimaxAssembly.lean:amplification_nonneg (L0)` | amplification_nonneg | unmatched |  |
| minimaxAmplification_le_of_budgeted | lemma | `Helpers/MinimaxAssembly.lean:minimaxAmplification_le_of_budgeted (L0)` | minimaxAmplification_le_of_budgeted | unmatched |  |
| minimaxAmplification_lower_of_forall | lemma | `Helpers/MinimaxAssembly.lean:minimaxAmplification_lower_of_forall (L0)` | minimaxAmplification_lower_of_forall | unmatched |  |
| budgetedSchedule_le_endpoint | lemma | `Helpers/MinimaxAssembly.lean:budgetedSchedule_le_endpoint (L0)` | budgetedSchedule_le_endpoint | unmatched |  |
| affine_mem_Icc_neg_one_one | lemma | `Helpers/MinimaxAssembly.lean:affine_mem_Icc_neg_one_one (L0)` | affine_mem_Icc_neg_one_one | unmatched |  |
| chebyshev_affine_natDegree_le | lemma | `Helpers/MinimaxAssembly.lean:chebyshev_affine_natDegree_le (L0)` | chebyshev_affine_natDegree_le | unmatched |  |
| chebyshev_amplification_lower | lemma | `Helpers/MinimaxAssembly.lean:chebyshev_amplification_lower (L0)` | chebyshev_amplification_lower | unmatched |  |
| lobatto_affine_comp_natDegree_le | lemma | `Helpers/MinimaxUpper.lean:lobatto_affine_comp_natDegree_le (L0)` | lobatto_affine_comp_natDegree_le | unmatched |  |
| chebyshev_amplification_upper | lemma | `Helpers/MinimaxUpper.lean:chebyshev_amplification_upper (L0)` | chebyshev_amplification_upper | unmatched |  |
| one_le_rhoCh | lemma | `T_chebyshev_minimax.lean:one_le_rhoCh (L0)` | one_le_rhoCh | unmatched |  |
