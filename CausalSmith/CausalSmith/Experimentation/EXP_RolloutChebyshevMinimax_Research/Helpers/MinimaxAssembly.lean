/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Chebyshev minimax theorem assembly helpers
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Amplification
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ChebyshevEndpoint
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.EhlichZeller
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Schedule

open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: chebyshev_lambda_eq_rho_div_q
lemma chebyshev_lambda_eq_rho_div_q {q : ℝ} (hq : 0 < q) (hq_lt_one : q < 1) :
    (2 / q - 1) + Real.sqrt ((2 / q - 1) ^ 2 - 1) =
      (1 + Real.sqrt (1 - q)) ^ 2 / q := by
  have hsqrt_nonneg : 0 ≤ 2 * Real.sqrt (1 - q) / q := by
    exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (le_of_lt hq)
  have hrad_nonneg : 0 ≤ (2 / q - 1) ^ 2 - 1 := by
    field_simp [ne_of_gt hq]
    nlinarith [hq, hq_lt_one]
  have hsqrt : Real.sqrt ((2 / q - 1) ^ 2 - 1) = 2 * Real.sqrt (1 - q) / q := by
    rw [Real.sqrt_eq_iff_eq_sq hrad_nonneg hsqrt_nonneg]
    field_simp [ne_of_gt hq]
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
    ring
  rw [hsqrt]
  field_simp [ne_of_gt hq]
  ring_nf
  rw [Real.sq_sqrt (by linarith)]
  ring

-- @node: amplification_nonneg
lemma amplification_nonneg (beta k : ℕ) (p : Fin (k + 1) → ℝ) :
    0 ≤ amplification beta k p := by
  unfold amplification
  apply Real.sInf_nonneg
  rintro v ⟨w, _hw, rfl⟩
  exact sq_nonneg _

-- @node: minimaxAmplification_le_of_budgeted
lemma minimaxAmplification_le_of_budgeted (beta k : ℕ) (q : ℝ)
    (p : Fin (k + 1) → ℝ) (hp : BudgetedSchedule k q p) :
    minimaxAmplification beta k q ≤ amplification beta k p := by
  unfold minimaxAmplification
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨p', _hp', rfl⟩
    exact amplification_nonneg beta k p'
  · exact ⟨p, hp, rfl⟩

-- @node: minimaxAmplification_lower_of_forall
lemma minimaxAmplification_lower_of_forall (beta k : ℕ) (q B : ℝ)
    (hne : ∃ p : Fin (k + 1) → ℝ, BudgetedSchedule k q p)
    (hlower : ∀ p : Fin (k + 1) → ℝ, BudgetedSchedule k q p →
      B ≤ amplification beta k p) :
    B ≤ minimaxAmplification beta k q := by
  unfold minimaxAmplification
  refine le_csInf ?hneSet ?_
  · rcases hne with ⟨p, hp⟩
    exact ⟨amplification beta k p, p, hp, rfl⟩
  · rintro v ⟨p, hp, rfl⟩
    exact hlower p hp

-- @node: budgetedSchedule_le_endpoint
lemma budgetedSchedule_le_endpoint {k : ℕ} {q : ℝ} {p : Fin (k + 1) → ℝ}
    (hp : BudgetedSchedule k q p) (j : Fin (k + 1)) :
    p j ≤ q := by
  have hlast : p (Fin.last k) = q := hp.2.2.2
  have hjle : j ≤ Fin.last k := by
    exact Fin.le_last j
  have hmono : Monotone p := hp.2.2.1.monotone
  simpa [hlast] using hmono hjle

-- @node: affine_mem_Icc_neg_one_one
lemma affine_mem_Icc_neg_one_one {q u : ℝ} (hq : 0 < q) (hu0 : 0 ≤ u) (huq : u ≤ q) :
    2 * u / q - 1 ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · rw [le_sub_iff_add_le, neg_add_cancel]
    exact div_nonneg (mul_nonneg (by norm_num) hu0) (le_of_lt hq)
  · rw [sub_le_iff_le_add, show (1 : ℝ) + 1 = 2 by norm_num]
    rw [div_le_iff₀ hq]
    nlinarith

-- @node: chebyshev_affine_natDegree_le
lemma chebyshev_affine_natDegree_le (beta : ℕ) (q : ℝ) :
    ((Polynomial.Chebyshev.T ℝ (beta : ℤ)).comp
        (Polynomial.C (2 / q) * Polynomial.X - Polynomial.C 1)).natDegree ≤ beta := by
  calc
    ((Polynomial.Chebyshev.T ℝ (beta : ℤ)).comp
        (Polynomial.C (2 / q) * Polynomial.X - Polynomial.C 1)).natDegree
        ≤ (Polynomial.Chebyshev.T ℝ (beta : ℤ)).natDegree *
            (Polynomial.C (2 / q) * Polynomial.X - Polynomial.C 1).natDegree :=
          Polynomial.natDegree_comp_le
    _ ≤ beta * 1 := by
          gcongr
          · simp [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
          · exact Polynomial.natDegree_sub_le_of_le
              ((Polynomial.natDegree_C_mul_le (2 / q) (Polynomial.X : Polynomial ℝ)).trans
                Polynomial.natDegree_X_le)
              (by rw [Polynomial.natDegree_C (R := ℝ) (a := (1 : ℝ))])
    _ = beta := by simp

-- @node: chebyshev_amplification_lower
lemma chebyshev_amplification_lower (qmax clower : ℝ) (hclower_pos : 0 < clower)
    (hendpoint_lower :
      ∀ (beta : ℕ) (q : ℝ), 1 ≤ beta → 0 < q → q ≤ qmax →
        (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (2 / q - 1) - 1 ≥
          clower * ((2 / q - 1) + Real.sqrt ((2 / q - 1) ^ 2 - 1)) ^ beta)
    {beta k : ℕ} {q : ℝ} (hbeta : 1 ≤ beta) (hkβ : beta ≤ k)
    (hq : 0 < q) (hqle : q ≤ qmax) (hqmax_lt : qmax < 1)
    (p : Fin (k + 1) → ℝ) (hp : BudgetedSchedule k q p) :
    amplification beta k p
      ≥ clower ^ 2 * ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta) := by
  let lam : ℝ := (2 / q - 1) + Real.sqrt ((2 / q - 1) ^ 2 - 1)
  let dualSet : Set ℝ := { t : ℝ | ∃ r : Polynomial ℝ, r.natDegree ≤ beta ∧
    (∀ j, |r.eval (p j)| ≤ 1) ∧ t = |r.eval 1 - r.eval 0| }
  let r : Polynomial ℝ :=
    (Polynomial.Chebyshev.T ℝ (beta : ℤ)).comp
      (Polynomial.C (2 / q) * Polynomial.X - Polynomial.C 1)
  have hq_lt_one : q < 1 := lt_of_le_of_lt hqle hqmax_lt
  have hxq_gt : 1 < 2 / q - 1 := by
    have hdiv : 1 < 1 / q := one_lt_one_div hq hq_lt_one
    nlinarith [show 2 / q = 2 * (1 / q) by ring]
  have hxq_one : 1 ≤ 2 / q - 1 := le_of_lt hxq_gt
  have hlam_gt : 1 < lam := by
    have hs : 0 ≤ Real.sqrt ((2 / q - 1) ^ 2 - 1) := Real.sqrt_nonneg _
    dsimp [lam]
    nlinarith
  have hlam_eq_base : lam = (1 + Real.sqrt (1 - q)) ^ 2 / q := by
    dsimp [lam]
    exact chebyshev_lambda_eq_rho_div_q hq hq_lt_one
  have hne : ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w :=
    unbiased_weight_set_nonempty beta k q p hbeta hkβ hp
  have hdual_eq : amplification beta k p = (sSup dualSet) ^ 2 := by
    simpa [dualSet] using (amplification_dual_norm beta k p hp.2.2.1.injective hne).2
  have hdual_bdd : BddAbove dualSet := by
    dsimp [dualSet]
    simpa [_root_.Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.dualValSet] using
      (_root_.Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.dualValSet_bddAbove
        (p := p) (β := beta) hp.2.2.1.injective hkβ)
  have hrdeg : r.natDegree ≤ beta := by
    simpa [r] using chebyshev_affine_natDegree_le beta q
  have hrbound : ∀ j, |r.eval (p j)| ≤ 1 := by
    intro j
    have hu0 : 0 ≤ p j := (hp.1 j).1
    have huq : p j ≤ q := budgetedSchedule_le_endpoint hp j
    have hxIcc : 2 * p j / q - 1 ∈ Set.Icc (-1 : ℝ) 1 :=
      affine_mem_Icc_neg_one_one hq hu0 huq
    have hxabs : |2 * p j / q - 1| ≤ 1 := by
      simpa [abs_le] using hxIcc
    have hxabs' : |2 / q * p j - 1| ≤ 1 := by
      have harg' : 2 / q * p j - 1 = 2 * p j / q - 1 := by
        field_simp [ne_of_gt hq]
      simpa [harg'] using hxabs
    have hcheb := Polynomial.Chebyshev.abs_eval_T_real_le_one (beta : ℤ) hxabs'
    have harg :
        (Polynomial.eval (p j) (Polynomial.C (2 / q) * Polynomial.X - Polynomial.C 1)) =
          2 / q * p j - 1 := by
      simp
    simpa [r, Polynomial.eval_comp, harg] using hcheb
  have hmem : |r.eval 1 - r.eval 0| ∈ dualSet := by
    exact ⟨r, hrdeg, hrbound, rfl⟩
  have hsup_ge_abs : |r.eval 1 - r.eval 0| ≤ sSup dualSet :=
    le_csSup hdual_bdd hmem
  have hTlower :
      clower * lam ^ beta ≤
        (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (2 / q - 1) - 1 := by
    simpa [lam] using hendpoint_lower beta q hbeta hq hqle
  have hTnonneg :
      0 ≤ (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (2 / q - 1) :=
    le_trans zero_le_one (Polynomial.Chebyshev.one_le_eval_T_real (beta : ℤ) hxq_one)
  have hTneg_abs :
      |(Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (-1)| ≤ 1 :=
    Polynomial.Chebyshev.abs_eval_T_real_le_one (beta : ℤ) (by norm_num)
  have hTminus_le_abs :
      (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (2 / q - 1) - 1 ≤
        |(Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (2 / q - 1) -
          (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (-1)| := by
    have hleft :
        |(Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (2 / q - 1)| -
            |(Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (-1)| ≤
          |(Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (2 / q - 1) -
            (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (-1)| :=
      abs_sub_abs_le_abs_sub _ _
    rw [abs_of_nonneg hTnonneg] at hleft
    nlinarith
  have hr_eval_one :
      r.eval 1 = (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (2 / q - 1) := by
    simp [r, Polynomial.eval_comp]
  have hr_eval_zero :
      r.eval 0 = (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (-1) := by
    simp [r, Polynomial.eval_comp]
  have hlower_abs : clower * lam ^ beta ≤ |r.eval 1 - r.eval 0| := by
    calc
      clower * lam ^ beta ≤
          (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (2 / q - 1) - 1 := hTlower
      _ ≤ |(Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (2 / q - 1) -
            (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (-1)| := hTminus_le_abs
      _ = |r.eval 1 - r.eval 0| := by rw [hr_eval_one, hr_eval_zero]
  have hdual_lower : clower * lam ^ beta ≤ sSup dualSet :=
    hlower_abs.trans hsup_ge_abs
  have hleft_nonneg : 0 ≤ clower * lam ^ beta :=
    mul_nonneg (le_of_lt hclower_pos) (pow_nonneg (le_of_lt (lt_trans zero_lt_one hlam_gt)) beta)
  have hpow : lam ^ (2 * beta) = (lam ^ beta) ^ 2 := by
    rw [Nat.mul_comm 2 beta, pow_mul]
  have htarget :
      clower ^ 2 * lam ^ (2 * beta) = (clower * lam ^ beta) ^ 2 := by
    rw [hpow]
    ring
  rw [hdual_eq, ← hlam_eq_base]
  rw [htarget]
  exact sq_le_sq' (by linarith [hleft_nonneg, hdual_lower]) hdual_lower

end CausalSmith.Experimentation.RolloutChebyshev
