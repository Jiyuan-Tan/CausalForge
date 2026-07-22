/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Chebyshev minimax upper-bound assembly
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.MinimaxAssembly

open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: lobatto_affine_comp_natDegree_le
lemma lobatto_affine_comp_natDegree_le {beta : ℕ} {q : ℝ} {r : Polynomial ℝ}
    (hrdeg : r.natDegree ≤ beta) :
    (r.comp (Polynomial.C (q / 2) * (Polynomial.X + Polynomial.C 1))).natDegree ≤ beta := by
  have haff :
      (Polynomial.C (q / 2) * (Polynomial.X + Polynomial.C 1 : Polynomial ℝ)).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_C_mul_le (q / 2)
      (Polynomial.X + Polynomial.C 1 : Polynomial ℝ)).trans
        (by rw [Polynomial.natDegree_X_add_C])
  calc
    (r.comp (Polynomial.C (q / 2) * (Polynomial.X + Polynomial.C 1))).natDegree
        ≤ r.natDegree *
            (Polynomial.C (q / 2) * (Polynomial.X + Polynomial.C 1 : Polynomial ℝ)).natDegree :=
          Polynomial.natDegree_comp_le
    _ ≤ beta * 1 := by gcongr
    _ = beta := by simp

-- @node: chebyshev_amplification_upper
lemma chebyshev_amplification_upper (c qmax Cupper K : ℝ) (hCupper_pos : 0 < Cupper)
    (hKpos : 0 < K)
    (hendpoint_upper :
      ∀ (beta : ℕ) (q : ℝ), 1 ≤ beta → 0 < q → q ≤ qmax →
        ∀ R : Polynomial ℝ, R.natDegree ≤ beta →
          (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |R.eval x| ≤ 1) →
          |R.eval (2 / q - 1) - R.eval (-1)| ≤
            Cupper * ((2 / q - 1) + Real.sqrt ((2 / q - 1) ^ 2 - 1)) ^ beta)
    (hnorming :
      ∀ (beta k : ℕ) (R : Polynomial ℝ), 1 ≤ beta → (k : ℝ) ≥ c * beta →
        R.natDegree ≤ beta →
        ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
          |R.eval x| ≤ K * Finset.univ.sup' Finset.univ_nonempty
            (fun j : Fin (k + 1) => |R.eval (-Real.cos (Real.pi * (j : ℝ) / (k : ℝ)))|))
    {beta k : ℕ} {q : ℝ} (hbeta : 1 ≤ beta) (hkβ : beta ≤ k)
    (hk : (k : ℝ) ≥ c * beta) (hq : 0 < q) (hqle : q ≤ qmax) (hqmax_lt : qmax < 1) :
    amplification beta k (chebyshevSchedule k q)
      ≤ (K * Cupper) ^ 2 * ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta) := by
  let p : Fin (k + 1) → ℝ := chebyshevSchedule k q
  let lam : ℝ := (2 / q - 1) + Real.sqrt ((2 / q - 1) ^ 2 - 1)
  let dualSet : Set ℝ := { t : ℝ | ∃ r : Polynomial ℝ, r.natDegree ≤ beta ∧
    (∀ j, |r.eval (p j)| ≤ 1) ∧ t = |r.eval 1 - r.eval 0| }
  have hq_lt_one : q < 1 := lt_of_le_of_lt hqle hqmax_lt
  have hq_le_one : q ≤ 1 := le_trans hqle (le_of_lt hqmax_lt)
  have hk_one : 1 ≤ k := hbeta.trans hkβ
  have hp : BudgetedSchedule k q p := by
    simpa [p] using chebyshev_schedule_admissible k q hk_one ⟨hq, hq_le_one⟩
  have hne : ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w :=
    unbiased_weight_set_nonempty beta k q p hbeta hkβ hp
  have hdual_eq : amplification beta k p = (sSup dualSet) ^ 2 := by
    simpa [dualSet] using (amplification_dual_norm beta k p hp.2.2.1.injective hne).2
  have hdual_bdd : BddAbove dualSet := by
    dsimp [dualSet]
    simpa [_root_.Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.dualValSet] using
      (_root_.Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.dualValSet_bddAbove
        (p := p) (β := beta) hp.2.2.1.injective hkβ)
  have hzero_mem : (0 : ℝ) ∈ dualSet := by
    refine ⟨0, by simp, ?_, by simp⟩
    intro j
    simp
  have hdual_nonneg : 0 ≤ sSup dualSet := le_csSup hdual_bdd hzero_mem
  have hlam_gt : 1 < lam := by
    have hxq_gt : 1 < 2 / q - 1 := by
      have hdiv : 1 < 1 / q := one_lt_one_div hq hq_lt_one
      nlinarith [show 2 / q = 2 * (1 / q) by ring]
    have hs : 0 ≤ Real.sqrt ((2 / q - 1) ^ 2 - 1) := Real.sqrt_nonneg _
    dsimp [lam]
    nlinarith
  have hlam_eq_base : lam = (1 + Real.sqrt (1 - q)) ^ 2 / q := by
    dsimp [lam]
    exact chebyshev_lambda_eq_rho_div_q hq hq_lt_one
  have hdual_upper : sSup dualSet ≤ K * Cupper * lam ^ beta := by
    refine csSup_le ?hneSet ?_
    · exact ⟨0, hzero_mem⟩
    · intro t ht
      rcases ht with ⟨r, hrdeg, hrnode, rfl⟩
      let aff : Polynomial ℝ := Polynomial.C (q / 2) * (Polynomial.X + Polynomial.C 1)
      let R : Polynomial ℝ := r.comp aff
      let S : Polynomial ℝ := Polynomial.C K⁻¹ * R
      have hRdeg : R.natDegree ≤ beta := by
        simpa [R, aff] using lobatto_affine_comp_natDegree_le (q := q) hrdeg
      have hSdeg : S.natDegree ≤ beta := by
        exact (Polynomial.natDegree_C_mul_le K⁻¹ R).trans hRdeg
      have hRnode : ∀ j : Fin (k + 1),
          R.eval (-Real.cos (Real.pi * (j : ℝ) / (k : ℝ))) = r.eval (p j) := by
        intro j
        simp [R, aff, p, Polynomial.eval_comp, chebyshevSchedule]
        ring_nf
      have hnode_sup_le :
          Finset.univ.sup' Finset.univ_nonempty
            (fun j : Fin (k + 1) =>
              |R.eval (-Real.cos (Real.pi * (j : ℝ) / (k : ℝ)))|) ≤ 1 := by
        refine Finset.sup'_le Finset.univ_nonempty _ ?_
        intro j _hj
        simpa [hRnode j] using hrnode j
      have hR_interval : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |R.eval x| ≤ K := by
        intro x hx
        calc
          |R.eval x| ≤ K * Finset.univ.sup' Finset.univ_nonempty
              (fun j : Fin (k + 1) =>
                |R.eval (-Real.cos (Real.pi * (j : ℝ) / (k : ℝ)))|) :=
            hnorming beta k R hbeta hk hRdeg x hx
          _ ≤ K * 1 := mul_le_mul_of_nonneg_left hnode_sup_le (le_of_lt hKpos)
          _ = K := by ring_nf
      have hS_bound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |S.eval x| ≤ 1 := by
        intro x hx
        have hR := hR_interval x hx
        calc
          |S.eval x| = K⁻¹ * |R.eval x| := by
            simp [S, abs_mul, abs_of_pos (inv_pos.mpr hKpos)]
          _ ≤ K⁻¹ * K :=
            mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr (le_of_lt hKpos))
          _ = 1 := by field_simp [ne_of_gt hKpos]
      have haff_xq : aff.eval (2 / q - 1) = 1 := by
        simp [aff]
        field_simp [ne_of_gt hq]
      have haff_neg_one : aff.eval (-1) = 0 := by
        simp [aff]
      have hR_xq : R.eval (2 / q - 1) = r.eval 1 := by
        simp [R, Polynomial.eval_comp, haff_xq]
      have hR_neg_one : R.eval (-1) = r.eval 0 := by
        simp [R, Polynomial.eval_comp, haff_neg_one]
      have hS_endpoint :
          |S.eval (2 / q - 1) - S.eval (-1)| ≤ Cupper * lam ^ beta := by
        simpa [lam] using hendpoint_upper beta q hbeta hq hqle S hSdeg hS_bound
      have hscaled : K⁻¹ * |r.eval 1 - r.eval 0| ≤ Cupper * lam ^ beta := by
        have hS_eval :
            |S.eval (2 / q - 1) - S.eval (-1)| = K⁻¹ * |r.eval 1 - r.eval 0| := by
          calc
            |S.eval (2 / q - 1) - S.eval (-1)|
                = |K⁻¹ * (r.eval 1 - r.eval 0)| := by
                    simp [S, Polynomial.eval_mul, hR_xq, hR_neg_one, mul_sub]
            _ = K⁻¹ * |r.eval 1 - r.eval 0| := by
                    rw [abs_mul, abs_of_pos (inv_pos.mpr hKpos)]
        simpa [hS_eval] using hS_endpoint
      calc
        |r.eval 1 - r.eval 0| = K * (K⁻¹ * |r.eval 1 - r.eval 0|) := by
          field_simp [ne_of_gt hKpos]
        _ ≤ K * (Cupper * lam ^ beta) :=
          mul_le_mul_of_nonneg_left hscaled (le_of_lt hKpos)
        _ = K * Cupper * lam ^ beta := by ring_nf
  have hright_nonneg : 0 ≤ K * Cupper * lam ^ beta :=
    mul_nonneg (mul_nonneg (le_of_lt hKpos) (le_of_lt hCupper_pos))
      (pow_nonneg (le_of_lt (lt_trans zero_lt_one hlam_gt)) beta)
  have hpow : lam ^ (2 * beta) = (lam ^ beta) ^ 2 := by
    rw [Nat.mul_comm 2 beta, pow_mul]
  have htarget :
      (K * Cupper) ^ 2 * lam ^ (2 * beta) = (K * Cupper * lam ^ beta) ^ 2 := by
    rw [hpow]
    ring_nf
  change amplification beta k p ≤ (K * Cupper) ^ 2 *
    ((1 + Real.sqrt (1 - q)) ^ 2 / q) ^ (2 * beta)
  rw [hdual_eq, ← hlam_eq_base, htarget]
  exact (sq_le_sq₀ hdual_nonneg hright_nonneg).2 hdual_upper

end CausalSmith.Experimentation.RolloutChebyshev
