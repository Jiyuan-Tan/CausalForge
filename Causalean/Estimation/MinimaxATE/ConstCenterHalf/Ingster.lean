/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Ingster χ² bound for the structure-agnostic ATE lower bound

A standalone real-analysis inequality used in the Jin–Syrgkanis structure-agnostic
ATE lower bound.  Averaging over Rademacher sign vectors `λ, λ' : Fin K → Bool`,

  `(2^K)⁻¹ (2^K)⁻¹ ∑_{λ,λ'} (1 + (2γ/K) ⟨sign λ, sign λ'⟩)^n ≤ 2`

whenever `0 ≤ γ`, `2γ ≤ 1` and `2 n² γ² ≤ K log 2`.  The proof linearizes
`1 + x ≤ exp x`, factorizes the resulting exponential average into `cosh^K`, and
applies `cosh x ≤ exp (x²/2)`.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Construction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Ingster Average Bound

This file proves the Ingster chi-squared average bound for Rademacher sign mixtures with a
common coordinate weight. The theorem `ingster_bound` controls the double average of
`(1 + (2γ/K) S)^n` over pairs of sign vectors by `2` when `0 ≤ γ`, `2γ ≤ 1`, and
`2 n² γ² ≤ K log 2`.

This analytic inequality is the step that turns the explicit one-observation overlap formula
into total-variation indistinguishability for the minimax lower bound.
-/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

/-- The Ingster χ² average bound: the doubly-averaged `(1 + cS)^n` over Rademacher
pairs is at most `2` under the regularity budget `2 n² γ² ≤ K log 2`. -/
theorem ingster_bound (K n : ℕ) [NeZero K] {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : 2 * γ ≤ 1) (hreg : 2 * (n : ℝ) ^ 2 * γ ^ 2 ≤ (K : ℝ) * Real.log 2) :
    ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
      ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹
        * (1 + (2 * γ / (K : ℝ)) * ∑ j, signOf (lam j) * signOf (lam' j)) ^ n ≤ 2 := by
  -- Basic facts about `K`.
  have hKpos : 0 < (K : ℝ) := by
    have := NeZero.ne K
    exact_mod_cast Nat.pos_of_ne_zero this
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  set c : ℝ := 2 * γ / (K : ℝ) with hc_def
  have hc0 : 0 ≤ c := by
    rw [hc_def]; positivity
  -- abbreviations
  set w : ℝ := ((2 : ℝ) ^ K)⁻¹ with hw_def
  have hw0 : 0 ≤ w := by rw [hw_def]; positivity
  -- Per-term: `(1 + c S)^n ≤ exp (n c S)` where `S = ∑ j, signOf (lam j) * signOf (lam' j)`.
  have step1 : ∀ lam lam' : Fin K → Bool,
      (1 + c * ∑ j, signOf (lam j) * signOf (lam' j)) ^ n
        ≤ Real.exp ((n : ℝ) * (c * ∑ j, signOf (lam j) * signOf (lam' j))) := by
    intro lam lam'
    set S : ℝ := ∑ j, signOf (lam j) * signOf (lam' j) with hS_def
    -- `-K ≤ S ≤ K`
    have hScard : ∀ j : Fin K, -1 ≤ signOf (lam j) * signOf (lam' j) ∧
        signOf (lam j) * signOf (lam' j) ≤ 1 := by
      intro j
      rcases signOf_mem (lam j) with h1 | h1 <;> rcases signOf_mem (lam' j) with h2 | h2 <;>
        simp [h1, h2]
    have hSlow : -(K : ℝ) ≤ S := by
      rw [hS_def]
      have : ∀ j ∈ Finset.univ, (-1 : ℝ) ≤ signOf (lam j) * signOf (lam' j) :=
        fun j _ => (hScard j).1
      calc -(K : ℝ) = ∑ _j : Fin K, (-1 : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp
        _ ≤ _ := Finset.sum_le_sum this
    -- `c * S ≥ -1`
    have hcS_ge : -1 ≤ c * S := by
      have : c * (-(K : ℝ)) ≤ c * S := mul_le_mul_of_nonneg_left hSlow hc0
      have hcK : c * (K : ℝ) = 2 * γ := by
        rw [hc_def]; field_simp
      calc (-1 : ℝ) ≤ -(2 * γ) := by linarith
        _ = c * (-(K : ℝ)) := by rw [mul_neg, hcK]
        _ ≤ c * S := this
    have h0 : (0 : ℝ) ≤ 1 + c * S := by linarith
    -- `1 + cS ≤ exp (cS)`
    have hexp : 1 + c * S ≤ Real.exp (c * S) := by
      have := Real.add_one_le_exp (c * S)
      linarith
    calc (1 + c * S) ^ n ≤ (Real.exp (c * S)) ^ n :=
            pow_le_pow_left₀ h0 hexp n
      _ = Real.exp ((n : ℝ) * (c * S)) := by rw [Real.exp_nat_mul]
  -- Step 2: bound the whole double sum by the exp double sum.
  have step2 :
      ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        w * w * (1 + c * ∑ j, signOf (lam j) * signOf (lam' j)) ^ n
      ≤ ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        w * w * Real.exp ((n : ℝ) * (c * ∑ j, signOf (lam j) * signOf (lam' j))) := by
    apply Finset.sum_le_sum
    intro lam _
    apply Finset.sum_le_sum
    intro lam' _
    apply mul_le_mul_of_nonneg_left (step1 lam lam')
    positivity
  -- Step 3: the exp double sum equals `(cosh (n c))^K`.
  have step3 :
      ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        w * w * Real.exp ((n : ℝ) * (c * ∑ j, signOf (lam j) * signOf (lam' j)))
      = (Real.cosh ((n : ℝ) * c)) ^ K := by
    -- Define the per-coordinate factor.
    set h : Bool × Bool → ℝ :=
      fun p => (1 / 4 : ℝ) * Real.exp ((n : ℝ) * c * (signOf p.1 * signOf p.2)) with hh_def
    -- The single-coordinate sum is cosh.
    have hsum_h : (∑ p : Bool × Bool, h p) = Real.cosh ((n : ℝ) * c) := by
      rw [Fintype.sum_prod_type]
      simp only [hh_def, Fintype.sum_bool, signOf_true, signOf_false]
      rw [show (n : ℝ) * c * (1 * 1) = (n : ℝ) * c by ring,
          show (n : ℝ) * c * (1 * -1) = -((n : ℝ) * c) by ring,
          show (n : ℝ) * c * (-1 * 1) = -((n : ℝ) * c) by ring,
          show (n : ℝ) * c * (-1 * -1) = (n : ℝ) * c by ring]
      rw [Real.cosh_eq]
      ring
    -- Now the double sum equals `(∑ p, h p)^K`.
    rw [← hsum_h]
    rw [Fintype.sum_pow]
    -- RHS is now `∑ ρ : Fin K → Bool × Bool, ∏ j, h (ρ j)`.
    -- LHS: convert the double sum into a sum over the product, then reindex by the equiv.
    rw [← Fintype.sum_prod_type
      (f := fun p : (Fin K → Bool) × (Fin K → Bool) =>
        w * w * Real.exp ((n : ℝ) * (c * ∑ j, signOf (p.1 j) * signOf (p.2 j))))]
    -- LHS : `∑ p : (Fin K → Bool) × (Fin K → Bool), w*w*exp(...)`
    rw [← Equiv.sum_comp
      (Equiv.arrowProdEquivProdArrow (Fin K) (fun _ => Bool) (fun _ => Bool)).symm]
    apply Finset.sum_congr rfl
    intro ρ _
    -- For a fixed `ρ : Fin K → Bool × Bool`.
    simp only [Equiv.arrowProdEquivProdArrow_symm_apply]
    -- Goal: w*w*exp((n)*(c*∑ j, signOf (ρ j).1 * signOf (ρ j).2)) = ∏ j, h (ρ j)
    rw [hh_def]
    -- ∏ j, (1/4)*exp(nc*(signOf (ρ j).1 * signOf (ρ j).2))
    rw [Finset.prod_mul_distrib]
    -- = (∏ j, 1/4) * (∏ j, exp(...))
    rw [← Real.exp_sum]
    -- ∏ j, exp = exp (∑ j ...)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    -- (1/4)^K * exp(∑ j, nc*(...))
    -- w*w = (1/4)^K
    have hww : w * w = (1 / 4 : ℝ) ^ K := by
      rw [hw_def]
      rw [← mul_inv]
      rw [show (2 : ℝ) ^ K * 2 ^ K = 4 ^ K by rw [← mul_pow]; norm_num]
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
      rw [inv_pow]
    rw [hww]
    -- now goal: (1/4)^K * exp((n)*(c*∑ j ...)) = (1/4)^K * exp(∑ j, nc*(...))
    congr 1
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- Step 4: `(cosh (n c))^K ≤ 2`.
  have step4 : (Real.cosh ((n : ℝ) * c)) ^ K ≤ 2 := by
    have hcosh_pos : 0 ≤ Real.cosh ((n : ℝ) * c) :=
      le_of_lt (Real.cosh_pos _)
    have hcosh_le : Real.cosh ((n : ℝ) * c) ≤ Real.exp (((n : ℝ) * c) ^ 2 / 2) :=
      Real.cosh_le_exp_half_sq _
    calc (Real.cosh ((n : ℝ) * c)) ^ K
          ≤ (Real.exp (((n : ℝ) * c) ^ 2 / 2)) ^ K :=
            pow_le_pow_left₀ hcosh_pos hcosh_le K
      _ = Real.exp ((K : ℝ) * (((n : ℝ) * c) ^ 2 / 2)) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp (Real.log 2) := by
            apply Real.exp_le_exp.mpr
            -- (K) * ((n c)^2/2) = 2 n^2 γ^2 / K ≤ log 2
            have hexp_eq : (K : ℝ) * (((n : ℝ) * c) ^ 2 / 2)
                = 2 * (n : ℝ) ^ 2 * γ ^ 2 / (K : ℝ) := by
              rw [hc_def]
              field_simp
            rw [hexp_eq]
            rw [div_le_iff₀ hKpos]
            calc 2 * (n : ℝ) ^ 2 * γ ^ 2 ≤ (K : ℝ) * Real.log 2 := hreg
              _ = Real.log 2 * (K : ℝ) := by ring
      _ = 2 := by rw [Real.exp_log]; norm_num
  -- Chain everything. The LHS of the goal matches step2's LHS.
  calc ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        w * w * (1 + c * ∑ j, signOf (lam j) * signOf (lam' j)) ^ n
        ≤ ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
          w * w * Real.exp ((n : ℝ) * (c * ∑ j, signOf (lam j) * signOf (lam' j))) := step2
    _ = (Real.cosh ((n : ℝ) * c)) ^ K := step3
    _ ≤ 2 := step4

end Causalean.Estimation.MinimaxATE
