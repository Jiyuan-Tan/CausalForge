/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Generalized Ingster χ² bound (non-uniform coefficients)

A non-uniform-coefficient variant of `ingster_bound` (see `Ingster.lean`).  Instead
of a single shared coefficient `2γ/K` on every coordinate, each coordinate `j`
carries its own weight `d j ≥ 0` with `∑ j, d j ≤ 1`.  Averaging over Rademacher
sign vectors `λ, λ' : Fin K → Bool`,

  `(2^K)⁻¹ (2^K)⁻¹ ∑_{λ,λ'} (1 + ∑ j, d j · signOf (λ j) · signOf (λ' j))^n ≤ 2`

whenever the regularity budget `(n²/2) ∑ j, (d j)² ≤ log 2` holds.  The proof
mirrors `Ingster.lean` exactly, except the factorization in step 3 now yields the
product `∏ j, cosh (n · d j)` over varying per-coordinate factors instead of
`(cosh (n c))^K`, and step 4 bounds each `cosh` separately via `cosh x ≤ exp(x²/2)`
before collapsing the product through `Real.exp_sum`.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Construction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Non-Uniform Ingster Bound

This file proves the Ingster chi-squared average bound with coordinate-specific
nonnegative weights.  The result supports the cell-varying lower-bound constructions,
where each covariate pair contributes its own overlap coefficient.

The public theorem `ingster_bound_general` bounds the doubly averaged Rademacher expression
`(1 + sum_j d j * signOf (lam j) * signOf (lam' j))^n` by `2`, assuming the weights are
nonnegative, have total mass at most `1`, and satisfy the regularity budget
`(n^2 / 2) * sum_j (d j)^2 <= log 2`.  This is the non-uniform chi-squared step used after
`chiSqOverlap_eqV` rewrites the cell-varying overlap. -/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

/-- The generalized Ingster χ² average bound: with per-coordinate weights
`d j ≥ 0` summing to at most `1`, the doubly-averaged
`(1 + ∑ j, d j · signOf (λ j) · signOf (λ' j))^n` over Rademacher pairs is at most
`2` under the regularity budget `(n²/2) ∑ j, (d j)² ≤ log 2`. -/
theorem ingster_bound_general (K n : ℕ) [NeZero K] {d : Fin K → ℝ}
    (hd0 : ∀ j, 0 ≤ d j) (hdsum : ∑ j, d j ≤ 1)
    (hreg : (n : ℝ) ^ 2 / 2 * ∑ j, (d j) ^ 2 ≤ Real.log 2) :
    ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
      ((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K)⁻¹
        * (1 + ∑ j, d j * (signOf (lam j) * signOf (lam' j))) ^ n ≤ 2 := by
  -- abbreviations
  set w : ℝ := ((2 : ℝ) ^ K)⁻¹ with hw_def
  have hw0 : 0 ≤ w := by rw [hw_def]; positivity
  -- Per-term: `(1 + S)^n ≤ exp (n S)` where `S = ∑ j, d j*(signOf (lam j)*signOf (lam' j))`.
  have step1 : ∀ lam lam' : Fin K → Bool,
      (1 + ∑ j, d j * (signOf (lam j) * signOf (lam' j))) ^ n
        ≤ Real.exp ((n : ℝ) * ∑ j, d j * (signOf (lam j) * signOf (lam' j))) := by
    intro lam lam'
    set S : ℝ := ∑ j, d j * (signOf (lam j) * signOf (lam' j)) with hS_def
    -- Each summand `d j * (signOf (lam j)*signOf (lam' j)) ≥ d j * (-1) = -(d j)`.
    have hSlow : -(1 : ℝ) ≤ S := by
      rw [hS_def]
      have hterm : ∀ j ∈ Finset.univ,
          -(d j) ≤ d j * (signOf (lam j) * signOf (lam' j)) := by
        intro j _
        have hmem : -1 ≤ signOf (lam j) * signOf (lam' j) := by
          rcases signOf_mem (lam j) with h1 | h1 <;> rcases signOf_mem (lam' j) with h2 | h2 <;>
            simp [h1, h2]
        have := mul_le_mul_of_nonneg_left hmem (hd0 j)
        simpa using this
      calc -(1 : ℝ) ≤ -(∑ j, d j) := by linarith
        _ = ∑ j, -(d j) := by rw [Finset.sum_neg_distrib]
        _ ≤ ∑ j, d j * (signOf (lam j) * signOf (lam' j)) := Finset.sum_le_sum hterm
    have h0 : (0 : ℝ) ≤ 1 + S := by linarith
    -- `1 + S ≤ exp (S)`
    have hexp : 1 + S ≤ Real.exp S := by
      have := Real.add_one_le_exp S
      linarith
    calc (1 + S) ^ n ≤ (Real.exp S) ^ n :=
            pow_le_pow_left₀ h0 hexp n
      _ = Real.exp ((n : ℝ) * S) := by rw [Real.exp_nat_mul]
  -- Step 2: bound the whole double sum by the exp double sum.
  have step2 :
      ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        w * w * (1 + ∑ j, d j * (signOf (lam j) * signOf (lam' j))) ^ n
      ≤ ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        w * w * Real.exp ((n : ℝ) * ∑ j, d j * (signOf (lam j) * signOf (lam' j))) := by
    apply Finset.sum_le_sum
    intro lam _
    apply Finset.sum_le_sum
    intro lam' _
    apply mul_le_mul_of_nonneg_left (step1 lam lam')
    positivity
  -- Step 3: the exp double sum equals `∏ j, cosh (n * d j)`.
  have step3 :
      ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        w * w * Real.exp ((n : ℝ) * ∑ j, d j * (signOf (lam j) * signOf (lam' j)))
      = ∏ j, Real.cosh ((n : ℝ) * d j) := by
    -- Define the per-coordinate factor.
    set h : Fin K → Bool × Bool → ℝ :=
      fun j p => (1 / 4 : ℝ) * Real.exp ((n : ℝ) * d j * (signOf p.1 * signOf p.2)) with hh_def
    -- The single-coordinate sum is cosh.
    have hsum_h : ∀ j, (∑ p : Bool × Bool, h j p) = Real.cosh ((n : ℝ) * d j) := by
      intro j
      rw [Fintype.sum_prod_type]
      simp only [hh_def, Fintype.sum_bool, signOf_true, signOf_false]
      rw [show (n : ℝ) * d j * (1 * 1) = (n : ℝ) * d j by ring,
          show (n : ℝ) * d j * (1 * -1) = -((n : ℝ) * d j) by ring,
          show (n : ℝ) * d j * (-1 * 1) = -((n : ℝ) * d j) by ring,
          show (n : ℝ) * d j * (-1 * -1) = (n : ℝ) * d j by ring]
      rw [Real.cosh_eq]
      ring
    -- Rewrite the RHS product as a product of single-coordinate sums.
    have hprod_eq : ∏ j, Real.cosh ((n : ℝ) * d j) = ∏ j, ∑ p : Bool × Bool, h j p := by
      apply Finset.prod_congr rfl
      intro j _
      rw [hsum_h j]
    rw [hprod_eq]
    -- `∏ j, ∑ p, h j p = ∑ ρ : Fin K → Bool×Bool, ∏ j, h j (ρ j)` (distribute product of sums).
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    -- LHS: convert the double sum into a sum over the product, then reindex by the equiv.
    rw [← Fintype.sum_prod_type
      (f := fun p : (Fin K → Bool) × (Fin K → Bool) =>
        w * w * Real.exp ((n : ℝ) * ∑ j, d j * (signOf (p.1 j) * signOf (p.2 j))))]
    rw [← Equiv.sum_comp
      (Equiv.arrowProdEquivProdArrow (Fin K) (fun _ => Bool) (fun _ => Bool)).symm]
    apply Finset.sum_congr rfl
    intro ρ _
    -- For a fixed `ρ : Fin K → Bool × Bool`.
    simp only [Equiv.arrowProdEquivProdArrow_symm_apply]
    -- Goal: w*w*exp((n)*∑ j, d j*(signOf (ρ j).1 * signOf (ρ j).2)) = ∏ j, h j (ρ j)
    rw [hh_def]
    -- ∏ j, (1/4)*exp(n*d j*(signOf (ρ j).1 * signOf (ρ j).2))
    rw [Finset.prod_mul_distrib]
    -- = (∏ j, 1/4) * (∏ j, exp(...))
    rw [← Real.exp_sum]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    -- w*w = (1/4)^K
    have hww : w * w = (1 / 4 : ℝ) ^ K := by
      rw [hw_def]
      rw [← mul_inv]
      rw [show (2 : ℝ) ^ K * 2 ^ K = 4 ^ K by rw [← mul_pow]; norm_num]
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
      rw [inv_pow]
    rw [hww]
    -- now goal: (1/4)^K * exp((n)*∑ j ...) = (1/4)^K * exp(∑ j, n*d j*(...))
    congr 1
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- Step 4: `∏ j, cosh (n * d j) ≤ 2`.
  have step4 : ∏ j, Real.cosh ((n : ℝ) * d j) ≤ 2 := by
    calc ∏ j, Real.cosh ((n : ℝ) * d j)
          ≤ ∏ j, Real.exp (((n : ℝ) * d j) ^ 2 / 2) := by
            apply Finset.prod_le_prod
            · intro j _; exact le_of_lt (Real.cosh_pos _)
            · intro j _; exact Real.cosh_le_exp_half_sq _
      _ = Real.exp (∑ j, ((n : ℝ) * d j) ^ 2 / 2) := by rw [← Real.exp_sum]
      _ ≤ Real.exp (Real.log 2) := by
            apply Real.exp_le_exp.mpr
            have hsum_eq : (∑ j, ((n : ℝ) * d j) ^ 2 / 2)
                = (n : ℝ) ^ 2 / 2 * ∑ j, (d j) ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
            rw [hsum_eq]
            exact hreg
      _ = 2 := by rw [Real.exp_log]; norm_num
  -- Chain everything. The LHS of the goal matches step2's LHS.
  calc ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
        w * w * (1 + ∑ j, d j * (signOf (lam j) * signOf (lam' j))) ^ n
        ≤ ∑ lam : Fin K → Bool, ∑ lam' : Fin K → Bool,
          w * w * Real.exp ((n : ℝ) * ∑ j, d j * (signOf (lam j) * signOf (lam' j))) := step2
    _ = ∏ j, Real.cosh ((n : ℝ) * d j) := step3
    _ ≤ 2 := step4

end Causalean.Estimation.MinimaxATE
