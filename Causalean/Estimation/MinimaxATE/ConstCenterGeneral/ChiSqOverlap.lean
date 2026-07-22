/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: χ²-overlap (general constant center)

The general-constant-center analogue of `ChiSqOverlap.lean`.  It records the closed form
of the single-observation χ²-overlap of two perturbed laws (indexed by sign vectors
`λ, λ'`) relative to the null, around a constant center `(m₀, g₀, g₁)`:

  `chiSqOverlapG λ λ' = 1 + (Γ/K) · Σⱼ signOf(λ j) signOf(λ' j)`,

where the per-cell overlap coefficient is

  `Γ = m₀·α²/g₁ + m₀·(α + β/g₁)²/(1 − g₁) + m₀²·β²/(g₁²·(1 − m₀))`.

At `m₀ = g₁ = 1/2` this collapses to `Γ = 2(α² + 2αβ + 3β²)`, matching the `2γ`
coefficient of `ChiSqOverlap.lean`.  The linear-in-`Δ` terms cancel by construction, and
summing over the two positions of a pair leaves only the `λ·λ'` cross term — exactly
the structure the abstract `ingster_bound` consumes (instantiated with `γ = Γ/2`).
-/

import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.Gap

/-! # General-Center Chi-Squared Second-Moment Overlap

This file derives the closed-form single-observation chi-squared overlap for two
general constant-center Rademacher perturbations relative to the null law.  The formula isolates
the per-cell overlap coefficient that feeds the Ingster second-moment argument,
with the linear perturbation terms canceling by construction.  "Overlap" here is
the χ² second-moment overlap of two likelihood ratios, not the causal
positivity/overlap condition.

The definition `Γ` is the per-cell coefficient, `chiSqOverlapG` is the raw
single-observation overlap, `obsReal_pertG_eq` gives the denominator-free
observed-mass formula for the four treatment/outcome cells, and
`chiSqOverlap_eqG` proves the closed form
`1 + (Γ / K) * ∑ j, signOf (lam j) * signOf (lam' j)`. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open scoped BigOperators

namespace GenConstr

variable {K : ℕ} (P : GenConstr)

/-- The per-cell χ²-overlap coefficient. -/
noncomputable def Γ : ℝ :=
  P.m₀ * P.α ^ 2 / P.g₁
    + P.m₀ * (P.α + P.β / P.g₁) ^ 2 / (1 - P.g₁)
    + P.m₀ ^ 2 * P.β ^ 2 / (P.g₁ ^ 2 * (1 - P.m₀))

/-- The single-observation χ² second-moment overlap of two perturbed laws relative to the null. -/
noncomputable def chiSqOverlapG (lam lam' : Fin K → Bool) : ℝ :=
  ∑ z : Obs (Fin K × Bool),
    obsReal (P.mPertG lam) (P.gPertG lam) z
      * obsReal (P.mPertG lam') (P.gPertG lam') z
      / obsReal P.mhatG P.ghatG z

/-- Denominator-free value of the perturbed observed mass `obsReal mλ gλ` at the four
`(d, y)` combinations.  The treated arm's denominator `1 − (β/g₁)Δ` cancels against
`mλ = m₀·(1 − (β/g₁)Δ)`. -/
theorem obsReal_pertG_eq (lam : Fin K → Bool) (x : Fin K × Bool) (d y : Bool) :
    obsReal (P.mPertG lam) (P.gPertG lam) (x, d, y)
      = (Fintype.card (Fin K × Bool) : ℝ)⁻¹ *
          (match d, y with
           | true, true => P.m₀ * (P.g₁ + P.α * Δ lam x)
           | true, false => P.m₀ * ((1 - P.g₁) - (P.α + P.β / P.g₁) * Δ lam x)
           | false, true => (1 - P.m₀ + P.m₀ * (P.β / P.g₁) * Δ lam x) * P.g₀
           | false, false => (1 - P.m₀ + P.m₀ * (P.β / P.g₁) * Δ lam x) * (1 - P.g₀)) := by
  have hd : (1 - (P.β / P.g₁) * Δ lam x) ≠ 0 := (P.denomG_pos lam x).ne'
  have hg₁ne : P.g₁ ≠ 0 := ne_of_gt P.hg₁0
  have hden : P.g₁ - P.β * Δ lam x ≠ 0 := by
    rcases Δ_mem lam x with h | h <;> rw [h] <;>
      · have := P.hβg₁; have := P.hβ; intro hc; nlinarith
  unfold obsReal mPertG gPertG
  cases d <;> cases y <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;>
    rw [mul_assoc] <;> refine congrArg _ ?_ <;> field_simp <;> ring

/-- The single-observation overlap equals one plus the per-cell coefficient times the
average sign agreement across pairs. -/
theorem chiSqOverlap_eqG [NeZero K] (lam lam' : Fin K → Bool) :
    P.chiSqOverlapG lam lam'
      = 1 + (P.Γ / (K : ℝ)) * ∑ j, signOf (lam j) * signOf (lam' j) := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have hcard : (Fintype.card (Fin K × Bool) : ℝ) = 2 * K := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; push_cast; ring
  have hg₁ne : P.g₁ ≠ 0 := ne_of_gt P.hg₁0
  have hm₀ne : P.m₀ ≠ 0 := ne_of_gt P.hm₀0
  have hg₀ne : P.g₀ ≠ 0 := ne_of_gt P.hg₀0
  have h1g₁ : (1 : ℝ) - P.g₁ ≠ 0 := by have := P.hg₁1; intro hc; linarith
  have h1m₀ : (1 : ℝ) - P.m₀ ≠ 0 := by have := P.hm₀1; intro hc; linarith
  have h1g₀ : (1 : ℝ) - P.g₀ ≠ 0 := by have := P.hg₀1; intro hc; linarith
  -- Rewrite the overlap as a per-cell sum, collapsing the inner `Bool × Bool` sum.
  have hsum : P.chiSqOverlapG lam lam' =
      ∑ j : Fin K, (1 / (K : ℝ))
        * (1 + P.Γ * (signOf (lam j) * signOf (lam' j))) := by
    unfold chiSqOverlapG
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [obsReal_pertG_eq]
    simp only [obsReal, mhatG, ghatG, Bool.false_eq_true, if_false, if_true]
    have e1 : Δ lam (j, true) = signOf (lam j) := by simp [Δ]
    have e2 : Δ lam (j, false) = -signOf (lam j) := by simp [Δ]
    have e3 : Δ lam' (j, true) = signOf (lam' j) := by simp [Δ]
    have e4 : Δ lam' (j, false) = -signOf (lam' j) := by simp [Δ]
    simp only [e1, e2, e3, e4]
    rw [hcard]
    -- evaluate at the four concrete sign combinations
    rcases signOf_mem (lam j) with h | h <;> rcases signOf_mem (lam' j) with h' | h' <;>
      rw [h, h'] <;>
      · simp only [Γ]
        field_simp
        ring
  rw [hsum]
  have hsplit : ∀ j : Fin K,
      (1 / (K : ℝ)) * (1 + P.Γ * (signOf (lam j) * signOf (lam' j)))
      = 1 / (K : ℝ) + P.Γ / (K : ℝ) * (signOf (lam j) * signOf (lam' j)) := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  field_simp

end GenConstr

end Causalean.Estimation.MinimaxATE
