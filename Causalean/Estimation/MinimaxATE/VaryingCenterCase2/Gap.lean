/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the exact ATE gap (second construction)

The Case-2 analogue of `VaryingCenterCase1/Gap.lean`.  For the propensity-dominant construction
`gλ(1,x) = g₁ⱼ / D`, `D = 1 + (β/g₁ⱼ)·Δ − αβ`, the two positions of a pair carry
`Δ = ±σ`, so summing the treated arm over the pair gives

  `g₁ⱼ/D₊ + g₁ⱼ/D₋ = 2 g₁ⱼ³ (1 − αβ) / Eⱼ`,   `Eⱼ := g₁ⱼ²(1 − αβ)² − β²`,

which is **independent of `λ`** (the `σ²` in `D₊D₋` collapses).  Hence the total
ATE of the perturbed family is `λ`-independent, and the gap any estimator must
straddle is the **nonnegative** quantity

  `ate gλ − ate ĝ = (1/2K)·2β·Σⱼ g₁ⱼ(α g₁ⱼ²(1 − αβ) + β)/Eⱼ ≥ 0`,

whose leading order is `2αβ·(1/2K)Σⱼ g₁ⱼ`, i.e. `s ≍ αβ ≍ √(εg·εm)`.
-/

import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.Construction
import Mathlib.Tactic.LinearCombination

/-! # Propensity-Dominant ATE Gap

This file computes the exact average treatment effect gap for the second
cell-varying perturbation family.  The calculation shows that the perturbed average
treatment effect is independent of the Rademacher sign vector and has the product
order required by the lower-bound construction.
-/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

namespace VarConstr2

variable {K : ℕ} (P : VarConstr2 K)

/-- `αβ ≤ 1` (a consequence of `hgU` and `g₁ⱼ > 0`). -/
theorem alphabeta_le_one (j : Fin K) : P.α * P.β ≤ 1 := by
  have := P.hgU j; have := P.ratio_nonneg j; have := P.hg₁0 j; nlinarith

/-- `g₁ⱼ(1 − αβ) − β ≥ g₁ⱼ² > 0`: clearing `hgU` by `g₁ⱼ`. -/
theorem g1_one_sub_ab_sub_beta (j : Fin K) :
    P.g₁ j ^ 2 ≤ P.g₁ j * (1 - P.α * P.β) - P.β := by
  have hg1 := P.hg₁0 j
  have hh : (P.β / P.g₁ j) * P.g₁ j = P.β := div_mul_cancel₀ _ (ne_of_gt hg1)
  have hkey := P.hgU j
  -- multiply hgU by g₁ⱼ > 0
  have : (P.g₁ j + P.β / P.g₁ j + P.α * P.β) * P.g₁ j ≤ 1 * P.g₁ j :=
    mul_le_mul_of_nonneg_right hkey hg1.le
  rw [add_mul, add_mul] at this
  rw [hh] at this
  nlinarith [this]

/-- The pair denominator `Eⱼ = g₁ⱼ²(1 − αβ)² − β² > 0`. -/
theorem denomE_pos (j : Fin K) : 0 < P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2 := by
  have hg1 := P.hg₁0 j
  have hlin := P.g1_one_sub_ab_sub_beta j
  have hβ := P.hβ
  -- E = (g₁(1−αβ) − β)(g₁(1−αβ) + β); first factor ≥ g₁² > 0, second ≥ β ≥ 0
  have h1 : 0 < P.g₁ j * (1 - P.α * P.β) - P.β := by nlinarith [hg1]
  have h2 : 0 < P.g₁ j * (1 - P.α * P.β) + P.β := by nlinarith [hg1]
  nlinarith [mul_pos h1 h2]

/-- **Cleared treated arm.**  `gλ(1,x) = g₁ x.1² / (g₁ x.1·(1 − αβ) + β·Δ)` — no
nested fractions, so `field_simp` can clear it given the (positive) denominator. -/
theorem gPert2_true_eq2 (lam : Fin K → Bool) (x : Fin K × Bool) :
    P.gPert2 lam true x
      = P.g₁ x.1 ^ 2 / (P.g₁ x.1 * (1 - P.α * P.β) + P.β * Δ lam x) := by
  have hg₁ne : P.g₁ x.1 ≠ 0 := ne_of_gt (P.hg₁0 x.1)
  have hD := P.D2_pos lam x
  have hdc : P.g₁ x.1 * (1 - P.α * P.β) + P.β * Δ lam x = P.g₁ x.1 * P.D2 lam x := by
    unfold D2; field_simp; ring
  simp only [gPert2, if_true]
  rw [hdc, sq, mul_div_mul_left _ _ hg₁ne]

/-- The cleared denominator `g₁ⱼ(1 − αβ) + β·σ` is positive. -/
theorem clearedDenom_pos (j : Fin K) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    0 < P.g₁ j * (1 - P.α * P.β) + P.β * σ := by
  have hg1 := P.hg₁0 j
  have hlin := P.g1_one_sub_ab_sub_beta j
  have hβ := P.hβ
  rcases hσ with h | h
  · rw [h]; nlinarith [hg1]
  · rw [h]; nlinarith [hg1]

/-- The null estimate `ĝ` has ATE `(1/2K) Σⱼ 2(g₁ⱼ − g₀ⱼ)`. -/
theorem ate_ghat2 :
    ate (P.ghat2 (K := K))
      = (Fintype.card (Fin K × Bool) : ℝ)⁻¹ * ∑ j : Fin K, 2 * (P.g₁ j - P.g₀ j) := by
  rw [ate]
  have hpt : ∀ x : Fin K × Bool, P.ghat2 true x - P.ghat2 false x = P.g₁ x.1 - P.g₀ x.1 := by
    intro x; simp [ghat2]
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  change (P.g₁ j - P.g₀ j) + (P.g₁ j - P.g₀ j) = 2 * (P.g₁ j - P.g₀ j)
  ring

/-- **Per-pair contribution.**  For a fixed pair `j`, the two positions contribute
`2 g₁ⱼ³(1 − αβ)/Eⱼ − 2 g₀ⱼ`, regardless of the sign. -/
private theorem perPair2 (lam : Fin K → Bool) (j : Fin K) :
    ((P.gPert2 lam true (j, true) - P.gPert2 lam false (j, true))
      + (P.gPert2 lam true (j, false) - P.gPert2 lam false (j, false)))
      = 2 * P.g₁ j ^ 3 * (1 - P.α * P.β)
          / (P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2) - 2 * P.g₀ j := by
  have hg1 := P.hg₁0 j
  have hg₁ne : P.g₁ j ≠ 0 := ne_of_gt hg1
  have hE := P.denomE_pos j
  have hEne : P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2 ≠ 0 := ne_of_gt hE
  have hΔt : Δ lam (j, true) = signOf (lam j) := by simp [Δ]
  have hΔf : Δ lam (j, false) = - signOf (lam j) := by simp [Δ]
  have hfalse : ∀ b, P.gPert2 lam false (j, b) = P.g₀ j := fun b => by simp [gPert2]
  have htrue : ∀ b, P.gPert2 lam true (j, b)
      = P.g₁ j ^ 2 / (P.g₁ j * (1 - P.α * P.β) + P.β * Δ lam (j, b)) := fun b =>
    P.gPert2_true_eq2 lam (j, b)
  simp only [htrue, hfalse, hΔt, hΔf]
  have hσ : signOf (lam j) ^ 2 = 1 := signOf_sq _
  -- cleared denominators positive (hence nonzero) for both positions
  have hd1 : P.g₁ j * (1 - P.α * P.β) + P.β * signOf (lam j) ≠ 0 :=
    ne_of_gt (P.clearedDenom_pos j _ (signOf_mem (lam j)))
  have hd2 : P.g₁ j * (1 - P.α * P.β) + P.β * (- signOf (lam j)) ≠ 0 := by
    refine ne_of_gt (P.clearedDenom_pos j (- signOf (lam j)) ?_)
    rcases signOf_mem (lam j) with h | h <;> rw [h] <;> simp
  -- the two cleared denominators multiply to `E` (using `σ² = 1`)
  have hprod : (P.g₁ j * (1 - P.α * P.β) + P.β * signOf (lam j))
        * (P.g₁ j * (1 - P.α * P.β) + P.β * (- signOf (lam j)))
        = P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2 := by
    linear_combination (-P.β ^ 2) * hσ
  -- so the two treated arms sum to `2 g₁³(1−αβ)/E`
  have key : P.g₁ j ^ 2 / (P.g₁ j * (1 - P.α * P.β) + P.β * signOf (lam j))
        + P.g₁ j ^ 2 / (P.g₁ j * (1 - P.α * P.β) + P.β * (- signOf (lam j)))
        = 2 * P.g₁ j ^ 3 * (1 - P.α * P.β)
            / (P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2) := by
    rw [div_add_div _ _ hd1 hd2, hprod,
      show P.g₁ j ^ 2 * (P.g₁ j * (1 - P.α * P.β) + P.β * (- signOf (lam j)))
          + (P.g₁ j * (1 - P.α * P.β) + P.β * signOf (lam j)) * P.g₁ j ^ 2
          = 2 * P.g₁ j ^ 3 * (1 - P.α * P.β) from by ring]
  linarith [key]

/-- **Exact ATE of the perturbed construction** (independent of `λ`). -/
theorem ate_gPert2 [NeZero K] (lam : Fin K → Bool) :
    ate (P.gPert2 lam)
      = (Fintype.card (Fin K × Bool) : ℝ)⁻¹
          * ∑ j : Fin K, (2 * P.g₁ j ^ 3 * (1 - P.α * P.β)
              / (P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2) - 2 * P.g₀ j) := by
  rw [ate, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  have := P.perPair2 lam j
  linarith [this]

/-- The ATE gap, written as `(1/2K)·2β·Σⱼ g₁ⱼ(α g₁ⱼ²(1−αβ) + β)/Eⱼ`. -/
theorem ate_gap2 [NeZero K] (lam : Fin K → Bool) :
    ate (P.gPert2 lam) - ate (P.ghat2 (K := K))
      = (Fintype.card (Fin K × Bool) : ℝ)⁻¹ * (2 * P.β)
          * ∑ j : Fin K, P.g₁ j * (P.α * P.g₁ j ^ 2 * (1 - P.α * P.β) + P.β)
              / (P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2) := by
  rw [P.ate_gPert2 lam, P.ate_ghat2, ← mul_sub, ← Finset.sum_sub_distrib, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hg₁ne : P.g₁ j ≠ 0 := ne_of_gt (P.hg₁0 j)
  have hE := P.denomE_pos j
  have hEne : P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2 ≠ 0 := ne_of_gt hE
  field_simp
  ring

/-- The ATE gap is nonnegative. -/
theorem ate_gap2_nonneg [NeZero K] (lam : Fin K → Bool) :
    0 ≤ ate (P.gPert2 lam) - ate (P.ghat2 (K := K)) := by
  rw [P.ate_gap2 lam]
  have hcard : (0 : ℝ) ≤ (Fintype.card (Fin K × Bool) : ℝ)⁻¹ := by positivity
  have hβ := P.hβ; have hα := P.hα
  have h2β : (0 : ℝ) ≤ 2 * P.β := by positivity
  have hsum : 0 ≤ ∑ j : Fin K, P.g₁ j * (P.α * P.g₁ j ^ 2 * (1 - P.α * P.β) + P.β)
      / (P.g₁ j ^ 2 * (1 - P.α * P.β) ^ 2 - P.β ^ 2) := by
    refine Finset.sum_nonneg fun j _ => ?_
    have hg1 := P.hg₁0 j
    have hE := P.denomE_pos j
    have hab := P.alphabeta_le_one j
    have hnum : 0 ≤ P.g₁ j * (P.α * P.g₁ j ^ 2 * (1 - P.α * P.β) + P.β) := by
      have : 0 ≤ P.α * P.g₁ j ^ 2 * (1 - P.α * P.β) := by
        apply mul_nonneg (by positivity); linarith
      have : 0 ≤ P.α * P.g₁ j ^ 2 * (1 - P.α * P.β) + P.β := by linarith
      exact mul_nonneg hg1.le this
    exact div_nonneg hnum hE.le
  positivity

end VarConstr2

end Causalean.Estimation.MinimaxATE
