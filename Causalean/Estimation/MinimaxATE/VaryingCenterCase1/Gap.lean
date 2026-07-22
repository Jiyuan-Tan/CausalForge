/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the exact ATE gap (cell-varying center)

The cell-varying-center analogue of `ConstCenterGeneral/Gap.lean`. Because the center is constant
*within* each Rademacher pair, the per-pair ATE contribution is exactly
`λ`-independent (the two positions `Δ = ±s` sum to a sign-invariant value), so the
total ATE of the perturbed family is

  `ate gλ = (1/2K) Σⱼ (2 g₁ⱼ (g₁ⱼ² + αβ)/(g₁ⱼ² − β²) − 2 g₀ⱼ)`,

independent of `λ`.  The null estimate has `ate ĝ = (1/2K) Σⱼ 2(g₁ⱼ − g₀ⱼ)`, so the
gap any estimator must straddle is the **nonnegative** quantity

  `ate gλ − ate ĝ = (1/2K)·2β(α+β)·Σⱼ g₁ⱼ/(g₁ⱼ² − β²) ≥ 0`,

which reduces to `ConstCenterGeneral.ate_gapG` when `g₁, g₀` are constant.
-/

import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Construction
import Mathlib.Tactic.LinearCombination

/-! # Cell-Varying ATE Gap

This file computes the exact average-treatment-effect gap for the cell-varying-center
Rademacher construction.  Because each paired cell shares the same nuisance center, the two
positions in a pair cancel the sign dependence and yield a nonnegative separation common to all
sign vectors.

The main public lemmas are `gPertV_true_eq`, which rewrites the treated perturbed arm with a
cleared denominator; `ate_ghatV`, the ATE of the cell-varying center; `ate_gPertV`, the exact ATE
of each perturbed sign vector; `ate_gapV`, the closed form for `ate (gPertV lam) - ate ghatV`; and
`ate_gap_nonneg`, the nonnegativity of that common gap. -/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

namespace VarConstr

variable {K : ℕ} (P : VarConstr K)

/-- `g₁ⱼ² − β² > 0` since `0 ≤ β < g₁ⱼ`. -/
theorem g1sq_sub_betasq_pos (j : Fin K) : 0 < P.g₁ j ^ 2 - P.β ^ 2 := by
  have := P.hβg₁ j; have := P.hβ; have := P.hg₁0 j; nlinarith

/-- **Cleared treated arm.**  `gλ(1,x) = (g₁ x.1² + α·g₁ x.1·Δ)/(g₁ x.1 − β·Δ)`. -/
theorem gPertV_true_eq (lam : Fin K → Bool) (x : Fin K × Bool) :
    P.gPertV lam true x
      = (P.g₁ x.1 ^ 2 + P.α * P.g₁ x.1 * Δ lam x) / (P.g₁ x.1 - P.β * Δ lam x) := by
  have hg₁ne : P.g₁ x.1 ≠ 0 := ne_of_gt (P.hg₁0 x.1)
  have hden0 := P.denomV_pos lam x
  have hden : P.g₁ x.1 - P.β * Δ lam x ≠ 0 := by
    rcases Δ_mem lam x with h | h <;> rw [h] <;>
      · have := P.hβg₁ x.1; have := P.hβ; intro hc; nlinarith
  simp only [gPertV, if_true]
  rw [div_eq_div_iff hden0.ne' hden]
  field_simp

/-- The null estimate `ĝ` has ATE `(1/2K) Σⱼ 2(g₁ⱼ − g₀ⱼ)`. -/
theorem ate_ghatV :
    ate (P.ghatV (K := K))
      = (Fintype.card (Fin K × Bool) : ℝ)⁻¹ * ∑ j : Fin K, 2 * (P.g₁ j - P.g₀ j) := by
  rw [ate]
  have hpt : ∀ x : Fin K × Bool, P.ghatV true x - P.ghatV false x = P.g₁ x.1 - P.g₀ x.1 := by
    intro x; simp [ghatV]
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  change (P.g₁ j - P.g₀ j) + (P.g₁ j - P.g₀ j) = 2 * (P.g₁ j - P.g₀ j)
  ring

/-- **Per-pair contribution.**  For a fixed pair `j`, the two positions contribute
`2 g₁ⱼ(g₁ⱼ²+αβ)/(g₁ⱼ²−β²) − 2 g₀ⱼ`, regardless of the sign. -/
private theorem perPairV (lam : Fin K → Bool) (j : Fin K) :
    ((P.gPertV lam true (j, true) - P.gPertV lam false (j, true))
      + (P.gPertV lam true (j, false) - P.gPertV lam false (j, false)))
      = 2 * P.g₁ j * (P.g₁ j ^ 2 + P.α * P.β) / (P.g₁ j ^ 2 - P.β ^ 2) - 2 * P.g₀ j := by
  have hg₁0 := P.hg₁0 j
  have hg₁ne : P.g₁ j ≠ 0 := ne_of_gt hg₁0
  have d3 : P.g₁ j ^ 2 - P.β ^ 2 ≠ 0 := ne_of_gt (P.g1sq_sub_betasq_pos j)
  have hΔt : Δ lam (j, true) = signOf (lam j) := by simp [Δ]
  have hΔf : Δ lam (j, false) = - signOf (lam j) := by simp [Δ]
  have hfalse : ∀ b, P.gPertV lam false (j, b) = P.g₀ j := fun b => by simp [gPertV]
  simp only [P.gPertV_true_eq, hfalse, hΔt, hΔf]
  have hβ := P.hβ
  have hβg₁ := P.hβg₁ j
  have e1 : P.g₁ j - P.β ≠ 0 := by intro hc; nlinarith
  have e2 : P.g₁ j + P.β ≠ 0 := by intro hc; nlinarith
  rcases signOf_mem (lam j) with h | h <;> rw [h] <;>
    simp only [mul_one, mul_neg, neg_neg, sub_neg_eq_add] <;>
    · field_simp
      ring

/-- **Exact ATE of the perturbed construction** (independent of `λ`). -/
theorem ate_gPertV [NeZero K] (lam : Fin K → Bool) :
    ate (P.gPertV lam)
      = (Fintype.card (Fin K × Bool) : ℝ)⁻¹
          * ∑ j : Fin K, (2 * P.g₁ j * (P.g₁ j ^ 2 + P.α * P.β) / (P.g₁ j ^ 2 - P.β ^ 2)
              - 2 * P.g₀ j) := by
  rw [ate, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  have := P.perPairV lam j
  linarith [this]

/-- The (nonnegative) per-pair gap summand `g₁ⱼ/(g₁ⱼ²−β²)`. -/
theorem ate_gapV [NeZero K] (lam : Fin K → Bool) :
    ate (P.gPertV lam) - ate (P.ghatV (K := K))
      = (Fintype.card (Fin K × Bool) : ℝ)⁻¹
          * (2 * P.β * (P.α + P.β)) * ∑ j : Fin K, P.g₁ j / (P.g₁ j ^ 2 - P.β ^ 2) := by
  rw [P.ate_gPertV lam, P.ate_ghatV, ← mul_sub, ← Finset.sum_sub_distrib, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hg₁ne : P.g₁ j ≠ 0 := ne_of_gt (P.hg₁0 j)
  have d3 : P.g₁ j ^ 2 - P.β ^ 2 ≠ 0 := ne_of_gt (P.g1sq_sub_betasq_pos j)
  field_simp
  ring

/-- The ATE gap is nonnegative. -/
theorem ate_gap_nonneg [NeZero K] (lam : Fin K → Bool) :
    0 ≤ ate (P.gPertV lam) - ate (P.ghatV (K := K)) := by
  rw [P.ate_gapV lam]
  have hcard : (0 : ℝ) ≤ (Fintype.card (Fin K × Bool) : ℝ)⁻¹ := by positivity
  have hβ := P.hβ; have hα := P.hα
  have hsum : 0 ≤ ∑ j : Fin K, P.g₁ j / (P.g₁ j ^ 2 - P.β ^ 2) := by
    refine Finset.sum_nonneg fun j _ => ?_
    exact div_nonneg (P.hg₁0 j).le (P.g1sq_sub_betasq_pos j).le
  have h2 : (0 : ℝ) ≤ 2 * P.β * (P.α + P.β) := by positivity
  positivity

end VarConstr

end Causalean.Estimation.MinimaxATE
