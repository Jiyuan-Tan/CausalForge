/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: χ²-overlap (second construction)

The Case-2 analogue of `VaryingCenterCase1/ChiSqOverlap.lean`.  Although the construction is non-linear
in `λ`, the *observed* masses are polynomial in `Δ` (the denominator `D` cancels in
`mλ·gλ(1)` and the propensity collapses to the affine `m₀(1 + κΔ)`).  Hence the
single-observation χ²-overlap of two perturbed laws keeps the clean form

  `overlap2 λ λ' = 1 + Σⱼ (Γⱼ/K) · signOf(λ j) signOf(λ' j)`,

with a **per-pair** coefficient (the `σσ'`-coefficient of the per-pair overlap):

  `Γⱼ = m₀ⱼ·α²·g₁ⱼ³
        + m₀ⱼ·(β/g₁ⱼ + α g₁ⱼ(1 − g₁ⱼ) − α²β g₁ⱼ)² / (1 − g₁ⱼ)
        + m₀ⱼ²·κⱼ² / (1 − m₀ⱼ)`,    `κⱼ = β/g₁ⱼ + α g₁ⱼ − α²β g₁ⱼ`.

The constant (`σ`-independent) part of each per-pair overlap is exactly `1` — the
finite-model manifestation of `E_λ qλ = p̂` — leaving only the `λ·λ'` cross term,
which is precisely the non-uniform structure the generalized `ingster_bound_general`
consumes (with `d j = Γⱼ/K`).
-/

import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.Gap

/-! # Propensity-Dominant Chi-Squared Second-Moment Overlap

This file computes the single-observation chi-squared overlap for the second
cell-varying perturbation family.  The closed form produces the per-pair coefficients
used by the non-uniform Ingster bound in the propensity-dominant lower-bound
assembly.  This overlap is a χ² second-moment quantity for the lower-bound
construction, not the causal positivity/overlap assumption.
-/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open scoped BigOperators

namespace VarConstr2

variable {K : ℕ} (P : VarConstr2 K)

/-- The per-pair χ²-overlap coefficient (second construction). -/
noncomputable def ΓV2 (j : Fin K) : ℝ :=
  P.m₀ j * P.α ^ 2 * P.g₁ j ^ 3
    + P.m₀ j * (P.β / P.g₁ j + P.α * P.g₁ j * (1 - P.g₁ j) - P.α ^ 2 * P.β * P.g₁ j) ^ 2
        / (1 - P.g₁ j)
    + P.m₀ j ^ 2 * P.κ j ^ 2 / (1 - P.m₀ j)

/-- `Γⱼ ≥ 0`. -/
theorem ΓV2_nonneg (j : Fin K) : 0 ≤ P.ΓV2 j := by
  have h1 := P.hm₀0 j; have h2 := P.hm₀1 j; have h3 := P.hg₁0 j; have h4 := P.hg₁1 j
  unfold ΓV2
  have t1 : 0 ≤ P.m₀ j * P.α ^ 2 * P.g₁ j ^ 3 := by positivity
  have t2 : 0 ≤ P.m₀ j * (P.β / P.g₁ j + P.α * P.g₁ j * (1 - P.g₁ j)
      - P.α ^ 2 * P.β * P.g₁ j) ^ 2 / (1 - P.g₁ j) := by
    apply div_nonneg (by positivity); linarith
  have t3 : 0 ≤ P.m₀ j ^ 2 * P.κ j ^ 2 / (1 - P.m₀ j) := by
    apply div_nonneg (by positivity); linarith
  linarith

/-- The single-observation χ² second-moment overlap of two perturbed laws relative to the null. -/
noncomputable def chiSqOverlapV2 (lam lam' : Fin K → Bool) : ℝ :=
  ∑ z : Obs (Fin K × Bool),
    obsReal (P.mPert2 lam) (P.gPert2 lam) z
      * obsReal (P.mPert2 lam') (P.gPert2 lam') z
      / obsReal P.mhat2 P.ghat2 z

/-- Denominator-free value of the perturbed observed mass at the four `(d, y)`. -/
theorem obsReal_pert2_eq (lam : Fin K → Bool) (x : Fin K × Bool) (d y : Bool) :
    obsReal (P.mPert2 lam) (P.gPert2 lam) (x, d, y)
      = (Fintype.card (Fin K × Bool) : ℝ)⁻¹ *
          (match d, y with
           | true, true => P.m₀ x.1 * (P.g₁ x.1 + P.α * P.g₁ x.1 ^ 2 * Δ lam x)
           | true, false => P.m₀ x.1 * (1 + P.α * P.g₁ x.1 * Δ lam x) * (P.D2 lam x - P.g₁ x.1)
           | false, true => (1 - P.m₀ x.1 - P.m₀ x.1 * P.κ x.1 * Δ lam x) * P.g₀ x.1
           | false, false =>
               (1 - P.m₀ x.1 - P.m₀ x.1 * P.κ x.1 * Δ lam x) * (1 - P.g₀ x.1)) := by
  have hDne : P.D2 lam x ≠ 0 := ne_of_gt (P.D2_pos lam x)
  have hg₁ne : P.g₁ x.1 ≠ 0 := ne_of_gt (P.hg₁0 x.1)
  have hmeq := P.mPert2_eq lam x
  unfold obsReal
  cases d <;> cases y <;>
    simp only [Bool.false_eq_true, if_false, if_true]
  · -- (false, false): (1 − mλ)·(1 − g₀)
    rw [hmeq]; simp only [gPert2, Bool.false_eq_true, if_false]
    rw [mul_assoc]; refine congrArg _ ?_; unfold κ; ring
  · -- (false, true): (1 − mλ)·g₀
    rw [hmeq]; simp only [gPert2, Bool.false_eq_true, if_false]
    rw [mul_assoc]; refine congrArg _ ?_; unfold κ; ring
  · -- (true, false): mλ·(1 − gλ(1))
    simp only [mPert2, gPert2, if_true]
    rw [mul_assoc]; refine congrArg _ ?_; field_simp
  · -- (true, true): mλ·gλ(1)
    simp only [mPert2, gPert2, if_true]
    rw [mul_assoc]; refine congrArg _ ?_; field_simp

/-- The single-observation overlap equals one plus the sum of propensity-dominant per-pair
coefficients times the paired sign agreements. -/
theorem chiSqOverlap_eq2 [NeZero K] (lam lam' : Fin K → Bool) :
    P.chiSqOverlapV2 lam lam'
      = 1 + ∑ j, (P.ΓV2 j / (K : ℝ)) * (signOf (lam j) * signOf (lam' j)) := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have hcard : (Fintype.card (Fin K × Bool) : ℝ) = 2 * K := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; push_cast; ring
  -- Rewrite the overlap as a per-pair sum.
  have hsum : P.chiSqOverlapV2 lam lam' =
      ∑ j : Fin K, (1 / (K : ℝ))
        * (1 + P.ΓV2 j * (signOf (lam j) * signOf (lam' j))) := by
    unfold chiSqOverlapV2
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [obsReal_pert2_eq, D2]
    simp only [obsReal, mhat2, ghat2, Bool.false_eq_true, if_false, if_true]
    have e1 : Δ lam (j, true) = signOf (lam j) := by simp [Δ]
    have e2 : Δ lam (j, false) = -signOf (lam j) := by simp [Δ]
    have e3 : Δ lam' (j, true) = signOf (lam' j) := by simp [Δ]
    have e4 : Δ lam' (j, false) = -signOf (lam' j) := by simp [Δ]
    simp only [e1, e2, e3, e4]
    rw [hcard]
    have hg₁ne : P.g₁ j ≠ 0 := ne_of_gt (P.hg₁0 j)
    have hm₀ne : P.m₀ j ≠ 0 := ne_of_gt (P.hm₀0 j)
    have hg₀ne : P.g₀ j ≠ 0 := ne_of_gt (P.hg₀0 j)
    have h1g₁ : (1 : ℝ) - P.g₁ j ≠ 0 := by have := P.hg₁1 j; intro hc; linarith
    have h1m₀ : (1 : ℝ) - P.m₀ j ≠ 0 := by have := P.hm₀1 j; intro hc; linarith
    have h1g₀ : (1 : ℝ) - P.g₀ j ≠ 0 := by have := P.hg₀1 j; intro hc; linarith
    rcases signOf_mem (lam j) with h | h <;> rcases signOf_mem (lam' j) with h' | h' <;>
      rw [h, h'] <;>
      · simp only [ΓV2, κ]
        field_simp
        ring
  rw [hsum]
  have hsplit : ∀ j : Fin K,
      (1 / (K : ℝ)) * (1 + P.ΓV2 j * (signOf (lam j) * signOf (lam' j)))
      = 1 / (K : ℝ) + P.ΓV2 j / (K : ℝ) * (signOf (lam j) * signOf (lam' j)) := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end VarConstr2

end Causalean.Estimation.MinimaxATE
