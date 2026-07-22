/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: χ²-overlap (cell-varying center)

The cell-varying-center analogue of `ConstCenterGeneral/ChiSqOverlap.lean`. Around a center that is
constant within each pair but varies across pairs, the single-observation χ²-overlap
of two perturbed laws keeps the clean form

  `chiSqOverlapV λ λ' = 1 + Σⱼ (Γⱼ/K) · signOf(λ j) signOf(λ' j)`,

with a **per-pair** coefficient

  `Γⱼ = m₀ⱼ·α²/g₁ⱼ + m₀ⱼ·(α + β/g₁ⱼ)²/(1 − g₁ⱼ) + m₀ⱼ²·β²/(g₁ⱼ²·(1 − m₀ⱼ))`.

The linear-in-`Δ` terms cancel within each pair (the center is shared by the two
positions), leaving only the `λ·λ'` cross term — exactly the non-uniform structure
the generalized `ingster_bound_general` consumes (with `d j = Γⱼ/K`).
-/

import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Gap

/-! # Cell-Varying Chi-Squared Second-Moment Overlap

This file computes the single-observation chi-squared overlap for the first
cell-varying perturbation family in the structure-agnostic average treatment effect
lower bound.  The result isolates the per-pair overlap coefficient that feeds the
non-uniform Ingster inequality.  This overlap is a χ² second-moment quantity for
the lower-bound construction, not the causal positivity/overlap assumption.

The declaration `ΓV` is the nonnegative per-pair coefficient proved by `ΓV_nonneg`.  The quantity
`chiSqOverlapV lam lam'` is the finite second moment of two perturbed observation laws relative to
the null.  The algebraic lemmas `obsReal_pertV_eq` and `chiSqOverlap_eqV` compute that overlap as
`1 + sum_j (ΓV j / K) * signOf (lam j) * signOf (lam' j)`, which is the form consumed by
`ingster_bound_general`. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open scoped BigOperators

namespace VarConstr

variable {K : ℕ} (P : VarConstr K)

/-- The per-pair χ²-overlap coefficient. -/
noncomputable def ΓV (j : Fin K) : ℝ :=
  P.m₀ j * P.α ^ 2 / P.g₁ j
    + P.m₀ j * (P.α + P.β / P.g₁ j) ^ 2 / (1 - P.g₁ j)
    + P.m₀ j ^ 2 * P.β ^ 2 / (P.g₁ j ^ 2 * (1 - P.m₀ j))

/-- `Γⱼ ≥ 0`. -/
theorem ΓV_nonneg (j : Fin K) : 0 ≤ P.ΓV j := by
  have h1 := P.hm₀0 j; have h2 := P.hm₀1 j; have h3 := P.hg₁0 j; have h4 := P.hg₁1 j
  unfold ΓV
  have t1 : 0 ≤ P.m₀ j * P.α ^ 2 / P.g₁ j := by positivity
  have t2 : 0 ≤ P.m₀ j * (P.α + P.β / P.g₁ j) ^ 2 / (1 - P.g₁ j) := by
    apply div_nonneg (by positivity); linarith
  have t3 : 0 ≤ P.m₀ j ^ 2 * P.β ^ 2 / (P.g₁ j ^ 2 * (1 - P.m₀ j)) := by
    apply div_nonneg (by positivity)
    have : 0 < 1 - P.m₀ j := by linarith
    positivity
  linarith

/-- The single-observation χ² second-moment overlap of two perturbed laws relative to the null. -/
noncomputable def chiSqOverlapV (lam lam' : Fin K → Bool) : ℝ :=
  ∑ z : Obs (Fin K × Bool),
    obsReal (P.mPertV lam) (P.gPertV lam) z
      * obsReal (P.mPertV lam') (P.gPertV lam') z
      / obsReal P.mhatV P.ghatV z

/-- Denominator-free value of the perturbed observed mass at the four `(d, y)`. -/
theorem obsReal_pertV_eq (lam : Fin K → Bool) (x : Fin K × Bool) (d y : Bool) :
    obsReal (P.mPertV lam) (P.gPertV lam) (x, d, y)
      = (Fintype.card (Fin K × Bool) : ℝ)⁻¹ *
          (match d, y with
           | true, true => P.m₀ x.1 * (P.g₁ x.1 + P.α * Δ lam x)
           | true, false => P.m₀ x.1 * ((1 - P.g₁ x.1) - (P.α + P.β / P.g₁ x.1) * Δ lam x)
           | false, true => (1 - P.m₀ x.1 + P.m₀ x.1 * (P.β / P.g₁ x.1) * Δ lam x) * P.g₀ x.1
           | false, false =>
               (1 - P.m₀ x.1 + P.m₀ x.1 * (P.β / P.g₁ x.1) * Δ lam x) * (1 - P.g₀ x.1)) := by
  have hd : (1 - (P.β / P.g₁ x.1) * Δ lam x) ≠ 0 := (P.denomV_pos lam x).ne'
  have hg₁ne : P.g₁ x.1 ≠ 0 := ne_of_gt (P.hg₁0 x.1)
  have hden : P.g₁ x.1 - P.β * Δ lam x ≠ 0 := by
    rcases Δ_mem lam x with h | h <;> rw [h] <;>
      · have := P.hβg₁ x.1; have := P.hβ; intro hc; nlinarith
  unfold obsReal mPertV gPertV
  cases d <;> cases y <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;>
    rw [mul_assoc] <;> refine congrArg _ ?_ <;> field_simp <;> ring

/-- The single-observation overlap equals one plus the sum of per-pair coefficients times
the paired sign agreements. -/
theorem chiSqOverlap_eqV [NeZero K] (lam lam' : Fin K → Bool) :
    P.chiSqOverlapV lam lam'
      = 1 + ∑ j, (P.ΓV j / (K : ℝ)) * (signOf (lam j) * signOf (lam' j)) := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have hcard : (Fintype.card (Fin K × Bool) : ℝ) = 2 * K := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; push_cast; ring
  -- Rewrite the overlap as a per-pair sum.
  have hsum : P.chiSqOverlapV lam lam' =
      ∑ j : Fin K, (1 / (K : ℝ))
        * (1 + P.ΓV j * (signOf (lam j) * signOf (lam' j))) := by
    unfold chiSqOverlapV
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [obsReal_pertV_eq]
    simp only [obsReal, mhatV, ghatV, Bool.false_eq_true, if_false, if_true]
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
      · simp only [ΓV]
        field_simp
        ring
  rw [hsum]
  have hsplit : ∀ j : Fin K,
      (1 / (K : ℝ)) * (1 + P.ΓV j * (signOf (lam j) * signOf (lam' j)))
      = 1 / (K : ℝ) + P.ΓV j / (K : ℝ) * (signOf (lam j) * signOf (lam' j)) := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end VarConstr

end Causalean.Estimation.MinimaxATE
