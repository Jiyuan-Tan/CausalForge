/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: class membership (second construction)

The Case-2 analogue of `VaryingCenterCase1/Membership.lean`, with the two nuisance roles
**swapped**.  Here the *propensity* deviation is the large one and the *outcome*
deviation is the small one:

* `mλ − m̂ = m₀ⱼ·κⱼ·Δ` is **exact** (`Δ² = 1`), so the propensity squared `L²` error
  is exactly `(m₀ⱼ·κⱼ)²`, controlled by the budget `(m₀ⱼ·κⱼ)² ≤ εm`, where
  `κⱼ = β/g₁ⱼ + α·g₁ⱼ − α²·β·g₁ⱼ = O(α + β)` carries the `√εm` weight;
* `gλ(1) − ĝ(1) = β·(α g₁ⱼ − Δ)/D` is `O(β)`, controlled by the worst-case (`Δ = −1`)
  budget `β²·(α g₁ⱼ + 1)²/(1 − β/g₁ⱼ − αβ)² ≤ εg`, carrying the `√εg` weight.

This is exactly the regime `εm > εg`: the propensity budget dominates.  Each
per-pair bound is *sufficient* (an average of terms `≤ ε` is `≤ ε`), so the
construction lands in `ℱ(εg, εm)`.
-/

import Causalean.Estimation.MinimaxATE.Reduction.Bump
import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.Gap

/-! # Propensity-Dominant Class Membership

This file proves that the second cell-varying perturbation family belongs to the
finite structure-agnostic nuisance class when the propensity and outcome-regression
budgets hold.  The estimates cover the regime in which the propensity perturbation
is the larger error component.
-/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

namespace VarConstr2

variable {K : ℕ} (P : VarConstr2 K)

/-- The propensity perturbation's squared `L²` error is exactly the average of
`(m₀ⱼ·κⱼ)²`, hence `≤ εm` whenever every pair satisfies `(m₀ⱼ·κⱼ)² ≤ εm`. -/
theorem l2sq_mPert2_le [NeZero K] {εm : ℝ}
    (hm : ∀ j, (P.m₀ j * P.κ j) ^ 2 ≤ εm) (lam : Fin K → Bool) :
    l2sq (P.mPert2 lam) (P.mhat2 (K := K)) ≤ εm := by
  set C := Fin K × Bool
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm : ∀ x : C, (P.mPert2 lam x - P.mhat2 x) ^ 2 ≤ εm := by
    intro x
    have hdiff : P.mPert2 lam x - P.mhat2 x = (P.m₀ x.1 * P.κ x.1) * Δ lam x := by
      rw [P.mPert2_eq lam x]; simp only [mhat2]; ring
    rw [hdiff, mul_pow, Δ_sq lam x, mul_one]
    exact hm x.1
  rw [l2sq]
  have hsum : ∑ x : C, (P.mPert2 lam x - P.mhat2 x) ^ 2 ≤ ∑ _x : C, εm :=
    Finset.sum_le_sum (fun x _ => hterm x)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc (Fintype.card C : ℝ)⁻¹ * ∑ x : C, (P.mPert2 lam x - P.mhat2 x) ^ 2
      ≤ (Fintype.card C : ℝ)⁻¹ * ((Fintype.card C : ℝ) * εm) := by
        apply mul_le_mul_of_nonneg_left hsum; positivity
    _ = εm := by field_simp

/-- The control outcome arm is unchanged, so its `L²` error is `0`. -/
theorem l2sq_gPert2_false (lam : Fin K → Bool) :
    l2sq (P.gPert2 lam false) (P.ghat2 false) = 0 := by
  have h : P.gPert2 lam false = P.ghat2 false := by
    funext x; simp only [gPert2, ghat2, Bool.false_eq_true, if_false]
  rw [h, l2sq_self]

/-- The treated arm's pointwise deviation from `ĝ(1,x) = g₁ x.1` is
`β·(α g₁ x.1 − Δ)/D`. -/
theorem gPert2_true_sub (lam : Fin K → Bool) (x : Fin K × Bool) :
    P.gPert2 lam true x - P.g₁ x.1
      = P.β * (P.α * P.g₁ x.1 - Δ lam x) / P.D2 lam x := by
  have hg₁ne : P.g₁ x.1 ≠ 0 := ne_of_gt (P.hg₁0 x.1)
  have hd := P.D2_pos lam x
  simp only [gPert2, if_true]
  rw [eq_div_iff (ne_of_gt hd), sub_mul, div_mul_cancel₀ _ (ne_of_gt hd)]
  unfold D2
  field_simp
  ring

/-- The treated arm's squared `L²` error is `≤ εg` whenever every pair satisfies
`β²·(α g₁ⱼ + 1)²/(1 − β/g₁ⱼ − αβ)² ≤ εg`. -/
theorem l2sq_gPert2_true_le [NeZero K] {εg : ℝ}
    (hg : ∀ j, P.β ^ 2 * (P.α * P.g₁ j + 1) ^ 2
        / (1 - P.β / P.g₁ j - P.α * P.β) ^ 2 ≤ εg) (lam : Fin K → Bool) :
    l2sq (P.gPert2 lam true) (P.ghat2 true) ≤ εg := by
  set C := Fin K × Bool
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm : ∀ x : C, (P.gPert2 lam true x - P.ghat2 true x) ^ 2 ≤ εg := by
    intro x
    have hghat : P.ghat2 true x = P.g₁ x.1 := by simp [ghat2]
    have hg10 := P.hg₁0 x.1
    have hα := P.hα; have hβ := P.hβ
    -- D_min = 1 − β/g₁ − αβ is positive (and ≤ D)
    have hDmin : 0 < 1 - P.β / P.g₁ x.1 - P.α * P.β := by
      have hgU := P.hgU x.1; have hr := P.ratio_nonneg x.1; nlinarith
    have hDmin2 : 0 < (1 - P.β / P.g₁ x.1 - P.α * P.β) ^ 2 := by positivity
    have hD := P.D2_pos lam x
    have hD2 : 0 < (P.D2 lam x) ^ 2 := by positivity
    rw [hghat, P.gPert2_true_sub lam x]
    have hsq : (P.β * (P.α * P.g₁ x.1 - Δ lam x) / P.D2 lam x) ^ 2
        = P.β ^ 2 * (P.α * P.g₁ x.1 - Δ lam x) ^ 2 / (P.D2 lam x) ^ 2 := by
      rw [div_pow, mul_pow]
    rw [hsq]
    refine le_trans ?_ (hg x.1)
    -- numerator: (α g₁ − Δ)² ≤ (α g₁ + 1)²; denominator: D² ≥ D_min²
    have hnum : P.β ^ 2 * (P.α * P.g₁ x.1 - Δ lam x) ^ 2
        ≤ P.β ^ 2 * (P.α * P.g₁ x.1 + 1) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hαg : 0 ≤ P.α * P.g₁ x.1 := mul_nonneg hα hg10.le
      rcases Δ_mem lam x with h | h
      · rw [h]; nlinarith
      · rw [h]; nlinarith
    have hden : (1 - P.β / P.g₁ x.1 - P.α * P.β) ^ 2 ≤ (P.D2 lam x) ^ 2 := by
      unfold D2
      have hr := P.ratio_nonneg x.1
      rcases Δ_mem lam x with h | h
      · rw [h]; nlinarith [hDmin]
      · rw [h]; nlinarith [hDmin]
    calc P.β ^ 2 * (P.α * P.g₁ x.1 - Δ lam x) ^ 2 / (P.D2 lam x) ^ 2
        ≤ P.β ^ 2 * (P.α * P.g₁ x.1 + 1) ^ 2 / (P.D2 lam x) ^ 2 := by
          exact (div_le_div_iff_of_pos_right hD2).mpr hnum
      _ ≤ P.β ^ 2 * (P.α * P.g₁ x.1 + 1) ^ 2 / (1 - P.β / P.g₁ x.1 - P.α * P.β) ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) hDmin2 hden
  rw [l2sq]
  have hsum : ∑ x : C, (P.gPert2 lam true x - P.ghat2 true x) ^ 2 ≤ ∑ _x : C, εg :=
    Finset.sum_le_sum (fun x _ => hterm x)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc (Fintype.card C : ℝ)⁻¹ * ∑ x : C, (P.gPert2 lam true x - P.ghat2 true x) ^ 2
      ≤ (Fintype.card C : ℝ)⁻¹ * ((Fintype.card C : ℝ) * εg) := by
        apply mul_le_mul_of_nonneg_left hsum; positivity
    _ = εg := by field_simp

/-- **Class membership.**  With the (propensity-dominant) per-pair budgets satisfied,
the perturbed DGP `(mλ, gλ)` lies in the structure-agnostic class `ℱ(εg, εm)` around
the cell-varying center `(m̂, ĝ)`. -/
theorem inClass2 [NeZero K] {εg εm : ℝ}
    (hm : ∀ j, (P.m₀ j * P.κ j) ^ 2 ≤ εm)
    (hg : ∀ j, P.β ^ 2 * (P.α * P.g₁ j + 1) ^ 2
        / (1 - P.β / P.g₁ j - P.α * P.β) ^ 2 ≤ εg)
    (hεg : 0 ≤ εg) (lam : Fin K → Bool) :
    InClass (P.mhat2 (K := K)) P.ghat2 εg εm (P.mPert2 lam) (P.gPert2 lam) := by
  refine ⟨P.validDGP_pert2 lam, ?_, ?_⟩
  · intro d
    cases d with
    | false => rw [P.l2sq_gPert2_false lam]; exact hεg
    | true => exact P.l2sq_gPert2_true_le hg lam
  · exact P.l2sq_mPert2_le hm lam

end VarConstr2

end Causalean.Estimation.MinimaxATE
