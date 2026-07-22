/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: class membership of the perturbed DGP

This file proves that the explicit Case-1 construction of `Construction.lean` lands
inside the structure-agnostic nuisance class `ℱ(εg, εm)` of `Model.lean`, once the
two scalars `α, β` respect the error budgets.  Concretely, around the centered
estimates `m̂ ≡ 1/2`, `ĝ ≡ 1/2`:

* the propensity perturbation `mλ = 1/2 − β·Δ` has **exact** squared `L²` size `β²`
  (a Rademacher bump of magnitude `β`, via `l2sq_bump`);
* the control arm `gλ(0,·) = 1/2` is unchanged, so its `L²` error is `0`;
* the treated arm `gλ(1,·)` deviates from `1/2` by `(α+β)·Δ/(1 − 2β·Δ)`, whose
  squared `L²` error is bounded uniformly by `(α+β)²/(1 − 2β)²`.

The capstone `inClass_perturbed` packages these into `InClass m̂ ĝ εg εm mλ gλ`
whenever `β² ≤ εm` and `(α+β)²/(1 − 2β)² ≤ εg`.
-/

import Causalean.Estimation.MinimaxATE.Reduction.Bump
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Construction

/-! # Base Class Membership

This file proves that the base paired-cell perturbation family lies inside the
structure-agnostic nuisance class when the propensity and outcome-regression error budgets are
satisfied. The supporting estimates are `l2sq_mPerturbed` for the exact propensity error,
`l2sq_gPerturbed_false` for the unchanged control arm, `gPerturbed_true_sub_half` for the
treated-arm pointwise deviation, and `l2sq_gPerturbed_true_le` for the treated-arm error bound.

The capstone `inClass_perturbed` connects the explicit construction to the finite minimax
lower-bound framework by producing an `InClass` witness under the stated budgets.
-/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

variable {K : ℕ} {α β : ℝ}

/-- The propensity perturbation has exact squared `L²` size `β²`: it is a Rademacher
bump of magnitude `β` on `Δ`. -/
theorem l2sq_mPerturbed [NeZero K] (lam : Fin K → Bool) :
    l2sq (mPerturbed β lam) mhat = β ^ 2 := by
  have hbump : (mPerturbed β lam)
      = (fun x => mhat x + β * (-(Δ lam x))) := by
    funext x
    simp only [mPerturbed, mhat]
    ring
  rw [hbump]
  exact l2sq_bump mhat β (fun x => -(Δ lam x)) (fun x => by
    have : (-(Δ lam x)) ^ 2 = (Δ lam x) ^ 2 := by ring
    rw [this, Δ_sq])

/-- The control outcome arm is unchanged (`gλ(0,·) = 1/2 = ĝ(0,·)`), so its `L²`
error is `0`. -/
theorem l2sq_gPerturbed_false (lam : Fin K → Bool) :
    l2sq (gPerturbed α β lam false) (ghat false) = 0 := by
  have h : gPerturbed α β lam false = ghat false := by
    funext x
    simp only [gPerturbed, ghat, Bool.false_eq_true, if_false]
  rw [h, l2sq_self]

/-- The treated outcome arm: its pointwise deviation from `ĝ(1) = 1/2` is
`(α+β)·Δ/(1 − 2β·Δ)`. -/
theorem gPerturbed_true_sub_half (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (lam : Fin K → Bool) (x : Fin K × Bool) :
    gPerturbed α β lam true x - 1 / 2 = (α + β) * Δ lam x / (1 - 2 * β * Δ lam x) := by
  have hd := denom_pos hβ hαβ hα lam x
  have hd0 : (1 - 2 * β * Δ lam x) ≠ 0 := ne_of_gt hd
  simp only [gPerturbed, if_true]
  rw [div_sub', div_eq_div_iff hd0 hd0]
  · ring
  · exact hd0

/-- Uniform bound on the treated arm's squared `L²` error: every pointwise term is
`≤ (α+β)²/(1 − 2β)²`, so the average is too. -/
theorem l2sq_gPerturbed_true_le [NeZero K] (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + 2 * β ≤ 1 / 2) (lam : Fin K → Bool) :
    l2sq (gPerturbed α β lam true) (ghat true) ≤ (α + β) ^ 2 / (1 - 2 * β) ^ 2 := by
  have hβ4 : β ≤ 1 / 4 := by linarith
  set C := Fin K × Bool
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hCpos : (0 : ℝ) < (Fintype.card C : ℝ) := by
    rcases (Fintype.card C).eq_zero_or_pos with h | h
    · exact absurd (Nat.cast_eq_zero.mpr h) hC
    · exact_mod_cast h
  -- denominator `1 − 2β` is positive
  have hden : (0 : ℝ) < 1 - 2 * β := by linarith
  have hden2 : (0 : ℝ) < (1 - 2 * β) ^ 2 := by positivity
  -- each summand equals `(α+β)²/(1 − 2β·Δ)²` and is bounded by `(α+β)²/(1 − 2β)²`
  have hterm : ∀ x : C,
      (gPerturbed α β lam true x - ghat true x) ^ 2
        ≤ (α + β) ^ 2 / (1 - 2 * β) ^ 2 := by
    intro x
    have hghat : ghat true x = (1 / 2 : ℝ) := by simp [ghat]
    rw [hghat, gPerturbed_true_sub_half hα hβ hαβ lam x]
    have hd := denom_pos hβ hαβ hα lam x
    have hdne : (1 - 2 * β * Δ lam x) ≠ 0 := ne_of_gt hd
    -- rewrite the squared term using `Δ² = 1`
    have hsq : ((α + β) * Δ lam x / (1 - 2 * β * Δ lam x)) ^ 2
        = (α + β) ^ 2 / (1 - 2 * β * Δ lam x) ^ 2 := by
      rw [div_pow, mul_pow, Δ_sq, mul_one]
    rw [hsq]
    -- compare denominators: `(1 − 2β)² ≤ (1 − 2β·Δ)²`
    have hdenΔ : (0 : ℝ) < (1 - 2 * β * Δ lam x) ^ 2 := by positivity
    have hcmp : (1 - 2 * β) ^ 2 ≤ (1 - 2 * β * Δ lam x) ^ 2 := by
      rcases Δ_mem lam x with h | h
      · rw [h]; nlinarith
      · rw [h]; nlinarith [hβ]
    apply div_le_div_of_nonneg_left (by positivity) hden2 hcmp
  -- average of bounded terms is bounded
  rw [l2sq]
  have hsum : ∑ x : C, (gPerturbed α β lam true x - ghat true x) ^ 2
      ≤ ∑ _x : C, (α + β) ^ 2 / (1 - 2 * β) ^ 2 :=
    Finset.sum_le_sum (fun x _ => hterm x)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc (Fintype.card C : ℝ)⁻¹ * ∑ x : C, (gPerturbed α β lam true x - ghat true x) ^ 2
      ≤ (Fintype.card C : ℝ)⁻¹ * ((Fintype.card C : ℝ) * ((α + β) ^ 2 / (1 - 2 * β) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hsum
        positivity
    _ = (α + β) ^ 2 / (1 - 2 * β) ^ 2 := by
        field_simp

/-- **Class membership.**  With the budgets `β² ≤ εm` and `(α+β)²/(1 − 2β)² ≤ εg`
satisfied, the perturbed DGP `(mλ, gλ)` lies in the structure-agnostic class
`ℱ(εg, εm)` around the centered estimates `(m̂, ĝ)`. -/
theorem inClass_perturbed [NeZero K] {εg εm : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (hm : β ^ 2 ≤ εm) (hg : (α + β) ^ 2 / (1 - 2 * β) ^ 2 ≤ εg)
    (lam : Fin K → Bool) :
    InClass mhat ghat εg εm (mPerturbed β lam) (gPerturbed α β lam) := by
  refine ⟨validDGP_perturbed hα hβ hαβ lam, ?_, ?_⟩
  · intro d
    cases d with
    | false =>
        rw [l2sq_gPerturbed_false lam]
        -- `0 ≤ εg` from `hg` (LHS is nonneg)
        have hnn : (0 : ℝ) ≤ (α + β) ^ 2 / (1 - 2 * β) ^ 2 := by positivity
        linarith
    | true =>
        exact le_trans (l2sq_gPerturbed_true_le hα hβ hαβ lam) hg
  · rw [l2sq_mPerturbed lam]
    exact hm

end Causalean.Estimation.MinimaxATE
