/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: single-observation mass and χ²-overlap

This file records two exact finite computations for the construction of
`Construction.lean`:

* `obsLaw_real_singleton` — the single-observation law assigns to each point
  `z` exactly the real mass `obsReal m g z`;
* `chiSqOverlap_eq` — the closed form of the single-observation χ²-overlap of two
  perturbed laws (indexed by sign vectors `λ, λ'`) relative to the null:

    `chiSqOverlap α β λ λ' = 1 + (2 (α² + 2αβ + 3β²) / K) Σ_j signOf(λ j) signOf(λ' j)`.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Construction

/-! # Base Chi-Squared Second-Moment Overlap

This file computes the singleton probabilities and the single-observation chi-squared overlap
for the base paired-cell perturbation family. The helper `obsLaw_real_singleton` identifies
the real mass of a singleton observation, `chiSqOverlap` defines the one-observation
second-moment overlap, and `obsReal_perturbed_eq` gives a denominator-free formula for each
perturbed observed-data mass.

The main theorem `chiSqOverlap_eq` proves the closed form used by the Ingster
indistinguishability argument. "Overlap" here means the χ² second-moment overlap between two
perturbed observed-data laws relative to the null; it is not the causal positivity/overlap
assumption.
-/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open scoped BigOperators

/-- The one-observation law assigns each observed point exactly its finite observed-data mass. -/
theorem obsLaw_real_singleton {C : Type*} [Fintype C] [Nonempty C] [MeasurableSpace C]
    [MeasurableSingletonClass C] {m : C → ℝ} {g : Bool → C → ℝ} (hv : ValidDGP m g)
    (z : Obs C) : (obsLaw hv).real {z} = obsReal m g z := by
  rw [measureReal_def, obsLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z),
    obsPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (obsReal_nonneg hv z)]

variable {K : ℕ} {α β : ℝ}

/-- The one-observation χ² second-moment overlap of two perturbed laws relative to the null. -/
noncomputable def chiSqOverlap (α β : ℝ) (lam lam' : Fin K → Bool) : ℝ :=
  ∑ z : Obs (Fin K × Bool),
    obsReal (mPerturbed β lam) (gPerturbed α β lam) z
      * obsReal (mPerturbed β lam') (gPerturbed α β lam') z
      / obsReal mhat ghat z

/-- The perturbed observed-data mass has an explicit denominator-free value at every
treatment-outcome cell.

In the treated arm, the outcome-regression denominator cancels against the perturbed propensity. -/
theorem obsReal_perturbed_eq (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (lam : Fin K → Bool) (x : Fin K × Bool) (d y : Bool) :
    obsReal (mPerturbed β lam) (gPerturbed α β lam) (x, d, y)
      = (Fintype.card (Fin K × Bool) : ℝ)⁻¹ *
          (match d, y with
           | true, true => (1 / 2 + α * Δ lam x) / 2
           | true, false => (1 / 2 - (α + 2 * β) * Δ lam x) / 2
           | false, true => (1 / 2 + β * Δ lam x) / 2
           | false, false => (1 / 2 + β * Δ lam x) / 2) := by
  have hd : (1 - 2 * β * Δ lam x) ≠ 0 := (denom_pos hβ hαβ hα lam x).ne'
  unfold obsReal mPerturbed gPerturbed
  cases d <;> cases y <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;>
    · rw [mul_assoc]
      refine congrArg _ ?_
      field_simp
      try ring

/-- The one-observation χ² second-moment overlap has the closed form used in the Ingster bound. -/
theorem chiSqOverlap_eq [NeZero K] (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (lam lam' : Fin K → Bool) :
    chiSqOverlap α β lam lam'
      = 1 + (2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) / (K : ℝ))
          * ∑ j, signOf (lam j) * signOf (lam' j) := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have hcard : (Fintype.card (Fin K × Bool) : ℝ) = 2 * K := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; push_cast; ring
  -- Rewrite the overlap sum as a sum over cells `j : Fin K` of an explicit
  -- per-cell value, by collapsing the inner `Bool × Bool` sum over `(d, y)`.
  have hsum : chiSqOverlap α β lam lam' =
      ∑ j : Fin K, 2 / (K : ℝ) *
        (1 / 2 + (α ^ 2 + 2 * α * β + 3 * β ^ 2) * (signOf (lam j) * signOf (lam' j))) := by
    unfold chiSqOverlap
    -- peel `Obs = (Fin K × Bool) × (Bool × Bool)` into `∑ (j,pos), ∑ (d,y)`,
    -- then split the covariate `Fin K × Bool` into `∑ j, ∑ pos`.
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    -- collapse the position sum `∑ pos : Bool` and the `(d, y) : Bool × Bool` sum;
    -- replace every perturbed mass by its denominator-free closed form, and the
    -- null mass `obsReal mhat ghat = (2K)⁻¹·(1/2)·(1/2)`.
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    -- perturbed masses → denominator-free closed forms; null mass → its constant
    simp only [obsReal_perturbed_eq hα hβ hαβ]
    simp only [obsReal, mhat, ghat, Bool.false_eq_true, if_false, if_true]
    have e1 : Δ lam (j, true) = signOf (lam j) := by simp [Δ]
    have e2 : Δ lam (j, false) = -signOf (lam j) := by simp [Δ]
    have e3 : Δ lam' (j, true) = signOf (lam' j) := by simp [Δ]
    have e4 : Δ lam' (j, false) = -signOf (lam' j) := by simp [Δ]
    simp only [e1, e2, e3, e4]
    rw [hcard]
    have hs : (signOf (lam j)) ^ 2 = 1 := signOf_sq _
    have hs' : (signOf (lam' j)) ^ 2 = 1 := signOf_sq _
    field_simp
    nlinarith [hs, hs', mul_self_nonneg (signOf (lam j) * signOf (lam' j))]
  rw [hsum]
  have hsplit : ∀ j : Fin K,
      2 / (K : ℝ) *
        (1 / 2 + (α ^ 2 + 2 * α * β + 3 * β ^ 2) * (signOf (lam j) * signOf (lam' j)))
      = 1 / (K : ℝ)
        + 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) / (K : ℝ)
            * (signOf (lam j) * signOf (lam' j)) := by
    intro j; field_simp
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  field_simp

end Causalean.Estimation.MinimaxATE
