/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Reusable finite weighted algebra

Finite-sum identities for normalized weights and weighted centered
covariance / variance.  These are paper-agnostic helpers consumed by the
estimand-characterization layer (Sloczynski, Goodman-Bacon, Sun-Abraham,
…) when re-expressing a regression coefficient `θ̂` as a finite weighted
sum `∑_r ω_r · τ_r`.

This file is a generalization of the original
`Causalean/Panel/EstimandCharacterization/FiniteWeighted.lean`: the underlying
results are pure weighted-sum algebra over a `Fintype` index, so we drop
the panel-specific `(I × T)` framing in favour of a single generic
index `ι`.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Normalized finite weights and pairwise moment identities

This file develops paper-agnostic finite-sum algebra for normalized weights,
weighted centered covariances, and weighted centered variances. It defines
`normalizedWeight`, proves the basic nonnegativity and sum-to-one facts
`normalizedWeight_nonneg` and `sum_normalizedWeight_eq_one`, and proves the
pairwise formulas `weighted_center_cov` and `weighted_center_var`.

These identities are reusable in regression-weight decompositions where a
coefficient is re-expressed as a finite weighted sum over cells or cohorts. -/

open scoped BigOperators

namespace Causalean
namespace Panel.Weighted
namespace NormalizedWeights

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private lemma double_sum_mul (a : ι → ℝ) (b : κ → ℝ) :
    (∑ i, ∑ j, a i * b j) = (∑ i, a i) * (∑ j, b j) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Finset.mul_sum]

variable {ι : Type*} [Fintype ι]

/-- Generic normalized finite weight `a_i / Σ_k a_k`. -/
noncomputable def normalizedWeight (a : ι → ℝ) (i : ι) : ℝ :=
  a i / ∑ k, a k

/-- Nonnegativity of normalized weights from nonnegative raw weights and a
positive normalizing sum. -/
lemma normalizedWeight_nonneg (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : 0 < ∑ i, a i) (i : ι) :
    0 ≤ normalizedWeight a i := by
  unfold normalizedWeight
  exact div_nonneg (ha i) (le_of_lt hsum)

/-- Normalized finite weights sum to one when the normalizing sum is positive. -/
lemma sum_normalizedWeight_eq_one (a : ι → ℝ) (hsum : 0 < ∑ i, a i) :
    ∑ i, normalizedWeight a i = 1 := by
  unfold normalizedWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hsum)

private lemma weighted_center_cov_left (p x y : ι → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, p i * (x i - ∑ j, p j * x j) * (y i - ∑ j, p j * y j) =
      (∑ i, p i * x i * y i) - (∑ j, p j * x j) * (∑ j, p j * y j) := by
  classical
  let mx := ∑ j, p j * x j
  let my := ∑ j, p j * y j
  have hpx : (∑ i, (p i * x i) * my) = mx * my := by
    dsimp [mx]
    rw [Finset.sum_mul]
  have hpy : (∑ i, (p i * y i) * mx) = my * mx := by
    dsimp [my]
    rw [Finset.sum_mul]
  have hpmy : (∑ i : ι, p i * mx * my) = mx * my := by
    calc
      (∑ i : ι, p i * mx * my) = ∑ i : ι, p i * (mx * my) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring
      _ = (∑ i : ι, p i) * (mx * my) := by
        exact (Finset.sum_mul (s := Finset.univ)
          (f := fun i : ι => p i) (a := mx * my)).symm
      _ = mx * my := by
        rw [hp]
        ring
  calc
    ∑ i, p i * (x i - ∑ j, p j * x j) * (y i - ∑ j, p j * y j)
        = ∑ i, (p i * x i * y i - (p i * x i) * my
            - (p i * y i) * mx + p i * mx * my) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          dsimp [mx, my]
          ring
    _ = (∑ i, p i * x i * y i) - (∑ i, (p i * x i) * my)
        - (∑ i, (p i * y i) * mx) + ∑ i, p i * mx * my := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ i, p i * x i * y i) - mx * my := by
          rw [hpx, hpy, hpmy]
          ring
    _ = (∑ i, p i * x i * y i) - (∑ j, p j * x j) * (∑ j, p j * y j) := by
          rfl

private lemma pairwise_cov_right (p x y : ι → ℝ) (hp : ∑ i, p i = 1) :
    (∑ i, ∑ j, p i * p j * (x i - x j) * (y i - y j)) =
      2 * ((∑ i, p i * x i * y i) -
        (∑ j, p j * x j) * (∑ j, p j * y j)) := by
  classical
  calc
    (∑ i, ∑ j, p i * p j * (x i - x j) * (y i - y j))
        = (∑ i, ∑ j, (((p i * x i * y i) * p j -
            (p i * x i) * (p j * y j))
            - (p i * y i) * (p j * x j) + p i * (p j * x j * y j))) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
    _ = ((∑ i, p i * x i * y i) * (∑ j, p j))
          - ((∑ i, p i * x i) * (∑ j, p j * y j))
          - ((∑ i, p i * y i) * (∑ j, p j * x j))
          + ((∑ i, p i) * (∑ j, p j * x j * y j)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [double_sum_mul (fun i => p i * x i * y i) (fun j => p j)]
          rw [double_sum_mul (fun i => p i * x i) (fun j => p j * y j)]
          rw [double_sum_mul (fun i => p i * y i) (fun j => p j * x j)]
          rw [double_sum_mul (fun i => p i) (fun j => p j * x j * y j)]
    _ = 2 * ((∑ i, p i * x i * y i) -
          (∑ j, p j * x j) * (∑ j, p j * y j)) := by
          rw [hp]
          ring

/-- Weighted centered covariance as half the average pairwise cross-product.

This is the finite-population identity
`Σᵢ pᵢ (xᵢ − x̄)(yᵢ − ȳ) =
  1/2 Σᵢ Σⱼ pᵢpⱼ (xᵢ − xⱼ)(yᵢ − yⱼ)`.
-/
lemma weighted_center_cov (p x y : ι → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, p i * (x i - ∑ j, p j * x j) * (y i - ∑ j, p j * y j) =
      (1 / 2) * ∑ i, ∑ j, p i * p j * (x i - x j) * (y i - y j) := by
  rw [weighted_center_cov_left p x y hp, pairwise_cov_right p x y hp]
  ring

/-- Weighted centered variance as half the average pairwise squared gap. -/
lemma weighted_center_var (p x : ι → ℝ) (hp : ∑ i, p i = 1) :
    ∑ i, p i * (x i - ∑ j, p j * x j)^2 =
      (1 / 2) * ∑ i, ∑ j, p i * p j * (x i - x j)^2 := by
  have h := weighted_center_cov p x x hp
  calc
    ∑ i, p i * (x i - ∑ j, p j * x j)^2
        = ∑ i, p i * (x i - ∑ j, p j * x j) *
            (x i - ∑ j, p j * x j) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = (1 / 2) * ∑ i, ∑ j, p i * p j * (x i - x j) * (x i - x j) := h
    _ = (1 / 2) * ∑ i, ∑ j, p i * p j * (x i - x j)^2 := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring

end NormalizedWeights
end Panel.Weighted
end Causalean
