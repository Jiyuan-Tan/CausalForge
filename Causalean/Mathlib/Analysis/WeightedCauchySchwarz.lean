/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt

/-!
# Cauchy–Schwarz against a finite nonnegative weight vector

Mathlib's discrete Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq` is stated for the
*unweighted* inner product.  Weighted versions (`⟨f, g⟩_w = Σ wᵢ fᵢ gᵢ` for a
nonnegative weight vector `w`) get re-derived by hand all over the library, so this
module records them once, over an arbitrary finite support.

* `weighted_inner_sq_le` — squared form `(Σ wᵢ fᵢ gᵢ)² ≤ (Σ wᵢ fᵢ²)(Σ wᵢ gᵢ²)`.
* `abs_weighted_inner_le` — square-root form with an absolute value on the left.
* `abs_weighted_mean_le_sqrt_weighted_sq` — the subprobability-weight (`Σ wᵢ ≤ 1`)
  specialization `|Σ wᵢ fᵢ| ≤ √(Σ wᵢ fᵢ²)`, i.e. Jensen for `x ↦ x²`.
* `weighted_sqrt_le_sqrt_weighted` — Jensen for `√·`: `Σ wᵢ √qᵢ ≤ √(Σ wᵢ qᵢ)`.

All four follow from the unweighted inequality by substituting `f ↦ √w · f`,
`g ↦ √w · g` and simplifying with `Real.sq_sqrt`.
-/

namespace Causalean.Mathlib.Analysis

open scoped BigOperators

variable {ι : Type*}

/-- **Weighted Cauchy-Schwarz inequality on a finite support, squared form.** Weighting a finite
collection of index points by [nonnegative weights](hyp:hw), [the square of the weighted inner
product of two real-valued functions is at most the product of their weighted sums of
squares](goal). -/
lemma weighted_inner_sq_le (s : Finset ι) (w f g : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (f i * g i)) ^ 2 ≤
      (∑ i ∈ s, w i * f i ^ 2) * (∑ i ∈ s, w i * g i ^ 2) := by
  have hprod : ∀ i ∈ s,
      Real.sqrt (w i) * f i * (Real.sqrt (w i) * g i) = w i * (f i * g i) := by
    intro i hi
    have : Real.sqrt (w i) * Real.sqrt (w i) = w i := Real.mul_self_sqrt (hw i hi)
    calc Real.sqrt (w i) * f i * (Real.sqrt (w i) * g i)
        = Real.sqrt (w i) * Real.sqrt (w i) * (f i * g i) := by ring
      _ = w i * (f i * g i) := by rw [this]
  have hsq : ∀ (h : ι → ℝ) (i : ι) (_ : i ∈ s),
      (Real.sqrt (w i) * h i) ^ 2 = w i * h i ^ 2 := by
    intro h i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hsumprod :
      ∑ i ∈ s, Real.sqrt (w i) * f i * (Real.sqrt (w i) * g i) =
        ∑ i ∈ s, w i * (f i * g i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hprod i hi
  have hsumsq (h : ι → ℝ) :
      ∑ i ∈ s, (Real.sqrt (w i) * h i) ^ 2 = ∑ i ∈ s, w i * h i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hsq h i hi
  have key := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (w i) * f i) (fun i => Real.sqrt (w i) * g i)
  rw [hsumprod, hsumsq f, hsumsq g] at key
  exact key

/-- **Weighted Cauchy-Schwarz inequality on a finite support, square-root form.** With
[nonnegative weights](hyp:hw), [the absolute value of the weighted inner product of two
real-valued functions is at most the product of the square roots of their weighted sums of
squares](goal). -/
lemma abs_weighted_inner_le (s : Finset ι) (w f g : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    |∑ i ∈ s, w i * (f i * g i)| ≤
      Real.sqrt (∑ i ∈ s, w i * f i ^ 2) * Real.sqrt (∑ i ∈ s, w i * g i ^ 2) := by
  have hP : (0 : ℝ) ≤ ∑ i ∈ s, w i * f i ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hstep : |∑ i ∈ s, w i * (f i * g i)|
      ≤ Real.sqrt ((∑ i ∈ s, w i * f i ^ 2) * (∑ i ∈ s, w i * g i ^ 2)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (weighted_inner_sq_le s w f g hw)
  rwa [Real.sqrt_mul hP] at hstep

/-- **Weighted mean is dominated by the weighted root-mean-square.** For weights that are
nonnegative and sum to at most one, the absolute value of the weighted average of a real-valued
function is at most the square root of the weighted average of its square. -/
lemma abs_weighted_mean_le_sqrt_weighted_sq (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (c : ℝ) (hmass : ∑ i ∈ s, w i ≤ c) :
    |∑ i ∈ s, w i * f i| ≤
      Real.sqrt c * Real.sqrt (∑ i ∈ s, w i * f i ^ 2) := by
  have key := abs_weighted_inner_le s w f (fun _ => 1) hw
  simp only [mul_one, one_pow] at key
  have hsqrt : Real.sqrt (∑ i ∈ s, w i) ≤ Real.sqrt c := by
    have := Real.sqrt_le_sqrt hmass
    exact this
  calc
    _ ≤ Real.sqrt (∑ i ∈ s, w i * f i ^ 2) * Real.sqrt (∑ i ∈ s, w i) := key
    _ ≤ Real.sqrt (∑ i ∈ s, w i * f i ^ 2) * Real.sqrt c :=
      mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

/-- **Jensen's inequality for the square root.** Averaging nonnegative values with weights
that are nonnegative and sum to at most one, the weighted average of their square roots is at most
the square root of their weighted average. -/
lemma weighted_sqrt_le_sqrt_weighted (s : Finset ι) (w q : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (c : ℝ) (hmass : ∑ i ∈ s, w i ≤ c)
    (hq : ∀ i ∈ s, 0 ≤ q i) :
    ∑ i ∈ s, w i * Real.sqrt (q i) ≤
      Real.sqrt c * Real.sqrt (∑ i ∈ s, w i * q i) := by
  have key := abs_weighted_mean_le_sqrt_weighted_sq s w (fun i => Real.sqrt (q i)) hw c hmass
  have hrw : ∀ i ∈ s, w i * Real.sqrt (q i) ^ 2 = w i * q i := by
    intro i hi; rw [Real.sq_sqrt (hq i hi)]
  have hsumrw :
      ∑ i ∈ s, w i * Real.sqrt (q i) ^ 2 = ∑ i ∈ s, w i * q i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hrw i hi
  rw [hsumrw] at key
  exact le_trans (le_abs_self _) key

end Causalean.Mathlib.Analysis
