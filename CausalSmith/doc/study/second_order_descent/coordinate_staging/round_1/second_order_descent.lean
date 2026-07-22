/-
Copyright (c) 2026 CausalSmith contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Taylor

/-!
# Second-order descent for one real variable

This module provides the one-dimensional smooth-optimization descent lemma. A real
function whose second derivative is bounded above on a segment lies below the
corresponding quadratic Taylor model, and a negative initial slope gives an explicit
positive decrease at the clipped quadratic-model step.

The statements are objective-agnostic. Callers supply the regularity on `Set.Icc 0 T`
and the pointwise second-derivative bound; this file only turns those hypotheses into
the quadratic upper bound and the optimized descent gap.
-/

open Set

namespace Causalean.Mathlib.Analysis

/-- The quadratic-model step chooses the endpoint when curvature is zero and otherwise
clips the unconstrained optimizer at the available interval length.

This is the step used by the descent-gap lemmas below: with curvature bound `M`, slope
margin `c`, and interval length `T`, it is `T` if `M = 0` and `min T (c / M)` otherwise. -/
noncomputable def descentStep (M c T : ℝ) : ℝ :=
  if M = 0 then T else min T (c / M)

/-- With zero curvature bound, the clipped quadratic-model step is the endpoint. -/
@[simp]
theorem descentStep_of_eq_zero (c T : ℝ) : descentStep 0 c T = T := by
  simp [descentStep]

/-- With a positive curvature bound, the clipped quadratic-model step is the smaller of the
available interval length and the unconstrained quadratic-model optimizer. -/
theorem descentStep_of_pos {M : ℝ} (hM : 0 < M) (c T : ℝ) :
    descentStep M c T = min T (c / M) := by
  simp [descentStep, hM.ne']

/-- The clipped quadratic-model step is feasible whenever the interval length, slope margin,
and curvature bound are nonnegative. -/
theorem descentStep_mem_Icc {M c T : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hT : 0 ≤ T) :
    descentStep M c T ∈ Icc 0 T := by
  unfold descentStep
  split_ifs with h
  · exact ⟨hT, le_rfl⟩
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm h)
    exact ⟨le_min hT (div_nonneg hc hM), min_le_left _ _⟩

/-! ### Quadratic upper bound -/

/-- A twice differentiable real function whose second derivative is bounded above on an
interval is no larger than its tangent at the left endpoint plus the quadratic curvature
allowance.

The formal statement is on `[0, T]`. It assumes twice continuous differentiability on that
closed interval, differentiability at the left endpoint, and a pointwise bound
`deriv (deriv f) ≤ M` throughout the interval. Mathlib's Taylor theorem with Lagrange
remainder supplies an intermediate point, and the pointwise bound controls the remainder. -/
theorem second_order_upper_bound {f : ℝ → ℝ} {M T : ℝ} (hT : 0 ≤ T)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T)) (hf0 : DifferentiableAt ℝ f 0)
    (hM : ∀ t ∈ Icc 0 T, deriv (deriv f) t ≤ M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    f t ≤ f 0 + deriv f 0 * t + (M / 2) * t ^ 2 := by
  have _hT : 0 ≤ T := hT
  rcases ht with ⟨ht0, htT⟩
  rcases ht0.eq_or_lt with rfl | htpos
  · simp
  · have hf' : ContDiffOn ℝ 2 f (Icc 0 t) := hf.mono (Icc_subset_Icc le_rfl htT)
    have htay :
        ∃ x' ∈ Ioo (0 : ℝ) t,
          f t - taylorWithinEval f 1 (Icc 0 t) 0 t =
            iteratedDeriv 2 f x' * (t - 0) ^ 2 / (Nat.factorial 2) := by
      have := taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := t) (x₀ := 0)
        (n := 1) htpos (by
          norm_num
          exact hf')
      simpa using this
    have hpoly : taylorWithinEval f 1 (Icc 0 t) 0 t = f 0 + deriv f 0 * t := by
      rw [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_one]
      · rw [hf0.derivWithin ((uniqueDiffOn_Icc htpos) 0 ⟨le_rfl, htpos.le⟩)]
        simp [mul_comm]
    have hid : iteratedDeriv 2 f = deriv (deriv f) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rcases htay with ⟨ξ, hξ, heq⟩
    have hb : deriv (deriv f) ξ ≤ M := hM ξ ⟨hξ.1.le, hξ.2.le.trans htT⟩
    have heq' :
        f t - (f 0 + deriv f 0 * t) = deriv (deriv f) ξ * t ^ 2 / 2 := by
      rw [hpoly, hid] at heq
      simpa [sub_zero, Nat.factorial] using heq
    have hquad :
        deriv (deriv f) ξ * t ^ 2 / 2 ≤ M * t ^ 2 / 2 := by
      nlinarith [sq_nonneg t, hb]
    nlinarith

/-- A real function with nonpositive second derivative on an interval lies below its tangent
line at the left endpoint.

This is the zero-curvature specialization of the second-order upper bound. It is useful
when the caller has concavity along the segment rather than a strictly positive curvature
constant. -/
theorem first_order_upper_bound {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T)) (hf0 : DifferentiableAt ℝ f 0)
    (hM : ∀ t ∈ Icc 0 T, deriv (deriv f) t ≤ 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    f t ≤ f 0 + deriv f 0 * t := by
  have h := second_order_upper_bound (M := 0) hT hf hf0 hM ht
  simpa using h

/-! ### Optimized descent gap -/

/-- A negative initial slope plus an upper curvature bound gives a guaranteed decrease at
the clipped quadratic-model step.

The conclusion exposes both feasibility of the chosen step and the raw quadratic-model
gap. This form is intended for callers that want to keep their own constants visible before
using the simplified closed forms below. -/
theorem second_order_descent_gap {f : ℝ → ℝ} {M c T : ℝ} (hT : 0 ≤ T) (hc : 0 < c)
    (hMnn : 0 ≤ M) (hf : ContDiffOn ℝ 2 f (Icc 0 T)) (hf0 : DifferentiableAt ℝ f 0)
    (hM : ∀ t ∈ Icc 0 T, deriv (deriv f) t ≤ M) (hslope : deriv f 0 ≤ -c) :
    descentStep M c T ∈ Icc 0 T ∧
      f 0 - f (descentStep M c T) ≥
        c * descentStep M c T - (M / 2) * descentStep M c T ^ 2 := by
  let s := descentStep M c T
  have hs : s ∈ Icc 0 T := descentStep_mem_Icc hMnn hc.le hT
  refine ⟨hs, ?_⟩
  have hs0 : 0 ≤ s := hs.1
  have hub : f s ≤ f 0 + deriv f 0 * s + (M / 2) * s ^ 2 :=
    second_order_upper_bound hT hf hf0 hM hs
  have hslope_mul : deriv f 0 * s ≤ -c * s :=
    mul_le_mul_of_nonneg_right hslope hs0
  nlinarith

/-- With positive curvature, the clipped quadratic-model step gives at least half of the
linear descent term.

The selected step is `min T (c / M)`, so the guaranteed decrease is at least
`(c / 2) * min T (c / M)`. The factor one half is the standard smooth-optimization
constant from optimizing a quadratic upper model. -/
theorem second_order_descent_gap_min {f : ℝ → ℝ} {M c T : ℝ} (hT : 0 ≤ T) (hc : 0 < c)
    (hMpos : 0 < M) (hf : ContDiffOn ℝ 2 f (Icc 0 T)) (hf0 : DifferentiableAt ℝ f 0)
    (hM : ∀ t ∈ Icc 0 T, deriv (deriv f) t ≤ M) (hslope : deriv f 0 ≤ -c) :
    f 0 - f (min T (c / M)) ≥ (c / 2) * min T (c / M) := by
  let s := min T (c / M)
  have hraw :
      f 0 - f s ≥ c * s - (M / 2) * s ^ 2 := by
    simpa [s, descentStep_of_pos hMpos] using
      (second_order_descent_gap hT hc hMpos.le hf hf0 hM hslope).2
  have hsle : s ≤ c / M := min_le_right T (c / M)
  have hMs : s * M ≤ c := (le_div_iff₀ hMpos).mp hsle
  have hs0 : 0 ≤ s := le_min hT (div_nonneg hc.le hMpos.le)
  nlinarith

/-- With zero curvature, the endpoint step gives the full linear descent guaranteed by the
negative initial slope.

This is the closed-form descent bound for the concave or affine-along-the-segment case. -/
theorem first_order_descent_gap {f : ℝ → ℝ} {c T : ℝ} (hT : 0 ≤ T) (hc : 0 < c)
    (hf : ContDiffOn ℝ 2 f (Icc 0 T)) (hf0 : DifferentiableAt ℝ f 0)
    (hM : ∀ t ∈ Icc 0 T, deriv (deriv f) t ≤ 0) (hslope : deriv f 0 ≤ -c) :
    f 0 - f T ≥ c * T := by
  have _hc : 0 ≤ c := hc.le
  have hub : f T ≤ f 0 + deriv f 0 * T :=
    first_order_upper_bound hT hf hf0 hM (right_mem_Icc.mpr hT)
  have hslope_mul : deriv f 0 * T ≤ -c * T :=
    mul_le_mul_of_nonneg_right hslope hT
  nlinarith

/-- In both zero and positive curvature regimes, the clipped quadratic-model step gives a
uniform half-linear decrease.

For zero curvature the sharper endpoint bound is `c * T`; for positive curvature the
selected step is `min T (c / M)`. This theorem packages the common guarantee together with
feasibility of the step. -/
theorem second_order_descent_gap_half {f : ℝ → ℝ} {M c T : ℝ} (hT : 0 ≤ T) (hc : 0 < c)
    (hMnn : 0 ≤ M) (hf : ContDiffOn ℝ 2 f (Icc 0 T)) (hf0 : DifferentiableAt ℝ f 0)
    (hM : ∀ t ∈ Icc 0 T, deriv (deriv f) t ≤ M) (hslope : deriv f 0 ≤ -c) :
    descentStep M c T ∈ Icc 0 T ∧
      f 0 - f (descentStep M c T) ≥ (c / 2) * descentStep M c T := by
  refine ⟨descentStep_mem_Icc hMnn hc.le hT, ?_⟩
  rcases hMnn.eq_or_lt with hMzero | hMpos
  · rw [← hMzero, descentStep_of_eq_zero]
    have hM0 : ∀ t ∈ Icc 0 T, deriv (deriv f) t ≤ 0 := by
      simpa [← hMzero] using hM
    have hgap : f 0 - f T ≥ c * T :=
      first_order_descent_gap hT hc hf hf0 hM0 hslope
    nlinarith
  · rw [descentStep_of_pos hMpos]
    exact second_order_descent_gap_min hT hc hMpos hf hf0 hM hslope

end Causalean.Mathlib.Analysis
