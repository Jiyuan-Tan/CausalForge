/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A globally `C¹` reciprocal with a floor near the singularity

The reciprocal `x ↦ x⁻¹` is singular at `0`. `recipC ε` is a modification that agrees with `x⁻¹`
on `x ≥ ε/2` but is smoothly damped to `0` on the neighbourhood of the singularity, so it is
globally `C¹` on all of `ℝ`. This is the reusable core of the "globally `C¹` extension of an
objective that is singular on the boundary of its feasible box" pattern: multiply the singular part
by a `Real.smoothTransition` cutoff that is `1` on the feasible region and `0` past the boundary.
-/

namespace Causalean.Mathlib

/-- **Floored reciprocal.** The reciprocal `x⁻¹` multiplied by a smooth cutoff that is `1` once
`x` is a definite distance above `0` and `0` near and below `0`. It coincides with `x⁻¹` on
`x ≥ ε/2` (see `recipC_eq_inv`) yet is globally `C¹` (see `recipC_contDiff`). -/
noncomputable def recipC (ε : ℝ) (x : ℝ) : ℝ :=
  Real.smoothTransition ((x - ε / 4) / (ε / 4)) * x⁻¹

/-- On the region `x ≥ ε/2` (with `ε > 0`) the floored reciprocal is exactly `x⁻¹`, because the
smooth cutoff has already saturated to `1` there. -/
lemma recipC_eq_inv {ε x : ℝ} (hε : 0 < ε) (hx : ε / 2 ≤ x) :
    recipC ε x = x⁻¹ := by
  unfold recipC
  have hden : 0 < ε / 4 := by positivity
  have hone : 1 ≤ (x - ε / 4) / (ε / 4) := by
    rw [le_div_iff₀ hden]
    linarith
  rw [Real.smoothTransition.one_of_one_le hone]
  ring

/-- The floored reciprocal is globally `Cⁿ` on all of `ℝ`, for EVERY smoothness order `n`: near
the singularity the smooth cutoff vanishes to infinite order, absorbing the blow-up of `x⁻¹`, and
away from the singularity it is a product of `Cⁿ` functions.

The order is arbitrary because both factors are: `Real.smoothTransition` is `C^∞`, and `x⁻¹` is
`C^∞` away from `0`. `recipC_contDiff` (`n = 1`) and `recipC_contDiff_two` (`n = 2`) are the
`fun_prop`-facing specializations. -/
lemma recipC_contDiff_of (n : ℕ∞) (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ n (recipC ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  unfold recipC
  by_cases hx : x < ε / 4
  · have hev :
        (fun y : ℝ => Real.smoothTransition ((y - ε / 4) / (ε / 4)) * y⁻¹)
          =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      have harg : (y - ε / 4) / (ε / 4) ≤ 0 := by
        have hden : 0 < ε / 4 := by positivity
        exact div_nonpos_of_nonpos_of_nonneg
          (by linarith [show y < ε / 4 from hy]) hden.le
      rw [Real.smoothTransition.zero_of_nonpos harg]
      simp
    exact
      (contDiffAt_const : ContDiffAt ℝ n (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
        hev
  · have hxpos : x ≠ 0 := by
      have hxge : ε / 4 ≤ x := le_of_not_gt hx
      have hpos : 0 < x := by linarith
      exact ne_of_gt hpos
    have hcut :
        ContDiffAt ℝ n
          (fun y : ℝ => Real.smoothTransition ((y - ε / 4) / (ε / 4))) x := by
      have hlin : ContDiff ℝ n (fun y : ℝ => (y - ε / 4) / (ε / 4)) := by fun_prop
      exact (Real.smoothTransition.contDiff.comp hlin).contDiffAt
    have hinv : ContDiffAt ℝ n (fun y : ℝ => y⁻¹) x := contDiffAt_inv ℝ hxpos
    exact hcut.mul hinv

/-- `recipC ε` is globally `C¹`. Specialization of `recipC_contDiff_of`. -/
@[fun_prop]
lemma recipC_contDiff (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ 1 (recipC ε) :=
  recipC_contDiff_of 1 ε hε

/-- `recipC ε` is globally `C²`. Specialization of `recipC_contDiff_of`; this is the order the
reciprocal-product envelope's directional curvature modulus needs. -/
@[fun_prop]
lemma recipC_contDiff_two (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ 2 (recipC ε) :=
  recipC_contDiff_of 2 ε hε

end Causalean.Mathlib
