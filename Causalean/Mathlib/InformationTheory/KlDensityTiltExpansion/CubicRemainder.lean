/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib

/-!
# Cubic Taylor remainder of `(1 + x) · log (1 + x)`

The analytic core of the KL density-tilt expansion.  The function
`f x = (1 + x) · log (1 + x)` has the second-order Taylor expansion
`f x = x + x² / 2 + O(x³)` at `0`, and on the band `|x| ≤ 1/2` the remainder is
controlled by `|x|³`.

Indeed `f 0 = 0`, `f' x = log (1 + x) + 1` so `f' 0 = 1`, `f'' x = 1 / (1 + x)`
so `f'' 0 = 1`, and `f''' x = -1 / (1 + x)²` with `|f''' x| ≤ 1 / (1/2)² = 4` for
`x ≥ -1/2`.  The Lagrange form of Taylor's theorem then gives
`|f x - (x + x²/2)| ≤ (4 / 3!) · |x|³ = (2/3) · |x|³ ≤ |x|³`.

This pointwise bound, applied with `x = h · s y`, yields the dominated `o(h²)`
remainder in `KLExpansion.lean`.
-/

open Real

namespace Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion

private lemma tiltAux_hasDerivAt_negR (t : ℝ) (ht : 1 + t ≠ 0) :
    HasDerivAt (fun u : ℝ => u + u ^ 2 / 2 - (1 + u) * Real.log (1 + u))
      (t - Real.log (1 + t)) t := by
  have hlog : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t := by
    have h := (Real.hasDerivAt_log (x := 1 + t) ht).comp t
      ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t))
    simpa [one_div] using h
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
    have h := (((hasDerivAt_id t).pow 2).const_mul ((2 : ℝ)⁻¹))
    simpa [div_eq_mul_inv, pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hprod : HasDerivAt (fun u : ℝ => (1 + u) * Real.log (1 + u))
      (Real.log (1 + t) + 1) t := by
    have hlin : HasDerivAt (fun u : ℝ => 1 + u) 1 t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
    convert hlin.mul hlog using 1
    field_simp [ht]
  convert ((hasDerivAt_id t).add hsq).sub hprod using 1
  ring

private lemma tiltAux_hasDerivAt_R_add_cube (t : ℝ) (ht : 1 + t ≠ 0) :
    HasDerivAt (fun u : ℝ => (1 + u) * Real.log (1 + u) - u - u ^ 2 / 2 + u ^ 3)
      (Real.log (1 + t) - t + 3 * t ^ 2) t := by
  have hlog : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t := by
    have h := (Real.hasDerivAt_log (x := 1 + t) ht).comp t
      ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t))
    simpa [one_div] using h
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
    have h := (((hasDerivAt_id t).pow 2).const_mul ((2 : ℝ)⁻¹))
    simpa [div_eq_mul_inv, pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hcube : HasDerivAt (fun u : ℝ => u ^ 3) (3 * t ^ 2) t := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using (hasDerivAt_id t).pow 3
  have hprod : HasDerivAt (fun u : ℝ => (1 + u) * Real.log (1 + u))
      (Real.log (1 + t) + 1) t := by
    have hlin : HasDerivAt (fun u : ℝ => 1 + u) 1 t := by
      simpa using (hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)
    convert hlin.mul hlog using 1
    field_simp [ht]
  convert (((hprod.sub (hasDerivAt_id t)).sub hsq).add hcube) using 1
  ring

private lemma tiltAux_monotone_negR (a b : ℝ) (hlo : -(1 / 2 : ℝ) ≤ a) :
    MonotoneOn (fun t : ℝ => t + t ^ 2 / 2 - (1 + t) * Real.log (1 + t))
      (Set.Icc a b) := by
  let A : ℝ → ℝ := fun t => t + t ^ 2 / 2 - (1 + t) * Real.log (1 + t)
  change MonotoneOn A (Set.Icc a b)
  have hcont : ContinuousOn A (Set.Icc a b) := by
    have hnonzero : ∀ t ∈ Set.Icc a b, 1 + t ≠ 0 := by
      intro t ht
      have htge : -(1 / 2 : ℝ) ≤ t := le_trans hlo ht.1
      nlinarith
    exact (continuousOn_id.add ((continuousOn_id.pow 2).div_const 2)).sub
      ((continuousOn_const.add continuousOn_id).mul
        ((continuousOn_const.add continuousOn_id).log hnonzero))
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => t - Real.log (1 + t))
    (convex_Icc a b) hcont ?_ ?_
  · intro t ht
    have htIcc : t ∈ Set.Icc a b := interior_subset ht
    have hne : 1 + t ≠ 0 := by
      have htge : -(1 / 2 : ℝ) ≤ t := le_trans hlo htIcc.1
      nlinarith
    exact (tiltAux_hasDerivAt_negR t hne).hasDerivWithinAt
  · intro t ht
    have htIcc : t ∈ Set.Icc a b := interior_subset ht
    have htpos : 0 < 1 + t := by
      have htge : -(1 / 2 : ℝ) ≤ t := le_trans hlo htIcc.1
      nlinarith
    have hlog := Real.log_le_sub_one_of_pos htpos
    nlinarith

private lemma tiltAux_monotone_R_add_cube (a b : ℝ) (hlo : -(1 / 2 : ℝ) ≤ a) :
    MonotoneOn (fun t : ℝ => (1 + t) * Real.log (1 + t) - t - t ^ 2 / 2 + t ^ 3)
      (Set.Icc a b) := by
  let B : ℝ → ℝ := fun t => (1 + t) * Real.log (1 + t) - t - t ^ 2 / 2 + t ^ 3
  change MonotoneOn B (Set.Icc a b)
  have hcont : ContinuousOn B (Set.Icc a b) := by
    have hnonzero : ∀ t ∈ Set.Icc a b, 1 + t ≠ 0 := by
      intro t ht
      have htge : -(1 / 2 : ℝ) ≤ t := le_trans hlo ht.1
      nlinarith
    exact (((continuousOn_const.add continuousOn_id).mul
        ((continuousOn_const.add continuousOn_id).log hnonzero)).sub continuousOn_id).sub
      ((continuousOn_id.pow 2).div_const 2) |>.add (continuousOn_id.pow 3)
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun t => Real.log (1 + t) - t + 3 * t ^ 2)
    (convex_Icc a b) hcont ?_ ?_
  · intro t ht
    have htIcc : t ∈ Set.Icc a b := interior_subset ht
    have hne : 1 + t ≠ 0 := by
      have htge : -(1 / 2 : ℝ) ≤ t := le_trans hlo htIcc.1
      nlinarith
    exact (tiltAux_hasDerivAt_R_add_cube t hne).hasDerivWithinAt
  · intro t ht
    have htIcc : t ∈ Set.Icc a b := interior_subset ht
    have htge : -(1 / 2 : ℝ) ≤ t := le_trans hlo htIcc.1
    have htpos : 0 < 1 + t := by nlinarith
    have hlog : 1 - (1 + t)⁻¹ ≤ Real.log (1 + t) :=
      Real.one_sub_inv_le_log_of_pos htpos
    have hinv_le_three : (1 + t)⁻¹ ≤ (3 : ℝ) := by
      have hhalf : (1 / 2 : ℝ) ≤ 1 + t := by nlinarith
      have hinv_le_two : (1 + t)⁻¹ ≤ (2 : ℝ) := by
        calc
          (1 + t)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ := (inv_le_inv₀ htpos (by norm_num)).2 hhalf
          _ = (2 : ℝ) := by norm_num
      linarith
    have hbase : 0 ≤ (1 - (1 + t)⁻¹) - t + 3 * t ^ 2 := by
      have hsq : 0 ≤ t ^ 2 := sq_nonneg t
      have hmul : 0 ≤ t ^ 2 * (3 - (1 + t)⁻¹) :=
        mul_nonneg hsq (sub_nonneg.mpr hinv_le_three)
      convert hmul using 1
      field_simp [htpos.ne']
      ring
    linarith

/-- **Cubic remainder bound for `(1 + x) · log (1 + x)`.**  On the band
`|x| ≤ 1/2`,

    |(1 + x) · log (1 + x) - x - x² / 2|  ≤  |x|³.

This is the second-order Taylor bound with the third-derivative estimate
`|f'''| ≤ 4` on `[-1/2, 1/2]` (giving the sharp constant `2/3 ≤ 1`).

Proof strategy: apply `taylor_mean_remainder_lagrange` (or the `uIcc` variant) to
`f x = (1 + x) * Real.log (1 + x)` at base point `0`, order `n = 2`.  The degree-2
Taylor polynomial is `x + x²/2` (`f 0 = 0`, `f' 0 = 1`, `f'' 0 = 1`), and the
remainder is `f''' ξ / 6 · x³` with `|f''' ξ| = 1/(1+ξ)² ≤ 4` since `ξ` lies
between `0` and `x`, so `1 + ξ ≥ 1/2`.  Hence the remainder is `≤ (4/6)|x|³ ≤ |x|³`.
Handle `x = 0` separately (both sides `0`) and the two sign cases of `x` via the
`uIcc` Taylor lemma.  Alternatively prove it by an elementary route: bound
`log (1 + x)` above/below by its own quadratic Taylor remainder and combine with
`nlinarith`. -/
lemma abs_tiltRemainder_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |(1 + x) * Real.log (1 + x) - x - x ^ 2 / 2| ≤ |x| ^ 3 := by
  have hxlo : -(1 / 2 : ℝ) ≤ x := by
    have h := abs_le.mp hx
    linarith
  by_cases hxnonneg : 0 ≤ x
  · have hAmono := tiltAux_monotone_negR 0 x (by norm_num)
    have hBmono := tiltAux_monotone_R_add_cube 0 x (by norm_num)
    have hR_nonpos : (1 + x) * Real.log (1 + x) - x - x ^ 2 / 2 ≤ 0 := by
      have hA : 0 ≤ x + x ^ 2 / 2 - (1 + x) * Real.log (1 + x) := by
        have h := hAmono (by simp [hxnonneg]) (by simp [hxnonneg]) hxnonneg
        simpa using h
      linarith
    have hR_lower : -x ^ 3 ≤ (1 + x) * Real.log (1 + x) - x - x ^ 2 / 2 := by
      have hB : 0 ≤ (1 + x) * Real.log (1 + x) - x - x ^ 2 / 2 + x ^ 3 := by
        have h := hBmono (by simp [hxnonneg]) (by simp [hxnonneg]) hxnonneg
        simpa using h
      linarith
    rw [abs_of_nonpos hR_nonpos, abs_of_nonneg hxnonneg]
    nlinarith
  · have hxnonpos : x ≤ 0 := le_of_not_ge hxnonneg
    have hAmono := tiltAux_monotone_negR x 0 hxlo
    have hBmono := tiltAux_monotone_R_add_cube x 0 hxlo
    have hR_nonneg : 0 ≤ (1 + x) * Real.log (1 + x) - x - x ^ 2 / 2 := by
      have hA : x + x ^ 2 / 2 - (1 + x) * Real.log (1 + x) ≤ 0 := by
        have h := hAmono (by simp [hxnonpos]) (by simp [hxnonpos]) hxnonpos
        simpa using h
      linarith
    have hR_upper : (1 + x) * Real.log (1 + x) - x - x ^ 2 / 2 ≤ -x ^ 3 := by
      have hB : (1 + x) * Real.log (1 + x) - x - x ^ 2 / 2 + x ^ 3 ≤ 0 := by
        have h := hBmono (by simp [hxnonpos]) (by simp [hxnonpos]) hxnonpos
        simpa using h
      linarith
    rw [abs_of_nonneg hR_nonneg, abs_of_nonpos hxnonpos]
    have hpow : (-x) ^ 3 = -x ^ 3 := by ring
    rw [hpow]
    exact hR_upper

end Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion
