/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bernoulli KL divergence is bounded by a multiple of squared difference on a band

For two Bernoulli success probabilities `p, q ∈ [1/4, 3/4]`, the
Kullback–Leibler divergence

  KL(Bern(p) ‖ Bern(q)) = p · log(p / q) + (1 - p) · log((1 - p) / (1 - q))

is bounded above by `4 · (p - q) ^ 2`.

The constant `4` is a convenient valid constant on this quarter band, not the
sharp curvature supremum.  The proof uses a convexity/Bregman argument on the
band where the relevant logarithmic curvature terms are uniformly bounded.

This statement is purely scalar — it depends only on `Real.log` and arithmetic
— and is a candidate for upstream contribution to Mathlib.
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! # Bernoulli KL Band Bound

This file proves a scalar upper bound on the Kullback--Leibler divergence between two
Bernoulli laws whose success probabilities both lie in the interval $[1/4,3/4]$.
It supplies a Mathlib-adjacent analytic estimate used by finite-sample information
arguments elsewhere in the library. -/

namespace Causalean.Mathlib.Analysis

open Set

private lemma hasDerivAt_bernEntropy (x : ℝ) (hx0 : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    HasDerivAt (fun t : ℝ => t * Real.log t + (1 - t) * Real.log (1 - t))
      (Real.log x - Real.log (1 - x)) x := by
  have h1 : HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log x + 1) x :=
    Real.hasDerivAt_mul_log hx0
  have h2log : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 - x)⁻¹) x := by
    simpa [div_eq_mul_inv] using (Real.hasDerivAt_log hx1).comp x
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
  have h2raw := (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).mul h2log)
  have h2 : HasDerivAt (fun t : ℝ => (1 - t) * Real.log (1 - t))
      (-(Real.log (1 - x)) - 1) x := by
    convert h2raw using 1
    simp only [Pi.sub_apply, id_eq]
    have hmul : (1 - x) * (-(1 - x)⁻¹) = -1 := by
      rw [mul_neg, mul_inv_cancel₀ hx1]
    rw [hmul]
    ring
  convert h1.add h2 using 1
  ring

private noncomputable def bernD (t : ℝ) : ℝ :=
  t * Real.log t + (1 - t) * Real.log (1 - t)

private noncomputable def bernH (q : ℝ) (t : ℝ) : ℝ :=
  4 * (t - q) ^ 2 + (Real.log q - Real.log (1 - q)) * (t - q) + bernD q - bernD t

private noncomputable def bernHDeriv (q : ℝ) (t : ℝ) : ℝ :=
  8 * (t - q) + (Real.log q - Real.log (1 - q)) -
    (Real.log t - Real.log (1 - t))

private lemma hasDerivAt_bernH (q x : ℝ) (hx0 : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    HasDerivAt (bernH q) (bernHDeriv q x) x := by
  unfold bernH bernHDeriv bernD
  have hd := hasDerivAt_bernEntropy x hx0 hx1
  have hquad := (hasDerivAt_const x (4 : ℝ)).mul (((hasDerivAt_id x).sub_const q).pow 2)
  have hlin := (hasDerivAt_const x (Real.log q - Real.log (1 - q))).mul
    ((hasDerivAt_id x).sub_const q)
  convert (((hquad.add hlin).add_const
      (q * Real.log q + (1 - q) * Real.log (1 - q))).sub hd) using 1
  simp only [id_eq, Nat.cast_ofNat]
  ring

private lemma hasDerivAt_bernHDeriv (q x : ℝ) (hx0 : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    HasDerivAt (bernHDeriv q) (8 - (x⁻¹ + (1 - x)⁻¹)) x := by
  unfold bernHDeriv
  have hlog1 : HasDerivAt (fun t : ℝ => Real.log t) x⁻¹ x := Real.hasDerivAt_log hx0
  have hlog2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 - x)⁻¹) x := by
    simpa [div_eq_mul_inv] using (Real.hasDerivAt_log hx1).comp x
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
  convert (((hasDerivAt_const x (8 : ℝ)).mul ((hasDerivAt_id x).sub_const q)).add_const
      (Real.log q - Real.log (1 - q))).sub (hlog1.sub hlog2) using 1
  ring

private lemma bernH_convexOn (q : ℝ) :
    ConvexOn ℝ (Icc ((1 : ℝ) / 4) (3 / 4)) (bernH q) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := bernHDeriv q)
    (f'' := fun x : ℝ => 8 - (x⁻¹ + (1 - x)⁻¹)) (convex_Icc _ _) ?_ ?_ ?_ ?_
  · intro x hx
    have hxpos : 0 < x := by nlinarith [hx.1]
    have hx1pos : 0 < 1 - x := by nlinarith [hx.2]
    exact (hasDerivAt_bernH q x hxpos.ne' hx1pos.ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxpos : 0 < x := by nlinarith [hx.1]
    have hx1pos : 0 < 1 - x := by nlinarith [hx.2]
    exact (hasDerivAt_bernH q x hxpos.ne' hx1pos.ne').hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxpos : 0 < x := by nlinarith [hx.1]
    have hx1pos : 0 < 1 - x := by nlinarith [hx.2]
    exact (hasDerivAt_bernHDeriv q x hxpos.ne' hx1pos.ne').hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxpos : 0 < x := by nlinarith [hx.1]
    have hx1pos : 0 < 1 - x := by nlinarith [hx.2]
    have hxinv : x⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ hxpos (by norm_num : (0 : ℝ) < 4)]
      nlinarith [hx.1]
    have hx1inv : (1 - x)⁻¹ ≤ 4 := by
      rw [inv_le_comm₀ hx1pos (by norm_num : (0 : ℝ) < 4)]
      nlinarith [hx.2]
    linarith

private lemma bernH_self (q : ℝ) : bernH q q = 0 := by
  unfold bernH
  ring

private lemma bernHDeriv_self (q : ℝ) : bernHDeriv q q = 0 := by
  unfold bernHDeriv
  ring

private lemma bernH_nonneg_of_mem_quarter_band {p q : ℝ}
    (hp_lo : (1 : ℝ) / 4 ≤ p) (hp_hi : p ≤ 3 / 4)
    (hq_lo : (1 : ℝ) / 4 ≤ q) (hq_hi : q ≤ 3 / 4) : 0 ≤ bernH q p := by
  have hconv := bernH_convexOn q
  have hp_mem : p ∈ Icc ((1 : ℝ) / 4) (3 / 4) := ⟨hp_lo, hp_hi⟩
  have hq_mem : q ∈ Icc ((1 : ℝ) / 4) (3 / 4) := ⟨hq_lo, hq_hi⟩
  have hqpos : 0 < q := by nlinarith
  have hq1pos : 0 < 1 - q := by nlinarith
  by_cases hpq : p = q
  · rw [hpq, bernH_self]
  · rcases lt_or_gt_of_ne hpq with hp_lt_q | hq_lt_p
    · have hslope_le := hconv.slope_le_of_hasDerivAt hp_mem hq_mem hp_lt_q
        (hasDerivAt_bernH q q hqpos.ne' hq1pos.ne')
      rw [bernHDeriv_self] at hslope_le
      rw [slope_def_field] at hslope_le
      have hden : 0 < q - p := sub_pos.mpr hp_lt_q
      have hnum_nonpos : bernH q q - bernH q p ≤ 0 := by
        have hmul := mul_le_mul_of_nonneg_right hslope_le (le_of_lt hden)
        rw [div_mul_cancel₀ _ hden.ne'] at hmul
        simpa using hmul
      rw [bernH_self] at hnum_nonpos
      linarith
    · have hzero_le_slope := hconv.le_slope_of_hasDerivAt hq_mem hp_mem hq_lt_p
        (hasDerivAt_bernH q q hqpos.ne' hq1pos.ne')
      rw [bernHDeriv_self] at hzero_le_slope
      rw [slope_def_field] at hzero_le_slope
      have hden : 0 < p - q := sub_pos.mpr hq_lt_p
      have hnum_nonneg : 0 ≤ bernH q p - bernH q q := by
        have hmul := mul_nonneg hzero_le_slope (le_of_lt hden)
        rw [div_mul_cancel₀ _ hden.ne'] at hmul
        simpa using hmul
      rw [bernH_self] at hnum_nonneg
      linarith

private lemma bernoulliKL_eq_bregman {p q : ℝ}
    (hp0 : p ≠ 0) (hp1 : 1 - p ≠ 0) (hq0 : q ≠ 0) (hq1 : 1 - q ≠ 0) :
    p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) =
      bernD p - bernD q - (Real.log q - Real.log (1 - q)) * (p - q) := by
  rw [Real.log_div hp0 hq0, Real.log_div hp1 hq1]
  unfold bernD
  ring

/-- Bernoulli KL divergence on the band `[1/4, 3/4]` is bounded by
`4 · (p - q) ^ 2`. -/
theorem bernoulli_kl_le_four_sq_sub_of_mem_quarter_band
    {p q : ℝ} (hp_lo : (1 : ℝ) / 4 ≤ p) (hp_hi : p ≤ 3 / 4)
    (hq_lo : (1 : ℝ) / 4 ≤ q) (hq_hi : q ≤ 3 / 4) :
    p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))
      ≤ 4 * (p - q) ^ 2 := by
  have hp0 : p ≠ 0 := by nlinarith
  have hp1 : 1 - p ≠ 0 := by nlinarith
  have hq0 : q ≠ 0 := by nlinarith
  have hq1 : 1 - q ≠ 0 := by nlinarith
  rw [bernoulliKL_eq_bregman hp0 hp1 hq0 hq1]
  have hnonneg := bernH_nonneg_of_mem_quarter_band hp_lo hp_hi hq_lo hq_hi
  unfold bernH at hnonneg
  linarith

end Causalean.Mathlib.Analysis
