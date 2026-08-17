import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.Names
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Rat.BigOperators

/-!
# Rational real transcendental enclosures

This module defines executable Machin/Taylor enclosures for π, sine, cosine,
and the real exponential. Raw rational bounds are recursively intersected, so
adjacent-fuel nesting follows from finite intersection rather than from an
order asserted between unrelated tolerance parameters. Complex exponential
composition and its magnitude-sensitive name semantics live in `ComplexExp`.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace Transcendental

/-- The rational alternating Taylor sum through degree `2 * fuel + 1`
approximates arctangent on the unit interval. -/
def atanPartial (q : ℚ) (fuel : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (fuel + 1),
    (-1 : ℚ) ^ k * q ^ (2 * k + 1) / (2 * k + 1 : ℕ)

/-- The first omitted arctangent term is a rational absolute error bound when
the argument has absolute value at most one. -/
def atanError (q : ℚ) (fuel : ℕ) : ℚ :=
  |q| ^ (2 * fuel + 3) / (2 * fuel + 3 : ℕ)

/-- A rational arctangent Taylor sum widened by its first omitted term. -/
def atanRaw (q : ℚ) (fuel : ℕ) : RatInterval :=
  ⟨atanPartial q fuel - atanError q fuel,
    atanPartial q fuel + atanError q fuel, by
      have : 0 ≤ atanError q fuel := by
        simp only [atanError]
        positivity
      linarith⟩

/-- Machin's formula combines two rational arctangent enclosures without
using an exact π endpoint. -/
def piRaw (fuel : ℕ) : RatInterval :=
  (RatInterval.point 4).mul
    ((RatInterval.point 4).mul (atanRaw (1 / 5) fuel) |>.sub
      (atanRaw (1 / 239) fuel))

/-- Successive π approximations are recursive finite intersections of Machin bounds. -/
def piInterval : ℕ → RatInterval
  | 0 => piRaw 0
  | fuel + 1 => (piInterval fuel).tighten (piRaw (fuel + 1))

/-- A denominator-sensitive executable fuel for a requested π width. -/
def piPrecision (ε : PosRat) : ℕ := 8 * (ε.1.den + 1)

private theorem atan_taylor_error_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (fuel : ℕ) :
    |Real.arctan q - ∑ k ∈ Finset.range (fuel + 1),
      (-1 : ℝ) ^ k * q ^ (2 * k + 1) / (2 * k + 1 : ℕ)| ≤
        |q| ^ (2 * fuel + 3) / (2 * fuel + 3 : ℕ) := by
  let f : ℕ → ℝ := fun k => q ^ (2 * k + 1) / (2 * k + 1 : ℕ)
  have hfanti : Antitone f := antitone_nat_of_succ_le (fun n => by
    dsimp [f]
    apply div_le_div₀ (by positivity)
      (pow_le_pow_of_le_one hq0 hq1.le (by omega)) (by positivity) (by norm_num))
  have harctan := Real.hasSum_arctan (x := q)
    (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0])
  have hsum : HasSum (fun n => (-1 : ℝ) ^ n * f n) (Real.arctan q) := by
    simpa only [f, div_eq_mul_inv, mul_assoc] using harctan
  have hfs : Summable f := by
    have hn := harctan.summable.norm
    convert hn using 1
    funext n
    simp only [f, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      abs_of_nonneg hq0, abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * n + 1 : ℕ))]
  have hb := alternating_series_error_bound f hfanti hfs (fuel + 1)
  rw [hsum.tsum_eq] at hb
  convert hb using 1 <;>
    simp [f, abs_of_nonneg hq0, div_eq_mul_inv] <;> ring

private theorem atanRaw_sound_of_nonneg_lt_one (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (fuel : ℕ) : (atanRaw q fuel).Contains (Real.arctan q) := by
  have hb := atan_taylor_error_bound (q : ℝ) (by exact_mod_cast hq0)
    (by exact_mod_cast hq1) fuel
  have hp : ((atanPartial q fuel : ℚ) : ℝ) =
      ∑ k ∈ Finset.range (fuel + 1),
        (-1 : ℝ) ^ k * (q : ℝ) ^ (2 * k + 1) / (2 * k + 1 : ℕ) := by
    simp [atanPartial]
  have he : ((atanError q fuel : ℚ) : ℝ) =
      |(q : ℝ)| ^ (2 * fuel + 3) / (2 * fuel + 3 : ℕ) := by
    simp [atanError]
  rw [← hp, ← he, abs_le] at hb
  exact ⟨by simpa [atanRaw] using hb.1, by simpa [atanRaw, add_comm] using hb.2⟩

/-- Every raw Machin rectangle contains the mathematical constant π. -/
theorem piRaw_sound (fuel : ℕ) : (piRaw fuel).Contains Real.pi := by
  have hfour := RatInterval.point_sound 4
  have h5 := atanRaw_sound_of_nonneg_lt_one (1 / 5) (by norm_num) (by norm_num) fuel
  have h239 := atanRaw_sound_of_nonneg_lt_one (1 / 239) (by norm_num) (by norm_num) fuel
  have h := RatInterval.mul_sound hfour
    (RatInterval.sub_sound (RatInterval.mul_sound hfour h5) h239)
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have heq : (4 : ℝ) * ((4 : ℝ) * Real.arctan (1 / 5 : ℝ) -
      Real.arctan (1 / 239 : ℝ)) = Real.pi := by
    norm_num [div_eq_mul_inv]
    nlinarith [hm]
  rw [← heq]
  simpa [piRaw] using h

/-- Every recursively intersected π rectangle contains π. -/
theorem piInterval_sound (fuel : ℕ) : (piInterval fuel).Contains Real.pi := by
  induction fuel with
  | zero => exact piRaw_sound 0
  | succ fuel ih =>
      exact RatInterval.tighten_sound ih (piRaw_sound (fuel + 1))

/-- Adjacent π fuel values are nested by construction through finite intersection. -/
theorem piInterval_nested (fuel : ℕ) :
    (piInterval (fuel + 1)).Subinterval (piInterval fuel) := by
  exact RatInterval.tighten_subinterval_left
    (piInterval_sound fuel) (piRaw_sound (fuel + 1))

private theorem width_point_mul (q : ℚ) (hq : 0 ≤ q) (I : RatInterval) :
    ((RatInterval.point q).mul I).width = q * I.width := by
  have h : q * I.lo ≤ q * I.hi := mul_le_mul_of_nonneg_left I.lo_le_hi hq
  simp [RatInterval.mul, RatInterval.point, RatInterval.width, h]
  ring

private theorem piRaw_width_eq (fuel : ℕ) :
    (piRaw fuel).width =
      32 * atanError (1 / 5) fuel + 8 * atanError (1 / 239) fuel := by
  rw [piRaw, width_point_mul 4 (by norm_num), RatInterval.width_sub,
    width_point_mul 4 (by norm_num)]
  simp [atanRaw, RatInterval.width]
  ring

private theorem piInterval_subinterval_raw (fuel : ℕ) :
    (piInterval fuel).Subinterval (piRaw fuel) := by
  cases fuel with
  | zero => exact RatInterval.subinterval_refl _
  | succ fuel =>
      rw [piInterval]
      exact Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.tighten_subinterval_right
        (piInterval_sound fuel) (piRaw_sound (fuel + 1))

/-- The explicit π precision returns an enclosure within the requested rational width. -/
theorem piInterval_width (ε : PosRat) :
    (piInterval (piPrecision ε)).width ≤ ε.1 := by
  let N := piPrecision ε
  have hw := RatInterval.width_mono (piInterval_subinterval_raw N)
  rw [piRaw_width_eq] at hw
  have hp5 : |(1 / 5 : ℚ)| ^ (2 * N + 3) ≤ 1 / 125 := by
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 5)]
    norm_num [show 2 * N + 3 = 3 + 2 * N by omega, pow_add]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hp239 : |(1 / 239 : ℚ)| ^ (2 * N + 3) ≤ 1 / 125 := by
    calc
      _ ≤ |(1 / 5 : ℚ)| ^ (2 * N + 3) := by gcongr <;> norm_num
      _ ≤ _ := hp5
  have he5 : atanError (1 / 5) N ≤ (1 / 125) / (2 * N + 3 : ℕ) := by
    rw [atanError]
    exact div_le_div_of_nonneg_right hp5 (by positivity)
  have he239 : atanError (1 / 239) N ≤ (1 / 125) / (2 * N + 3 : ℕ) := by
    rw [atanError]
    exact div_le_div_of_nonneg_right hp239 (by positivity)
  have hden : (16 : ℚ) * ε.1.den ≤ (2 * N + 3 : ℕ) := by
    dsimp [N, piPrecision]
    push_cast
    nlinarith
  have hεden : (1 : ℚ) ≤ ε.1 * ε.1.den := by
    have hn : 0 < ε.1.num := (Rat.num_pos).2 ε.2
    have hr := Rat.num_div_den ε.1
    have hd : (0 : ℚ) < ε.1.den := by exact_mod_cast ε.1.den_pos
    have heq : (ε.1.num : ℚ) = ε.1 * ε.1.den := (div_eq_iff hd.ne').mp hr
    rw [← heq]
    exact_mod_cast hn
  have hcoarse : 40 * ((1 / 125 : ℚ) / (2 * N + 3 : ℕ)) ≤ ε.1 := by
    rw [show 40 * ((1 / 125 : ℚ) / (2 * N + 3 : ℕ)) =
      (40 * (1 / 125 : ℚ)) / (2 * N + 3 : ℕ) by ring]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < (2 * N + 3 : ℕ))).2
    have hprod : 16 ≤ ε.1 * (2 * N + 3 : ℕ) := by
      nlinarith [mul_le_mul_of_nonneg_left hden ε.2.le]
    norm_num [Nat.cast_add, Nat.cast_mul] at hprod ⊢
    exact (by norm_num : (8 / 25 : ℚ) ≤ 16).trans hprod
  exact hw.trans (by nlinarith [he5, he239, hcoarse])

/-- The Machin enclosure sequence packages π as an effectively refining certified real name. -/
noncomputable def piName : CertifiedReal where
  value := Real.pi
  approx := piInterval
  nested := piInterval_nested
  contains := piInterval_sound
  modulus := piPrecision
  width_modulus := piInterval_width

/-- The rational sine Taylor polynomial retains terms through the requested fuel. -/
def sinPartial (q : ℚ) (fuel : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (fuel + 1),
    (-1 : ℚ) ^ k * q ^ (2 * k + 1) / ((2 * k + 1).factorial : ℚ)

/-- The absolute first omitted sine Taylor scale is an executable rational remainder bound. -/
def sinError (q : ℚ) (fuel : ℕ) : ℚ :=
  |q| ^ (2 * fuel + 3) / ((2 * fuel + 3).factorial : ℚ)

/-- The rational cosine Taylor polynomial retains terms through the requested fuel. -/
def cosPartial (q : ℚ) (fuel : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (fuel + 1),
    (-1 : ℚ) ^ k * q ^ (2 * k) / ((2 * k).factorial : ℚ)

/-- The absolute first omitted cosine Taylor scale is an executable rational remainder bound. -/
def cosError (q : ℚ) (fuel : ℕ) : ℚ :=
  |q| ^ (2 * fuel + 2) / ((2 * fuel + 2).factorial : ℚ)

/-- A rational sine Taylor value widened by its explicit remainder. -/
def sinRaw (q : ℚ) (fuel : ℕ) : RatInterval :=
  ⟨sinPartial q fuel - sinError q fuel,
    sinPartial q fuel + sinError q fuel, by
      have : 0 ≤ sinError q fuel := by
        simp only [sinError]
        positivity
      linarith⟩

/-- A rational cosine Taylor value widened by its explicit remainder. -/
def cosRaw (q : ℚ) (fuel : ℕ) : RatInterval :=
  ⟨cosPartial q fuel - cosError q fuel,
    cosPartial q fuel + cosError q fuel, by
      have : 0 ≤ cosError q fuel := by
        simp only [cosError]
        positivity
      linarith⟩

/-- The rational midpoint of an interval is used only as a Taylor expansion center. -/
def intervalMid (I : RatInterval) : ℚ := (I.lo + I.hi) / 2

/-- Half the rational interval width bounds distance from every enclosed point to its midpoint. -/
def intervalRadius (I : RatInterval) : ℚ := I.width / 2

/-- Raw sine interval evaluation adds the input-radius Lipschitz error to a
rational Taylor enclosure at the midpoint. -/
def sinIntervalRaw (I : RatInterval) (fuel : ℕ) : RatInterval :=
  (sinRaw (intervalMid I) fuel).expand (intervalRadius I) (by
    exact div_nonneg (RatInterval.width_nonneg I) (by norm_num))

/-- Raw cosine interval evaluation adds the input-radius Lipschitz error to a
rational Taylor enclosure at the midpoint. -/
def cosIntervalRaw (I : RatInterval) (fuel : ℕ) : RatInterval :=
  (cosRaw (intervalMid I) fuel).expand (intervalRadius I) (by
    exact div_nonneg (RatInterval.width_nonneg I) (by norm_num))

/-- Sine interval outputs recursively intersect all raw bounds seen so far. -/
def sinInterval (I : RatInterval) : ℕ → RatInterval
  | 0 => sinIntervalRaw I 0
  | fuel + 1 => (sinInterval I fuel).tighten (sinIntervalRaw I (fuel + 1))

/-- Cosine interval outputs recursively intersect all raw bounds seen so far. -/
def cosInterval (I : RatInterval) : ℕ → RatInterval
  | 0 => cosIntervalRaw I 0
  | fuel + 1 => (cosInterval I fuel).tighten (cosIntervalRaw I (fuel + 1))

private theorem taylorWithinEval_sin_eq (q : ℝ) (hq : 0 < q) (fuel : ℕ) :
    taylorWithinEval Real.sin (2 * fuel + 2) (Set.Icc 0 q) 0 q =
      ∑ k ∈ Finset.range (fuel + 1),
        (-1 : ℝ) ^ k * q ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) := by
  have hder (m : ℕ) : iteratedDerivWithin m Real.sin (Set.Icc 0 q) 0 =
      iteratedDeriv m Real.sin 0 :=
    Real.iteratedDerivWithin_sin_Icc m hq ⟨le_rfl, hq.le⟩
  induction fuel with
  | zero =>
      rw [show 2 * 0 + 2 = 0 + 1 + 1 by omega]
      rw [taylorWithinEval_succ, taylorWithinEval_succ]
      simp [hder]
  | succ n ih =>
      rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 1 + 1 by omega]
      rw [taylorWithinEval_succ, taylorWithinEval_succ, ih, hder, hder]
      have ho : iteratedDeriv (2 * n + 2 + 1) Real.sin 0 = (-1 : ℝ) ^ (n + 1) := by
        rw [show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by omega,
          Real.iteratedDeriv_odd_sin]
        simp
      have he : iteratedDeriv (2 * n + 2 + 1 + 1) Real.sin 0 = 0 := by
        rw [show 2 * n + 2 + 1 + 1 = 2 * (n + 2) by omega,
          Real.iteratedDeriv_even_sin]
        simp
      rw [ho, he]
      simp only [mul_zero, add_zero, smul_eq_mul]
      conv_rhs => rw [Finset.sum_range_succ]
      congr 1
      rw [show (2 * n + 2).factorial = (2 * n + 2) * (2 * n + 1).factorial by
        rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.factorial_succ],
        show (2 * (n + 1) + 1).factorial =
            (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial by
          rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega,
            show 2 * n + 3 = (2 * n + 2) + 1 by omega, Nat.factorial_succ,
            show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.factorial_succ]
          ring]
      push_cast
      field_simp
      ring

private theorem taylorWithinEval_cos_eq (q : ℝ) (hq : 0 < q) (fuel : ℕ) :
    taylorWithinEval Real.cos (2 * fuel + 1) (Set.Icc 0 q) 0 q =
      ∑ k ∈ Finset.range (fuel + 1),
        (-1 : ℝ) ^ k * q ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  have hder (m : ℕ) : iteratedDerivWithin m Real.cos (Set.Icc 0 q) 0 =
      iteratedDeriv m Real.cos 0 :=
    Real.iteratedDerivWithin_cos_Icc m hq ⟨le_rfl, hq.le⟩
  induction fuel with
  | zero =>
      rw [show 2 * 0 + 1 = 0 + 1 by omega, taylorWithinEval_succ]
      simp [hder]
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
      rw [taylorWithinEval_succ, taylorWithinEval_succ, ih, hder, hder]
      have he : iteratedDeriv (2 * n + 1 + 1) Real.cos 0 = (-1 : ℝ) ^ (n + 1) := by
        rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
          Real.iteratedDeriv_even_cos]
        simp
      have ho : iteratedDeriv (2 * n + 1 + 1 + 1) Real.cos 0 = 0 := by
        rw [show 2 * n + 1 + 1 + 1 = 2 * (n + 1) + 1 by omega,
          Real.iteratedDeriv_odd_cos]
        simp
      rw [he, ho]
      simp only [mul_zero, add_zero, smul_eq_mul]
      conv_rhs => rw [Finset.sum_range_succ]
      congr 1
      rw [show (2 * n + 1).factorial = (2 * n + 1) * (2 * n).factorial by
        rw [Nat.factorial_succ],
        show (2 * (n + 1)).factorial =
            (2 * n + 2) * (2 * n + 1) * (2 * n).factorial by
          rw [show 2 * (n + 1) = 2 * n + 2 by omega,
            show 2 * n + 2 = (2 * n + 1) + 1 by omega,
            Nat.factorial_succ, Nat.factorial_succ]
          ring]
      push_cast
      field_simp
      ring

private theorem sin_taylor_error_bound_pos (q : ℝ) (hq : 0 < q) (fuel : ℕ) :
    |Real.sin q - ∑ k ∈ Finset.range (fuel + 1),
      (-1 : ℝ) ^ k * q ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)| ≤
        |q| ^ (2 * fuel + 3) / ((2 * fuel + 3).factorial : ℝ) := by
  obtain ⟨x', _, hr⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.sin) (x₀ := 0) (x := q) (n := 2 * fuel + 2) hq
      Real.contDiff_sin.contDiffOn
  rw [taylorWithinEval_sin_eq q hq fuel] at hr
  rw [hr]
  simp only [show 2 * fuel + 2 + 1 = 2 * fuel + 3 by omega, sub_zero]
  have hfac : |(((2 * fuel + 3).factorial : ℕ) : ℝ)| =
      ((2 * fuel + 3).factorial : ℝ) := abs_of_nonneg (by positivity)
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hq, hfac]
  have hd := Real.abs_iteratedDeriv_sin_le_one (2 * fuel + 3) x'
  have hp : 0 ≤ q ^ (2 * fuel + 3) := by positivity
  have hf : (0 : ℝ) < (2 * fuel + 3).factorial := by positivity
  apply (div_le_div_iff_of_pos_right hf).2
  nlinarith

private theorem sin_taylor_error_bound (q : ℝ) (fuel : ℕ) :
    |Real.sin q - ∑ k ∈ Finset.range (fuel + 1),
      (-1 : ℝ) ^ k * q ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)| ≤
        |q| ^ (2 * fuel + 3) / ((2 * fuel + 3).factorial : ℝ) := by
  rcases lt_trichotomy q 0 with hneg | rfl | hpos
  · have h := sin_taylor_error_bound_pos (-q) (neg_pos.mpr hneg) fuel
    have hsum :
        (∑ k ∈ Finset.range (fuel + 1),
          (-1 : ℝ) ^ k * (-q) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) =
        -(∑ k ∈ Finset.range (fuel + 1),
          (-1 : ℝ) ^ k * q ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp [pow_succ, pow_mul]
      ring
    rw [hsum] at h
    have hrewrite : Real.sin (-q) -
        -(∑ k ∈ Finset.range (fuel + 1),
          (-1 : ℝ) ^ k * q ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) =
        -(Real.sin q - ∑ k ∈ Finset.range (fuel + 1),
          (-1 : ℝ) ^ k * q ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) := by
      rw [Real.sin_neg]
      ring
    rw [hrewrite, abs_neg] at h
    simpa using h
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb0
      simp [hb0]
    · simp
  · exact sin_taylor_error_bound_pos q hpos fuel

private theorem cos_taylor_error_bound_pos (q : ℝ) (hq : 0 < q) (fuel : ℕ) :
    |Real.cos q - ∑ k ∈ Finset.range (fuel + 1),
      (-1 : ℝ) ^ k * q ^ (2 * k) / ((2 * k).factorial : ℝ)| ≤
        |q| ^ (2 * fuel + 2) / ((2 * fuel + 2).factorial : ℝ) := by
  obtain ⟨x', _, hr⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.cos) (x₀ := 0) (x := q) (n := 2 * fuel + 1) hq
      Real.contDiff_cos.contDiffOn
  rw [taylorWithinEval_cos_eq q hq fuel] at hr
  rw [hr]
  simp only [show 2 * fuel + 1 + 1 = 2 * fuel + 2 by omega, sub_zero]
  have hfac : |(((2 * fuel + 2).factorial : ℕ) : ℝ)| =
      ((2 * fuel + 2).factorial : ℝ) := abs_of_nonneg (by positivity)
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hq, hfac]
  have hd := Real.abs_iteratedDeriv_cos_le_one (2 * fuel + 2) x'
  have hp : 0 ≤ q ^ (2 * fuel + 2) := by positivity
  have hf : (0 : ℝ) < (2 * fuel + 2).factorial := by positivity
  apply (div_le_div_iff_of_pos_right hf).2
  nlinarith

private theorem cos_taylor_error_bound (q : ℝ) (fuel : ℕ) :
    |Real.cos q - ∑ k ∈ Finset.range (fuel + 1),
      (-1 : ℝ) ^ k * q ^ (2 * k) / ((2 * k).factorial : ℝ)| ≤
        |q| ^ (2 * fuel + 2) / ((2 * fuel + 2).factorial : ℝ) := by
  rcases lt_trichotomy q 0 with hneg | rfl | hpos
  · have h := cos_taylor_error_bound_pos (-q) (neg_pos.mpr hneg) fuel
    have hsum :
        (∑ k ∈ Finset.range (fuel + 1),
          (-1 : ℝ) ^ k * (-q) ^ (2 * k) / ((2 * k).factorial : ℝ)) =
        ∑ k ∈ Finset.range (fuel + 1),
          (-1 : ℝ) ^ k * q ^ (2 * k) / ((2 * k).factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      simp [pow_mul]
    rw [hsum] at h
    simpa using h
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb0
      simp [hb0]
    · simp
  · exact cos_taylor_error_bound_pos q hpos fuel

/-- Raw rational sine bounds contain the exact sine at every rational center. -/
theorem sinRaw_sound (q : ℚ) (fuel : ℕ) :
    (sinRaw q fuel).Contains (Real.sin q) := by
  have hb := sin_taylor_error_bound (q : ℝ) fuel
  have hp : ((sinPartial q fuel : ℚ) : ℝ) =
      ∑ k ∈ Finset.range (fuel + 1),
        (-1 : ℝ) ^ k * (q : ℝ) ^ (2 * k + 1) /
          ((2 * k + 1).factorial : ℝ) := by simp [sinPartial]
  have he : ((sinError q fuel : ℚ) : ℝ) =
      |(q : ℝ)| ^ (2 * fuel + 3) / ((2 * fuel + 3).factorial : ℝ) := by
    simp [sinError]
  rw [← hp, ← he, abs_le] at hb
  exact ⟨by simpa [sinRaw] using hb.1, by simpa [sinRaw, add_comm] using hb.2⟩

/-- Raw rational cosine bounds contain the exact cosine at every rational center. -/
theorem cosRaw_sound (q : ℚ) (fuel : ℕ) :
    (cosRaw q fuel).Contains (Real.cos q) := by
  have hb := cos_taylor_error_bound (q : ℝ) fuel
  have hp : ((cosPartial q fuel : ℚ) : ℝ) =
      ∑ k ∈ Finset.range (fuel + 1),
        (-1 : ℝ) ^ k * (q : ℝ) ^ (2 * k) / ((2 * k).factorial : ℝ) := by
    simp [cosPartial]
  have he : ((cosError q fuel : ℚ) : ℝ) =
      |(q : ℝ)| ^ (2 * fuel + 2) / ((2 * fuel + 2).factorial : ℝ) := by
    simp [cosError]
  rw [← hp, ← he, abs_le] at hb
  exact ⟨by simpa [cosRaw] using hb.1, by simpa [cosRaw, add_comm] using hb.2⟩

private theorem abs_sub_intervalMid_le_radius {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) : |x - (intervalMid I : ℝ)| ≤ (intervalRadius I : ℝ) := by
  have hlo : (I.lo : ℝ) ≤ x := hx.1
  have hhi : x ≤ (I.hi : ℝ) := hx.2
  rw [abs_le]
  simp only [intervalMid, intervalRadius, RatInterval.width, Rat.cast_div,
    Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat]
  constructor <;> linarith

private theorem sinIntervalRaw_sound {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) (fuel : ℕ) :
    (sinIntervalRaw I fuel).Contains (Real.sin x) := by
  have hc := sinRaw_sound (intervalMid I) fuel
  have hd := (Real.abs_sin_sub_sin_le x (intervalMid I : ℝ)).trans
    (abs_sub_intervalMid_le_radius hx)
  rw [abs_le] at hd
  unfold sinIntervalRaw
  simp only [RatInterval.expand, RatInterval.Contains, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith [hc.1, hc.2, hd.1, hd.2]

private theorem cosIntervalRaw_sound {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) (fuel : ℕ) :
    (cosIntervalRaw I fuel).Contains (Real.cos x) := by
  have hc := cosRaw_sound (intervalMid I) fuel
  have hd := (Real.abs_cos_sub_cos_le x (intervalMid I : ℝ)).trans
    (abs_sub_intervalMid_le_radius hx)
  rw [abs_le] at hd
  unfold cosIntervalRaw
  simp only [RatInterval.expand, RatInterval.Contains, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith [hc.1, hc.2, hd.1, hd.2]

/-- Sine interval evaluation encloses sine throughout the input interval. -/
theorem sinInterval_sound {I : RatInterval} {x : ℝ} (hx : I.Contains x) (fuel : ℕ) :
    (sinInterval I fuel).Contains (Real.sin x) := by
  induction fuel with
  | zero => exact sinIntervalRaw_sound hx 0
  | succ fuel ih => exact RatInterval.tighten_sound ih (sinIntervalRaw_sound hx (fuel + 1))

/-- Cosine interval evaluation encloses cosine throughout the input interval. -/
theorem cosInterval_sound {I : RatInterval} {x : ℝ} (hx : I.Contains x) (fuel : ℕ) :
    (cosInterval I fuel).Contains (Real.cos x) := by
  induction fuel with
  | zero => exact cosIntervalRaw_sound hx 0
  | succ fuel ih => exact RatInterval.tighten_sound ih (cosIntervalRaw_sound hx (fuel + 1))

/-- Adjacent sine outputs are nested by recursive finite intersection. -/
theorem sinInterval_nested (I : RatInterval) (fuel : ℕ) :
    (sinInterval I (fuel + 1)).Subinterval (sinInterval I fuel) := by
  have hmid : I.Contains (intervalMid I : ℝ) := by
    constructor <;> exact_mod_cast (by
      dsimp [intervalMid]
      linarith [I.lo_le_hi])
  exact RatInterval.tighten_subinterval_left
    (sinInterval_sound hmid fuel) (sinIntervalRaw_sound hmid (fuel + 1))

/-- Adjacent cosine outputs are nested by recursive finite intersection. -/
theorem cosInterval_nested (I : RatInterval) (fuel : ℕ) :
    (cosInterval I (fuel + 1)).Subinterval (cosInterval I fuel) := by
  have hmid : I.Contains (intervalMid I : ℝ) := by
    constructor <;> exact_mod_cast (by
      dsimp [intervalMid]
      linarith [I.lo_le_hi])
  exact RatInterval.tighten_subinterval_left
    (cosInterval_sound hmid fuel) (cosIntervalRaw_sound hmid (fuel + 1))

/-- Sine output width is the shrinking input diameter plus its explicit Taylor error. -/
theorem sinInterval_width (I : RatInterval) (fuel : ℕ) :
    (sinInterval I fuel).width ≤ I.width + 2 * sinError (intervalMid I) fuel := by
  have hraw : (sinIntervalRaw I fuel).width =
      I.width + 2 * sinError (intervalMid I) fuel := by
    rw [sinIntervalRaw, RatInterval.width_expand]
    simp [sinRaw, intervalRadius, RatInterval.width]
    ring
  cases fuel with
  | zero => exact hraw.le
  | succ fuel =>
      have hmid : I.Contains (intervalMid I : ℝ) := by
        constructor <;> exact_mod_cast (by
          dsimp [intervalMid]
          linarith [I.lo_le_hi])
      exact (RatInterval.width_mono
        (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.tighten_subinterval_right
          (sinInterval_sound hmid fuel) (sinIntervalRaw_sound hmid (fuel + 1)))).trans_eq hraw

/-- Cosine output width is the shrinking input diameter plus its explicit Taylor error. -/
theorem cosInterval_width (I : RatInterval) (fuel : ℕ) :
    (cosInterval I fuel).width ≤ I.width + 2 * cosError (intervalMid I) fuel := by
  have hraw : (cosIntervalRaw I fuel).width =
      I.width + 2 * cosError (intervalMid I) fuel := by
    rw [cosIntervalRaw, RatInterval.width_expand]
    simp [cosRaw, intervalRadius, RatInterval.width]
    ring
  cases fuel with
  | zero => exact hraw.le
  | succ fuel =>
      have hmid : I.Contains (intervalMid I : ℝ) := by
        constructor <;> exact_mod_cast (by
          dsimp [intervalMid]
          linarith [I.lo_le_hi])
      exact (RatInterval.width_mono
        (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.tighten_subinterval_right
          (cosInterval_sound hmid fuel) (cosIntervalRaw_sound hmid (fuel + 1)))).trans_eq hraw

end Transcendental

end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex
