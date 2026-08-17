import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.TrigNames

/-!
# Certified exponential interval evaluation

This module evaluates the real exponential on rational intervals using midpoint enclosures and a magnitude-dependent Lipschitz allowance.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace Transcendental

/-- The exponential midpoint extension uses the promoted scalar exponential
and a magnitude-dependent Lipschitz expansion for the input radius. -/
def expIntervalRaw (I : RatInterval) (fuel : ℕ) : RatInterval :=
  let center := intervalMid I
  let ecenter :=
    Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
      center fuel
  let upper :=
    (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
      I.maxAbs fuel).hi
  ecenter.expand (upper * intervalRadius I) (by
    have hs :=
      Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar_sound
        I.maxAbs fuel
    have hu : 0 ≤ upper := by
      dsimp only [upper]
      exact_mod_cast (Real.exp_pos (I.maxAbs : ℝ)).le.trans hs.2
    exact mul_nonneg hu (div_nonneg (RatInterval.width_nonneg I) (by norm_num)))

/-- Exponential interval outputs recursively intersect all midpoint bounds seen so far. -/
def expInterval (I : RatInterval) : ℕ → RatInterval
  | 0 => expIntervalRaw I 0
  | fuel + 1 => (expInterval I fuel).tighten (expIntervalRaw I (fuel + 1))

private theorem expIntervalRaw_sound {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) (fuel : ℕ) :
    (expIntervalRaw I fuel).Contains (Real.exp x) := by
  let c : ℚ := intervalMid I
  let M : ℚ := I.maxAbs
  let E :=
    Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar c fuel
  let U : ℚ :=
    (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar M fuel).hi
  have hcI : I.Contains (c : ℝ) := by
    constructor <;> exact_mod_cast (by
      dsimp [c, intervalMid]
      linarith [I.lo_le_hi])
  have hxM : |x| ≤ (M : ℝ) := by
    exact_mod_cast abs_le_max_abs_abs hx.1 hx.2
  have hcM : |(c : ℝ)| ≤ (M : ℝ) := by
    exact_mod_cast abs_le_max_abs_abs hcI.1 hcI.2
  have hM0 : (0 : ℝ) ≤ M := (abs_nonneg x).trans hxM
  have hLip : |Real.exp x - Real.exp (c : ℝ)| ≤
      Real.exp (M : ℝ) * |x - (c : ℝ)| := by
    simpa [Real.norm_eq_abs] using
      (Convex.norm_image_sub_le_of_norm_deriv_le
        (f := Real.exp) (s := Set.Icc (-(M : ℝ)) (M : ℝ))
        (x := (c : ℝ)) (y := x) (C := Real.exp (M : ℝ))
        (fun y _ => (Real.hasDerivAt_exp y).differentiableAt)
        (fun y hy => by
          rw [Real.deriv_exp, Real.norm_eq_abs, Real.abs_exp]
          exact Real.exp_le_exp.mpr hy.2)
        (convex_Icc _ _) (by simpa [abs_le] using hcM) (by simpa [abs_le] using hxM))
  have hdist := abs_sub_intervalMid_le_radius hx
  have hES :=
    Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar_sound
      c fuel
  have hUS :=
    Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar_sound
      M fuel
  have hU : (Real.exp (M : ℝ)) ≤ (U : ℝ) := by exact hUS.2
  have hU0 : (0 : ℝ) ≤ U := (Real.exp_pos (M : ℝ)).le.trans hU
  have hr0 : (0 : ℝ) ≤ intervalRadius I := by
    exact_mod_cast div_nonneg (RatInterval.width_nonneg I) (by norm_num)
  have hd : |Real.exp x - Real.exp (c : ℝ)| ≤
      (U : ℝ) * (intervalRadius I : ℝ) :=
    hLip.trans (mul_le_mul hU hdist (abs_nonneg _) hU0)
  rw [abs_le] at hd
  unfold expIntervalRaw
  dsimp only
  simp only [RatInterval.expand, RatInterval.Contains, Rat.cast_sub, Rat.cast_add,
    Rat.cast_mul]
  constructor <;> linarith [hES.1, hES.2, hd.1, hd.2]

/-- The magnitude-dependent exponential interval contains the exponential of
every enclosed real input. -/
theorem expInterval_sound {I : RatInterval} {x : ℝ} (hx : I.Contains x) (fuel : ℕ) :
    (expInterval I fuel).Contains (Real.exp x) := by
  induction fuel with
  | zero => exact expIntervalRaw_sound hx 0
  | succ fuel ih => exact RatInterval.tighten_sound ih (expIntervalRaw_sound hx (fuel + 1))

/-- Adjacent midpoint exponential outputs are nested by finite intersection. -/
theorem expInterval_nested (I : RatInterval) (fuel : ℕ) :
    (expInterval I (fuel + 1)).Subinterval (expInterval I fuel) := by
  have hmid : I.Contains (intervalMid I : ℝ) := by
    constructor <;> exact_mod_cast (by
      dsimp [intervalMid]
      linarith [I.lo_le_hi])
  exact RatInterval.tighten_subinterval_left
    (expInterval_sound hmid fuel) (expIntervalRaw_sound hmid (fuel + 1))

/-- Exponential width propagation includes both scalar Taylor error and the
input radius amplified by a certified exponential magnitude bound. -/
theorem expInterval_width (I : RatInterval) (fuel : ℕ) :
    (expInterval I fuel).width ≤
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
        (intervalMid I) fuel).width +
      2 * (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
        I.maxAbs fuel).hi * intervalRadius I := by
  have hraw : (expIntervalRaw I fuel).width =
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
        (intervalMid I) fuel).width +
      2 * (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
        I.maxAbs fuel).hi * intervalRadius I := by
    rw [expIntervalRaw, RatInterval.width_expand]
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
          (expInterval_sound hmid fuel) (expIntervalRaw_sound hmid (fuel + 1)))).trans_eq hraw


end Transcendental

end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex
