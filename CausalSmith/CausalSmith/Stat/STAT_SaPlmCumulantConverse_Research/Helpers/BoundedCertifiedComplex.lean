import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.API
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.CertifiedTranscendental
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Paper-local bounded certified-complex combinators

The generic contour API deliberately does not package multiplication of two
certified values, because its global map interface is too strong for empirical
exponential sums.  This file supplies the bounded name-level operations needed
by the finite spectral evaluator.  Every executable approximation remains a
rational rectangle; semantic values occur only in the external certificate.
-/

noncomputable section

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

namespace CausalSmith.Stat.SaPlmCumulantConverse.BoundedCertifiedComplex

/-- [The certified name built for the complex exponential of a certified complex number denotes
exactly the complex exponential of that number's exact value](goal). -/
@[simp] lemma complexExpName_value (z : CertifiedComplex) :
    (Transcendental.complexExpName z).value = Complex.exp z.value := rfl

/-- [The certified name for the circle constant denotes exactly the real number pi](goal). -/
@[simp] lemma piName_value : Transcendental.piName.value = Real.pi := rfl

/-- [The exact value of the certified sum of two certified complex numbers is the sum of their
exact values](goal). -/
@[simp] lemma certifiedAdd_value (z w : CertifiedComplex) :
    (z.add w).value = z.value + w.value := rfl

private lemma width_mono {I J : ComplexRatInterval} (h : I.Subinterval J) :
    I.width ≤ J.width :=
  max_le_max (RatInterval.width_mono h.1) (RatInterval.width_mono h.2)

private lemma maxAbs_mono {I J : ComplexRatInterval} (h : I.Subinterval J) :
    I.maxAbs ≤ J.maxAbs :=
  max_le_max (ComplexRatInterval.rat_maxAbs_mono h.1)
    (ComplexRatInterval.rat_maxAbs_mono h.2)

private lemma approx_mono (z : CertifiedComplex) {m n : ℕ} (h : m ≤ n) :
    (z.approx n).Subinterval (z.approx m) := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩
  | succ n h ih =>
      exact ⟨RatInterval.subinterval_trans (z.nested n).1 ih.1,
        RatInterval.subinterval_trans (z.nested n).2 ih.2⟩

/-- A certified real regarded as a certified complex number with zero imaginary part. -/
def ofReal (x : CertifiedReal) : CertifiedComplex where
  value := x.value
  approx := fun n ↦ ⟨x.approx n, RatInterval.point 0⟩
  nested := fun n ↦ ⟨x.nested n, RatInterval.subinterval_refl _⟩
  contains := fun n ↦ ⟨by simpa using x.contains n,
    by simpa using RatInterval.point_sound 0⟩
  modulus := x.modulus
  width_modulus := by
    intro ε
    simp only [ComplexRatInterval.width, RatInterval.width, RatInterval.point, sub_self]
    apply max_le
    · exact x.width_modulus ε
    · exact ε.2.le

/-- [Viewing a certified real number as a certified complex number with zero imaginary part
leaves its exact value unchanged](goal). -/
@[simp] lemma ofReal_value (x : CertifiedReal) : (ofReal x).value = x.value := rfl

/-- Recursive intersections of raw rectangle products. -/
def mulApprox (z w : CertifiedComplex) : ℕ → ComplexRatInterval
  | 0 => (z.approx 0).mul (w.approx 0)
  | n + 1 => (mulApprox z w n).tighten ((z.approx (n + 1)).mul (w.approx (n + 1)))

/-- [Every stage of the recursively intersected rectangle products encloses the product of the
two exact values, the stages are nested one inside the previous one, and each stage refines the
raw rectangle product of the two inputs at that same stage](goal).

These are exactly the three obligations needed to package the sequence as a certified complex
number: soundness, nestedness, and no loss relative to the plain interval product. -/
lemma mulApprox_spec (z w : CertifiedComplex) (n : ℕ) :
    (mulApprox z w n).Contains (z.value * w.value) ∧
      (mulApprox z w (n + 1)).Subinterval (mulApprox z w n) ∧
      (mulApprox z w n).Subinterval ((z.approx n).mul (w.approx n)) := by
  induction n with
  | zero =>
      have h := ComplexRatInterval.mul_sound (z.contains 0) (w.contains 0)
      exact ⟨h, (ComplexRatInterval.tighten_sound_left h
        (ComplexRatInterval.mul_sound (z.contains 1) (w.contains 1))).2,
        ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩⟩
  | succ n ih =>
      have hnew := ComplexRatInterval.mul_sound (z.contains (n + 1)) (w.contains (n + 1))
      have hcur : (mulApprox z w (n + 1)).Contains (z.value * w.value) := by
        rw [mulApprox]
        exact (ComplexRatInterval.tighten_sound_left ih.1 hnew).1
      have hnext := ComplexRatInterval.mul_sound (z.contains (n + 2)) (w.contains (n + 2))
      exact ⟨hcur, by
        rw [show n + 1 + 1 = n + 2 by omega, mulApprox]
        exact (ComplexRatInterval.tighten_sound_left hcur hnext).2,
        by
          rw [mulApprox]
          exact ⟨
            Transcendental.tighten_subinterval_right ih.1.1 hnew.1,
            Transcendental.tighten_subinterval_right ih.1.2 hnew.2⟩⟩

private def mulTolerance (z w : CertifiedComplex) (ε : PosRat) : PosRat :=
  let A := (z.approx 0).maxAbs
  let B := (w.approx 0).maxAbs
  ⟨ε.1 / (4 * (A + B + 1)), by
    have hA : 0 ≤ A := (abs_nonneg (z.approx 0).re.lo).trans
      ((le_max_left _ _).trans (le_max_left _ _))
    have hB : 0 ≤ B := (abs_nonneg (w.approx 0).re.lo).trans
      ((le_max_left _ _).trans (le_max_left _ _))
    exact div_pos ε.2 (mul_pos (by norm_num) (by linarith))⟩

/-- The stage index at which the certified product of two complex numbers is guaranteed to be
accurate to a requested rational tolerance: the larger of the two stage indices at which each
factor's own modulus of convergence delivers an internally derived, magnitude-adjusted
tolerance. -/
def mulPrecision (z w : CertifiedComplex) (ε : PosRat) : ℕ :=
  max (z.modulus (mulTolerance z w ε)) (w.modulus (mulTolerance z w ε))

/-- [At the stage index selected by the product precision schedule, the rectangle enclosing the
product of two certified complex numbers has width at most the requested tolerance](goal). -/
lemma mul_width_at_precision (z w : CertifiedComplex) (ε : PosRat) :
    (mulApprox z w (mulPrecision z w ε)).width ≤ ε.1 := by
  let δ := mulTolerance z w ε
  let k := mulPrecision z w ε
  let A := (z.approx 0).maxAbs
  let B := (w.approx 0).maxAbs
  have hzmono : (z.approx k).Subinterval (z.approx 0) :=
    approx_mono z (Nat.zero_le k)
  have hwmono : (w.approx k).Subinterval (w.approx 0) :=
    approx_mono w (Nat.zero_le k)
  have hzwidth : (z.approx k).width ≤ δ.1 :=
    (width_mono (approx_mono z (le_max_left _ _))).trans
      (z.width_modulus δ)
  have hwwidth : (w.approx k).width ≤ δ.1 :=
    (width_mono (approx_mono w (le_max_right _ _))).trans
      (w.width_modulus δ)
  have hzA : (z.approx k).maxAbs ≤ A := maxAbs_mono hzmono
  have hwB : (w.approx k).maxAbs ≤ B := maxAbs_mono hwmono
  have hA : 0 ≤ A := (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hB : 0 ≤ B := (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hzA0 : 0 ≤ (z.approx k).maxAbs :=
    (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hwB0 : 0 ≤ (w.approx k).maxAbs :=
    (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hraw := ComplexRatInterval.mul_width (z.approx k) (w.approx k)
  have htight := width_mono (mulApprox_spec z w k).2.2
  calc
    (mulApprox z w k).width ≤ ((z.approx k).mul (w.approx k)).width := htight
    _ ≤ 2 * ((z.approx k).maxAbs * (w.approx k).width +
        (w.approx k).maxAbs * (z.approx k).width) := hraw
    _ ≤ 2 * (A * δ.1 + B * δ.1) := by
      have hzw0 : 0 ≤ (z.approx k).width :=
        (RatInterval.width_nonneg _).trans (le_max_left _ _)
      have hww0 : 0 ≤ (w.approx k).width :=
        (RatInterval.width_nonneg _).trans (le_max_left _ _)
      nlinarith [mul_le_mul hzA hwwidth hww0 hA,
        mul_le_mul hwB hzwidth hzw0 hB]
    _ ≤ ε.1 := by
      dsimp [δ, mulTolerance, A, B]
      have hden : 0 < 4 * ((z.approx 0).maxAbs + (w.approx 0).maxAbs + 1) := by
        positivity
      calc
        2 * ((z.approx 0).maxAbs *
              (ε.1 / (4 * ((z.approx 0).maxAbs + (w.approx 0).maxAbs + 1))) +
            (w.approx 0).maxAbs *
              (ε.1 / (4 * ((z.approx 0).maxAbs + (w.approx 0).maxAbs + 1)))) =
            (2 * ε.1 * ((z.approx 0).maxAbs + (w.approx 0).maxAbs)) /
              (4 * ((z.approx 0).maxAbs + (w.approx 0).maxAbs + 1)) := by ring
        _ ≤ ε.1 := by
          rw [div_le_iff₀ hden]
          nlinarith [ε.2]

/-- Multiplication of bounded certified complex names. -/
def mul (z w : CertifiedComplex) : CertifiedComplex where
  value := z.value * w.value
  approx := mulApprox z w
  nested := fun n ↦ (mulApprox_spec z w n).2.1
  contains := fun n ↦ (mulApprox_spec z w n).1
  modulus := mulPrecision z w
  width_modulus := mul_width_at_precision z w

/-- [The exact value of the certified product of two certified complex numbers is the product of
their exact values](goal). -/
@[simp] lemma mul_value (z w : CertifiedComplex) : (mul z w).value = z.value * w.value := rfl

/-- Scaling a certified complex number by a rational number, realized as the certified product
with the exact constant name for that rational. -/
def smulRat (q : ℚ) (z : CertifiedComplex) : CertifiedComplex :=
  mul (CertifiedComplex.ofRatPair q 0) z

/-- [Scaling a certified complex number by a rational number multiplies its exact value by that
rational](goal). -/
@[simp] lemma smulRat_value (q : ℚ) (z : CertifiedComplex) :
    (smulRat q z).value = (q : ℂ) * z.value := by
  simp [smulRat, CertifiedComplex.ofRatPair]

/-- Repeated certified multiplication: the zero-th power is the certified constant one, and
each further power multiplies the previous one by the base.  Every intermediate product is
itself a certified value, so the recursion carries its enclosure along. -/
def npow : CertifiedComplex → ℕ → CertifiedComplex
  | _, 0 => CertifiedComplex.ofRatPair 1 0
  | z, n + 1 => mul (npow z n) z

/-- [The exact value of the n-fold certified power of a certified complex number is the n-th
power of its exact value](goal). -/
@[simp] lemma npow_value (z : CertifiedComplex) (n : ℕ) :
    (npow z n).value = z.value ^ n := by
  induction n with
  | zero => simp [npow, CertifiedComplex.ofRatPair]
  | succ n ih => simp [npow, ih, pow_succ]

/-- The certified sum of a finite list of certified complex numbers, obtained by folding certified
addition along the list with the exact constant zero as the empty case. -/
def sum : List CertifiedComplex → CertifiedComplex
  | [] => CertifiedComplex.ofRatPair 0 0
  | z :: zs => CertifiedComplex.add z (sum zs)

/-- [The exact value of the certified sum of a list of certified complex numbers is the ordinary
sum of their exact values](goal). -/
@[simp] lemma sum_value (xs : List CertifiedComplex) :
    (sum xs).value = (xs.map CertifiedComplex.value).sum := by
  induction xs with
  | nil => simp [sum, CertifiedComplex.ofRatPair]
  | cons z zs ih =>
      rw [sum]
      change z.value + (sum zs).value = z.value + (zs.map CertifiedComplex.value).sum
      rw [ih]

/-! ## Midpoint-centered complex exponential

The direct interval extension of `exp` is not quantitatively uniform in the
reduced numerators of rational endpoints.  The spectral maps therefore
evaluate `exp` at the rational midpoint name and widen that certified point
enclosure by a box-local Lipschitz allowance.  This preserves the exact
semantic exponential while making the input-width contribution explicit.
-/

/-- Rational midpoint of a complex rectangle, coordinate by coordinate. -/
def rectangleMidpoint (I : ComplexRatInterval) : ℚ × ℚ :=
  (Transcendental.intervalMid I.re, Transcendental.intervalMid I.im)

/-- The midpoint represented as a constant certified complex name. -/
def centeredExpCenterName (I : ComplexRatInterval) : CertifiedComplex :=
  CertifiedComplex.ofRatPair (rectangleMidpoint I).1 (rectangleMidpoint I).2

/-- A rational envelope for the real exponential on the argument rectangle.
The base three dominates Euler's number, and negative real parts are covered
by the exponent zero branch. -/
def centeredExpEnvelope (I : ComplexRatInterval) : ℚ :=
  (3 : ℚ) ^ Int.toNat ⌈max 0 I.re.hi⌉

/-- [The rational exponential envelope attached to a complex rectangle is nonnegative](goal). -/
lemma centeredExpEnvelope_nonneg (I : ComplexRatInterval) :
    0 ≤ centeredExpEnvelope I := by
  unfold centeredExpEnvelope
  positivity

/-- Deterministic Taylor fuel used by the certified exponential stage at the
rational midpoint.  This name is included in traces and schedule accounting. -/
def centeredExpStageFuel (I : ComplexRatInterval) (stage : ℕ) : ℕ :=
  Transcendental.complexExpStageFuel (centeredExpCenterName I) stage

/-- Nested certified exponential enclosure at the rational midpoint. -/
def centeredExpCenterCore (I : ComplexRatInterval) (stage : ℕ) :
    ComplexRatInterval :=
  Transcendental.complexExpNameApprox (centeredExpCenterName I) stage

/-- [The Taylor fuel recorded for the midpoint-centered exponential stage on a rectangle is, by
definition, the certified-exponential stage fuel of the constant name for that rectangle's
rational midpoint](goal). -/
@[simp] lemma centeredExpStageFuel_eq (I : ComplexRatInterval) (stage : ℕ) :
    centeredExpStageFuel I stage =
      Transcendental.complexExpStageFuel (centeredExpCenterName I) stage := rfl

/-- Midpoint-centered exponential interval.  Its only dependence on the
argument rectangle width is the displayed coordinatewise expansion. -/
def centeredComplexExp (I : ComplexRatInterval) (stage : ℕ) :
    ComplexRatInterval :=
  let allowance := centeredExpEnvelope I * I.width
  (centeredExpCenterCore I stage).expand allowance
    (mul_nonneg (centeredExpEnvelope_nonneg I)
      ((RatInterval.width_nonneg I.re).trans (le_max_left _ _)))

/-- The rational envelope bounds the real exponential at every real
coordinate represented by the argument rectangle. -/
lemma centeredExpEnvelope_sound (I : ComplexRatInterval) {x : ℝ}
    (hx : I.re.Contains x) :
    Real.exp x ≤ centeredExpEnvelope I := by
  let q : ℚ := max 0 I.re.hi
  let k : ℤ := ⌈q⌉
  let n : ℕ := k.toNat
  have hq0 : 0 ≤ q := by simp [q]
  have hqk : q ≤ (k : ℚ) := Int.le_ceil q
  have hk0 : 0 ≤ k := by
    have : (0 : ℚ) ≤ (k : ℚ) := hq0.trans hqk
    exact_mod_cast this
  have hqn : q ≤ (n : ℚ) := by
    have hkn : (n : ℤ) = k := by
      exact Int.toNat_of_nonneg hk0
    rw [← hkn] at hqk
    exact_mod_cast hqk
  have hxn : x ≤ (n : ℕ) := by
    have hxhi : x ≤ (I.re.hi : ℝ) := hx.2
    have hhiq : I.re.hi ≤ q := by simp [q]
    have hhiqR : (I.re.hi : ℝ) ≤ (q : ℝ) := by exact_mod_cast hhiq
    have hqnR : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hqn
    exact hxhi.trans (hhiqR.trans hqnR)
  have hexp : Real.exp x ≤ Real.exp (n : ℝ) :=
    Real.exp_le_exp.mpr hxn
  have hbase : Real.exp 1 ≤ (3 : ℝ) := (Real.exp_one_lt_three).le
  have hpow : Real.exp (n : ℝ) ≤ (3 : ℝ) ^ n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le hbase n
  exact hexp.trans (by
    simpa [centeredExpEnvelope, q, k, n] using hpow)

/-- Midpoint Lipschitz control makes the widened midpoint enclosure sound for
every complex point in the argument rectangle. -/
lemma centeredComplexExp_sound (I : ComplexRatInterval) (stage : ℕ) {z : ℂ}
    (hz : I.Contains z) :
    (centeredComplexExp I stage).Contains (Complex.exp z) := by
  let c : ℚ := Transcendental.intervalMid I.re
  let d : ℚ := Transcendental.intervalMid I.im
  let E : ℝ := centeredExpEnvelope I
  have hcI : I.re.Contains (c : ℝ) := by
    constructor <;> exact_mod_cast (by
      dsimp [c, Transcendental.intervalMid]
      linarith [I.re.lo_le_hi])
  have hdI : I.im.Contains (d : ℝ) := by
    constructor <;> exact_mod_cast (by
      dsimp [d, Transcendental.intervalMid]
      linarith [I.im.lo_le_hi])
  have hE0 : 0 ≤ E := by
    dsimp [E]
    exact_mod_cast centeredExpEnvelope_nonneg I
  have hLip : |Real.exp z.re - Real.exp (c : ℝ)| ≤
      E * |z.re - (c : ℝ)| := by
    simpa [Real.norm_eq_abs] using
      (Convex.norm_image_sub_le_of_norm_deriv_le
        (f := Real.exp) (s := Set.Icc (I.re.lo : ℝ) (I.re.hi : ℝ))
        (x := (c : ℝ)) (y := z.re) (C := E)
        (fun y _ => (Real.hasDerivAt_exp y).differentiableAt)
        (fun y hy => by
          rw [Real.deriv_exp, Real.norm_eq_abs, Real.abs_exp]
          exact centeredExpEnvelope_sound I hy)
        (convex_Icc _ _) hcI hz.1)
  have hcos := Real.abs_cos_sub_cos_le z.im (d : ℝ)
  have hsin := Real.abs_sin_sub_sin_le z.im (d : ℝ)
  have hxc := Transcendental.abs_sub_intervalMid_le_radius hz.1
  have hyd := Transcendental.abs_sub_intervalMid_le_radius hz.2
  have hreWidth : (I.re.width : ℝ) ≤ (I.width : ℝ) := by
    exact_mod_cast le_max_left I.re.width I.im.width
  have himWidth : (I.im.width : ℝ) ≤ (I.width : ℝ) := by
    exact_mod_cast le_max_right I.re.width I.im.width
  have hdist : |z.re - (c : ℝ)| + |z.im - (d : ℝ)| ≤ (I.width : ℝ) := by
    dsimp [c, d]
    simp only [Transcendental.intervalRadius, Rat.cast_div, Rat.cast_ofNat] at hxc hyd
    linarith
  have hEc : Real.exp (c : ℝ) ≤ E := centeredExpEnvelope_sound I hcI
  have hmidRe : (((c : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re = (c : ℝ) := by
    simp
  have hmidIm : (((c : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im = (d : ℝ) := by
    simp
  have hreDiff :
      |(Complex.exp z).re -
          (Complex.exp ((c : ℝ) + (d : ℝ) * Complex.I)).re| ≤
        E * (I.width : ℝ) := by
    rw [Complex.exp_re, Complex.exp_re, hmidRe, hmidIm]
    calc
      _ = |(Real.exp z.re - Real.exp (c : ℝ)) * Real.cos z.im +
          Real.exp (c : ℝ) * (Real.cos z.im - Real.cos (d : ℝ))| := by
            congr 1
            ring
      _ ≤ |Real.exp z.re - Real.exp (c : ℝ)| * |Real.cos z.im| +
          |Real.exp (c : ℝ)| * |Real.cos z.im - Real.cos (d : ℝ)| := by
            simpa [abs_mul, Real.abs_exp] using
              (abs_add_le
                ((Real.exp z.re - Real.exp (c : ℝ)) * Real.cos z.im)
                (Real.exp (c : ℝ) * (Real.cos z.im - Real.cos (d : ℝ))))
      _ ≤ E * |z.re - (c : ℝ)| + E * |z.im - (d : ℝ)| := by
            have hcosOne : |Real.cos z.im| ≤ 1 := Real.abs_cos_le_one z.im
            have hEcAbs : |Real.exp (c : ℝ)| ≤ E := by
              rw [Real.abs_exp]
              exact hEc
            apply add_le_add
            · calc
                _ ≤ (E * |z.re - (c : ℝ)|) * |Real.cos z.im| :=
                  mul_le_mul_of_nonneg_right hLip (abs_nonneg _)
                _ ≤ (E * |z.re - (c : ℝ)|) * 1 :=
                  mul_le_mul_of_nonneg_left hcosOne (mul_nonneg hE0 (abs_nonneg _))
                _ = E * |z.re - (c : ℝ)| := mul_one _
            · calc
                _ ≤ E * |Real.cos z.im - Real.cos (d : ℝ)| :=
                  mul_le_mul_of_nonneg_right hEcAbs (abs_nonneg _)
                _ ≤ E * |z.im - (d : ℝ)| := mul_le_mul_of_nonneg_left hcos hE0
      _ = E * (|z.re - (c : ℝ)| + |z.im - (d : ℝ)|) := by ring
      _ ≤ E * (I.width : ℝ) := mul_le_mul_of_nonneg_left hdist hE0
  have himDiff :
      |(Complex.exp z).im -
          (Complex.exp ((c : ℝ) + (d : ℝ) * Complex.I)).im| ≤
        E * (I.width : ℝ) := by
    rw [Complex.exp_im, Complex.exp_im, hmidRe, hmidIm]
    calc
      _ = |(Real.exp z.re - Real.exp (c : ℝ)) * Real.sin z.im +
          Real.exp (c : ℝ) * (Real.sin z.im - Real.sin (d : ℝ))| := by
            congr 1
            ring
      _ ≤ |Real.exp z.re - Real.exp (c : ℝ)| * |Real.sin z.im| +
          |Real.exp (c : ℝ)| * |Real.sin z.im - Real.sin (d : ℝ)| := by
            simpa [abs_mul, Real.abs_exp] using
              (abs_add_le
                ((Real.exp z.re - Real.exp (c : ℝ)) * Real.sin z.im)
                (Real.exp (c : ℝ) * (Real.sin z.im - Real.sin (d : ℝ))))
      _ ≤ E * |z.re - (c : ℝ)| + E * |z.im - (d : ℝ)| := by
            have hsinOne : |Real.sin z.im| ≤ 1 := Real.abs_sin_le_one z.im
            have hEcAbs : |Real.exp (c : ℝ)| ≤ E := by
              rw [Real.abs_exp]
              exact hEc
            apply add_le_add
            · calc
                _ ≤ (E * |z.re - (c : ℝ)|) * |Real.sin z.im| :=
                  mul_le_mul_of_nonneg_right hLip (abs_nonneg _)
                _ ≤ (E * |z.re - (c : ℝ)|) * 1 :=
                  mul_le_mul_of_nonneg_left hsinOne (mul_nonneg hE0 (abs_nonneg _))
                _ = E * |z.re - (c : ℝ)| := mul_one _
            · calc
                _ ≤ E * |Real.sin z.im - Real.sin (d : ℝ)| :=
                  mul_le_mul_of_nonneg_right hEcAbs (abs_nonneg _)
                _ ≤ E * |z.im - (d : ℝ)| := mul_le_mul_of_nonneg_left hsin hE0
      _ = E * (|z.re - (c : ℝ)| + |z.im - (d : ℝ)|) := by ring
      _ ≤ E * (I.width : ℝ) := mul_le_mul_of_nonneg_left hdist hE0
  have hcenter :=
    (Transcendental.complexExpNameApprox_spec (centeredExpCenterName I) stage).1
  have hcenter' :
      (centeredExpCenterCore I stage).Contains
        (Complex.exp ((c : ℝ) + (d : ℝ) * Complex.I)) := by
    simpa [centeredExpCenterCore, centeredExpCenterName, rectangleMidpoint, c, d,
      CertifiedComplex.ofRatPair] using hcenter
  rw [abs_le] at hreDiff himDiff
  rw [centeredComplexExp]
  unfold ComplexRatInterval.Contains ComplexRatInterval.expand
  simp only [RatInterval.Contains, RatInterval.expand, Rat.cast_sub, Rat.cast_add,
    Rat.cast_mul]
  constructor <;> constructor <;>
    linarith [hcenter'.1.1, hcenter'.1.2, hcenter'.2.1, hcenter'.2.2,
      hreDiff.1, hreDiff.2, himDiff.1, himDiff.2]

/-- At the promoted complex-exponential precision, centered evaluation costs
the algorithmic remainder plus exactly twice the explicit input-width
allowance. -/
lemma centeredComplexExp_width_at_precision (I : ComplexRatInterval)
    (e : PosRat) :
    (centeredComplexExp I
      (Transcendental.complexExpPrecision (centeredExpCenterName I) e)).width ≤
      2 * centeredExpEnvelope I * I.width + e.1 := by
  let allowance := centeredExpEnvelope I * I.width
  have hallowance : 0 ≤ allowance := by
    exact mul_nonneg (centeredExpEnvelope_nonneg I)
      ((RatInterval.width_nonneg I.re).trans (le_max_left _ _))
  have hcore :
      (centeredExpCenterCore I
        (Transcendental.complexExpPrecision (centeredExpCenterName I) e)).width ≤ e.1 := by
    exact Transcendental.complexExp_width_at_precision (centeredExpCenterName I) e
  rw [centeredComplexExp, ComplexRatInterval.width, ComplexRatInterval.expand,
    RatInterval.width_expand, RatInterval.width_expand]
  rw [max_add_add_right]
  simpa [ComplexRatInterval.width, allowance, mul_assoc, add_comm] using
    (add_le_add_right hcore (2 * centeredExpEnvelope I * I.width))

end CausalSmith.Stat.SaPlmCumulantConverse.BoundedCertifiedComplex

namespace CausalSmith.Stat.SaPlmCumulantConverse

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

/-- Promote a real rational interval to the real axis. -/
def realRect (I : RatInterval) : ComplexRatInterval :=
  ⟨I, RatInterval.point 0⟩

/-- [Whenever a rational interval encloses a real number](hyp:hr), [the rectangle obtained by
placing that interval on the real axis encloses the same number viewed as a complex
number](goal). -/
lemma realRect_sound {I : RatInterval} {r : ℝ} (hr : I.Contains r) :
    (realRect I).Contains ((r : ℝ) : ℂ) := by
  exact ⟨by simpa [realRect] using hr,
    by simpa [realRect] using RatInterval.point_sound 0⟩

/-- [Placing a rational interval on the real axis yields a rectangle of exactly the same width as
the interval](goal). -/
@[simp] lemma realRect_width (I : RatInterval) :
    (realRect I).width = I.width := by
  rw [realRect, ComplexRatInterval.width]
  simp only [RatInterval.point, RatInterval.width, sub_self]
  exact max_eq_left (RatInterval.width_nonneg I)

/-- The certified-real bank radius is refined before it is multiplied by a
unit-circle node.  This is the only place where the bank radius enters a
circle node. -/
def bankRadiusRect (radius : CertifiedReal) (precision : PosRat) :
    ComplexRatInterval :=
  realRect (CertifiedReal.refine radius precision)

/-- [Refining a certified real radius to a requested rational precision and placing the resulting
interval on the real axis yields a rectangle that encloses the exact value of the radius](goal). -/
lemma bankRadiusRect_sound (radius : CertifiedReal) (precision : PosRat) :
    (bankRadiusRect radius precision).Contains ((radius.value : ℝ) : ℂ) := by
  exact realRect_sound (CertifiedReal.refine_contains radius precision)

/-- [The refined radius rectangle has width at most the requested rational precision](goal). -/
lemma bankRadiusRect_width (radius : CertifiedReal) (precision : PosRat) :
    (bankRadiusRect radius precision).width ≤ precision.1 := by
  simpa [bankRadiusRect, realRect_width] using CertifiedReal.refine_width radius precision

/-- A certified-real radius times the reused rational-radius-one circle node. -/
def certifiedRadiusNode (radius : CertifiedReal) (precision : PosRat)
    (schedule : Schedule) (k : ℕ) : ComplexRatInterval :=
  (bankRadiusRect radius precision).mul (circleNode 1 schedule k)

/-- A Machin-π rectangle for `2 π i`. -/
def twoPiIRect (precision : ℕ) : ComplexRatInterval :=
  ⟨RatInterval.point 0,
    (RatInterval.point 2).mul (Transcendental.piInterval precision)⟩

private lemma piInterval_lo_pos (precision : ℕ) :
    0 < (Transcendental.piInterval precision).lo := by
  have hzero : 0 < (Transcendental.piInterval 0).lo := by
    norm_num [Transcendental.piInterval, Transcendental.piRaw,
      Transcendental.atanRaw, Transcendental.atanPartial,
      Transcendental.atanError, RatInterval.mul, RatInterval.sub,
      RatInterval.add, RatInterval.neg, RatInterval.point]
  have hsub : (Transcendental.piInterval precision).Subinterval
      (Transcendental.piInterval 0) := by
    simpa [Transcendental.piName] using
      CertifiedReal.approx_mono Transcendental.piName (Nat.zero_le precision)
  exact hzero.trans_le hsub.1

private lemma twoPiIRect_away (precision count : ℕ) :
    ((twoPiIRect precision).smulRat (max count 1)).normSq.AwayFromZero := by
  right
  have hcount : (0 : ℚ) < max count 1 := by positivity
  have hpi := piInterval_lo_pos precision
  have hpile : (Transcendental.piInterval precision).lo ≤
      (Transcendental.piInterval precision).hi :=
    (Transcendental.piInterval precision).lo_le_hi
  let D := (twoPiIRect precision).smulRat (max count 1)
  have hDim : 0 < D.im.lo := by
    dsimp [D, twoPiIRect, ComplexRatInterval.smulRat]
    simp [RatInterval.point, RatInterval.mul, min_eq_left, max_eq_right,
      hpile, hpi.le, hcount.le]
    positivity
  have hre : 0 ≤ D.re.sq.lo := by
    unfold RatInterval.sq
    split_ifs <;> dsimp <;> positivity
  have him : 0 < D.im.sq.lo := by
    have hhi : 0 ≤ D.im.hi := hDim.le.trans D.im.lo_le_hi
    simp [RatInterval.sq, not_lt_of_ge hhi, hDim]
  simpa [D, ComplexRatInterval.normSq, RatInterval.add] using add_pos_of_nonneg_of_pos hre him

/-- [The Machin-series rectangle built at any precision encloses the complex number two pi
times the imaginary unit](goal). -/
lemma twoPiIRect_sound (precision : ℕ) :
    (twoPiIRect precision).Contains (((2 : ℝ) * Real.pi : ℂ) * Complex.I) := by
  constructor
  · simpa [twoPiIRect] using RatInterval.point_sound (0 : ℚ)
  · simpa [twoPiIRect] using RatInterval.mul_sound
      (RatInterval.point_sound (2 : ℚ))
      (Transcendental.piInterval_sound precision)

/-- The tangent rectangle is `2 π i` times the certified-radius node. -/
def tangentNode (radius : CertifiedReal) (radiusPrecision : PosRat)
    (piPrecision : ℕ) (schedule : Schedule) (k : ℕ) : ComplexRatInterval :=
  (twoPiIRect piPrecision).mul
    (certifiedRadiusNode radius radiusPrecision schedule k)

/-- The map-level target is quadratically smaller than the requested branch
tolerance.  The second factor of the requested tolerance pays for the
box-local derivative term in `BoundedComplexMap.Valid`; the rational factor
sixteen leaves room for quotient, tangent, quadrature, and normalization
amplification. -/
def spectralNodeTarget (tolerance : PosRat) : PosRat :=
  ⟨tolerance.1 ^ 2 / 16, div_pos (sq_pos_of_pos tolerance.2) (by norm_num)⟩

/-- Closed-form finite empirical-map fuel. -/
def spectralEmpiricalMapFuel (tolerance : PosRat) (operations : ℕ) (L : ℚ) : ℕ :=
  64 * (operations + 1) * (tolerance.1.den + 1) * (L.num.natAbs + 2) ^ 2

/-- Closed-form modulus fuel used at a scheduled node. -/
def spectralNormFuel (tolerance : PosRat) : ℕ := tolerance.1.den + 1

/-- Closed-form rational-bisection fuel used by the modulus square root. -/
def spectralSqrtFuel (tolerance : PosRat) : ℕ := 2 * (tolerance.1.den + 1)

/-- Magnitude-aware Newton fuel for applying `normInterval` directly to a
raw map rectangle. -/
def spectralRawNormFuel (tolerance : PosRat) (L : ℚ) : ℕ :=
  64 * (tolerance.1.den + 1) * (L.num.natAbs + 3) ^ 2

/-- Closed fuel for the finite rational endpoint operations at one node. -/
def spectralEndpointFuel (operations : ℕ) : ℕ := operations + 1

/-- One bound dominating every non-circle finite-map fuel used by a node. -/
def spectralDerivedFuel (tolerance : PosRat) (operations : ℕ) (L : ℚ) : ℕ :=
  max (spectralEmpiricalMapFuel tolerance operations L)
    (max (spectralNormFuel tolerance)
      (max (spectralSqrtFuel tolerance) (spectralEndpointFuel operations)))

/-- One third of the requested tolerance, packaged for the exact mesh
constructor. -/
def spectralMeshBudget (tolerance : PosRat) : PosRat :=
  ⟨tolerance.1 / 3, div_pos tolerance.2 (by norm_num)⟩

/-- Exact endpoint-complete mesh from the local certified-transcendental
schedule. -/
def spectralMesh (tolerance : PosRat) (L : ℚ) : ℕ :=
  explicitMeshFuel L (spectralMeshBudget tolerance)

/-- [For a nonnegative Lipschitz magnitude](hyp:hL), [dividing that magnitude by the mesh count
chosen by the spectral schedule leaves a discretization error of at most one third of the
requested tolerance](goal). -/
lemma spectralMesh_error_le (tolerance : PosRat) (L : ℚ) (hL : 0 ≤ L) :
    L / spectralMesh tolerance L ≤ tolerance.1 / 3 := by
  let e := spectralMeshBudget tolerance
  have he : 0 < e.1 := e.2
  have hx0 : 0 ≤ L / e.1 := div_nonneg hL he.le
  have hceil0 : 0 ≤ ⌈L / e.1⌉ := Int.ceil_nonneg hx0
  have hceil : L / e.1 ≤ (⌈L / e.1⌉ : ℚ) := Int.le_ceil _
  have hcast : ((Int.toNat ⌈L / e.1⌉ : ℕ) : ℚ) = (⌈L / e.1⌉ : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hceil0
  have hratio : L / e.1 ≤ ((Int.toNat ⌈L / e.1⌉ + 1 : ℕ) : ℚ) := by
    rw [Nat.cast_add, Nat.cast_one, hcast]
    exact hceil.trans (le_add_of_nonneg_right zero_le_one)
  have hmeshPos : (0 : ℚ) < (Int.toNat ⌈L / e.1⌉ + 1 : ℕ) := by
    positivity
  unfold spectralMesh explicitMeshFuel
  change L / ((Int.toNat ⌈L / e.1⌉ + 1 : ℕ) : ℚ) ≤ e.1
  apply (div_le_iff₀ hmeshPos).2
  simpa [mul_comm] using (div_le_iff₀ he).1 hratio

/-- Paper-local explicit schedule with exact circle precision and dominating
circle, empirical-map, norm, and square-root fuel. -/
def spectralSchedule (tolerance : PosRat) (operations : ℕ)
    (lipschitz amplification : ℚ) (hL : 0 ≤ lipschitz)
    (_hAmp : 0 ≤ amplification) : Schedule where
  tolerance := tolerance
  operationCount := operations
  inputPrecision := circleInputPrecision 1 (spectralNodeTarget tolerance)
  mesh := spectralMesh tolerance lipschitz
  mesh_pos := by unfold spectralMesh explicitMeshFuel; positivity
  fuel := max
    (circleExpFuel 1 (spectralMesh tolerance lipschitz) (spectralNodeTarget tolerance))
    (max (spectralDerivedFuel (spectralNodeTarget tolerance) operations amplification)
      (spectralRawNormFuel tolerance amplification))
  magnitude := lipschitz
  magnitude_nonneg := hL
  nodeBudget := tolerance.1 / 3
  meshBudget := tolerance.1 / 3
  quadratureBudget := tolerance.1 / 3
  nodeBudget_nonneg := div_nonneg tolerance.2.le (by norm_num)
  meshBudget_nonneg := div_nonneg tolerance.2.le (by norm_num)
  quadratureBudget_nonneg := div_nonneg tolerance.2.le (by norm_num)
  budget_sum_le := by linarith
  mesh_error_le := spectralMesh_error_le tolerance lipschitz hL

/-- [For a nonnegative Lipschitz magnitude](hyp:hL) and [a nonnegative amplification
factor](hyp:hAmp), [the input precision recorded by the paper's spectral schedule is exactly the
circle input precision at radius one for the quadratically reduced node target](goal). -/
@[simp] lemma spectralSchedule_inputPrecision (tolerance : PosRat)
    (operations : ℕ) (lipschitz amplification : ℚ)
    (hL : 0 ≤ lipschitz) (hAmp : 0 ≤ amplification) :
    (spectralSchedule tolerance operations lipschitz amplification hL hAmp).inputPrecision =
      circleInputPrecision 1 (spectralNodeTarget tolerance) := rfl

/-- [For a nonnegative Lipschitz magnitude](hyp:hL) and [a nonnegative amplification
factor](hyp:hAmp), [the magnitude recorded by the paper's spectral schedule is exactly the
supplied Lipschitz constant](goal). -/
@[simp] lemma spectralSchedule_magnitude (tolerance : PosRat)
    (operations : ℕ) (lipschitz amplification : ℚ)
    (hL : 0 ≤ lipschitz) (hAmp : 0 ≤ amplification) :
    (spectralSchedule tolerance operations lipschitz amplification hL hAmp).magnitude =
      lipschitz := rfl

/-- [For a nonnegative Lipschitz magnitude](hyp:hL) and [a nonnegative amplification
factor](hyp:hAmp), [the circle exponential fuel at radius one, taken at the schedule's own mesh
and at the reduced node target, does not exceed the fuel the schedule budgets](goal). -/
lemma spectralSchedule_circleExpFuel_le (tolerance : PosRat)
    (operations : ℕ) (lipschitz amplification : ℚ)
    (hL : 0 ≤ lipschitz) (hAmp : 0 ≤ amplification) :
    circleExpFuel 1
        (spectralSchedule tolerance operations lipschitz amplification hL hAmp).mesh
        (spectralNodeTarget tolerance) ≤
      (spectralSchedule tolerance operations lipschitz amplification hL hAmp).fuel := by
  exact le_max_left _ _

/-- [For a nonnegative Lipschitz magnitude](hyp:hL) and [a nonnegative amplification
factor](hyp:hAmp), [the dominating non-circle fuel bound at the reduced node target does not
exceed the fuel the spectral schedule budgets](goal). -/
lemma spectralSchedule_derivedFuel_le (tolerance : PosRat)
    (operations : ℕ) (lipschitz amplification : ℚ)
    (hL : 0 ≤ lipschitz) (hAmp : 0 ≤ amplification) :
    spectralDerivedFuel (spectralNodeTarget tolerance) operations amplification ≤
      (spectralSchedule tolerance operations lipschitz amplification hL hAmp).fuel := by
  exact (le_max_left _ _).trans (le_max_right _ _)

/-- [For a nonnegative Lipschitz magnitude](hyp:hL) and [a nonnegative amplification
factor](hyp:hAmp), [the magnitude-aware Newton fuel for taking the modulus of a raw map
rectangle does not exceed the fuel the spectral schedule budgets](goal). -/
lemma spectralSchedule_rawNormFuel_le (tolerance : PosRat)
    (operations : ℕ) (lipschitz amplification : ℚ)
    (hL : 0 ≤ lipschitz) (hAmp : 0 ≤ amplification) :
    spectralRawNormFuel tolerance amplification ≤
      (spectralSchedule tolerance operations lipschitz amplification hL hAmp).fuel := by
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- [For a nonnegative Lipschitz magnitude](hyp:hL) and [a nonnegative amplification
factor](hyp:hAmp), [the empirical-map fuel at the reduced node target does not exceed the fuel
the spectral schedule budgets](goal). -/
lemma spectralSchedule_empiricalMapFuel_le (tolerance : PosRat)
    (operations : ℕ) (lipschitz amplification : ℚ)
    (hL : 0 ≤ lipschitz) (hAmp : 0 ≤ amplification) :
    spectralEmpiricalMapFuel (spectralNodeTarget tolerance) operations amplification ≤
      (spectralSchedule tolerance operations lipschitz amplification hL hAmp).fuel := by
  exact (le_max_left _ _).trans
    (spectralSchedule_derivedFuel_le tolerance operations lipschitz amplification hL hAmp)

/-- [For a nonnegative Lipschitz magnitude](hyp:hL) and [a nonnegative amplification
factor](hyp:hAmp), [the modulus fuel at the reduced node target does not exceed the fuel the
spectral schedule budgets](goal). -/
lemma spectralSchedule_normFuel_le (tolerance : PosRat)
    (operations : ℕ) (lipschitz amplification : ℚ)
    (hL : 0 ≤ lipschitz) (hAmp : 0 ≤ amplification) :
    spectralNormFuel (spectralNodeTarget tolerance) ≤
      (spectralSchedule tolerance operations lipschitz amplification hL hAmp).fuel := by
  exact ((le_max_left _ _).trans (le_max_right _ _)).trans
    (spectralSchedule_derivedFuel_le tolerance operations lipschitz amplification hL hAmp)

/-- [For a nonnegative Lipschitz magnitude](hyp:hL) and [a nonnegative amplification
factor](hyp:hAmp), [the rational-bisection fuel used by the modulus square root at the reduced
node target does not exceed the fuel the spectral schedule budgets](goal). -/
lemma spectralSchedule_sqrtFuel_le (tolerance : PosRat)
    (operations : ℕ) (lipschitz amplification : ℚ)
    (hL : 0 ≤ lipschitz) (hAmp : 0 ≤ amplification) :
    spectralSqrtFuel (spectralNodeTarget tolerance) ≤
      (spectralSchedule tolerance operations lipschitz amplification hL hAmp).fuel := by
  exact ((le_max_left _ _).trans (le_max_right _ _)).trans
    ((le_max_right _ _).trans
      (spectralSchedule_derivedFuel_le tolerance operations lipschitz amplification hL hAmp))

/-- [For a nonnegative Lipschitz magnitude](hyp:hL) and [a nonnegative amplification
factor](hyp:hAmp), [the fuel for the finite rational endpoint operations at one node does not
exceed the fuel the spectral schedule budgets](goal). -/
lemma spectralSchedule_endpointFuel_le (tolerance : PosRat)
    (operations : ℕ) (lipschitz amplification : ℚ)
    (hL : 0 ≤ lipschitz) (hAmp : 0 ≤ amplification) :
    spectralEndpointFuel operations ≤
      (spectralSchedule tolerance operations lipschitz amplification hL hAmp).fuel := by
  exact (le_max_right _ _).trans
    ((le_max_right _ _).trans
      ((le_max_right _ _).trans
        (spectralSchedule_derivedFuel_le tolerance operations lipschitz amplification hL hAmp)))

/-- A complex map whose interval program is certified only on one fixed box.
The proof obligations are kept in `BoundedComplexMap.Valid`, allowing the
finite program itself to remain executable data. -/
structure BoundedComplexMap (box : ComplexRatInterval) where
  value : ℂ → ℂ
  eval : ComplexRatInterval → ℕ → ComplexRatInterval
  operationCount : ℕ
  magnitudeEnvelope : ℚ
  derivativeEnvelope : ℚ
  precision : PosRat → ℕ

/-- The correctness conditions carried by a box-local certified complex map: its magnitude and
derivative envelopes are nonnegative, and for every rectangle contained in the fixed box and
every complex point that rectangle encloses, all of the map's interval evaluations enclose the
true value, the evaluations shrink as fuel increases, and at the stage chosen by the map's own
precision schedule the output width is at most the derivative envelope times the input width
plus the requested tolerance. -/
def BoundedComplexMap.Valid {box : ComplexRatInterval}
    (map : BoundedComplexMap box) : Prop :=
  0 ≤ map.magnitudeEnvelope ∧ 0 ≤ map.derivativeEnvelope ∧
  ∀ {I : ComplexRatInterval} {z : ℂ}, I.Subinterval box → I.Contains z →
    (∀ fuel, (map.eval I fuel).Contains (map.value z)) ∧
    (∀ fuel, (map.eval I (fuel + 1)).Subinterval (map.eval I fuel)) ∧
    ∀ e, (map.eval I (map.precision e)).width ≤
      map.derivativeEnvelope * I.width + e.1

private def halfTolerance (e : PosRat) : PosRat :=
  ⟨e.1 / 2, div_pos e.2 (by norm_num)⟩

private def productTolerance (A B : ℚ) (e : PosRat) : PosRat :=
  ⟨e.1 / (4 * (|A| + |B| + 1)), by
    exact div_pos e.2
      (mul_pos (by norm_num) (by linarith [abs_nonneg A, abs_nonneg B]))⟩

/-- The box-local map that sends every point to one fixed rational complex number. Its interval
evaluation is the degenerate rectangle at that number, its magnitude envelope is the sum of the
absolute values of the two coordinates, and its derivative envelope is zero. -/
def BoundedComplexMap.constant (box : ComplexRatInterval) (x y : ℚ) :
    BoundedComplexMap box where
  value := fun _ ↦ (x : ℝ) + (y : ℝ) * Complex.I
  eval := fun _ _ ↦ ComplexRatInterval.point x y
  operationCount := 1
  magnitudeEnvelope := |x| + |y|
  derivativeEnvelope := 0
  precision := fun _ ↦ 0

/-- The box-local identity map. Its interval evaluation returns the input rectangle unchanged,
its magnitude envelope is the largest modulus attained on the fixed box, and its derivative
envelope is one. -/
def BoundedComplexMap.identity (box : ComplexRatInterval) : BoundedComplexMap box where
  value := id
  eval := fun I _ ↦ I
  operationCount := 1
  magnitudeEnvelope := box.maxAbs
  derivativeEnvelope := 1
  precision := fun _ ↦ 0

/-- Box-local addition.  The two maps are added pointwise and their interval evaluators are
added at matching fuel; the operation count, magnitude envelope and derivative envelope of the
sum are the sums of those of the summands, and each summand is asked for half the requested
tolerance so the combined error meets it. -/
def BoundedComplexMap.add {box : ComplexRatInterval}
    (f g : BoundedComplexMap box) : BoundedComplexMap box where
  value := fun z ↦ f.value z + g.value z
  eval := fun I fuel ↦ (f.eval I fuel).add (g.eval I fuel)
  operationCount := f.operationCount + g.operationCount + 1
  magnitudeEnvelope := f.magnitudeEnvelope + g.magnitudeEnvelope
  derivativeEnvelope := f.derivativeEnvelope + g.derivativeEnvelope
  precision := fun e ↦ max (f.precision (halfTolerance e))
    (g.precision (halfTolerance e))

/-- Box-local subtraction.  The two maps are subtracted pointwise and their interval evaluators
are subtracted at matching fuel; the operation count, magnitude envelope and derivative envelope
add rather than cancel, since they bound magnitudes, and each operand is asked for half the
requested tolerance. -/
def BoundedComplexMap.sub {box : ComplexRatInterval}
    (f g : BoundedComplexMap box) : BoundedComplexMap box where
  value := fun z ↦ f.value z - g.value z
  eval := fun I fuel ↦ (f.eval I fuel).sub (g.eval I fuel)
  operationCount := f.operationCount + g.operationCount + 1
  magnitudeEnvelope := f.magnitudeEnvelope + g.magnitudeEnvelope
  derivativeEnvelope := f.derivativeEnvelope + g.derivativeEnvelope
  precision := fun e ↦ max (f.precision (halfTolerance e))
    (g.precision (halfTolerance e))

/-- Box-local multiplication.  The displayed envelopes are rational input
data used by the local width schedule. -/
def BoundedComplexMap.mulOnBox {box : ComplexRatInterval}
    (f g : BoundedComplexMap box) : BoundedComplexMap box where
  value := fun z ↦ f.value z * g.value z
  eval := fun I fuel ↦ (f.eval I fuel).mul (g.eval I fuel)
  operationCount := f.operationCount + g.operationCount + 1
  magnitudeEnvelope := 2 * f.magnitudeEnvelope * g.magnitudeEnvelope
  derivativeEnvelope :=
    2 * (f.derivativeEnvelope * g.magnitudeEnvelope +
      g.derivativeEnvelope * f.magnitudeEnvelope)
  precision := fun e ↦
    let δ := productTolerance f.magnitudeEnvelope g.magnitudeEnvelope e
    max (f.precision δ) (g.precision δ)

/-- Box-local interval extension of `z ↦ exp(c*z)`. -/
def BoundedComplexMap.expScaledOnBox (box : ComplexRatInterval) (c : ℚ × ℚ) :
    BoundedComplexMap box where
  value := fun z ↦ Complex.exp (((c.1 : ℝ) + (c.2 : ℝ) * Complex.I) * z)
  eval := fun I fuel ↦
    Transcendental.complexExp ((ComplexRatInterval.point c.1 c.2).mul I) fuel
  operationCount := 8
  magnitudeEnvelope := 3 ^ Int.toNat ⌈max 0 ((|c.1| + |c.2|) * box.maxAbs)⌉
  derivativeEnvelope := (|c.1| + |c.2|) *
    (3 ^ Int.toNat ⌈max 0 ((|c.1| + |c.2|) * box.maxAbs)⌉)
  precision := fun e ↦ spectralEmpiricalMapFuel e 8
    ((|c.1| + |c.2|) *
      (3 ^ Int.toNat ⌈max 0 ((|c.1| + |c.2|) * box.maxAbs)⌉))

/-- A tangent-corrected guarded quotient evaluator on a fixed disk. -/
structure BoundedCircleEvaluator (box : ComplexRatInterval) where
  numerator : BoundedComplexMap box
  denominator : BoundedComplexMap box
  radius : CertifiedReal
  radiusPrecision : PosRat
  piPrecision : ℕ
  schedule : Schedule
  mapFuel : ℕ
  lipschitz : ℚ
  lipschitz_nonneg : 0 ≤ lipschitz
  normalizationCount : ℕ

/-- The correctness conditions carried by a tangent-corrected guarded quotient evaluator on a
fixed disk: the numerator and denominator maps are both valid on the box; at every mesh index up
to the schedule's mesh the certified radius node lies inside the box and the denominator's
evaluated rectangle there has squared modulus bounded away from zero; and the circle integrand
of the quotient is Lipschitz in the circle parameter with the recorded constant. -/
def BoundedCircleEvaluator.Valid {box : ComplexRatInterval}
    (ev : BoundedCircleEvaluator box) : Prop :=
  ev.numerator.Valid ∧ ev.denominator.Valid ∧
  (∀ k ≤ ev.schedule.mesh,
    (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).Subinterval box ∧
    (ev.denominator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).normSq.AwayFromZero) ∧
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖CircleMesh.circleIntegrand
        (fun z ↦ ev.numerator.value z / ev.denominator.value z)
        0 ev.radius.value s -
      CircleMesh.circleIntegrand
        (fun z ↦ ev.numerator.value z / ev.denominator.value z)
        0 ev.radius.value t‖ ≤ (ev.lipschitz : ℝ) * |s - t|

/-- One full contour-integrand node.  Its value is the guarded quotient times
the tangent; the radius is not multiplied anywhere else. -/
noncomputable def BoundedCircleEvaluator.node {box : ComplexRatInterval}
    (ev : BoundedCircleEvaluator box) (k : ℕ) : ComplexRatInterval :=
  let z := certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k
  let num := ev.numerator.eval z ev.mapFuel
  let den := ev.denominator.eval z ev.mapFuel
  let quotient := if h : den.normSq.hi < 0 ∨ 0 < den.normSq.lo then num.div den h
    else ComplexRatInterval.zero
  quotient.mul (tangentNode ev.radius ev.radiusPrecision ev.piPrecision ev.schedule k)

/-- The endpoint-complete finite quadrature uses every index `k ≤ mesh`,
including the terminal trapezoid endpoint. -/
def boundedContourEvaluate {box : ComplexRatInterval}
    (ev : BoundedCircleEvaluator box) : ComplexRatInterval :=
  CircleMesh.integralEnclosure ev.node ev.lipschitz ev.lipschitz_nonneg
    ev.schedule.mesh ev.schedule.mesh_pos

/-- Post-quadrature normalization by `N * 2 π i`; no normalization is
hidden in the node family. -/
def boundedContourDivisor (count piPrecision : ℕ) : ComplexRatInterval :=
  (twoPiIRect piPrecision).smulRat (max count 1)

/-- Divides a rectangle by the post-quadrature normalizing constant, the node count times two pi
times the imaginary unit, using guarded rectangle division when that divisor is certified away
from zero and returning the zero rectangle otherwise. -/
noncomputable def boundedContourNormalize (I : ComplexRatInterval) (count piPrecision : ℕ) :
    ComplexRatInterval :=
  let divisor := boundedContourDivisor count piPrecision
  if h : divisor.normSq.hi < 0 ∨ 0 < divisor.normSq.lo then I.div divisor h
  else ComplexRatInterval.zero

/-- The exact rational width expression supplied by guarded rectangle
division.  Keeping it named makes the post-quadrature amplification visible to
the branch schedule instead of hiding it in a fuel-only argument. -/
def boundedContourNormalizationWidthBound (I : ComplexRatInterval)
    (count piPrecision : ℕ) (δ : ℚ) : ℚ :=
  let divisor := boundedContourDivisor count piPrecision
  (I.mul divisor.conj).maxAbs * divisor.normSq.width / δ ^ 2 +
    (I.mul divisor.conj).width / δ

/-- [Whenever a rectangle encloses a complex number](hyp:hz), [the normalized rectangle encloses
that number divided by the node count times two pi times the imaginary unit](goal). -/
lemma boundedContourNormalize_contains (I : ComplexRatInterval) (count piPrecision : ℕ)
    {z : ℂ} (hz : I.Contains z) :
    (boundedContourNormalize I count piPrecision).Contains
      (z / (((max count 1 : ℚ) : ℂ) *
        (((2 : ℝ) * Real.pi : ℂ) * Complex.I))) := by
  have haway := twoPiIRect_away piPrecision count
  have hdivisor := ComplexRatInterval.smulRat_sound (max count 1 : ℚ)
    (twoPiIRect_sound piPrecision)
  unfold boundedContourNormalize
  dsimp only
  split
  · rename_i hbranch
    exact ComplexRatInterval.div_sound hbranch hz hdivisor
  · rename_i hbranch
    exact (hbranch haway).elim

/-- [For a positive separation constant](hyp:hδ) that [bounds from below the squared modulus of
the normalizing divisor](hyp:hsep), [the normalized rectangle has width at most the explicit
rational amplification bound recorded for guarded division](goal). -/
lemma boundedContourNormalize_width (I : ComplexRatInterval) (count piPrecision : ℕ)
    (δ : ℚ) (hδ : 0 < δ)
    (hsep : δ ≤ (boundedContourDivisor count piPrecision).normSq.lo) :
    (boundedContourNormalize I count piPrecision).width ≤
      boundedContourNormalizationWidthBound I count piPrecision δ := by
  have haway : (boundedContourDivisor count piPrecision).normSq.hi < 0 ∨
      0 < (boundedContourDivisor count piPrecision).normSq.lo := by
    exact twoPiIRect_away piPrecision count
  unfold boundedContourNormalize
  dsimp only
  split
  · rename_i hbranch
    simpa [boundedContourNormalizationWidthBound] using
      (ComplexRatInterval.div_width hbranch hδ hsep)
  · rename_i hbranch
    exact (hbranch haway).elim

/-- [For a positive separation constant](hyp:hδ) that [bounds from below the squared modulus of
the normalizing divisor](hyp:hsep), and [a target that the explicit amplification bound does not
exceed](hyp:hbound), [the normalized rectangle has width at most that target](goal). -/
lemma boundedContourNormalize_width_le (I : ComplexRatInterval)
    (count piPrecision : ℕ) (δ target : ℚ) (hδ : 0 < δ)
    (hsep : δ ≤ (boundedContourDivisor count piPrecision).normSq.lo)
    (hbound : boundedContourNormalizationWidthBound I count piPrecision δ ≤ target) :
    (boundedContourNormalize I count piPrecision).width ≤ target :=
  (boundedContourNormalize_width I count piPrecision δ hδ hsep).trans hbound

/-- [For any mesh index no larger than the schedule's mesh](hyp:hk), [the certified radius node
encloses the point of the circle of that radius, centered at the origin, at the corresponding
mesh parameter](goal). -/
lemma certifiedRadiusNode_sound (radius : CertifiedReal) (precision : PosRat)
    (schedule : Schedule) {k : ℕ} (hk : k ≤ schedule.mesh) :
    (certifiedRadiusNode radius precision schedule k).Contains
      (CircleMesh.circleMap 0 radius.value (CircleMesh.meshPoint schedule.mesh k)) := by
  have hr := bankRadiusRect_sound radius precision
  have hu := circleNode_sound 1 schedule hk
  have hmul := ComplexRatInterval.mul_sound hr hu
  simpa [certifiedRadiusNode, exactCircleNode, CircleMesh.circleMap,
    CircleMesh.meshPoint] using hmul

/-- [For a mesh index no larger than the schedule's mesh](hyp:hk), given [a bound on the largest
modulus attained by the refined radius rectangle](hyp:hU), [a bound on the width of the
unit-radius circle node](hyp:hw), and [the matching bound of one plus that width on the node's
largest modulus](hyp:hunit), [the certified radius node has width at most twice the sum of the
modulus bound times the width bound and the shifted modulus bound times the radius
precision](goal). -/
lemma certifiedRadiusNode_width (radius : CertifiedReal) (precision : PosRat)
    (schedule : Schedule) (U w : ℚ) {k : ℕ} (hk : k ≤ schedule.mesh)
    (hU : (bankRadiusRect radius precision).maxAbs ≤ U)
    (hw : (circleNode 1 schedule k).width ≤ w)
    (hunit : (circleNode 1 schedule k).maxAbs ≤ 1 + w) :
    (certifiedRadiusNode radius precision schedule k).width ≤
      2 * (U * w + (1 + w) * precision.1) := by
  have hraw := ComplexRatInterval.mul_width
    (bankRadiusRect radius precision) (circleNode 1 schedule k)
  have hrw := bankRadiusRect_width radius precision
  have hr0 : 0 ≤ (bankRadiusRect radius precision).maxAbs :=
    (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hu0 : 0 ≤ (circleNode 1 schedule k).maxAbs :=
    (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hrWidth0 : 0 ≤ (bankRadiusRect radius precision).width :=
    (RatInterval.width_nonneg _).trans (le_max_left _ _)
  have huWidth0 : 0 ≤ (circleNode 1 schedule k).width :=
    (RatInterval.width_nonneg _).trans (le_max_left _ _)
  unfold certifiedRadiusNode
  calc
    ((bankRadiusRect radius precision).mul (circleNode 1 schedule k)).width
        ≤ 2 * ((bankRadiusRect radius precision).maxAbs *
            (circleNode 1 schedule k).width +
          (circleNode 1 schedule k).maxAbs *
            (bankRadiusRect radius precision).width) := hraw
    _ ≤ 2 * (U * w + (1 + w) * precision.1) := by
      nlinarith [mul_le_mul hU hw huWidth0 (by linarith),
        mul_le_mul hunit hrw hrWidth0 (by linarith)]

/-- [For any mesh index no larger than the schedule's mesh](hyp:hk), [the tangent rectangle
encloses the tangent vector of the circle of that radius at the corresponding mesh
parameter](goal). -/
lemma tangentNode_sound (radius : CertifiedReal) (radiusPrecision : PosRat)
    (piPrecision : ℕ) (schedule : Schedule) {k : ℕ}
    (hk : k ≤ schedule.mesh) :
    (tangentNode radius radiusPrecision piPrecision schedule k).Contains
      (CircleMesh.circleTangent radius.value (CircleMesh.meshPoint schedule.mesh k)) := by
  have htwoPi : (twoPiIRect piPrecision).Contains
      (((2 : ℝ) * Real.pi : ℂ) * Complex.I) := by
    constructor
    · simpa [twoPiIRect] using RatInterval.point_sound (0 : ℚ)
    · simpa [twoPiIRect] using RatInterval.mul_sound
        (RatInterval.point_sound (2 : ℚ))
        (Transcendental.piInterval_sound piPrecision)
  have hnode := certifiedRadiusNode_sound radius radiusPrecision schedule hk
  have hmul := ComplexRatInterval.mul_sound htwoPi hnode
  unfold tangentNode
  convert hmul using 1
  simp only [CircleMesh.circleTangent, CircleMesh.circleMap,
    CircleMesh.meshPoint, zero_add]
  ring_nf
  norm_num

/-- [For an evaluator satisfying its validity conditions](hyp:hvalid), [the finite
endpoint-complete quadrature rectangle encloses the true contour integral of the numerator over
denominator quotient around the circle of the evaluator's radius](goal). -/
lemma boundedContourEvaluate_contains {box : ComplexRatInterval}
    (ev : BoundedCircleEvaluator box) (hvalid : ev.Valid) :
    (boundedContourEvaluate ev).Contains
      (CircleMesh.circleContourIntegral
        (fun z ↦ ev.numerator.value z / ev.denominator.value z) 0 ev.radius.value) := by
  rcases hvalid with ⟨hnumValid, hdenValid, hboundary, hLip⟩
  apply CircleMesh.circleContourIntegral_enclosed ev.lipschitz_nonneg
    ev.schedule.mesh_pos hLip
  intro k hk
  have hz := certifiedRadiusNode_sound ev.radius ev.radiusPrecision ev.schedule hk
  rcases hboundary k hk with ⟨hbox, haway⟩
  have hnum := (hnumValid.2.2 hbox hz).1 ev.mapFuel
  have hden := (hdenValid.2.2 hbox hz).1 ev.mapFuel
  have hquot := ComplexRatInterval.div_sound haway hnum hden
  have htangent := tangentNode_sound ev.radius ev.radiusPrecision ev.piPrecision
    ev.schedule hk
  dsimp only [BoundedCircleEvaluator.node]
  split
  · simpa [CircleMesh.circleIntegrand] using
      ComplexRatInterval.mul_sound hquot htangent
  · contradiction

/-- [For an evaluator satisfying its validity conditions](hyp:hvalid) and [a common width bound
met by every node rectangle up to the mesh](hyp:hnode), [the quadrature rectangle has
width at most that node width plus the Lipschitz constant divided by the mesh count](goal). -/
lemma boundedContourEvaluate_width {box : ComplexRatInterval}
    (ev : BoundedCircleEvaluator box) (hvalid : ev.Valid)
    (nodeWidth : ℚ) (hnode : ∀ k ≤ ev.schedule.mesh, (ev.node k).width ≤ nodeWidth) :
    (boundedContourEvaluate ev).width ≤
      nodeWidth + ev.lipschitz / ev.schedule.mesh := by
  have hnode0 := hnode 0 (Nat.zero_le ev.schedule.mesh)
  have hw : 0 ≤ nodeWidth :=
    (RatInterval.width_nonneg (ev.node 0).re).trans
      ((le_max_left _ _).trans hnode0)
  have hcoords : ∀ k ≤ ev.schedule.mesh,
      (ev.node k).re.width ≤ nodeWidth ∧ (ev.node k).im.width ≤ nodeWidth := by
    intro k hk
    have hk' := hnode k hk
    exact ⟨(le_max_left _ _).trans hk', (le_max_right _ _).trans hk'⟩
  have hwidth := CircleMesh.integralEnclosure_width hw ev.lipschitz_nonneg
    ev.schedule.mesh_pos hcoords
  unfold boundedContourEvaluate ComplexRatInterval.width
  exact max_le hwidth.1 hwidth.2

/-- Executable rational endpoint operations.  No semantic real or complex
value is stored in this table: represented inputs are the value-opaque local
approximant structures and their meanings are supplied externally. -/
structure CertifiedComplexOperations where
  realRefine : RationalRealApproximants → ℕ → RatInterval
  realAdd : RatInterval → RatInterval → RatInterval
  realSub : RatInterval → RatInterval → RatInterval
  realMul : RatInterval → RatInterval → RatInterval
  realAbs : RatInterval → RatInterval
  sqrtInterval : RatInterval → ℕ → RatInterval
  complexAdd : ComplexRatInterval → ComplexRatInterval → ComplexRatInterval
  complexSub : ComplexRatInterval → ComplexRatInterval → ComplexRatInterval
  complexConj : ComplexRatInterval → ComplexRatInterval
  complexMul : ComplexRatInterval → ComplexRatInterval → ComplexRatInterval
  complexNormSq : ComplexRatInterval → RatInterval
  complexNorm : ComplexRatInterval → ℕ → RatInterval
  guardedDiv : (I J : ComplexRatInterval) → (m : ℚ) → 0 < m →
    m ≤ (cxModulusSq J).lo → ComplexRatInterval
  piInterval : ℕ → RatInterval
  expInterval : RatInterval → ℕ → RatInterval
  sinInterval : RatInterval → ℕ → RatInterval
  cosInterval : RatInterval → ℕ → RatInterval
  complexExp : ComplexRatInterval → ℕ → ComplexRatInterval
  expNameApprox : RationalRealApproximants → ℕ → RatInterval
  sinNameApprox : RationalRealApproximants → ℕ → RatInterval
  cosNameApprox : RationalRealApproximants → ℕ → RatInterval
  complexExpNameApprox : RationalComplexApproximants → ℕ → ComplexRatInterval
  radiusNode : ExecutablePositiveRealName → ℕ → ℕ → CircleSchedule →
    ComplexRatInterval
  tangentNode : ExecutablePositiveRealName → ℕ → ℕ → CircleSchedule →
    ComplexRatInterval
  evaluateNode : RationalComplexNodeApproximants → NodeEvaluationSchedule → ℕ →
    ComplexRatInterval
  finiteInfimum : (nodes : ℕ → RatInterval) → (L : ℚ) → 0 ≤ L →
    (mesh : ℕ) → 0 < mesh → RatInterval
  finiteSupremum : (nodes : ℕ → RatInterval) → (L : ℚ) → 0 ≤ L →
    (mesh : ℕ) → 0 < mesh → RatInterval
  quadrature : (nodes : ℕ → ComplexRatInterval) → (L : ℚ) → 0 ≤ L →
    (mesh : ℕ) → 0 < mesh → ComplexRatInterval

/-- The square-free endpoint rule used by the concrete bounded build for the
absolute value of a real interval. -/
def canonicalRealAbsInterval (I : RatInterval) : RatInterval := absInterval I

/-- The complete, lossless resource trace is the schedule itself. -/
def CertifiedComplexOperations.fuelTrace (_operations : CertifiedComplexOperations)
    (name : RationalComplexNodeApproximants) (input : ComplexRatInterval)
    (L : ℚ) (e : PosRat) (endpointOperations : ℕ) : NodeEvaluationSchedule :=
  nodeEvaluationScheduleProgram name input L e endpointOperations

/-- The list of mesh indices a node evaluation schedule visits: every index from zero up to and
including the schedule's mesh fuel, so the terminal trapezoid endpoint is enumerated. -/
def CertifiedComplexOperations.nodeEnumerator (_operations : CertifiedComplexOperations)
    (schedule : NodeEvaluationSchedule) : List ℕ :=
  List.range (schedule.meshFuel + 1)

/-- Exact executable algorithms required by the paper's bounded-build
specification.  This prevents an arbitrary sound operation table from being
mistaken for the specified Machin/Taylor/bisection implementation. -/
def CertifiedComplexOperations.IsCanonical
    (operations : CertifiedComplexOperations) : Prop :=
  (∀ x fuel, operations.realRefine x fuel = x.approx fuel) ∧
  (∀ I J, operations.realAdd I J = I.add J) ∧
  (∀ I J, operations.realSub I J = I.sub J) ∧
  (∀ I J, operations.realMul I J = I.mul J) ∧
  (∀ I, operations.realAbs I = canonicalRealAbsInterval I) ∧
  (∀ I fuel, operations.sqrtInterval I fuel = sqrtBisectInterval I fuel) ∧
  (∀ I J, operations.complexAdd I J = I.add J) ∧
  (∀ I J, operations.complexSub I J = I.sub J) ∧
  (∀ I, operations.complexConj I = I.conj) ∧
  (∀ I J, operations.complexMul I J = I.mul J) ∧
  (∀ I, operations.complexNormSq I = cxModulusSq I) ∧
  (∀ I fuel, operations.complexNorm I fuel = cxModulus I fuel) ∧
  (∀ I J m hm hguard,
    operations.guardedDiv I J m hm hguard = cxDiv I J m hm hguard) ∧
  operations.piInterval = machinPiInterval ∧
  (∀ I fuel, operations.expInterval I fuel = expTaylorInterval I fuel) ∧
  (∀ I fuel, operations.sinInterval I fuel =
    CausalSmith.Stat.SaPlmCumulantConverse.sinInterval I fuel) ∧
  (∀ I fuel, operations.cosInterval I fuel =
    CausalSmith.Stat.SaPlmCumulantConverse.cosInterval I fuel) ∧
  (∀ I fuel, operations.complexExp I fuel = cexpInterval I fuel) ∧
  (∀ x fuel, operations.expNameApprox x fuel =
    realOutputSequence expTaylorInterval x fuel) ∧
  (∀ x fuel, operations.sinNameApprox x fuel =
    realOutputSequence CausalSmith.Stat.SaPlmCumulantConverse.sinInterval x fuel) ∧
  (∀ x fuel, operations.cosNameApprox x fuel =
    realOutputSequence CausalSmith.Stat.SaPlmCumulantConverse.cosInterval x fuel) ∧
  (∀ z fuel, operations.complexExpNameApprox z fuel =
    complexExpOutputSequence z fuel) ∧
  (∀ radius N q schedule,
    operations.radiusNode radius N q schedule =
      circleNodeFromPositiveName radius N q schedule) ∧
  (∀ radius N q schedule,
    operations.tangentNode radius N q schedule =
      circleTangentFromPositiveName radius N q schedule) ∧
  (∀ name schedule k, operations.evaluateNode name schedule k =
    evaluateComplexNode name schedule k) ∧
  (∀ nodes L hL mesh hmesh,
    operations.finiteInfimum nodes L hL mesh hmesh =
      CircleMesh.infEnclosure nodes L hL mesh hmesh) ∧
  (∀ nodes L hL mesh hmesh,
    operations.finiteSupremum nodes L hL mesh hmesh =
      CircleMesh.supEnclosure nodes L hL mesh hmesh) ∧
  (∀ nodes L hL mesh hmesh,
    operations.quadrature nodes L hL mesh hmesh =
      CircleMesh.integralEnclosure nodes L hL mesh hmesh)

/-- [When an operation table is the canonical one specified by the paper's bounded
build](hyp:h), [its real interval addition is the ordinary endpointwise addition of rational
intervals](goal). -/
lemma CertifiedComplexOperations.IsCanonical.realAdd_eq
    {operations : CertifiedComplexOperations} (h : operations.IsCanonical)
    (I J : RatInterval) : operations.realAdd I J = I.add J := h.2.1 I J

/-- [When an operation table is the canonical one specified by the paper's bounded
build](hyp:h), [its complex interval addition is the ordinary coordinatewise addition of
rational rectangles](goal). -/
lemma CertifiedComplexOperations.IsCanonical.complexAdd_eq
    {operations : CertifiedComplexOperations} (h : operations.IsCanonical)
    (I J : ComplexRatInterval) : operations.complexAdd I J = I.add J :=
  h.2.2.2.2.2.2.1 I J

/-- [When an operation table is the canonical one specified by the paper's bounded
build](hyp:h), its finite-infimum routine applied to a family of node intervals with [a
nonnegative Lipschitz constant](hyp:hL) and [a positive mesh count](hyp:hmesh) [returns the
standard circle-mesh infimum enclosure](goal). -/
lemma CertifiedComplexOperations.IsCanonical.finiteInfimum_eq
    {operations : CertifiedComplexOperations} (h : operations.IsCanonical)
    (nodes : ℕ → RatInterval) (L : ℚ) (hL : 0 ≤ L)
    (mesh : ℕ) (hmesh : 0 < mesh) :
    operations.finiteInfimum nodes L hL mesh hmesh =
      CircleMesh.infEnclosure nodes L hL mesh hmesh := by
  unfold CertifiedComplexOperations.IsCanonical at h
  aesop

/-- [When an operation table is the canonical one specified by the paper's bounded
build](hyp:h), its quadrature routine applied to a family of node rectangles with [a nonnegative
Lipschitz constant](hyp:hL) and [a positive mesh count](hyp:hmesh) [returns the standard
circle-mesh integral enclosure](goal). -/
lemma CertifiedComplexOperations.IsCanonical.quadrature_eq
    {operations : CertifiedComplexOperations} (h : operations.IsCanonical)
    (nodes : ℕ → ComplexRatInterval) (L : ℚ) (hL : 0 ≤ L)
    (mesh : ℕ) (hmesh : 0 < mesh) :
    operations.quadrature nodes L hL mesh hmesh =
      CircleMesh.integralEnclosure nodes L hL mesh hmesh := by
  unfold CertifiedComplexOperations.IsCanonical at h
  aesop

/-- Full conditional build carrier for represented execution.  It bundles
the executable rational/complex arithmetic, guarded division, constructed
transcendentals, circle nodes, finite extrema and quadrature, together with
semantic soundness, effective fuel/modulus, endpoint, trace, and compilation
certificates.  Paper-specific spectral maps and schedules remain local
derived facts and are not fields of this generic carrier. -/
structure ComplexCertifiedIntervalArithmetic where
  operations : CertifiedComplexOperations
  canonicalAlgorithms : operations.IsCanonical
  realRefine_sound : ∀ (name : RationalRealApproximants) (x : ℝ),
    name.Represents x → ∀ fuel, (operations.realRefine name fuel).Contains x
  realRefine_width : ∀ (name : RationalRealApproximants) (e : PosRat),
    (operations.realRefine name (name.modulus e)).width ≤ e.1
  realAdd_sound : ∀ {I J : RatInterval} {x y : ℝ},
    I.Contains x → J.Contains y → (operations.realAdd I J).Contains (x + y)
  realSub_sound : ∀ {I J : RatInterval} {x y : ℝ},
    I.Contains x → J.Contains y → (operations.realSub I J).Contains (x - y)
  realMul_sound : ∀ {I J : RatInterval} {x y : ℝ},
    I.Contains x → J.Contains y → (operations.realMul I J).Contains (x * y)
  realAbs_sound : ∀ {I : RatInterval} {x : ℝ},
    I.Contains x → (operations.realAbs I).Contains |x|
  sqrt_sound : ∀ {I : RatInterval} (hI : 0 ≤ I.lo) {x : ℝ},
    I.Contains x → 0 ≤ x → ∀ fuel,
      (operations.sqrtInterval I fuel).Contains (Real.sqrt x)
  sqrt_width : ∀ x fuel,
    sqrtHiBisect x fuel - sqrtLoBisect x fuel ≤
      ((sqrtInitial x).hi - (sqrtInitial x).lo) * (1 / 2 : ℚ) ^ fuel
  complexAdd_sound : ∀ {I J : ComplexRatInterval} {z w : ℂ},
    I.Contains z → J.Contains w → (operations.complexAdd I J).Contains (z + w)
  complexSub_sound : ∀ {I J : ComplexRatInterval} {z w : ℂ},
    I.Contains z → J.Contains w → (operations.complexSub I J).Contains (z - w)
  complexConj_sound : ∀ {I : ComplexRatInterval} {z : ℂ},
    I.Contains z → (operations.complexConj I).Contains (star z)
  complexMul_sound : ∀ {I J : ComplexRatInterval} {z w : ℂ},
    I.Contains z → J.Contains w → (operations.complexMul I J).Contains (z * w)
  complexNormSq_sound : ∀ {I : ComplexRatInterval} {z : ℂ},
    I.Contains z → (operations.complexNormSq I).Contains (Complex.normSq z)
  complexNorm_sound : ∀ {I : ComplexRatInterval} {z : ℂ},
    I.Contains z → ∀ fuel, (operations.complexNorm I fuel).Contains ‖z‖
  guardedDiv_sound : ∀ {I J : ComplexRatInterval} {z w : ℂ}
      (m : ℚ) (hm : 0 < m) (hguard : m ≤ (cxModulusSq J).lo),
    I.Contains z → J.Contains w →
      (operations.guardedDiv I J m hm hguard).Contains (z / w)
  pi_sound : ∀ fuel, (operations.piInterval fuel).Contains Real.pi
  pi_nested : ∀ fuel,
    (operations.piInterval (fuel + 1)).Subinterval (operations.piInterval fuel)
  pi_effective : ∀ e,
    (operations.piInterval (machinPiFuel e)).width ≤ e.1
  exp_sound : ∀ {I : RatInterval} {x : ℝ}, I.Contains x → ∀ fuel,
    (operations.expInterval I fuel).Contains (Real.exp x)
  sin_sound : ∀ {I : RatInterval} {x : ℝ}, I.Contains x → ∀ fuel,
    (operations.sinInterval I fuel).Contains (Real.sin x)
  cos_sound : ∀ {I : RatInterval} {x : ℝ}, I.Contains x → ∀ fuel,
    (operations.cosInterval I fuel).Contains (Real.cos x)
  complexExp_sound : ∀ {I : ComplexRatInterval} {z : ℂ}, I.Contains z → ∀ fuel,
    (operations.complexExp I fuel).Contains (Complex.exp z)
  complexExp_nested : ∀ I fuel,
    (operations.complexExp I (fuel + 1)).Subinterval (operations.complexExp I fuel)
  expNameContract : RealTranscendentalContract expTaylorInterval Real.exp expScheduleProgram
  sinNameContract : RealTranscendentalContract
    CausalSmith.Stat.SaPlmCumulantConverse.sinInterval Real.sin trigScheduleProgram
  cosNameContract : RealTranscendentalContract
    CausalSmith.Stat.SaPlmCumulantConverse.cosInterval Real.cos trigScheduleProgram
  complexExpNameContract : ComplexExpContract cexpScheduleProgram
  circleProgramContract : CircleProgramContract
    circleNodeScheduleProgram circleTangentScheduleProgram
  nodeEvaluationContract : NodeEvaluationContract nodeEvaluationScheduleProgram
  finiteInfimum_sound : ∀ {f : ℝ → ℝ} {nodes : ℕ → RatInterval}
      {L : ℚ} (hL : 0 ≤ L) {mesh : ℕ} (hmesh : 0 < mesh),
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |f s - f t| ≤ (L : ℝ) * |s - t|) →
    (∀ k ≤ mesh, (nodes k).Contains (f (CircleMesh.meshPoint mesh k))) →
    (operations.finiteInfimum nodes L hL mesh hmesh).Contains
      (sInf (f '' Set.Icc (0 : ℝ) 1))
  finiteSupremum_sound : ∀ {f : ℝ → ℝ} {nodes : ℕ → RatInterval}
      {L : ℚ} (hL : 0 ≤ L) {mesh : ℕ} (hmesh : 0 < mesh),
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |f s - f t| ≤ (L : ℝ) * |s - t|) →
    (∀ k ≤ mesh, (nodes k).Contains (f (CircleMesh.meshPoint mesh k))) →
    (operations.finiteSupremum nodes L hL mesh hmesh).Contains
      (sSup (f '' Set.Icc (0 : ℝ) 1))
  quadrature_sound : ∀ {g : ℝ → ℂ} {nodes : ℕ → ComplexRatInterval}
      {L : ℚ} (hL : 0 ≤ L) {mesh : ℕ} (hmesh : 0 < mesh),
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖g s - g t‖ ≤ (L : ℝ) * |s - t|) →
    (∀ k ≤ mesh, (nodes k).Contains (g (CircleMesh.meshPoint mesh k))) →
    (operations.quadrature nodes L hL mesh hmesh).Contains (∫ u in (0 : ℝ)..1, g u)
  endpointContract : ∀ schedule : NodeEvaluationSchedule,
    operations.nodeEnumerator schedule = List.range (schedule.meshFuel + 1) ∧
    ∀ k ∈ operations.nodeEnumerator schedule, k ≤ schedule.meshFuel
  traceFuelContract : ∀ name input L e endpointOperations,
    operations.fuelTrace name input L e endpointOperations =
      nodeEvaluationScheduleProgram name input L e endpointOperations

/-- Conditional carrier for represented execution. -/
-- @node: def:certified-contour-arithmetic-substrate
def complexCertifiedIntervalArithmetic : Type := ComplexCertifiedIntervalArithmetic

end CausalSmith.Stat.SaPlmCumulantConverse
