import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.API
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Mesh

/-!
# Certified complex rectangle arithmetic

This file supplies the complex-algebra half missing from the promoted real
certified interval API.  Every executable operation uses rational endpoints;
exact complex values occur only in the semantic soundness contracts.
-/

open scoped ComplexConjugate

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace CausalSmith.Stat.SaPlmCumulantConverse

/-- Coordinatewise complex rectangle subtraction. -/
def cxSub (I J : ComplexRatInterval) : ComplexRatInterval :=
  ⟨I.re.sub J.re, I.im.sub J.im⟩

/-- Complex conjugation negates the imaginary interval. -/
def cxConj (I : ComplexRatInterval) : ComplexRatInterval :=
  ⟨I.re, I.im.neg⟩

/-- Outward complex multiplication assembled from the promoted real API. -/
def cxMul (I J : ComplexRatInterval) : ComplexRatInterval :=
  ⟨(I.re.mul J.re).sub (I.im.mul J.im),
    (I.re.mul J.im).add (I.im.mul J.re)⟩

/-- Rational lower bound for the square of every point of an interval. -/
def sqLo (I : RatInterval) : ℚ :=
  if I.lo ≤ 0 ∧ 0 ≤ I.hi then 0 else min (I.lo ^ 2) (I.hi ^ 2)

/-- Rational upper bound for the square of every point of an interval. -/
def sqHi (I : RatInterval) : ℚ := max (I.lo ^ 2) (I.hi ^ 2)

private lemma sqLo_le_sqHi (I : RatInterval) : sqLo I ≤ sqHi I := by
  unfold sqLo sqHi
  split_ifs
  · exact (sq_nonneg I.lo).trans (le_max_left _ _)
  · exact min_le_max

/-- Squared modulus enclosure obtained by adding coordinate-square bounds. -/
def cxModulusSq (I : ComplexRatInterval) : RatInterval :=
  ⟨sqLo I.re + sqLo I.im, sqHi I.re + sqHi I.im,
    add_le_add (sqLo_le_sqHi I.re) (sqLo_le_sqHi I.im)⟩

/-- One rational bisection state. -/
structure SqrtBracket where
  lo : ℚ
  hi : ℚ

/-- Initial nonnegative bracket used by the square-root routines. -/
def sqrtInitial (x : ℚ) : SqrtBracket := ⟨0, max 1 x⟩

/-- Bisection from below, using only a rational square comparison. -/
def sqrtLoStep (x : ℚ) (b : SqrtBracket) : SqrtBracket :=
  let mid := (b.lo + b.hi) / 2
  if mid ^ 2 ≤ x then ⟨mid, b.hi⟩ else ⟨b.lo, mid⟩

/-- Bisection from above, using only a rational square comparison. -/
def sqrtHiStep (x : ℚ) (b : SqrtBracket) : SqrtBracket :=
  let mid := (b.lo + b.hi) / 2
  if x ≤ mid ^ 2 then ⟨b.lo, mid⟩ else ⟨mid, b.hi⟩

/-- Fixed-fuel lower square-root bisection. -/
def sqrtLoBisect (x : ℚ) (fuel : ℕ) : ℚ :=
  (Nat.iterate (sqrtLoStep x) fuel (sqrtInitial x)).lo

/-- Fixed-fuel upper square-root bisection. -/
def sqrtHiBisect (x : ℚ) (fuel : ℕ) : ℚ :=
  (Nat.iterate (sqrtLoStep x) fuel (sqrtInitial x)).hi

/-- Rational bisection enclosure for square roots on a nonnegative interval.
The two endpoint bisections are deliberately exposed, so the executable
algorithm is fixed independently of the promoted interval API. -/
def sqrtBisectInterval (I : RatInterval) (fuel : ℕ) : RatInterval :=
  ⟨min (sqrtLoBisect I.lo fuel) (sqrtHiBisect I.hi fuel),
    max (sqrtLoBisect I.lo fuel) (sqrtHiBisect I.hi fuel), min_le_max⟩

/-- Fixed-fuel rational enclosure of the modulus of a complex rectangle. -/
def cxModulus (I : ComplexRatInterval) (fuel : ℕ) : RatInterval :=
  let S := cxModulusSq I
  ⟨min (sqrtLoBisect S.lo fuel) (sqrtHiBisect S.hi fuel),
    max (sqrtLoBisect S.lo fuel) (sqrtHiBisect S.hi fuel), min_le_max⟩

/-- Guarded complex division via multiplication by the conjugate and an
outward reciprocal of the squared modulus interval. -/
def cxDivGuarded (I J : ComplexRatInterval) (m : ℚ) (hm : 0 < m)
    (hguard : m ≤ (cxModulusSq J).lo) : ComplexRatInterval :=
  let S := cxModulusSq J
  have hS : S.AwayFromZero := Or.inr (hm.trans_le hguard)
  let numerator := cxMul I (cxConj J)
  ⟨numerator.re.div S hS, numerator.im.div S hS⟩

/-- Public exact guarded-division primitive used by the bounded carrier. -/
abbrev cxDiv := cxDivGuarded

/-- Endpoint rule for the absolute value of a real interval. -/
def absInterval (I : RatInterval) : RatInterval :=
  if h : I.lo ≤ 0 ∧ 0 ≤ I.hi then
    ⟨0, max |I.lo| |I.hi|, (abs_nonneg I.lo).trans (le_max_left _ _)⟩
  else
    ⟨min |I.lo| |I.hi|, max |I.lo| |I.hi|, min_le_max⟩

/-- Rectangle subtraction is sound: if [a complex number lies in the first
rectangle](hyp:hz) and [a second complex number lies in the second
rectangle](hyp:hw), then [their difference lies in the rectangle obtained by
subtracting the two rectangles coordinate by coordinate](goal).

The real and imaginary sides are handled independently by the promoted real
interval subtraction, so no outward rounding beyond the real API is needed. -/
lemma cxSub_sound {I J : ComplexRatInterval} {z w : ℂ}
    (hz : I.Contains z) (hw : J.Contains w) : (cxSub I J).Contains (z - w) := by
  exact ⟨RatInterval.sub_sound hz.1 hw.1, RatInterval.sub_sound hz.2 hw.2⟩

/-- Conjugation of rectangles is sound: if [a complex number lies in a
rectangle](hyp:hz), then [its complex conjugate lies in the rectangle whose
imaginary side has been negated and whose real side is unchanged](goal). -/
lemma cxConj_sound {I : ComplexRatInterval} {z : ℂ}
    (hz : I.Contains z) : (cxConj I).Contains (starRingEnd ℂ z) := by
  exact ⟨hz.1, RatInterval.neg_sound hz.2⟩

/-- Rectangle multiplication is sound: if [a complex number lies in the first
rectangle](hyp:hz) and [a second complex number lies in the second
rectangle](hyp:hw), then [their product lies in the outward product
rectangle](goal), whose real side encloses the real part built from the
cross-products of the coordinate intervals and whose imaginary side encloses
the corresponding imaginary part. -/
lemma cxMul_sound {I J : ComplexRatInterval} {z w : ℂ}
    (hz : I.Contains z) (hw : J.Contains w) : (cxMul I J).Contains (z * w) := by
  constructor
  · exact RatInterval.sub_sound
      (RatInterval.mul_sound hz.1 hw.1) (RatInterval.mul_sound hz.2 hw.2)
  · exact RatInterval.add_sound
      (RatInterval.mul_sound hz.1 hw.2) (RatInterval.mul_sound hz.2 hw.1)

/-- The rational square bounds are sound: if [a real number lies in a rational
interval](hyp:hx), then [its square is at least the interval's rational lower
square bound and at most its rational upper square bound](goal).

The lower bound is zero when the interval straddles the origin and otherwise the
smaller of the two endpoint squares; the upper bound is always the larger of the
two endpoint squares. -/
lemma sq_bounds_sound {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (sqLo I : ℝ) ≤ x ^ 2 ∧ x ^ 2 ≤ (sqHi I : ℝ) := by
  have hlohi : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.lo_le_hi
  have hupper : x ^ 2 ≤ max ((I.lo : ℝ) ^ 2) ((I.hi : ℝ) ^ 2) := by
    by_cases hx0 : 0 ≤ x
    · apply le_max_of_le_right
      nlinarith [hx.2]
    · have hx0' : x ≤ 0 := le_of_not_ge hx0
      apply le_max_of_le_left
      nlinarith [hx.1]
  unfold sqLo sqHi
  split_ifs with h
  · simp only [Rat.cast_zero, Rat.cast_max, Rat.cast_pow]
    exact ⟨sq_nonneg x, hupper⟩
  · rcases not_and_or.mp h with hlo | hhi
    · have hloposQ : (0 : ℚ) < I.lo := lt_of_not_ge hlo
      have hlopos : (0 : ℝ) < I.lo := by exact_mod_cast hloposQ
      have hxpos : 0 < x := hlopos.trans_le hx.1
      simp only [Rat.cast_min, Rat.cast_max, Rat.cast_pow]
      constructor
      · apply min_le_of_left_le
        nlinarith [hx.1]
      · exact hupper
    · have hhinegQ : I.hi < (0 : ℚ) := lt_of_not_ge hhi
      have hhineg : (I.hi : ℝ) < 0 := by exact_mod_cast hhinegQ
      have hxneg : x < 0 := hx.2.trans_lt hhineg
      simp only [Rat.cast_min, Rat.cast_max, Rat.cast_pow]
      constructor
      · apply min_le_of_right_le
        nlinarith [hx.2]
      · exact hupper

/-- The starting bracket of the square-root bisection is valid: for [a
nonnegative rational number](hyp:hx), [the initial bracket has a nonnegative
lower endpoint, its lower endpoint does not exceed its upper endpoint, the
square of its lower endpoint is at most the number, and the number is at most
the square of its upper endpoint](goal).

The bracket starts at zero on the left and at the larger of one and the number
on the right, which is why the right endpoint's square already dominates the
number. -/
lemma sqrtInitial_brackets {x : ℚ} (hx : 0 ≤ x) :
    0 ≤ (sqrtInitial x).lo ∧ (sqrtInitial x).lo ≤ (sqrtInitial x).hi ∧
      (sqrtInitial x).lo ^ 2 ≤ x ∧
      x ≤ (sqrtInitial x).hi ^ 2 := by
  simp only [sqrtInitial]
  constructor
  · norm_num
  constructor
  · simp
  constructor
  · simpa using hx
  · by_cases hx1 : x ≤ 1
    · rw [max_eq_left (show (1 : ℚ) ≥ x from hx1)]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hx1)]
      nlinarith

/-- One bisection step preserves the bracketing invariant: if [a bracket has a
nonnegative lower endpoint, is correctly ordered, and its endpoint squares
straddle the target number](hyp:hb), then [the bracket produced by one lower
bisection step again has a nonnegative lower endpoint, is correctly ordered, and
has endpoint squares straddling the same number](goal).

The step compares the square of the midpoint with the target using only rational
arithmetic, keeping whichever half still brackets the square root. -/
lemma sqrtLoStep_brackets {x : ℚ} {b : SqrtBracket}
    (hb : 0 ≤ b.lo ∧ b.lo ≤ b.hi ∧ b.lo ^ 2 ≤ x ∧ x ≤ b.hi ^ 2) :
    0 ≤ (sqrtLoStep x b).lo ∧ (sqrtLoStep x b).lo ≤ (sqrtLoStep x b).hi ∧
      (sqrtLoStep x b).lo ^ 2 ≤ x ∧
      x ≤ (sqrtLoStep x b).hi ^ 2 := by
  simp only [sqrtLoStep]
  split_ifs with hmid <;> dsimp
  · refine ⟨by linarith [hb.1, hb.2.1], by linarith [hb.2.1], hmid, hb.2.2.2⟩
  · exact ⟨hb.1, by linarith [hb.2.1], hb.2.2.1, le_of_not_ge hmid⟩

/-- The bracketing invariant survives any number of bisection steps: for [a
nonnegative rational number](hyp:hx), [after iterating the lower bisection step
any fixed number of times starting from the initial bracket, the resulting
bracket still has a nonnegative lower endpoint, is correctly ordered, and its
endpoint squares straddle the number](goal). -/
lemma sqrtLoIterate_brackets {x : ℚ} (hx : 0 ≤ x) (fuel : ℕ) :
    0 ≤ (Nat.iterate (sqrtLoStep x) fuel (sqrtInitial x)).lo ∧
      (Nat.iterate (sqrtLoStep x) fuel (sqrtInitial x)).lo ≤
        (Nat.iterate (sqrtLoStep x) fuel (sqrtInitial x)).hi ∧
      (Nat.iterate (sqrtLoStep x) fuel (sqrtInitial x)).lo ^ 2 ≤ x ∧
      x ≤ (Nat.iterate (sqrtLoStep x) fuel (sqrtInitial x)).hi ^ 2 := by
  induction fuel with
  | zero => simpa using sqrtInitial_brackets hx
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        ← (Function.Commute.refl (sqrtLoStep x)).iterate_right fuel (sqrtInitial x)]
      exact sqrtLoStep_brackets ih

/-- The lower bisection output never overshoots: for [a nonnegative rational
number](hyp:hx), [the rational value returned by the fixed-fuel lower bisection
is at most the true real square root of that number](goal). -/
lemma sqrtLoBisect_le_sqrt {x : ℚ} (hx : 0 ≤ x) (fuel : ℕ) :
    (sqrtLoBisect x fuel : ℝ) ≤ Real.sqrt x := by
  have hb := sqrtLoIterate_brackets hx fuel
  rw [Real.le_sqrt (by exact_mod_cast hb.1) (by exact_mod_cast hx)]
  exact_mod_cast hb.2.2.1

/-- The upper bisection output never undershoots: for [a nonnegative rational
number](hyp:hx), [the true real square root of that number is at most the
rational value returned by the fixed-fuel upper bisection](goal). -/
lemma sqrt_le_sqrtHiBisect {x : ℚ} (hx : 0 ≤ x) (fuel : ℕ) :
    Real.sqrt x ≤ (sqrtHiBisect x fuel : ℝ) := by
  have hb := sqrtLoIterate_brackets hx fuel
  have hhi : 0 ≤ (Nat.iterate (sqrtLoStep x) fuel (sqrtInitial x)).hi := by
    linarith [hb.1, hb.2.1]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact_mod_cast hhi
  · exact_mod_cast hb.2.2.2

/-- [The rational lower square bound of any interval is nonnegative](goal),
since it is either zero, when the interval straddles the origin, or the smaller
of two squares. -/
lemma sqLo_nonneg (I : RatInterval) : 0 ≤ sqLo I := by
  unfold sqLo
  split_ifs
  · norm_num
  · exact le_min (sq_nonneg _) (sq_nonneg _)

/-- The modulus enclosure is sound: if [a complex number lies in a
rectangle](hyp:hz), then [its modulus lies in the rational interval produced by
the fixed-fuel modulus routine for that rectangle](goal), for any amount of
bisection fuel.

The routine bounds the squared modulus by adding the coordinate square bounds
and then brackets the square root of that interval by rational bisection. -/
lemma cxModulus_sound {I : ComplexRatInterval} {z : ℂ}
    (hz : I.Contains z) (fuel : ℕ) : (cxModulus I fuel).Contains ‖z‖ := by
  have hsre := sq_bounds_sound hz.1
  have hsim := sq_bounds_sound hz.2
  have hSlo : 0 ≤ (cxModulusSq I).lo := by
    exact add_nonneg (sqLo_nonneg I.re) (sqLo_nonneg I.im)
  have hShi : 0 ≤ (cxModulusSq I).hi := by
    dsimp [cxModulusSq, sqHi]
    positivity
  have hnormsq : (cxModulusSq I).lo ≤ Complex.normSq z ∧
      Complex.normSq z ≤ (cxModulusSq I).hi := by
    dsimp [cxModulusSq]
    simp only [Complex.normSq_apply, Rat.cast_add]
    exact ⟨by simpa [pow_two] using add_le_add hsre.1 hsim.1,
      by simpa [pow_two] using add_le_add hsre.2 hsim.2⟩
  change ((min (sqrtLoBisect (cxModulusSq I).lo fuel)
      (sqrtHiBisect (cxModulusSq I).hi fuel) : ℚ) : ℝ) ≤ ‖z‖ ∧
    ‖z‖ ≤ ((max (sqrtLoBisect (cxModulusSq I).lo fuel)
      (sqrtHiBisect (cxModulusSq I).hi fuel) : ℚ) : ℝ)
  simp only [Rat.cast_min, Rat.cast_max]
  constructor
  · apply min_le_of_left_le
    calc
      (sqrtLoBisect (cxModulusSq I).lo fuel : ℝ)
          ≤ Real.sqrt (cxModulusSq I).lo := sqrtLoBisect_le_sqrt hSlo fuel
      _ ≤ Real.sqrt (Complex.normSq z) := Real.sqrt_le_sqrt (by exact_mod_cast hnormsq.1)
      _ = ‖z‖ := by rfl
  · apply le_max_of_le_right
    calc
      ‖z‖ = Real.sqrt (Complex.normSq z) := by rfl
      _ ≤ Real.sqrt (cxModulusSq I).hi := Real.sqrt_le_sqrt (by exact_mod_cast hnormsq.2)
      _ ≤ (sqrtHiBisect (cxModulusSq I).hi fuel : ℝ) :=
        sqrt_le_sqrtHiBisect hShi fuel

/-- The square-root enclosure is sound: for [an interval whose lower endpoint is
nonnegative](hyp:hI), if [a real number lies in that interval](hyp:hx), then
[its square root lies in the rational interval produced by the fixed-fuel
bisection enclosure](goal), for any amount of bisection fuel. -/
lemma sqrtBisectInterval_sound {I : RatInterval} (hI : 0 ≤ I.lo)
    {x : ℝ} (hx : I.Contains x) (fuel : ℕ) :
    (sqrtBisectInterval I fuel).Contains (Real.sqrt x) := by
  change ((min (sqrtLoBisect I.lo fuel) (sqrtHiBisect I.hi fuel) : ℚ) : ℝ) ≤
      Real.sqrt x ∧
    Real.sqrt x ≤
      ((max (sqrtLoBisect I.lo fuel) (sqrtHiBisect I.hi fuel) : ℚ) : ℝ)
  simp only [Rat.cast_min, Rat.cast_max]
  constructor
  · apply min_le_of_left_le
    exact (sqrtLoBisect_le_sqrt hI fuel).trans
      (Real.sqrt_le_sqrt (by exact_mod_cast hx.1))
  · apply le_max_of_le_right
    exact (Real.sqrt_le_sqrt (by exact_mod_cast hx.2)).trans
      (sqrt_le_sqrtHiBisect (hI.trans I.lo_le_hi) fuel)

/-- [One step of the lower bisection halves the width of the bracket](goal): the
distance between the new endpoints is exactly half the distance between the old
ones, whichever branch the midpoint test takes. -/
lemma sqrtLoStep_width (x : ℚ) (b : SqrtBracket) :
    (sqrtLoStep x b).hi - (sqrtLoStep x b).lo = (b.hi - b.lo) / 2 := by
  simp only [sqrtLoStep]
  split <;> dsimp <;> ring

/-- [One step of the upper bisection halves the width of the bracket](goal): the
distance between the new endpoints is exactly half the distance between the old
ones, whichever branch the midpoint test takes. -/
lemma sqrtHiStep_width (x : ℚ) (b : SqrtBracket) :
    (sqrtHiStep x b).hi - (sqrtHiStep x b).lo = (b.hi - b.lo) / 2 := by
  simp only [sqrtHiStep]
  split <;> dsimp <;> ring

/-- Halving compounds geometrically: for [a bracket update rule that always
halves the width of the bracket it is applied to](hyp:hstep), [iterating that
rule a fixed number of times shrinks the width of any starting bracket by a
factor of one half raised to the number of iterations](goal). -/
lemma sqrtStep_iterate_width (step : SqrtBracket → SqrtBracket)
    (hstep : ∀ b, (step b).hi - (step b).lo = (b.hi - b.lo) / 2)
    (b : SqrtBracket) (fuel : ℕ) :
    (Nat.iterate step fuel b).hi - (Nat.iterate step fuel b).lo =
      (b.hi - b.lo) * (1 / 2 : ℚ) ^ fuel := by
  induction fuel generalizing b with
  | zero => simp
  | succ fuel ih =>
      rw [Function.iterate_succ_apply,
        ← (Function.Commute.refl step).iterate_right fuel b, hstep, ih, pow_succ]
      ring

/-- [The gap between the upper and lower square-root bisection outputs is at
most the width of the initial bracket times one half raised to the amount of
fuel](goal), so the enclosure tightens geometrically in the number of bisection
steps. -/
lemma sqrt_bisect_width (x : ℚ) (fuel : ℕ) :
    sqrtHiBisect x fuel - sqrtLoBisect x fuel ≤
      ((sqrtInitial x).hi - (sqrtInitial x).lo) * (1 / 2 : ℚ) ^ fuel := by
  unfold sqrtHiBisect sqrtLoBisect
  exact le_of_eq (sqrtStep_iterate_width (sqrtLoStep x)
    (sqrtLoStep_width x) (sqrtInitial x) fuel)

/-- Guarded rectangle division is sound: if [a complex number lies in the
numerator rectangle](hyp:hz), [a second complex number lies in the denominator
rectangle](hyp:hw), and [a strictly positive rational guard](hyp:hm) [bounds the
squared modulus of the denominator rectangle away from zero from below](hyp:hguard),
then [the quotient of the two complex numbers lies in the rectangle returned by
the guarded division](goal).

The division multiplies by the conjugate of the denominator rectangle and then
divides both coordinates by the squared-modulus interval, which the guard
certifies to be bounded away from zero. -/
lemma cxDivGuarded_sound {I J : ComplexRatInterval} {z w : ℂ}
    (hz : I.Contains z) (hw : J.Contains w) (m : ℚ) (hm : 0 < m)
    (hguard : m ≤ (cxModulusSq J).lo) :
    (cxDivGuarded I J m hm hguard).Contains (z / w) := by
  let S := cxModulusSq J
  have hS : S.AwayFromZero := Or.inr (hm.trans_le hguard)
  have hnum : (cxMul I (cxConj J)).Contains (z * starRingEnd ℂ w) :=
    cxMul_sound hz (cxConj_sound hw)
  have hsqre := sq_bounds_sound hw.1
  have hsqim := sq_bounds_sound hw.2
  have hden : S.Contains (Complex.normSq w) := by
    dsimp [S, cxModulusSq]
    simp only [Complex.normSq_apply, Rat.cast_add]
    exact ⟨by simpa [pow_two] using add_le_add hsqre.1 hsqim.1,
      by simpa [pow_two] using add_le_add hsqre.2 hsqim.2⟩
  change ((cxMul I (cxConj J)).re.div S hS).Contains (z / w).re ∧
    ((cxMul I (cxConj J)).im.div S hS).Contains (z / w).im
  constructor
  · convert RatInterval.div_sound hS hnum.1 hden using 1
    rw [Complex.div_re, Complex.mul_re]
    rw [show (starRingEnd ℂ w).re = w.re by simp,
      show (starRingEnd ℂ w).im = -w.im by simp]
    ring
  · convert RatInterval.div_sound hS hnum.2 hden using 1
    rw [Complex.div_im, Complex.mul_im]
    rw [show (starRingEnd ℂ w).re = w.re by simp,
      show (starRingEnd ℂ w).im = -w.im by simp]
    ring

/-- The absolute-value endpoint rule is sound: if [a real number lies in a
rational interval](hyp:hx), then [its absolute value lies in the interval
produced by the absolute-value rule](goal).

That rule returns the interval from zero to the larger endpoint magnitude when
the input interval straddles the origin, and otherwise the interval between the
smaller and larger endpoint magnitudes. -/
lemma absInterval_sound {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (absInterval I).Contains |x| := by
  unfold absInterval
  split_ifs with h
  · simp only [RatInterval.Contains, Rat.cast_zero, Rat.cast_max, Rat.cast_abs]
    exact ⟨abs_nonneg x, abs_le_max_abs_abs hx.1 hx.2⟩
  · rcases not_and_or.mp h with hlo | hhi
    · have hIloposQ : (0 : ℚ) < I.lo := lt_of_not_ge hlo
      have hIlopos : (0 : ℝ) < I.lo := by exact_mod_cast hIloposQ
      have hIhipos : (0 : ℝ) < I.hi := hIlopos.trans_le (by exact_mod_cast I.lo_le_hi)
      have hxpos : 0 < x := hIlopos.trans_le hx.1
      simp only [RatInterval.Contains, Rat.cast_min, Rat.cast_max, Rat.cast_abs]
      rw [abs_of_pos hIlopos, abs_of_pos hIhipos, abs_of_pos hxpos]
      exact ⟨min_le_of_left_le hx.1, le_max_of_le_right hx.2⟩
    · have hIhinegQ : I.hi < (0 : ℚ) := lt_of_not_ge hhi
      have hIhineg : (I.hi : ℝ) < 0 := by exact_mod_cast hIhinegQ
      have hIlohi : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.lo_le_hi
      have hIloneg : (I.lo : ℝ) < 0 := hIlohi.trans_lt hIhineg
      have hxneg : x < 0 := hx.2.trans_lt hIhineg
      simp only [RatInterval.Contains, Rat.cast_min, Rat.cast_max, Rat.cast_abs]
      rw [abs_of_neg hIloneg, abs_of_neg hIhineg, abs_of_neg hxneg]
      exact ⟨min_le_of_right_le (neg_le_neg hx.2),
        le_max_of_le_left (neg_le_neg hx.1)⟩

end CausalSmith.Stat.SaPlmCumulantConverse
