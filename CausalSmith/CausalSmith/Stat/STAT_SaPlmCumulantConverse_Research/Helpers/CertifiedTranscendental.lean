import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.CertifiedComplex
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.FiniteSearch
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Quadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Conditional certified transcendental substrate

This file defines the genuine rational, finite-fuel algorithms required by the
paper.  It deliberately does not manufacture a certified implementation.  The
record at the end is the contract that a future compiled implementation must
discharge.

The convergence clauses consume shrinking input approximants.  In particular,
there is no claim that the image of one fixed nondegenerate interval under
`exp`, `sin`, `cos`, or complex `exp` can have arbitrarily small width.
-/

open scoped BigOperators Interval

open MeasureTheory Set intervalIntegral

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace CausalSmith.Stat.SaPlmCumulantConverse

/-- Rational alternating arctangent polynomial through index `N`. -/
def atanPartial (x : ℚ) (N : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (N + 1),
    (if Even j then 1 else -1) * x ^ (2 * j + 1) / (2 * j + 1)

/-- Alternating-series remainder radius. -/
def atanRemainder (x : ℚ) (N : ℕ) : ℚ :=
  |x| ^ (2 * N + 3) / (2 * N + 3)

/-- Raw rational enclosure of the arctangent at the rational point `x`: the
alternating Taylor partial sum truncated at index `N`, widened symmetrically by
the alternating-series remainder radius attached to that truncation.

The interval is well formed because the remainder radius is nonnegative, so the
lower endpoint never exceeds the upper one. -/
def atanRaw (x : ℚ) (N : ℕ) : RatInterval :=
  ⟨atanPartial x N - atanRemainder x N,
    atanPartial x N + atanRemainder x N, by
      have hden : (0 : ℚ) < 2 * N + 3 := by positivity
      have h : 0 ≤ atanRemainder x N :=
        div_nonneg (pow_nonneg (abs_nonneg x) _) hden.le
      linarith⟩

/-- Nested arctangent enclosure obtained by finite intersections. -/
def atanInterval (x : ℚ) : ℕ → RatInterval
  | 0 => atanRaw x 0
  | N + 1 => (atanInterval x N).tighten (atanRaw x (N + 1))

/-- Raw Machin enclosure `16 atan(1/5) - 4 atan(1/239)`. -/
def machinPiRaw (N : ℕ) : RatInterval :=
  ((RatInterval.point 16).mul (atanInterval (1 / 5) N)).sub
    ((RatInterval.point 4).mul (atanInterval (1 / 239) N))

/-- Nested Machin enclosure. -/
def machinPiInterval : ℕ → RatInterval
  | 0 => machinPiRaw 0
  | N + 1 => (machinPiInterval N).tighten (machinPiRaw (N + 1))

/-- Displayed finite Machin cutoff for a positive rational tolerance. -/
def machinPiFuel (ε : PosRat) : ℕ := 5 * ε.1.den + 5

/-- The Machin enclosures of π never widen as the cutoff index grows:
[the enclosure computed at cutoff `N + 1` is contained in the one computed at
cutoff `N`](goal). -/
lemma machinPi_nested (N : ℕ) :
    (machinPiInterval (N + 1)).Subinterval (machinPiInterval N) := by
  simp only [machinPiInterval]
  unfold RatInterval.tighten
  split
  · exact ⟨le_max_left _ _, min_le_left _ _⟩
  · exact RatInterval.subinterval_refl _

/-- Interval evaluation of a rational-coefficient polynomial by primitive
recursion. -/
def intervalPolynomial (coeff : ℕ → ℚ) (I : RatInterval) : ℕ → RatInterval
  | 0 => RatInterval.point (coeff 0)
  | N + 1 => (intervalPolynomial coeff I N).add
      ((RatInterval.point (coeff (N + 1))).mul (I.npow (N + 1)))

/-- The Taylor coefficient of the exponential function at index `j`, namely the
reciprocal of `j` factorial. -/
def expCoeff (j : ℕ) : ℚ := (j.factorial : ℚ)⁻¹

/-- The Taylor coefficient of the sine function at index `j`: zero at every even
index, and at an odd index the alternating sign attached to that term divided by
`j` factorial. -/
def sinCoeff (j : ℕ) : ℚ :=
  if Even j then 0 else
    (if Even ((j - 1) / 2) then 1 else -1) / (j.factorial : ℚ)

/-- The Taylor coefficient of the cosine function at index `j`: zero at every
odd index, and at an even index the alternating sign attached to that term
divided by `j` factorial. -/
def cosCoeff (j : ℕ) : ℚ :=
  if Odd j then 0 else
    (if Even (j / 2) then 1 else -1) / (j.factorial : ℚ)

/-- The displayed Taylor cutoff. -/
def taylorCutoff (I : RatInterval) (precision : ℕ) : ℕ :=
  Int.toNat ⌈2 * I.maxAbs⌉ + precision +
    2 * Int.toNat ⌈I.maxAbs⌉ + 2

/-- A rational bound for the exponential's Taylor remainder past degree `N` over
an interval: the largest endpoint magnitude of the interval raised to the power
`N + 1`, divided by `N + 1` factorial, and scaled by three raised to the ceiling
of that magnitude.

The extra power of three dominates the growth of the exponential over the
interval, so the product is a valid remainder envelope. -/
def expRemainderBound (I : RatInterval) (N : ℕ) : ℚ :=
  3 ^ (Int.toNat ⌈I.maxAbs⌉) * I.maxAbs ^ (N + 1) / ((N + 1).factorial : ℚ)

/-- A rational bound for the sine or cosine Taylor remainder past degree `N` over
an interval: the largest endpoint magnitude of the interval raised to the power
`N + 1`, divided by `N + 1` factorial.

No growth factor is needed here, because every derivative of sine and cosine is
bounded in absolute value by one. -/
def trigRemainderBound (I : RatInterval) (N : ℕ) : ℚ :=
  I.maxAbs ^ (N + 1) / ((N + 1).factorial : ℚ)

/-- Raw enclosure of the exponential over a rational interval at a requested
precision: evaluate the exponential's Taylor polynomial in interval arithmetic up
to the displayed cutoff degree for that interval and precision, then widen the
result on both sides by the matching exponential remainder bound. -/
def expTaylorRaw (I : RatInterval) (precision : ℕ) : RatInterval :=
  let N := taylorCutoff I precision
  let e := expRemainderBound I N
  (intervalPolynomial expCoeff I N).expand e (by
    have hB : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
    exact div_nonneg (mul_nonneg (by positivity) (pow_nonneg hB _)) (by positivity))

/-- Raw enclosure of the sine over a rational interval at a requested precision:
evaluate the sine's Taylor polynomial in interval arithmetic up to the displayed
cutoff degree, then widen the result on both sides by the trigonometric
remainder bound. -/
def sinTaylorRaw (I : RatInterval) (precision : ℕ) : RatInterval :=
  let N := taylorCutoff I precision
  let e := trigRemainderBound I N
  (intervalPolynomial sinCoeff I N).expand e (by
    have hB : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
    exact div_nonneg (pow_nonneg hB _) (by positivity))

/-- Raw enclosure of the cosine over a rational interval at a requested
precision: evaluate the cosine's Taylor polynomial in interval arithmetic up to
the displayed cutoff degree, then widen the result on both sides by the
trigonometric remainder bound. -/
def cosTaylorRaw (I : RatInterval) (precision : ℕ) : RatInterval :=
  let N := taylorCutoff I precision
  let e := trigRemainderBound I N
  (intervalPolynomial cosCoeff I N).expand e (by
    have hB : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
    exact div_nonneg (pow_nonneg hB _) (by positivity))

/-- Fuel-indexed exponential enclosure over a rational interval: at fuel zero it
is the raw Taylor enclosure at precision zero, and each further unit of fuel
intersects the enclosure obtained so far with the raw enclosure computed at the
next precision, so the family can only shrink. -/
def expTaylorInterval (I : RatInterval) : ℕ → RatInterval
  | 0 => expTaylorRaw I 0
  | N + 1 => (expTaylorInterval I N).tighten (expTaylorRaw I (N + 1))

/-- Fuel-indexed sine enclosure over a rational interval: at fuel zero it is the
raw Taylor enclosure at precision zero, and each further unit of fuel intersects
the enclosure obtained so far with the raw enclosure computed at the next
precision. -/
def sinInterval (I : RatInterval) : ℕ → RatInterval
  | 0 => sinTaylorRaw I 0
  | N + 1 => (sinInterval I N).tighten (sinTaylorRaw I (N + 1))

/-- Fuel-indexed cosine enclosure over a rational interval: at fuel zero it is
the raw Taylor enclosure at precision zero, and each further unit of fuel
intersects the enclosure obtained so far with the raw enclosure computed at the
next precision. -/
def cosInterval (I : RatInterval) : ℕ → RatInterval
  | 0 => cosTaylorRaw I 0
  | N + 1 => (cosInterval I N).tighten (cosTaylorRaw I (N + 1))

/-- The finite Taylor cutoff spent on one real transcendental evaluation over a
rational interval at a requested positive tolerance: the displayed cutoff
formula applied to that interval, with the precision taken to be the denominator
of the tolerance. -/
def transcendentalFuel (I : RatInterval) (ε : PosRat) : ℕ :=
  taylorCutoff I ε.1.den

/-- Certified rectangle extension of `exp(x+iy)=exp(x)(cos y+i sin y)`. -/
def cexpInterval (I : ComplexRatInterval) (precision : ℕ) : ComplexRatInterval :=
  cxMul ⟨expTaylorInterval I.re precision, RatInterval.point 0⟩
    ⟨cosInterval I.im precision, sinInterval I.im precision⟩

/-- The finite fuel spent on one complex exponential evaluation over a rational
rectangle at a requested positive tolerance: the larger of the real
transcendental cutoffs computed for the rectangle's real side and for its
imaginary side. -/
def cexpFuel (I : ComplexRatInterval) (ε : PosRat) : ℕ :=
  max (transcendentalFuel I.re ε) (transcendentalFuel I.im ε)

/-- The fuel-indexed exponential enclosures over a fixed rational interval never
widen: [the enclosure at fuel `N + 1` is contained in the enclosure at fuel
`N`](goal). -/
lemma expTaylor_nested (I : RatInterval) (N : ℕ) :
    (expTaylorInterval I (N + 1)).Subinterval (expTaylorInterval I N) := by
  simp only [expTaylorInterval]
  unfold RatInterval.tighten
  split
  · exact ⟨le_max_left _ _, min_le_left _ _⟩
  · exact RatInterval.subinterval_refl _

/-- The fuel-indexed sine enclosures over a fixed rational interval never widen:
[the enclosure at fuel `N + 1` is contained in the enclosure at fuel `N`](goal). -/
lemma sinInterval_nested (I : RatInterval) (N : ℕ) :
    (sinInterval I (N + 1)).Subinterval (sinInterval I N) := by
  simp only [sinInterval]
  unfold RatInterval.tighten
  split
  · exact ⟨le_max_left _ _, min_le_left _ _⟩
  · exact RatInterval.subinterval_refl _

/-- The fuel-indexed cosine enclosures over a fixed rational interval never
widen: [the enclosure at fuel `N + 1` is contained in the enclosure at fuel
`N`](goal). -/
lemma cosInterval_nested (I : RatInterval) (N : ℕ) :
    (cosInterval I (N + 1)).Subinterval (cosInterval I N) := by
  simp only [cosInterval]
  unfold RatInterval.tighten
  split
  · exact ⟨le_max_left _ _, min_le_left _ _⟩
  · exact RatInterval.subinterval_refl _

/-- Pure represented-real input.  Executable code sees no semantic exact real. -/
structure RationalRealApproximants where
  approx : ℕ → RatInterval
  modulus : PosRat → ℕ
  nested : ∀ fuel, (approx (fuel + 1)).Subinterval (approx fuel)
  width_modulus : ∀ ε, (approx (modulus ε)).width ≤ ε.1

/-- A family of rational approximants represents a given real number when every
enclosure it produces, at every fuel level, contains that number.

This is the external semantics of a value-opaque real name: the real number
itself is never part of the executable data. -/
def RationalRealApproximants.Represents
    (name : RationalRealApproximants) (x : ℝ) : Prop :=
  ∀ fuel, (name.approx fuel).Contains x

/-- Pure represented-complex input with a common effective modulus. -/
structure RationalComplexApproximants where
  approx : ℕ → ComplexRatInterval
  modulus : PosRat → ℕ
  nested : ∀ fuel, (approx (fuel + 1)).Subinterval (approx fuel)
  width_modulus : ∀ ε,
    (approx (modulus ε)).re.width ≤ ε.1 ∧
      (approx (modulus ε)).im.width ≤ ε.1

/-- A family of rational rectangle approximants represents a given complex
number when every rectangle it produces, at every fuel level, contains that
number. -/
def RationalComplexApproximants.Represents
    (name : RationalComplexApproximants) (z : ℂ) : Prop :=
  ∀ fuel, (name.approx fuel).Contains z

/-- A value-opaque positive real name.  Positivity is carried by a rational
lower certificate; the represented real remains external to executable data. -/
structure ExecutablePositiveRealName extends RationalRealApproximants where
  positiveLower : ℚ
  positiveLower_pos : 0 < positiveLower

/-- External semantics of a value-opaque positive name. -/
def ExecutablePositiveRealName.RepresentsPositive
    (name : ExecutablePositiveRealName) (x : ℝ) : Prop :=
  name.toRationalRealApproximants.Represents x ∧ (name.positiveLower : ℝ) ≤ x

/-- Finite compositional fuel for one real transcendental call.  The input
tolerance is selected from the bounded input enclosure and requested output
tolerance; it is not a hard-coded fraction of the latter. -/
structure RealTranscendentalSchedule where
  inputTolerance : PosRat
  inputFuel : ℕ
  taylorTolerance : PosRat
  taylorFuel : ℕ

/-- Finite compositional fuel for one complex exponential call. -/
structure ComplexTranscendentalSchedule where
  inputTolerance : PosRat
  inputFuel : ℕ
  taylorTolerance : PosRat
  taylorFuel : ℕ

/-- Coordinatewise finite intersection of complex rectangles. -/
def cxTighten (I J : ComplexRatInterval) : ComplexRatInterval :=
  ⟨I.re.tighten J.re, I.im.tighten J.im⟩

private lemma rat_tighten_subinterval_left (I J : RatInterval) :
    (I.tighten J).Subinterval I := by
  unfold RatInterval.tighten
  split
  · exact ⟨le_max_left _ _, min_le_left _ _⟩
  · exact RatInterval.subinterval_refl _

/-- Intersecting a complex rectangle with another one can only shrink it:
[the coordinatewise intersection of two rectangles is contained in the first
rectangle](goal). -/
lemma cxTighten_subinterval_left (I J : ComplexRatInterval) :
    (cxTighten I J).Subinterval I := by
  exact ⟨rat_tighten_subinterval_left I.re J.re,
    rat_tighten_subinterval_left I.im J.im⟩

/-- Coordinatewise intersection of complex rectangles is sound: whenever a
complex number [lies in the first rectangle](hyp:hI) and [lies in the second
rectangle](hyp:hJ), [it also lies in their intersection](goal). -/
lemma cxTighten_sound {I J : ComplexRatInterval} {z : ℂ}
    (hI : I.Contains z) (hJ : J.Contains z) : (cxTighten I J).Contains z := by
  exact ⟨RatInterval.tighten_sound hI.1 hJ.1,
    RatInterval.tighten_sound hI.2 hJ.2⟩

/-- For one fixed represented input, evaluate the rational program at fuel
`m` and intersect it with every previous output.  Nesting is therefore indexed
by fuel, not inferred from an ordering of requested tolerances. -/
def realOutputSequence (eval : RatInterval → ℕ → RatInterval)
    (name : RationalRealApproximants) : ℕ → RatInterval
  | 0 => eval (name.approx 0) 0
  | fuel + 1 => (realOutputSequence eval name fuel).tighten
      (eval (name.approx (fuel + 1)) (fuel + 1))

/-- Fuel-indexed complex-exponential outputs, recursively intersected with the
previous rectangle. -/
def complexExpOutputSequence (name : RationalComplexApproximants) :
    ℕ → ComplexRatInterval
  | 0 => cexpInterval (name.approx 0) 0
  | fuel + 1 => cxTighten (complexExpOutputSequence name fuel)
      (cexpInterval (name.approx (fuel + 1)) (fuel + 1))

/-- The accumulated outputs of a real evaluation program on a fixed represented
input never widen as fuel grows: [the output enclosure at one more unit of fuel
is contained in the output enclosure at the current fuel](goal). -/
lemma realOutputSequence_nested (eval : RatInterval → ℕ → RatInterval)
    (name : RationalRealApproximants) (fuel : ℕ) :
    (realOutputSequence eval name (fuel + 1)).Subinterval
      (realOutputSequence eval name fuel) := by
  simp only [realOutputSequence]
  exact rat_tighten_subinterval_left _ _

/-- The accumulated complex-exponential output rectangles on a fixed represented
input never widen as fuel grows: [the rectangle at one more unit of fuel is
contained in the rectangle at the current fuel](goal). -/
lemma complexExpOutputSequence_nested (name : RationalComplexApproximants)
    (fuel : ℕ) :
    (complexExpOutputSequence name (fuel + 1)).Subinterval
      (complexExpOutputSequence name fuel) := by
  simp only [complexExpOutputSequence]
  exact cxTighten_subinterval_left _ _

/-- Accumulating intersections preserves soundness for real programs: if [every
raw evaluation of the program, at every fuel level, encloses the target real
number](hyp:hraw), then [every accumulated output enclosure encloses it as
well](goal). -/
lemma realOutputSequence_contains (eval : RatInterval → ℕ → RatInterval)
    (name : RationalRealApproximants) (x : ℝ)
    (hraw : ∀ fuel, (eval (name.approx fuel) fuel).Contains x) :
    ∀ fuel, (realOutputSequence eval name fuel).Contains x := by
  intro fuel
  induction fuel with
  | zero => exact hraw 0
  | succ fuel ih =>
      exact RatInterval.tighten_sound ih (hraw (fuel + 1))

/-- Accumulating intersections preserves soundness for the complex exponential:
if [every raw exponential rectangle, at every fuel level, encloses the target
complex number](hyp:hraw), then [every accumulated output rectangle encloses it
as well](goal). -/
lemma complexExpOutputSequence_contains (name : RationalComplexApproximants)
    (z : ℂ) (hraw : ∀ fuel, (cexpInterval (name.approx fuel) fuel).Contains z) :
    ∀ fuel, (complexExpOutputSequence name fuel).Contains z := by
  intro fuel
  induction fuel with
  | zero => exact hraw 0
  | succ fuel ih => exact cxTighten_sound ih (hraw (fuel + 1))

/-- The fuel at which a real transcendental call is finally read off: the larger
of the schedule's input-refinement fuel and its Taylor fuel. -/
def RealTranscendentalSchedule.outputFuel (schedule : RealTranscendentalSchedule) : ℕ :=
  max schedule.inputFuel schedule.taylorFuel

/-- The fuel at which a complex exponential call is finally read off: the larger
of the schedule's input-refinement fuel and its Taylor fuel. -/
def ComplexTranscendentalSchedule.outputFuel
    (schedule : ComplexTranscendentalSchedule) : ℕ :=
  max schedule.inputFuel schedule.taylorFuel

/-- The rational enclosure a real transcendental program returns under a given
schedule: the accumulated output enclosure on the represented input, read at the
schedule's output fuel. -/
def scheduledRealInterval (eval : RatInterval → ℕ → RatInterval)
    (name : RationalRealApproximants) (schedule : RealTranscendentalSchedule) :
    RatInterval :=
  realOutputSequence eval name schedule.outputFuel

/-- The rational rectangle the complex exponential program returns under a given
schedule: the accumulated output rectangle on the represented input, read at the
schedule's output fuel. -/
def scheduledComplexExpInterval (name : RationalComplexApproximants)
    (schedule : ComplexTranscendentalSchedule) : ComplexRatInterval :=
  complexExpOutputSequence name schedule.outputFuel

/-- Split a requested tolerance into a displayed finite number of positive
pieces using rational arithmetic only. -/
def dividedTolerance (ε : PosRat) (parts : ℕ) : PosRat :=
  ⟨ε.1 / ((max parts 1 : ℕ) : ℚ), div_pos ε.2 (by positivity)⟩

/-- Fixed compositional schedule for real exponential evaluation.  Its input
budget includes a rational Lipschitz envelope computed from the first supplied
input interval; its Taylor budget is a separate quarter of the requested
error. -/
def expScheduleProgram (name : RationalRealApproximants) (ε : PosRat) :
    RealTranscendentalSchedule :=
  let inputParts := 4 * 3 ^ (Int.toNat ⌈(name.approx 0).maxAbs⌉ + 1)
  let inputTolerance := dividedTolerance ε inputParts
  let taylorTolerance := dividedTolerance ε 4
  let inputFuel := name.modulus inputTolerance
  { inputTolerance := inputTolerance
    inputFuel := inputFuel
    taylorTolerance := taylorTolerance
    taylorFuel := taylorCutoff (name.approx inputFuel) taylorTolerance.1.den }

/-- Fixed compositional schedule for sine and cosine evaluation. -/
def trigScheduleProgram (name : RationalRealApproximants) (ε : PosRat) :
    RealTranscendentalSchedule :=
  let inputTolerance := dividedTolerance ε 4
  let taylorTolerance := dividedTolerance ε 4
  let inputFuel := name.modulus inputTolerance
  { inputTolerance := inputTolerance
    inputFuel := inputFuel
    taylorTolerance := taylorTolerance
    taylorFuel := taylorCutoff (name.approx inputFuel) taylorTolerance.1.den }

/-- Fixed compositional schedule for complex exponential evaluation on a
shrinking rectangle name. -/
def cexpScheduleProgram (name : RationalComplexApproximants) (ε : PosRat) :
    ComplexTranscendentalSchedule :=
  let inputParts := 16 * 3 ^ (Int.toNat ⌈(name.approx 0).re.maxAbs⌉ + 1)
  let inputTolerance := dividedTolerance ε inputParts
  let taylorTolerance := dividedTolerance ε 8
  let inputFuel := name.modulus inputTolerance
  { inputTolerance := inputTolerance
    inputFuel := inputFuel
    taylorTolerance := taylorTolerance
    taylorFuel := max
      (taylorCutoff (name.approx inputFuel).re taylorTolerance.1.den)
      (taylorCutoff (name.approx inputFuel).im taylorTolerance.1.den) }

/-- Sound effective convergence of a rational finite-fuel real
transcendental program on shrinking certified inputs. -/
def RealTranscendentalContract (eval : RatInterval → ℕ → RatInterval)
    (semantic : ℝ → ℝ)
    (schedule : RationalRealApproximants → PosRat → RealTranscendentalSchedule) : Prop :=
  ∀ (name : RationalRealApproximants) (x : ℝ), name.Represents x →
    (∀ fuel, (eval (name.approx fuel) fuel).Contains (semantic x)) ∧
    ∀ ε : PosRat,
      let s := schedule name ε
      s.inputFuel = name.modulus s.inputTolerance ∧
      s.taylorFuel = taylorCutoff (name.approx s.inputFuel) s.taylorTolerance.1.den ∧
      (scheduledRealInterval eval name s).Contains (semantic x) ∧
      (scheduledRealInterval eval name s).width ≤ ε.1

/-- Sound effective convergence of the rational finite-fuel complex
exponential program on shrinking certified rectangles. -/
def ComplexExpContract
    (schedule : RationalComplexApproximants → PosRat → ComplexTranscendentalSchedule) :
    Prop :=
  ∀ (name : RationalComplexApproximants) (z : ℂ), name.Represents z →
    (∀ fuel, (cexpInterval (name.approx fuel) fuel).Contains (Complex.exp z)) ∧
    ∀ ε : PosRat,
      let s := schedule name ε
      s.inputFuel = name.modulus s.inputTolerance ∧
      s.taylorFuel = max
        (taylorCutoff (name.approx s.inputFuel).re s.taylorTolerance.1.den)
        (taylorCutoff (name.approx s.inputFuel).im s.taylorTolerance.1.den) ∧
      (scheduledComplexExpInterval name s).Contains (Complex.exp z) ∧
      (scheduledComplexExpInterval name s).re.width ≤ ε.1 ∧
      (scheduledComplexExpInterval name s).im.width ≤ ε.1

/-- Circle fuel composes the radius-name modulus, Machin cutoff, and Taylor
cutoff. -/
structure CircleSchedule where
  radiusTolerance : PosRat
  radiusFuel : ℕ
  piFuel : ℕ
  taylorFuel : ℕ

/-- The fuel at which a circle-node or circle-tangent call is finally read off:
the largest of the schedule's radius fuel, its Machin fuel for π, and its Taylor
fuel. -/
def CircleSchedule.outputFuel (schedule : CircleSchedule) : ℕ :=
  max schedule.radiusFuel (max schedule.piFuel schedule.taylorFuel)

/-- Certified rectangle for the `q`-th of `N` equally spaced points on the
circle of radius given by a positive real name: multiply the radius enclosure,
read at the schedule's radius fuel, by the complex exponential enclosure of the
purely imaginary angle obtained from twice `q` over `N` times the Machin
enclosure of π.

All ingredients are rational intervals, so the whole construction is
executable. -/
def circleNodeFromPositiveName (rName : ExecutablePositiveRealName)
    (N q : ℕ) (schedule : CircleSchedule) : ComplexRatInterval :=
  let scale : ℚ := 2 * q / max N 1
  let angle : ComplexRatInterval :=
    ⟨RatInterval.point 0,
      (RatInterval.point scale).mul (machinPiInterval schedule.piFuel)⟩
  cxMul ⟨rName.approx schedule.radiusFuel, RatInterval.point 0⟩
    (cexpInterval angle schedule.taylorFuel)

/-- Certified rectangle for the tangent (parametric velocity) of the same circle
at its `q`-th of `N` equally spaced points: form the purely imaginary quantity
two times π times the radius, using the Machin enclosure of π and the radius
enclosure at the schedule's radius fuel, and multiply it by the complex
exponential enclosure of the same angle. -/
def circleTangentFromPositiveName (rName : ExecutablePositiveRealName)
    (N q : ℕ) (schedule : CircleSchedule) : ComplexRatInterval :=
  let twoPiR := (RatInterval.point 2).mul
    ((machinPiInterval schedule.piFuel).mul (rName.approx schedule.radiusFuel))
  cxMul ⟨RatInterval.point 0, twoPiR⟩
    (cexpInterval
      ⟨RatInterval.point 0,
        (RatInterval.point (2 * q / max N 1)).mul
          (machinPiInterval schedule.piFuel)⟩
      schedule.taylorFuel)

private def unitTolerance : PosRat := ⟨1, by norm_num⟩

private def circleScheduleAtFuel (fuel : ℕ) : CircleSchedule where
  radiusTolerance := unitTolerance
  radiusFuel := fuel
  piFuel := fuel
  taylorFuel := fuel

/-- Raw circle node at one common finite fuel. -/
def circleNodeAtFuel (rName : ExecutablePositiveRealName) (N q fuel : ℕ) :
    ComplexRatInterval :=
  circleNodeFromPositiveName rName N q (circleScheduleAtFuel fuel)

/-- Raw circle tangent at one common finite fuel. -/
def circleTangentAtFuel (rName : ExecutablePositiveRealName) (N q fuel : ℕ) :
    ComplexRatInterval :=
  circleTangentFromPositiveName rName N q (circleScheduleAtFuel fuel)

/-- Circle nodes for fixed radius data and mesh indices, recursively
intersected by fuel. -/
def circleNodeOutputSequence (rName : ExecutablePositiveRealName) (N q : ℕ) :
    ℕ → ComplexRatInterval
  | 0 => circleNodeAtFuel rName N q 0
  | fuel + 1 => cxTighten (circleNodeOutputSequence rName N q fuel)
      (circleNodeAtFuel rName N q (fuel + 1))

/-- Circle tangents for fixed radius data and mesh indices, recursively
intersected by fuel. -/
def circleTangentOutputSequence (rName : ExecutablePositiveRealName) (N q : ℕ) :
    ℕ → ComplexRatInterval
  | 0 => circleTangentAtFuel rName N q 0
  | fuel + 1 => cxTighten (circleTangentOutputSequence rName N q fuel)
      (circleTangentAtFuel rName N q (fuel + 1))

/-- The accumulated circle-node rectangles for fixed radius data and mesh
indices never widen as fuel grows: [the rectangle at one more unit of fuel is
contained in the rectangle at the current fuel](goal). -/
lemma circleNodeOutputSequence_nested (rName : ExecutablePositiveRealName)
    (N q fuel : ℕ) :
    (circleNodeOutputSequence rName N q (fuel + 1)).Subinterval
      (circleNodeOutputSequence rName N q fuel) := by
  simp only [circleNodeOutputSequence]
  exact cxTighten_subinterval_left _ _

/-- The accumulated circle-tangent rectangles for fixed radius data and mesh
indices never widen as fuel grows: [the rectangle at one more unit of fuel is
contained in the rectangle at the current fuel](goal). -/
lemma circleTangentOutputSequence_nested (rName : ExecutablePositiveRealName)
    (N q fuel : ℕ) :
    (circleTangentOutputSequence rName N q (fuel + 1)).Subinterval
      (circleTangentOutputSequence rName N q fuel) := by
  simp only [circleTangentOutputSequence]
  exact cxTighten_subinterval_left _ _

/-- Accumulating intersections preserves soundness for circle nodes: if [every
raw node rectangle, at every fuel level, contains the target complex
value](hyp:hraw), then [every accumulated node rectangle contains it as
well](goal). -/
lemma circleNodeOutputSequence_contains (rName : ExecutablePositiveRealName)
    (N q : ℕ) (z : ℂ)
    (hraw : ∀ fuel, (circleNodeAtFuel rName N q fuel).Contains z) :
    ∀ fuel, (circleNodeOutputSequence rName N q fuel).Contains z := by
  intro fuel
  induction fuel with
  | zero => exact hraw 0
  | succ fuel ih => exact cxTighten_sound ih (hraw (fuel + 1))

/-- Accumulating intersections preserves soundness for circle tangents: if
[every raw tangent rectangle, at every fuel level, contains the target complex
value](hyp:hraw), then [every accumulated tangent rectangle contains it as
well](goal). -/
lemma circleTangentOutputSequence_contains (rName : ExecutablePositiveRealName)
    (N q : ℕ) (z : ℂ)
    (hraw : ∀ fuel, (circleTangentAtFuel rName N q fuel).Contains z) :
    ∀ fuel, (circleTangentOutputSequence rName N q fuel).Contains z := by
  intro fuel
  induction fuel with
  | zero => exact hraw 0
  | succ fuel ih => exact cxTighten_sound ih (hraw (fuel + 1))

/-- The circle-node rectangle returned under a given schedule: the accumulated
node sequence for that radius name and mesh index, read at the schedule's output
fuel. -/
def scheduledCircleNode (rName : ExecutablePositiveRealName) (N q : ℕ)
    (schedule : CircleSchedule) : ComplexRatInterval :=
  circleNodeOutputSequence rName N q schedule.outputFuel

/-- The circle-tangent rectangle returned under a given schedule: the
accumulated tangent sequence for that radius name and mesh index, read at the
schedule's output fuel. -/
def scheduledCircleTangent (rName : ExecutablePositiveRealName) (N q : ℕ)
    (schedule : CircleSchedule) : ComplexRatInterval :=
  circleTangentOutputSequence rName N q schedule.outputFuel

/-- Fixed finite schedule for a circle node.  Every component is computed from
the requested tolerance, the supplied radius modulus, and the displayed
Machin/Taylor programs. -/
def circleNodeScheduleProgram (rName : ExecutablePositiveRealName)
    (N q : ℕ) (ε : PosRat) : CircleSchedule :=
  let budget := dividedTolerance ε (16 * (max N 1 + 1))
  let radiusFuel := rName.modulus budget
  let piFuel := machinPiFuel budget
  let angle : ComplexRatInterval :=
    ⟨RatInterval.point 0,
      (RatInterval.point (2 * q / max N 1)).mul (machinPiInterval piFuel)⟩
  { radiusTolerance := budget
    radiusFuel := radiusFuel
    piFuel := piFuel
    taylorFuel := cexpFuel angle budget }

/-- Fixed finite schedule for the corresponding circle tangent. -/
def circleTangentScheduleProgram (rName : ExecutablePositiveRealName)
    (N q : ℕ) (ε : PosRat) : CircleSchedule :=
  let budget := dividedTolerance ε (24 * (max N 1 + 1))
  let radiusFuel := rName.modulus budget
  let piFuel := machinPiFuel budget
  let angle : ComplexRatInterval :=
    ⟨RatInterval.point 0,
      (RatInterval.point (2 * q / max N 1)).mul (machinPiInterval piFuel)⟩
  { radiusTolerance := budget
    radiusFuel := radiusFuel
    piFuel := piFuel
    taylorFuel := cexpFuel angle budget }

/-- Complete soundness and effective-modulus contract for positive-radius
circle nodes and tangents. -/
def CircleProgramContract
    (nodeSchedule tangentSchedule :
      ExecutablePositiveRealName → ℕ → ℕ → PosRat → CircleSchedule) : Prop :=
  ∀ (rName : ExecutablePositiveRealName) (r : ℝ),
    rName.RepresentsPositive r → ∀ (N q : ℕ), 1 ≤ N → q < N →
      let nodeValue :=
        (r : ℂ) * Complex.exp (((2 * Real.pi * q / N : ℝ) : ℂ) * Complex.I)
      let tangentValue := (2 * (Real.pi : ℂ) * Complex.I) * r *
        Complex.exp (((2 * Real.pi * q / N : ℝ) : ℂ) * Complex.I)
      (∀ fuel, (circleNodeAtFuel rName N q fuel).Contains nodeValue ∧
        (circleTangentAtFuel rName N q fuel).Contains tangentValue) ∧
      ∀ ε : PosRat,
      let sn := nodeSchedule rName N q ε
      let st := tangentSchedule rName N q ε
      sn.radiusFuel = rName.modulus sn.radiusTolerance ∧
      st.radiusFuel = rName.modulus st.radiusTolerance ∧
      sn.piFuel = machinPiFuel sn.radiusTolerance ∧
      st.piFuel = machinPiFuel st.radiusTolerance ∧
      (scheduledCircleNode rName N q sn).Contains nodeValue ∧
      (scheduledCircleTangent rName N q st).Contains tangentValue ∧
      (scheduledCircleNode rName N q sn).re.width ≤ ε.1 ∧
      (scheduledCircleNode rName N q sn).im.width ≤ ε.1 ∧
      (scheduledCircleTangent rName N q st).re.width ≤ ε.1 ∧
      (scheduledCircleTangent rName N q st).im.width ≤ ε.1

/-- The explicit number of mesh subdivisions used for a Lipschitz constant `L`
and a requested positive tolerance: the ceiling of the constant divided by the
tolerance, plus one.

Adding one makes the count strictly positive and keeps the discretization
contribution, the Lipschitz constant divided by the mesh size, within the
requested tolerance. -/
def explicitMeshFuel (L : ℚ) (ε : PosRat) : ℕ :=
  Int.toNat ⌈L / ε.1⌉ + 1

/-- Legacy contract for the retired callable-table finite-extrema interface.
The canonical bounded-domain adapter exposes its paper-specific contract in
`SelectorSoundness`. -/
def LegacyFiniteExtremaContract : Prop :=
  ∀ (f : ℝ → ℝ) (nodes : ℕ → RatInterval) (L : ℚ) (hL : 0 ≤ L)
      (n : ℕ) (hn : 0 < n),
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |f s - f t| ≤ (L : ℝ) * |s - t|) →
    (∀ k ≤ n, (nodes k).Contains
      (f (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CircleMesh.meshPoint
        n k))) →
    (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CircleMesh.infEnclosure
      nodes L hL n hn).Contains (sInf (f '' Icc (0 : ℝ) 1)) ∧
    (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CircleMesh.supEnclosure
      nodes L hL n hn).Contains (sSup (f '' Icc (0 : ℝ) 1)) ∧
    ∀ (w : ℚ), 0 ≤ w → (∀ k ≤ n, (nodes k).width ≤ w) →
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CircleMesh.infEnclosure
        nodes L hL n hn).width ≤ w + L / n ∧
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CircleMesh.supEnclosure
        nodes L hL n hn).width ≤ w + L / n

/-- The promoted primitive-recursive trapezoidal enclosure, with its exact
Lipschitz soundness and the irreducible uniform node-width contribution. -/
def TrapezoidalEnclosureContract : Prop :=
  ∀ (g : ℝ → ℂ) (nodes : ℕ → ComplexRatInterval) (L : ℚ) (hL : 0 ≤ L)
      (n : ℕ) (hn : 0 < n),
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖g s - g t‖ ≤ (L : ℝ) * |s - t|) →
    (∀ k ≤ n, (nodes k).Contains
      (g (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CircleMesh.meshPoint
        n k))) →
    (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CircleMesh.integralEnclosure
      nodes L hL n hn).Contains (∫ u in (0 : ℝ)..1, g u) ∧
    ∀ (w : ℚ), 0 ≤ w →
      (∀ k ≤ n, (nodes k).re.width ≤ w ∧ (nodes k).im.width ≤ w) →
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CircleMesh.integralEnclosure
        nodes L hL n hn).re.width ≤ w + L / n ∧
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CircleMesh.integralEnclosure
        nodes L hL n hn).im.width ≤ w + L / n

/-- Uniform finite-fuel names for the complex values at every node of every
finite mesh.  The semantic function is supplied only to the external
`RepresentsNodeFunction` relation and is not executable data. -/
structure RationalComplexNodeApproximants where
  approx : ℕ → ℕ → ℕ → ComplexRatInterval
  modulus : PosRat → ℕ
  nested : ∀ mesh k fuel,
    (approx mesh k (fuel + 1)).Subinterval (approx mesh k fuel)
  width_modulus : ∀ ε mesh k,
    (approx mesh k (modulus ε)).re.width ≤ ε.1 ∧
      (approx mesh k (modulus ε)).im.width ≤ ε.1

/-- A family of node approximants represents a complex-valued function on the
unit parameter interval when, for every mesh size, every node index not
exceeding that mesh size, and every fuel level, the rectangle it produces
contains the value of the function at the corresponding mesh point.

The function itself appears only in this external relation and is never part of
the executable data. -/
def RationalComplexNodeApproximants.RepresentsNodeFunction
    (name : RationalComplexNodeApproximants) (g : ℝ → ℂ) : Prop :=
  ∀ mesh k, k ≤ mesh → ∀ fuel,
    (name.approx mesh k fuel).Contains
      (g (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CircleMesh.meshPoint
        mesh k))

/-- The displayed finite resources for node evaluation and mesh aggregation. -/
structure NodeEvaluationSchedule where
  meshFuel : ℕ
  nodeCalls : ℕ
  nodeTolerance : PosRat
  nodeFuel : ℕ
  taylorFuel : ℕ
  sqrtFuel : ℕ
  endpointOperations : ℕ

/-- The actual callable node evaluator: select the requested rational
rectangle from a value-opaque node name using only mesh indices and fuel. -/
def evaluateComplexNode (name : RationalComplexNodeApproximants)
    (schedule : NodeEvaluationSchedule) (k : ℕ) : ComplexRatInterval :=
  name.approx schedule.meshFuel k schedule.nodeFuel

/-- A closed-form finite bisection budget.  It depends only on rational
endpoint data and the requested positive tolerance; no least witness or
unbounded search is used. -/
def sqrtBisectionFuelProgram (input : ComplexRatInterval) (ε : PosRat) : ℕ :=
  let width := (sqrtInitial (cxModulusSq input).hi).hi -
    (sqrtInitial (cxModulusSq input).hi).lo
  Int.natAbs width.num + width.den + ε.1.den + 2

/-- Fixed node/mesh schedule from the displayed operation count and rational
error budget. -/
def nodeEvaluationScheduleProgram (name : RationalComplexNodeApproximants)
    (input : ComplexRatInterval) (L : ℚ) (ε : PosRat) (operations : ℕ) :
    NodeEvaluationSchedule :=
  let nodeTolerance := dividedTolerance ε (max operations 1 + 1)
  { meshFuel := explicitMeshFuel L ε
    nodeCalls := explicitMeshFuel L ε + 1
    nodeTolerance := nodeTolerance
    nodeFuel := name.modulus nodeTolerance
    taylorFuel := cexpFuel input nodeTolerance
    sqrtFuel := sqrtBisectionFuelProgram input nodeTolerance
    endpointOperations := operations }

/-- The exact mesh, node-call, Taylor, square-root, and endpoint-operation fuel
obligations from the bounded-build specification. -/
def NodeEvaluationFuelContract
    (schedule : RationalComplexNodeApproximants → ComplexRatInterval → ℚ →
      PosRat → ℕ → NodeEvaluationSchedule) : Prop :=
  ∀ (name : RationalComplexNodeApproximants) (input : ComplexRatInterval)
      (L : ℚ) (ε : PosRat) (operations : ℕ), 0 ≤ L →
    let s := schedule name input L ε operations
    s.meshFuel = explicitMeshFuel L ε ∧
      0 < s.meshFuel ∧
      s.nodeCalls = s.meshFuel + 1 ∧
      s.nodeFuel = name.modulus s.nodeTolerance ∧
      s.taylorFuel = cexpFuel input s.nodeTolerance ∧
      s.endpointOperations = operations ∧
      s.nodeTolerance.1 * ((max operations 1 : ℕ) : ℚ) ≤ ε.1 ∧
      ((sqrtInitial (cxModulusSq input).hi).hi -
          (sqrtInitial (cxModulusSq input).hi).lo) *
          (1 / 2 : ℚ) ^ s.sqrtFuel ≤ s.nodeTolerance.1

/-- Sound, nested node evaluation at the displayed finite fuel. -/
def NodeEvaluationContract
    (schedule : RationalComplexNodeApproximants → ComplexRatInterval → ℚ →
      PosRat → ℕ → NodeEvaluationSchedule) : Prop :=
  NodeEvaluationFuelContract schedule ∧
    ∀ (name : RationalComplexNodeApproximants) (g : ℝ → ℂ),
      name.RepresentsNodeFunction g →
      ∀ (input : ComplexRatInterval) (L : ℚ) (ε : PosRat) (operations : ℕ),
        0 ≤ L →
        let s := schedule name input L ε operations
        ∀ k ≤ s.meshFuel,
          (evaluateComplexNode name s k).Contains
              (g (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CircleMesh.meshPoint
                s.meshFuel k)) ∧
            (evaluateComplexNode name s k).re.width ≤ s.nodeTolerance.1 ∧
            (evaluateComplexNode name s k).im.width ≤ s.nodeTolerance.1 ∧
            ∀ fuel,
              (name.approx s.meshFuel k (fuel + 1)).Subinterval
                (name.approx s.meshFuel k fuel)

/-! The obsolete fixed callable-table interface formerly ended this file.
The canonical bounded-domain adapter and the conditional build carrier now
live in `BoundedCertifiedComplex`; this file retains only the proved local
Taylor helpers used by older analytic arguments. -/

end CausalSmith.Stat.SaPlmCumulantConverse
