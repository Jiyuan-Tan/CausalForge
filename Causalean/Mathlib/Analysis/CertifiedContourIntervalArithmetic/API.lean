import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Operations
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.FiniteSearch

/-!
# Packaged certified contour interval arithmetic

This module collects exact rational interval arithmetic, certified-real
refinement, transcendental interval extensions, finite mesh enclosures, and
total measurable finite searches into one paper-independent interface.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- This interface packages sound rational interval arithmetic and total
certified-real refinement behind a paper-independent interface. -/
structure CertifiedIntervalArithmetic where
  /-- The packaged outward addition operation. -/
  add : RatInterval → RatInterval → RatInterval
  /-- Packaged addition encloses sums of enclosed real operands. -/
  add_sound : ∀ {I J : RatInterval} {x y : ℝ},
    I.Contains x → J.Contains y → (add I J).Contains (x + y)
  /-- The packaged outward subtraction operation. -/
  sub : RatInterval → RatInterval → RatInterval
  /-- Packaged subtraction encloses differences of enclosed real operands. -/
  sub_sound : ∀ {I J : RatInterval} {x y : ℝ},
    I.Contains x → J.Contains y → (sub I J).Contains (x - y)
  /-- The packaged outward multiplication operation. -/
  mul : RatInterval → RatInterval → RatInterval
  /-- Packaged multiplication encloses products of enclosed real operands. -/
  mul_sound : ∀ {I J : RatInterval} {x y : ℝ},
    I.Contains x → J.Contains y → (mul I J).Contains (x * y)
  /-- The packaged outward division operation requires a denominator interval
  separated from zero. -/
  div : (I J : RatInterval) → J.AwayFromZero → RatInterval
  /-- Packaged division encloses quotients of enclosed operands away from zero. -/
  div_sound : ∀ {I J : RatInterval} {x y : ℝ} (hJ : J.AwayFromZero),
    I.Contains x → J.Contains y → (div I J hJ).Contains (x / y)
  /-- The packaged outward exponential extension at a requested natural precision. -/
  exp : RatInterval → ℕ → RatInterval
  /-- Packaged exponential evaluation encloses exponentials of enclosed reals. -/
  exp_sound : ∀ {I : RatInterval} {x : ℝ},
    I.Contains x → ∀ n, (exp I n).Contains (Real.exp x)
  /-- The packaged outward logarithm extension requires a strictly positive interval. -/
  log : (I : RatInterval) → 0 < I.lo → ℕ → RatInterval
  /-- Packaged logarithm evaluation encloses logarithms on a certified positive interval. -/
  log_sound : ∀ {I : RatInterval} {x : ℝ} (hI : 0 < I.lo),
    I.Contains x → ∀ n, (log I hI n).Contains (Real.log x)
  /-- The packaged real-power extension requires a strictly positive base interval. -/
  rpow : (base exponent : RatInterval) → 0 < base.lo → ℕ → RatInterval
  /-- Packaged real-power evaluation encloses real powers on the positive-base domain. -/
  rpow_sound : ∀ {base exponent : RatInterval} {x y : ℝ}
    (hbase : 0 < base.lo), base.Contains x → exponent.Contains y →
      ∀ n, (rpow base exponent hbase n).Contains (x ^ y)
  /-- The packaged total refinement operation for certified real names. -/
  refine : CertifiedReal → PosRat → RatInterval
  /-- Packaged refinement preserves enclosure of the named real value. -/
  refine_contains : ∀ (x : CertifiedReal) (ε : PosRat),
    (refine x ε).Contains x.value
  /-- Packaged refinement returns no more than the requested rational width. -/
  refine_width : ∀ (x : CertifiedReal) (ε : PosRat),
    (refine x ε).width ≤ ε.1

/-- The concrete certified interval arithmetic implementation uses exact
rational primitives, rational Taylor/atanh enclosures, and stored effective
moduli for certified real refinement. -/
def certifiedIntervalArithmetic : CertifiedIntervalArithmetic where
  add := RatInterval.add
  add_sound := RatInterval.add_sound
  sub := RatInterval.sub
  sub_sound := RatInterval.sub_sound
  mul := RatInterval.mul
  mul_sound := RatInterval.mul_sound
  div := RatInterval.div
  div_sound := RatInterval.div_sound
  exp := Transcendental.expInterval
  exp_sound := by
    intro I x hx n
    exact Transcendental.expInterval_sound hx n
  log := Transcendental.logInterval
  log_sound := by
    intro I x hI hx n
    exact Transcendental.logInterval_sound hI hx n
  rpow := Transcendental.rpowInterval
  rpow_sound := by
    intro base exponent x y hbase hx hy n
    exact Transcendental.rpowInterval_sound hbase hx hy n
  refine := CertifiedReal.refine
  refine_contains := CertifiedReal.refine_contains
  refine_width := CertifiedReal.refine_width

end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
