import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Exponential
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Logarithm

/-!
# Transcendental interval extensions

This module lifts the certified scalar exponential and logarithm constructions
to rational input intervals.  It supplies sound and nested interval extensions
for exponential, positive-domain logarithm, and positive-base real powers.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
namespace Transcendental

/-- Exponential interval evaluation uses monotonicity and scalar endpoint enclosures. -/
private def expIntervalLo (I : RatInterval) (n : ℕ) : ℚ :=
  (expScalar I.lo n).lo

private def expIntervalHi (I : RatInterval) (n : ℕ) : ℚ :=
  (expScalar I.hi n).hi

private theorem expInterval_wellFormed (I : RatInterval) (n : ℕ) :
    expIntervalLo I n ≤ expIntervalHi I n := by
  unfold expIntervalLo expIntervalHi
  have hlo := (expScalar_sound I.lo n).1
  have hhi := (expScalar_sound I.hi n).2
  have hmono : Real.exp (I.lo : ℝ) ≤ Real.exp (I.hi : ℝ) :=
    Real.exp_monotone (by exact_mod_cast I.lo_le_hi)
  exact_mod_cast hlo.trans (hmono.trans hhi)

/-- Exponential interval evaluation encloses the exponential of every real
number contained in its input interval. -/
def expInterval (I : RatInterval) (n : ℕ) : RatInterval :=
  ⟨expIntervalLo I n, expIntervalHi I n, expInterval_wellFormed I n⟩

/-- Positive logarithm interval evaluation uses monotonicity and scalar endpoint enclosures. -/
private theorem logInterval_wellFormed (I : RatInterval) (hI : 0 < I.lo) (n : ℕ) :
    (logScalar I.lo hI n).lo ≤
      (logScalar I.hi (hI.trans_le I.lo_le_hi) n).hi := by
  have hlo := (logScalar_sound I.lo hI n).1
  have hhi := (logScalar_sound I.hi (hI.trans_le I.lo_le_hi) n).2
  have hmono : Real.log (I.lo : ℝ) ≤ Real.log (I.hi : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by show (0 : ℝ) < I.lo; exact_mod_cast hI)
      (by show (0 : ℝ) < I.hi; exact_mod_cast hI.trans_le I.lo_le_hi)
      (by exact_mod_cast I.lo_le_hi)
  exact_mod_cast hlo.trans (hmono.trans hhi)

/-- Positive logarithm interval evaluation encloses the logarithm of every real
number contained in its certified positive input interval. -/
def logInterval (I : RatInterval) (hI : 0 < I.lo) (n : ℕ) : RatInterval :=
  ⟨(logScalar I.lo hI n).lo,
    (logScalar I.hi (hI.trans_le I.lo_le_hi) n).hi,
    logInterval_wellFormed I hI n⟩

/-- Raw real-power evaluation on a strictly positive base composes logarithm,
multiplication, and exponential interval evaluation. -/
def rpowRaw (base exponent : RatInterval) (hbase : 0 < base.lo) (n : ℕ) : RatInterval :=
  expInterval (RatInterval.mul exponent (logInterval base hbase n)) n

/-- Real-power interval evaluation tightens all raw evaluations up to the requested precision. -/
def rpowInterval (base exponent : RatInterval) (hbase : 0 < base.lo) :
    ℕ → RatInterval
  | 0 => rpowRaw base exponent hbase 0
  | n + 1 => RatInterval.tighten (rpowInterval base exponent hbase n)
      (rpowRaw base exponent hbase (n + 1))

private theorem rpowInterval_succ (base exponent : RatInterval) (hbase : 0 < base.lo)
    (n : ℕ) :
    rpowInterval base exponent hbase (n + 1) =
      RatInterval.tighten (rpowInterval base exponent hbase n)
        (rpowRaw base exponent hbase (n + 1)) := rfl

/-- Exponential interval evaluation encloses the exponential of every enclosed real input. -/
theorem expInterval_sound {I : RatInterval} {x : ℝ} (hx : I.Contains x) (n : ℕ) :
    (expInterval I n).Contains (Real.exp x) := by
  constructor
  · exact (expScalar_sound I.lo n).1.trans (Real.exp_monotone hx.1)
  · exact (Real.exp_monotone hx.2).trans (expScalar_sound I.hi n).2

/-- Positive logarithm interval evaluation encloses the logarithm of every enclosed real input. -/
theorem logInterval_sound {I : RatInterval} {x : ℝ} (hI : 0 < I.lo)
    (hx : I.Contains x) (n : ℕ) :
    (logInterval I hI n).Contains (Real.log x) := by
  have hlo : (0 : ℝ) < I.lo := by exact_mod_cast hI
  have hxpos : 0 < x := (by exact_mod_cast hI : (0 : ℝ) < I.lo).trans_le hx.1
  have hhipos : (0 : ℝ) < I.hi := hxpos.trans_le hx.2
  constructor
  · exact (logScalar_sound I.lo hI n).1.trans
      (Real.strictMonoOn_log.monotoneOn hlo hxpos hx.1)
  · exact (Real.strictMonoOn_log.monotoneOn hxpos hhipos hx.2).trans
      (logScalar_sound I.hi (hI.trans_le I.lo_le_hi) n).2

private theorem rpowRaw_sound {base exponent : RatInterval} {x y : ℝ}
    (hbase : 0 < base.lo) (hx : base.Contains x) (hy : exponent.Contains y) (n : ℕ) :
    (rpowRaw base exponent hbase n).Contains (x ^ y) := by
  have hxpos : 0 < x := (by exact_mod_cast hbase : (0 : ℝ) < base.lo).trans_le hx.1
  have hlog := logInterval_sound hbase hx n
  have hmul := RatInterval.mul_sound hy hlog
  have hexp := expInterval_sound hmul n
  simpa [rpowRaw, Real.rpow_def_of_pos hxpos, mul_comm] using hexp

/-- Real-power interval evaluation encloses a positive base raised to an
enclosed real exponent whenever the base interval is strictly positive. -/
theorem rpowInterval_sound {base exponent : RatInterval} {x y : ℝ}
    (hbase : 0 < base.lo) (hx : base.Contains x) (hy : exponent.Contains y) (n : ℕ) :
    (rpowInterval base exponent hbase n).Contains (x ^ y) := by
  induction n with
  | zero => exact rpowRaw_sound hbase hx hy 0
  | succ n ih => exact RatInterval.tighten_sound ih (rpowRaw_sound hbase hx hy (n + 1))

/-- Exponential interval evaluation is nested in its precision argument. -/
theorem expInterval_nested (I : RatInterval) (n : ℕ) :
    (expInterval I (n + 1)).Subinterval (expInterval I n) := by
  change expIntervalLo I n ≤ expIntervalLo I (n + 1) ∧
    expIntervalHi I (n + 1) ≤ expIntervalHi I n
  unfold expIntervalLo expIntervalHi
  exact ⟨(expScalar_nested I.lo n).1, (expScalar_nested I.hi n).2⟩

/-- Positive logarithm interval evaluation is nested in its precision argument. -/
theorem logInterval_nested (I : RatInterval) (hI : 0 < I.lo) (n : ℕ) :
    (logInterval I hI (n + 1)).Subinterval (logInterval I hI n) := by
  change (logScalar I.lo hI n).lo ≤ (logScalar I.lo hI (n + 1)).lo ∧
    (logScalar I.hi (hI.trans_le I.lo_le_hi) (n + 1)).hi ≤
      (logScalar I.hi (hI.trans_le I.lo_le_hi) n).hi
  exact ⟨(logScalar_nested I.lo hI n).1,
    (logScalar_nested I.hi (hI.trans_le I.lo_le_hi) n).2⟩

/-- Real-power interval evaluation is nested in its precision argument. -/
theorem rpowInterval_nested (base exponent : RatInterval) (hbase : 0 < base.lo) (n : ℕ) :
    (rpowInterval base exponent hbase (n + 1)).Subinterval
      (rpowInterval base exponent hbase n) := by
  rw [rpowInterval_succ]
  let x : ℝ := base.lo
  let y : ℝ := exponent.lo
  have hx : base.Contains x :=
    ⟨le_rfl, by dsimp [x]; exact_mod_cast base.lo_le_hi⟩
  have hy : exponent.Contains y :=
    ⟨le_rfl, by dsimp [y]; exact_mod_cast exponent.lo_le_hi⟩
  have h₀ := rpowInterval_sound hbase hx hy n
  have h₁ := rpowRaw_sound hbase hx hy (n + 1)
  exact RatInterval.tighten_subinterval_left h₀ h₁

end Transcendental
end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
