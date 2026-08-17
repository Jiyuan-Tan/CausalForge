import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.API

/-!
# Executable rational complex rectangles

This module extends the promoted real interval layer with exact rational
rectangle operations, guarded complex division, square-root/modulus bounds,
and nested names for complex numbers. Every returned rectangle is computed
from rational endpoints; exact values occur only in containment semantics.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace RatInterval

/-- Squaring a rational interval uses zero as the lower bound exactly when the
interval crosses zero and the larger squared endpoint as the upper bound. -/
def sq (I : RatInterval) : RatInterval :=
  if hneg : I.hi < 0 then
    ⟨I.hi ^ 2, I.lo ^ 2, by nlinarith [I.lo_le_hi]⟩
  else if hpos : 0 < I.lo then
    ⟨I.lo ^ 2, I.hi ^ 2, by nlinarith [I.lo_le_hi]⟩
  else
    ⟨0, max (I.lo ^ 2) (I.hi ^ 2), by positivity⟩

/-- The sign-aware rational square enclosure contains the square of every
real number contained in the input interval. -/
theorem sq_sound {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    I.sq.Contains (x ^ 2) := by
  rcases hx with ⟨hxlo, hxhi⟩
  unfold sq
  split_ifs with hneg hpos
  · have hneg' : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
    constructor <;> simp only [Rat.cast_pow]
    · nlinarith [hxhi]
    · nlinarith [hxlo, hxhi]
  · have hpos' : (0 : ℝ) < I.lo := by exact_mod_cast hpos
    have hhi' : (0 : ℝ) < I.hi := hpos'.trans_le (by exact_mod_cast I.lo_le_hi)
    constructor <;> simp only [Rat.cast_pow]
    · nlinarith [hxlo]
    · nlinarith [hxhi]
  · constructor
    · simpa using sq_nonneg x
    · simp only [Rat.cast_max, Rat.cast_pow]
      by_cases hx0 : x ≤ 0
      · exact le_max_of_le_left (by nlinarith [hxlo])
      · exact le_max_of_le_right (by nlinarith [hxhi])

/-- Squaring is inclusion-isotone for rational intervals. -/
theorem sq_mono {I J : RatInterval} (hIJ : I.Subinterval J) :
    I.sq.Subinterval J.sq := by
  have Ilo : J.Contains (I.lo : ℝ) := by
    constructor
    · exact_mod_cast hIJ.1
    · exact_mod_cast I.lo_le_hi.trans hIJ.2
  have Ihi : J.Contains (I.hi : ℝ) := by
    constructor
    · exact_mod_cast hIJ.1.trans I.lo_le_hi
    · exact_mod_cast hIJ.2
  have hlo := sq_sound Ilo
  have hhi := sq_sound Ihi
  rw [sq]
  split_ifs with Ihneg Ihpos
  · exact ⟨by exact_mod_cast hhi.1, by exact_mod_cast hlo.2⟩
  · exact ⟨by exact_mod_cast hlo.1, by exact_mod_cast hhi.2⟩
  · have hIlo : I.lo ≤ 0 := le_of_not_gt Ihpos
    have hIhi : 0 ≤ I.hi := le_of_not_gt Ihneg
    have hzero : J.Contains (0 : ℝ) := by
      constructor
      · exact_mod_cast hIJ.1.trans hIlo
      · exact_mod_cast hIhi.trans hIJ.2
    have hz := sq_sound hzero
    constructor
    · exact_mod_cast hz.1
    · exact max_le (by exact_mod_cast hlo.2) (by exact_mod_cast hhi.2)

/-- The Newton upper iterate is an executable rational approximation to the
square root of a nonnegative rational. -/
def sqrtUpper (q : ℚ) : ℕ → ℚ
  | 0 => |q| + 1
  | n + 1 =>
      let u := sqrtUpper q n
      (u + q / u) / 2

/-- Dividing a nonnegative rational by its Newton upper iterate gives a
matching executable lower square-root bound. -/
def sqrtLower (q : ℚ) (n : ℕ) : ℚ := q / sqrtUpper q n

private theorem sqrtUpper_invariants (q : ℚ) (hq : 0 ≤ q) (n : ℕ) :
    0 < sqrtUpper q n ∧ q ≤ (sqrtUpper q n) ^ 2 := by
  induction n with
  | zero =>
      rw [sqrtUpper]
      have habs : |q| = q := abs_of_nonneg hq
      rw [habs]
      constructor <;> nlinarith [sq_nonneg q]
  | succ n ih =>
      rw [sqrtUpper]
      have hu : 0 < sqrtUpper q n := ih.1
      have hqu : 0 ≤ q / sqrtUpper q n := div_nonneg hq hu.le
      have hmul : (q / sqrtUpper q n) * sqrtUpper q n = q := div_mul_cancel₀ q hu.ne'
      constructor
      · linarith
      · nlinarith [sq_nonneg (sqrtUpper q n - q / sqrtUpper q n)]

/-- Newton's rational lower and upper iterates enclose the real square root of
a nonnegative rational at every fuel. -/
theorem sqrt_iterates_sound (q : ℚ) (hq : 0 ≤ q) (n : ℕ) :
    (sqrtLower q n : ℝ) ≤ Real.sqrt q ∧ Real.sqrt q ≤ (sqrtUpper q n : ℝ) := by
  obtain ⟨hu, hsq⟩ := sqrtUpper_invariants q hq n
  have hqu : 0 ≤ q / sqrtUpper q n := div_nonneg hq hu.le
  have hmul : (q / sqrtUpper q n) * sqrtUpper q n = q :=
    div_mul_cancel₀ q hu.ne'
  have hl_sq : (q / sqrtUpper q n) ^ 2 ≤ q := by
    nlinarith [sq_nonneg (sqrtUpper q n - q / sqrtUpper q n)]
  constructor
  · apply (Real.le_sqrt (by exact_mod_cast hqu) (by exact_mod_cast hq)).2
    exact_mod_cast hl_sq
  · apply Real.sqrt_le_left (by exact_mod_cast hu.le) |>.2
    exact_mod_cast hsq

private theorem sqrtLower_le_upper (q : ℚ) (hq : 0 ≤ q) (n : ℕ) :
    sqrtLower q n ≤ sqrtUpper q n := by
  obtain ⟨hu, hsq⟩ := sqrtUpper_invariants q hq n
  rw [sqrtLower]
  exact (div_le_iff₀ hu).2 (by simpa [pow_two] using hsq)

private theorem sqrtLower_mono_step (q : ℚ) (hq : 0 ≤ q) (n : ℕ) :
    sqrtLower q n ≤ sqrtLower q (n + 1) := by
  have hu := (sqrtUpper_invariants q hq n).1
  have hlu := sqrtLower_le_upper q hq n
  have hv : 0 < sqrtUpper q (n + 1) := (sqrtUpper_invariants q hq (n + 1)).1
  have hvu : sqrtUpper q (n + 1) ≤ sqrtUpper q n := by
    rw [sqrtUpper]
    rw [show q / sqrtUpper q n = sqrtLower q n by rfl]
    linarith
  exact div_le_div_of_nonneg_left hq hv hvu

/-- The Newton upper-minus-lower gap is bounded by an explicit reciprocal fuel rate. -/
theorem sqrt_gap_rate (q : ℚ) (hq : 0 ≤ q) (n : ℕ) :
    sqrtUpper q n - sqrtLower q n ≤ (q + 1) / (n + 1) := by
  induction n with
  | zero =>
      rw [sqrtUpper, abs_of_nonneg hq]
      have hl : 0 ≤ sqrtLower q 0 :=
        div_nonneg hq (sqrtUpper_invariants q hq 0).1.le
      norm_num
      linarith
  | succ n ih =>
      have hstep : sqrtUpper q (n + 1) - sqrtLower q (n + 1) ≤
          (sqrtUpper q n - sqrtLower q n) / 2 := by
        rw [sqrtUpper]
        rw [show q / sqrtUpper q n = sqrtLower q n by rfl]
        have hm := sqrtLower_mono_step q hq n
        linarith
      have hA : 0 ≤ q + 1 := by linarith
      calc
        sqrtUpper q (n + 1) - sqrtLower q (n + 1) ≤
            (sqrtUpper q n - sqrtLower q n) / 2 := hstep
        _ ≤ ((q + 1) / (n + 1)) / 2 := div_le_div_of_nonneg_right ih (by norm_num)
        _ ≤ (q + 1) / (n + 1 + 1) := by
          rw [div_div]
          apply div_le_div_of_nonneg_left hA (by positivity)
          have hn0 : (0 : ℚ) ≤ n := by positivity
          push_cast
          nlinarith
        _ = (q + 1) / ((n + 1 : ℕ) + 1) := by norm_num [Nat.cast_add]

/-- The gap between the Newton lower and upper square-root bounds converges
effectively to zero. -/
theorem sqrt_iterates_converge (q : ℚ) (hq : 0 ≤ q) (ε : PosRat) :
    ∃ n, sqrtUpper q n - sqrtLower q n ≤ ε.1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((q + 1) / ε.1)
  refine ⟨n, (sqrt_gap_rate q hq n).trans ?_⟩
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < n + 1)).2
  have hn' : q + 1 < ε.1 * n := by
    simpa [mul_comm] using (div_lt_iff₀ ε.2).mp hn
  push_cast
  nlinarith [ε.2]

/-- A nonnegative rational interval is mapped to a rational square-root
interval by applying lower and upper Newton bounds to its endpoints. -/
def sqrtInterval (I : RatInterval) (hI : 0 ≤ I.lo) (fuel : ℕ) : RatInterval :=
  ⟨sqrtLower I.lo fuel, sqrtUpper I.hi fuel, by
    have hhi : 0 ≤ I.hi := hI.trans I.lo_le_hi
    have hlo_sound := sqrt_iterates_sound I.lo hI fuel
    have hhi_sound := sqrt_iterates_sound I.hi hhi fuel
    have hsqrt : Real.sqrt (I.lo : ℝ) ≤ Real.sqrt (I.hi : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast I.lo_le_hi)
    exact_mod_cast hlo_sound.1.trans (hsqrt.trans hhi_sound.2)⟩

/-- The executable square-root interval encloses the square root of every
nonnegative real contained in its input. -/
theorem sqrtInterval_sound {I : RatInterval} (hI : 0 ≤ I.lo) {x : ℝ}
    (hx : I.Contains x) (fuel : ℕ) :
    (sqrtInterval I hI fuel).Contains (Real.sqrt x) := by
  have hhi : 0 ≤ I.hi := hI.trans I.lo_le_hi
  have hlo_sound := sqrt_iterates_sound I.lo hI fuel
  have hhi_sound := sqrt_iterates_sound I.hi hhi fuel
  constructor
  · exact hlo_sound.1.trans (Real.sqrt_le_sqrt hx.1)
  · exact (Real.sqrt_le_sqrt hx.2).trans hhi_sound.2

/-- Square-root interval width is exactly the endpoint Newton gap, exposing
both input-diameter and iteration-error contributions. -/
theorem sqrtInterval_width (I : RatInterval) (hI : 0 ≤ I.lo) (fuel : ℕ) :
    (sqrtInterval I hI fuel).width =
      sqrtUpper I.hi fuel - sqrtLower I.lo fuel := by
  rfl

/-- Containment of one real value together with interval width controls both
endpoint magnitudes. -/
theorem maxAbs_le_of_contains_width {I : RatInterval} {x : ℝ}
    {C w : ℚ} (hx : I.Contains x) (habs : |x| ≤ C) (hw : I.width ≤ w) :
    I.maxAbs ≤ C + w := by
  rw [abs_le] at habs
  rcases hx with ⟨hxlo, hxhi⟩
  rcases habs with ⟨habslo, habshi⟩
  have hw' : (I.hi : ℝ) - I.lo ≤ w := by exact_mod_cast hw
  apply max_le
  · rw [abs_le]
    constructor
    · exact_mod_cast (show (-(C + w) : ℝ) ≤ (I.lo : ℚ) by
        push_cast
        linarith)
    · exact_mod_cast (show (((I.lo : ℚ) : ℝ) ≤ (C + w : ℚ)) by
        push_cast
        linarith)
  · rw [abs_le]
    constructor
    · exact_mod_cast (show (-(C + w) : ℝ) ≤ (I.hi : ℚ) by
        push_cast
        linarith)
    · exact_mod_cast (show (((I.hi : ℚ) : ℝ) ≤ (C + w : ℚ)) by
        push_cast
        linarith)

/-- Negation preserves the maximum endpoint magnitude. -/
theorem maxAbs_neg (I : RatInterval) : I.neg.maxAbs = I.maxAbs := by
  simp [RatInterval.neg, RatInterval.maxAbs, max_comm]

/-- Addition increases endpoint magnitude by at most the sum of operand bounds. -/
theorem maxAbs_add (I J : RatInterval) :
    (I.add J).maxAbs ≤ I.maxAbs + J.maxAbs := by
  apply max_le
  · simpa [RatInterval.add, RatInterval.maxAbs] using
      (abs_add_le I.lo J.lo).trans
        (add_le_add (le_max_left _ _) (le_max_left _ _))
  · simpa [RatInterval.add, RatInterval.maxAbs] using
      (abs_add_le I.hi J.hi).trans
        (add_le_add (le_max_right _ _) (le_max_right _ _))

/-- Subtraction increases endpoint magnitude by at most the sum of operand bounds. -/
theorem maxAbs_sub (I J : RatInterval) :
    (I.sub J).maxAbs ≤ I.maxAbs + J.maxAbs := by
  simpa [RatInterval.sub, maxAbs_neg] using maxAbs_add I J.neg

/-- Interval multiplication has the product of operand endpoint magnitudes as
an executable magnitude bound. -/
theorem maxAbs_mul (I J : RatInterval) :
    (I.mul J).maxAbs ≤ I.maxAbs * J.maxAbs := by
  have hI0 : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
  have hp (x y : ℚ) (hx : |x| ≤ I.maxAbs) (hy : |y| ≤ J.maxAbs) :
      |x * y| ≤ I.maxAbs * J.maxAbs := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg y) hI0
  have ha := hp I.lo J.lo (le_max_left _ _) (le_max_left _ _)
  have hb := hp I.lo J.hi (le_max_left _ _) (le_max_right _ _)
  have hc := hp I.hi J.lo (le_max_right _ _) (le_max_left _ _)
  have hd := hp I.hi J.hi (le_max_right _ _) (le_max_right _ _)
  simp only [RatInterval.maxAbs, RatInterval.mul]
  apply max_le
  · calc
      |min (min (I.lo * J.lo) (I.lo * J.hi))
          (min (I.hi * J.lo) (I.hi * J.hi))| ≤
          max |min (I.lo * J.lo) (I.lo * J.hi)|
            |min (I.hi * J.lo) (I.hi * J.hi)| := abs_min_le_max_abs_abs
      _ ≤ max (max |I.lo * J.lo| |I.lo * J.hi|)
          (max |I.hi * J.lo| |I.hi * J.hi|) :=
        max_le_max abs_min_le_max_abs_abs abs_min_le_max_abs_abs
      _ ≤ I.maxAbs * J.maxAbs := max_le (max_le ha hb) (max_le hc hd)
  · calc
      |max (max (I.lo * J.lo) (I.lo * J.hi))
          (max (I.hi * J.lo) (I.hi * J.hi))| ≤
          max |max (I.lo * J.lo) (I.lo * J.hi)|
            |max (I.hi * J.lo) (I.hi * J.hi)| := abs_max_le_max_abs_abs
      _ ≤ max (max |I.lo * J.lo| |I.lo * J.hi|)
          (max |I.hi * J.lo| |I.hi * J.hi|) :=
        max_le_max abs_max_le_max_abs_abs abs_max_le_max_abs_abs
      _ ≤ I.maxAbs * J.maxAbs := max_le (max_le ha hb) (max_le hc hd)

end RatInterval
