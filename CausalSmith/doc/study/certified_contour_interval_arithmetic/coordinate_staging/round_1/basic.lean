import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact rational interval arithmetic

This module provides closed intervals with rational endpoints and exact endpoint
algorithms for the elementary arithmetic operations.  Each operation is proved
to enclose the corresponding real-number calculation, and the inclusion order
records safe refinement of an enclosure.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- A rational closed interval is a pair of rational endpoints in increasing order. -/
@[ext]
structure RatInterval where
  /-- The rational lower endpoint of the enclosure. -/
  lo : ℚ
  /-- The rational upper endpoint of the enclosure. -/
  hi : ℚ
  /-- The lower endpoint does not exceed the upper endpoint. -/
  lo_le_hi : lo ≤ hi

namespace RatInterval

/-- A real number is contained in a rational interval when it lies between the
real casts of its endpoints. -/
def Contains (I : RatInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- The width of a rational interval is its upper endpoint minus its lower endpoint. -/
def width (I : RatInterval) : ℚ := I.hi - I.lo

/-- The maximum endpoint magnitude is a rational bound for the absolute value
of every real number in the interval. -/
def maxAbs (I : RatInterval) : ℚ := max |I.lo| |I.hi|

/-- Interval inclusion means that every point in the first enclosure also lies in the second. -/
def Subinterval (I J : RatInterval) : Prop :=
  J.lo ≤ I.lo ∧ I.hi ≤ J.hi

/-- A point interval contains exactly one rational value. -/
def point (q : ℚ) : RatInterval := ⟨q, q, le_rfl⟩

/-- The convex hull of two rational intervals is their least endpoint-wise hull. -/
def hull (I J : RatInterval) : RatInterval :=
  ⟨min I.lo J.lo, max I.hi J.hi, by
    exact (min_le_left _ _).trans (I.lo_le_hi.trans (le_max_left _ _))⟩

/-- Addition evaluates all possible sums by adding the two lower and two upper endpoints. -/
def add (I J : RatInterval) : RatInterval :=
  ⟨I.lo + J.lo, I.hi + J.hi, add_le_add I.lo_le_hi J.lo_le_hi⟩

/-- Negation reverses and negates the endpoints. -/
def neg (I : RatInterval) : RatInterval :=
  ⟨-I.hi, -I.lo, neg_le_neg I.lo_le_hi⟩

/-- Subtraction is addition with the negated second interval. -/
def sub (I J : RatInterval) : RatInterval := add I (neg J)

/-- Multiplication takes the minimum and maximum of the four endpoint products. -/
def mul (I J : RatInterval) : RatInterval :=
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  ⟨min (min a b) (min c d), max (max a b) (max c d), by
    exact (min_le_left _ _).trans
      ((min_le_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))⟩

/-- An interval is separated from zero when it lies strictly on one side of zero. -/
def AwayFromZero (I : RatInterval) : Prop := I.hi < 0 ∨ 0 < I.lo

/-- Reciprocal reverses the endpoints of an interval certified away from zero. -/
def inv (I : RatInterval) (hI : I.AwayFromZero) : RatInterval :=
  ⟨I.hi⁻¹, I.lo⁻¹, by
    rcases hI with hI | hI
    · exact (inv_le_inv_of_neg hI (I.lo_le_hi.trans_lt hI)).2 I.lo_le_hi
    · exact (inv_le_inv₀ (hI.trans_le I.lo_le_hi) hI).2 I.lo_le_hi⟩

/-- Division multiplies by the reciprocal of a denominator interval certified away from zero. -/
def div (I J : RatInterval) (hJ : J.AwayFromZero) : RatInterval := mul I (inv J hJ)

/-- Natural powers are evaluated by repeated rational interval multiplication. -/
def npow (I : RatInterval) : ℕ → RatInterval
  | 0 => point 1
  | n + 1 => mul (npow I n) I

/-- Conditional intersection keeps the exact intersection when its rational
endpoints overlap, and otherwise returns the first interval. -/
def tighten (I J : RatInterval) : RatInterval :=
  if h : max I.lo J.lo ≤ min I.hi J.hi then
    ⟨max I.lo J.lo, min I.hi J.hi, h⟩
  else I

/-- Widening by a nonnegative rational amount subtracts it below and adds it above. -/
def expand (I : RatInterval) (e : ℚ) (he : 0 ≤ e) : RatInterval :=
  ⟨I.lo - e, I.hi + e, by linarith [I.lo_le_hi]⟩

/-- Every rational interval has nonnegative width. -/
theorem width_nonneg (I : RatInterval) : 0 ≤ I.width := by
  exact sub_nonneg.mpr I.lo_le_hi

/-- Containment in a point interval is equality with that rational point. -/
@[simp]
theorem contains_point_iff (q : ℚ) (x : ℝ) : (point q).Contains x ↔ x = (q : ℝ) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    exact le_antisymm hhi hlo
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

/-- Subinterval is reflexive. -/
theorem subinterval_refl (I : RatInterval) : I.Subinterval I := by
  exact ⟨le_rfl, le_rfl⟩

/-- Subinterval is transitive. -/
theorem subinterval_trans {I J K : RatInterval} :
    I.Subinterval J → J.Subinterval K → I.Subinterval K := by
  rintro ⟨hlo₁, hhi₁⟩ ⟨hlo₂, hhi₂⟩
  exact ⟨hlo₂.trans hlo₁, hhi₁.trans hhi₂⟩

/-- A real point contained in a subinterval is contained in the enclosing interval. -/
theorem Contains.mono {I J : RatInterval} {x : ℝ}
    (hIJ : I.Subinterval J) (hx : I.Contains x) : J.Contains x := by
  have hlo : (J.lo : ℝ) ≤ I.lo := by exact_mod_cast hIJ.1
  have hhi : (I.hi : ℝ) ≤ J.hi := by exact_mod_cast hIJ.2
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

/-- Inclusion of rational intervals cannot increase their width. -/
theorem width_mono {I J : RatInterval} (hIJ : I.Subinterval J) : I.width ≤ J.width := by
  unfold width
  linarith [hIJ.1, hIJ.2]

/-- The point interval soundly encloses its rational value viewed as a real. -/
theorem point_sound (q : ℚ) : (point q).Contains (q : ℝ) := by
  simp

/-- Rational interval addition encloses the sum of any enclosed real operands. -/
theorem add_sound {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (add I J).Contains (x + y) := by
  constructor <;> simp only [add, Contains, Rat.cast_add]
  · exact add_le_add hx.1 hy.1
  · exact add_le_add hx.2 hy.2

/-- Rational interval negation encloses the negation of every enclosed real operand. -/
theorem neg_sound {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) : I.neg.Contains (-x) := by
  constructor <;> simp only [neg, Contains, Rat.cast_neg]
  · exact neg_le_neg hx.2
  · exact neg_le_neg hx.1

/-- Rational interval subtraction encloses the difference of any enclosed real operands. -/
theorem sub_sound {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (sub I J).Contains (x - y) := by
  simpa [sub_eq_add_neg, sub] using add_sound hx (neg_sound hy)

/-- Rational interval multiplication encloses the product of any enclosed real operands. -/
theorem mul_sound {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (mul I J).Contains (x * y) := by
  rcases hx with ⟨hxl, hxu⟩
  rcases hy with ⟨hyl, hyu⟩
  simp only [mul, Contains, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  constructor
  · by_cases hx0 : 0 ≤ x
    · by_cases hy0 : 0 ≤ y
      · by_cases hIl : 0 ≤ (I.lo : ℝ)
        · refine (min_le_of_left_le (min_le_of_left_le ?_))
          calc
            (I.lo : ℝ) * J.lo ≤ I.lo * y := mul_le_mul_of_nonneg_left hyl hIl
            _ ≤ x * y := mul_le_mul_of_nonneg_right hxl hy0
        · refine (min_le_of_left_le (min_le_of_right_le ?_))
          calc
            (I.lo : ℝ) * J.hi ≤ I.lo * y := mul_le_mul_of_nonpos_left hyu (le_of_not_ge hIl)
            _ ≤ x * y := mul_le_mul_of_nonneg_right hxl hy0
      · have hy0' : y ≤ 0 := le_of_not_ge hy0
        refine (min_le_of_right_le (min_le_of_left_le ?_))
        calc
          (I.hi : ℝ) * J.lo ≤ I.hi * y :=
            mul_le_mul_of_nonneg_left hyl (hx0.trans hxu)
          _ ≤ x * y := mul_le_mul_of_nonpos_right hxu hy0'
    · have hx0' : x ≤ 0 := le_of_not_ge hx0
      by_cases hy0 : 0 ≤ y
      · refine (min_le_of_left_le (min_le_of_right_le ?_))
        calc
          (I.lo : ℝ) * J.hi ≤ x * J.hi :=
            mul_le_mul_of_nonneg_right hxl (hy0.trans hyu)
          _ ≤ x * y := mul_le_mul_of_nonpos_left hyu hx0'
      · have hy0' : y ≤ 0 := le_of_not_ge hy0
        by_cases hIh : (I.hi : ℝ) ≤ 0
        · refine (min_le_of_right_le (min_le_of_right_le ?_))
          calc
            (I.hi : ℝ) * J.hi ≤ I.hi * y := mul_le_mul_of_nonpos_left hyu hIh
            _ ≤ x * y := mul_le_mul_of_nonpos_right hxu hy0'
        · refine (min_le_of_right_le (min_le_of_left_le ?_))
          calc
            (I.hi : ℝ) * J.lo ≤ I.hi * y :=
              mul_le_mul_of_nonneg_left hyl (le_of_not_ge hIh)
            _ ≤ x * y := mul_le_mul_of_nonpos_right hxu hy0'
  · by_cases hx0 : 0 ≤ x
    · by_cases hy0 : 0 ≤ y
      · refine (le_max_of_le_right (le_max_of_le_right ?_))
        calc
          x * y ≤ (I.hi : ℝ) * y := mul_le_mul_of_nonneg_right hxu hy0
          _ ≤ I.hi * J.hi := mul_le_mul_of_nonneg_left hyu (hx0.trans hxu)
      · have hy0' : y ≤ 0 := le_of_not_ge hy0
        by_cases hIl : 0 ≤ (I.lo : ℝ)
        · refine (le_max_of_le_left (le_max_of_le_right ?_))
          calc
            x * y ≤ (I.lo : ℝ) * y := mul_le_mul_of_nonpos_right hxl hy0'
            _ ≤ I.lo * J.hi := mul_le_mul_of_nonneg_left hyu hIl
        · refine (le_max_of_le_left (le_max_of_le_left ?_))
          calc
            x * y ≤ (I.lo : ℝ) * y := mul_le_mul_of_nonpos_right hxl hy0'
            _ ≤ I.lo * J.lo := mul_le_mul_of_nonpos_left hyl (le_of_not_ge hIl)
    · have hx0' : x ≤ 0 := le_of_not_ge hx0
      by_cases hy0 : 0 ≤ y
      · by_cases hJl : 0 ≤ (J.lo : ℝ)
        · refine (le_max_of_le_right (le_max_of_le_left ?_))
          calc
            x * y ≤ x * (J.lo : ℝ) := mul_le_mul_of_nonpos_left hyl hx0'
            _ ≤ I.hi * J.lo := mul_le_mul_of_nonneg_right hxu hJl
        · refine (le_max_of_le_left (le_max_of_le_left ?_))
          calc
            x * y ≤ x * (J.lo : ℝ) := mul_le_mul_of_nonpos_left hyl hx0'
            _ ≤ I.lo * J.lo := mul_le_mul_of_nonpos_right hxl (le_of_not_ge hJl)
      · have hy0' : y ≤ 0 := le_of_not_ge hy0
        refine (le_max_of_le_left (le_max_of_le_left ?_))
        calc
          x * y ≤ (I.lo : ℝ) * y := mul_le_mul_of_nonpos_right hxl hy0'
          _ ≤ I.lo * J.lo := mul_le_mul_of_nonpos_left hyl (hxl.trans hx0')

/-- A real number contained in an interval separated from zero is nonzero. -/
theorem ne_zero_of_contains {I : RatInterval} {x : ℝ}
    (hI : I.AwayFromZero) (hx : I.Contains x) : x ≠ 0 := by
  rcases hI with hI | hI
  · have hI' : (I.hi : ℝ) < 0 := by exact_mod_cast hI
    exact ne_of_lt (hx.2.trans_lt hI')
  · have hI' : (0 : ℝ) < I.lo := by exact_mod_cast hI
    exact ne_of_gt (hI'.trans_le hx.1)

/-- Rational interval reciprocal encloses the reciprocal of every enclosed real operand. -/
theorem inv_sound {I : RatInterval} {x : ℝ} (hI : I.AwayFromZero)
    (hx : I.Contains x) : (inv I hI).Contains x⁻¹ := by
  rcases hI with hneg | hpos
  · have hhineg : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
    have hloneg : (I.lo : ℝ) < 0 := by exact_mod_cast I.lo_le_hi.trans_lt hneg
    have hxneg : x < 0 := hx.2.trans_lt hhineg
    simp only [inv, Contains, Rat.cast_inv]
    exact ⟨(inv_le_inv_of_neg hhineg hxneg).2 hx.2,
      (inv_le_inv_of_neg hxneg hloneg).2 hx.1⟩
  · have hlopos : (0 : ℝ) < I.lo := by exact_mod_cast hpos
    have hhipos : (0 : ℝ) < I.hi := by exact_mod_cast hpos.trans_le I.lo_le_hi
    have hxpos : 0 < x := hlopos.trans_le hx.1
    simp only [inv, Contains, Rat.cast_inv]
    exact ⟨(inv_le_inv₀ hhipos hxpos).2 hx.2,
      (inv_le_inv₀ hxpos hlopos).2 hx.1⟩

/-- Rational interval division encloses every quotient whose denominator interval avoids zero. -/
theorem div_sound {I J : RatInterval} {x y : ℝ} (hJ : J.AwayFromZero)
    (hx : I.Contains x) (hy : J.Contains y) : (div I J hJ).Contains (x / y) := by
  simpa [div, div_eq_mul_inv] using mul_sound hx (inv_sound hJ hy)

/-- Repeated interval multiplication encloses every natural power of an enclosed real number. -/
theorem npow_sound {I : RatInterval} {x : ℝ} (hx : I.Contains x) (n : ℕ) :
    (I.npow n).Contains (x ^ n) := by
  induction n with
  | zero => simpa [npow] using point_sound 1
  | succ n ih => simpa [npow, pow_succ] using mul_sound ih hx

/-- Tightening two intervals that share an enclosed real point returns their
intersection and continues to enclose that point. -/
theorem tighten_sound {I J : RatInterval} {x : ℝ}
    (hI : I.Contains x) (hJ : J.Contains x) :
    (tighten I J).Contains x := by
  have hlohi : max I.lo J.lo ≤ min I.hi J.hi := by
    apply max_le
    · apply le_min I.lo_le_hi
      exact_mod_cast hI.1.trans hJ.2
    · apply le_min
      · exact_mod_cast hJ.1.trans hI.2
      · exact J.lo_le_hi
  simp only [tighten, hlohi, dif_pos, Contains, Rat.cast_max, Rat.cast_min]
  exact ⟨max_le hI.1 hJ.1, le_min hI.2 hJ.2⟩

/-- Tightening by another sound interval produces a subinterval of the first interval. -/
theorem tighten_subinterval_left {I J : RatInterval} {x : ℝ}
    (hI : I.Contains x) (hJ : J.Contains x) :
    (tighten I J).Subinterval I := by
  have hlohi : max I.lo J.lo ≤ min I.hi J.hi := by
    apply max_le
    · apply le_min I.lo_le_hi
      exact_mod_cast hI.1.trans hJ.2
    · apply le_min
      · exact_mod_cast hJ.1.trans hI.2
      · exact J.lo_le_hi
  simp only [tighten, hlohi, dif_pos, Subinterval]
  exact ⟨le_max_left _ _, min_le_left _ _⟩

/-- Addition is inclusion-isotone in both interval arguments. -/
theorem add_mono {I I' J J' : RatInterval}
    (hI : I.Subinterval I') (hJ : J.Subinterval J') :
    (add I J).Subinterval (add I' J') := by
  exact ⟨add_le_add hI.1 hJ.1, add_le_add hI.2 hJ.2⟩

/-- Negation preserves interval inclusion. -/
theorem neg_mono {I J : RatInterval} (hIJ : I.Subinterval J) :
    I.neg.Subinterval J.neg := by
  exact ⟨neg_le_neg hIJ.2, neg_le_neg hIJ.1⟩

/-- Subtraction is inclusion-isotone in both interval arguments. -/
theorem sub_mono {I I' J J' : RatInterval}
    (hI : I.Subinterval I') (hJ : J.Subinterval J') :
    (sub I J).Subinterval (sub I' J') := by
  exact add_mono hI (neg_mono hJ)

/-- Multiplication is inclusion-isotone in both interval arguments. -/
theorem mul_mono {I I' J J' : RatInterval}
    (hI : I.Subinterval I') (hJ : J.Subinterval J') :
    (mul I J).Subinterval (mul I' J') := by
  have Ilo : I.Contains (I.lo : ℝ) :=
    ⟨le_rfl, by exact_mod_cast I.lo_le_hi⟩
  have Ihi : I.Contains (I.hi : ℝ) :=
    ⟨by exact_mod_cast I.lo_le_hi, le_rfl⟩
  have Jlo : J.Contains (J.lo : ℝ) :=
    ⟨le_rfl, by exact_mod_cast J.lo_le_hi⟩
  have Jhi : J.Contains (J.hi : ℝ) :=
    ⟨by exact_mod_cast J.lo_le_hi, le_rfl⟩
  have p₁ : (mul I' J').Contains ((I.lo : ℝ) * (J.lo : ℝ)) :=
    mul_sound (Contains.mono hI Ilo) (Contains.mono hJ Jlo)
  have p₂ : (mul I' J').Contains ((I.lo : ℝ) * (J.hi : ℝ)) :=
    mul_sound (Contains.mono hI Ilo) (Contains.mono hJ Jhi)
  have p₃ : (mul I' J').Contains ((I.hi : ℝ) * (J.lo : ℝ)) :=
    mul_sound (Contains.mono hI Ihi) (Contains.mono hJ Jlo)
  have p₄ : (mul I' J').Contains ((I.hi : ℝ) * (J.hi : ℝ)) :=
    mul_sound (Contains.mono hI Ihi) (Contains.mono hJ Jhi)
  simp only [Subinterval, mul]
  constructor
  · apply le_min
    · apply le_min
      · exact_mod_cast p₁.1
      · exact_mod_cast p₂.1
    · apply le_min
      · exact_mod_cast p₃.1
      · exact_mod_cast p₄.1
  · apply max_le
    · apply max_le
      · exact_mod_cast p₁.2
      · exact_mod_cast p₂.2
    · apply max_le
      · exact_mod_cast p₃.2
      · exact_mod_cast p₄.2

/-- Natural interval powers preserve interval inclusion. -/
theorem npow_mono {I J : RatInterval} (hIJ : I.Subinterval J) (n : ℕ) :
    (I.npow n).Subinterval (J.npow n) := by
  induction n with
  | zero => exact subinterval_refl _
  | succ n ih => exact mul_mono ih hIJ

/-- Reciprocal preserves inclusion when both intervals are certified away from zero. -/
theorem inv_mono {I J : RatInterval} (hIJ : I.Subinterval J)
    (hI : I.AwayFromZero) (hJ : J.AwayFromZero) :
    (inv I hI).Subinterval (inv J hJ) := by
  simp only [Subinterval, inv]
  constructor
  · rcases hJ with hJneg | hJpos
    · exact (inv_le_inv_of_neg hJneg (hIJ.2.trans_lt hJneg)).2 hIJ.2
    · exact (inv_le_inv₀ (hJpos.trans_le J.lo_le_hi)
        ((hJpos.trans_le hIJ.1).trans_le I.lo_le_hi)).2 hIJ.2
  · rcases hJ with hJneg | hJpos
    · exact (inv_le_inv_of_neg
        (I.lo_le_hi.trans_lt (hIJ.2.trans_lt hJneg))
        (J.lo_le_hi.trans_lt hJneg)).2 hIJ.1
    · exact (inv_le_inv₀ (hJpos.trans_le hIJ.1) hJpos).2 hIJ.1

/-- Division is inclusion-isotone when both denominator intervals avoid zero. -/
theorem div_mono {I I' J J' : RatInterval}
    (hI : I.Subinterval I') (hJ : J.Subinterval J')
    (hJ0 : J.AwayFromZero) (hJ0' : J'.AwayFromZero) :
    (div I J hJ0).Subinterval (div I' J' hJ0') := by
  exact mul_mono hI (inv_mono hJ hJ0 hJ0')

/-- Addition makes widths add exactly. -/
theorem width_add (I J : RatInterval) : (add I J).width = I.width + J.width := by
  simp [width, add]
  ring

/-- Negation preserves interval width exactly. -/
theorem width_neg (I : RatInterval) : I.neg.width = I.width := by
  simp [width, neg]
  ring

/-- Subtraction makes widths add exactly. -/
theorem width_sub (I J : RatInterval) : (sub I J).width = I.width + J.width := by
  simp [sub, width_add, width_neg]

/-- Widening an interval by a nonnegative amount on each side increases its width
by twice that amount. -/
theorem width_expand (I : RatInterval) (e : ℚ) (he : 0 ≤ e) :
    (expand I e he).width = I.width + 2 * e := by
  simp [expand, width]
  ring

end RatInterval

end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
