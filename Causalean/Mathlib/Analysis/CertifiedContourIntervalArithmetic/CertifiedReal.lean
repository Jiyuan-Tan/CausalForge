import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Basic
import Mathlib.Data.Real.Archimedean

/-!
# Certified real names and effective refinement

This module represents a real quantity by nested rational enclosures together
with a computable precision rule.  It turns any positive rational error target
into a concrete interval that still contains the quantity and is no wider than
that target.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- A positive rational is a rational number bundled with a proof that it is strictly positive. -/
abbrev PosRat := {q : ℚ // 0 < q}

/-- A certified real name represents [a real number](hyp:value) by [a sequence of rational
interval enclosures indexed by precision](hyp:approx) that is [nested — each successive enclosure
a subinterval of the one before](hyp:nested) — and [always contains the represented
value](hyp:contains), together with [a computable rule selecting, for any requested positive
rational error, a precision level](hyp:modulus) [whose enclosure is no wider than that
error](hyp:width_modulus). -/
structure CertifiedReal where
  /-- The real number denoted by the certified name. -/
  value : ℝ
  /-- The rational enclosure returned at each natural precision. -/
  approx : ℕ → RatInterval
  /-- Increasing precision produces a subinterval of the preceding enclosure. -/
  nested : ∀ n, (approx (n + 1)).Subinterval (approx n)
  /-- Every rational approximation encloses the denoted real value. -/
  contains : ∀ n, (approx n).Contains value
  /-- The computable precision selected for a requested positive rational width. -/
  modulus : PosRat → ℕ
  /-- The interval at the selected precision has at most the requested width. -/
  width_modulus : ∀ ε : PosRat, (approx (modulus ε)).width ≤ ε.1

namespace CertifiedReal

/-- Nestedness extends from successive precisions to every pair of ordered precisions. -/
theorem approx_mono (x : CertifiedReal) {m n : ℕ} (hmn : m ≤ n) :
    (x.approx n).Subinterval (x.approx m) := by
  induction n, hmn using Nat.le_induction with
  | base => exact RatInterval.subinterval_refl _
  | succ n hmn ih =>
      exact RatInterval.subinterval_trans (x.nested n) ih

/-- Refinement evaluates the certified modulus and returns its rational enclosure. -/
def refine (x : CertifiedReal) (ε : PosRat) : RatInterval :=
  x.approx (x.modulus ε)

/-- Refinement always encloses the real value named by the certificate. -/
theorem refine_contains (x : CertifiedReal) (ε : PosRat) :
    (x.refine ε).Contains x.value := by
  exact x.contains (x.modulus ε)

/-- For [a certified real number `x`](hyp:x) and [a requested positive rational tolerance
`ε`](hyp:ε), [refining `x` to the precision selected by `ε`'s modulus yields an enclosure
whose width is at most `ε`](goal). -/
theorem refine_width (x : CertifiedReal) (ε : PosRat) :
    (x.refine ε).width ≤ ε.1 := by
  exact x.width_modulus ε

/-- Every positive rational tolerance admits an explicitly returned enclosing
interval of at most that width. -/
theorem exists_refinement (x : CertifiedReal) (ε : ℚ) (hε : 0 < ε) :
    ∃ n : ℕ, (x.approx n).Contains x.value ∧ (x.approx n).width ≤ ε := by
  exact ⟨x.modulus ⟨ε, hε⟩, x.contains _, x.width_modulus ⟨ε, hε⟩⟩

/-- A rational number has the constant point interval as a certified real name. -/
def ofRat (q : ℚ) : CertifiedReal where
  value := q
  approx := fun _ => RatInterval.point q
  nested := by
    intro n
    exact RatInterval.subinterval_refl _
  contains := by
    intro n
    exact RatInterval.point_sound q
  modulus := fun _ => 0
  width_modulus := by
    intro ε
    simpa [RatInterval.width, RatInterval.point] using ε.2.le

/-- Negating a certified name negates every rational enclosure and preserves its modulus. -/
def neg (x : CertifiedReal) : CertifiedReal where
  value := -x.value
  approx := fun n => (x.approx n).neg
  nested := by
    intro n
    exact RatInterval.neg_mono (x.nested n)
  contains := by
    intro n
    exact RatInterval.neg_sound (x.contains n)
  modulus := x.modulus
  width_modulus := by
    intro ε
    simpa [RatInterval.width_neg] using x.width_modulus ε

/-- Adding certified names adds equal-precision interval enclosures and uses
half of the requested tolerance for each input. -/
def add (x y : CertifiedReal) : CertifiedReal where
  value := x.value + y.value
  approx := fun n => RatInterval.add (x.approx n) (y.approx n)
  nested := by
    intro n
    exact RatInterval.add_mono (x.nested n) (y.nested n)
  contains := by
    intro n
    exact RatInterval.add_sound (x.contains n) (y.contains n)
  modulus := fun ε =>
    max (x.modulus ⟨ε.1 / 2, div_pos ε.2 (by decide)⟩)
      (y.modulus ⟨ε.1 / 2, div_pos ε.2 (by decide)⟩)
  width_modulus := by
    intro ε
    let δ : PosRat := ⟨ε.1 / 2, div_pos ε.2 (by norm_num)⟩
    have hx : (x.approx (max (x.modulus δ) (y.modulus δ))).width ≤ δ.1 :=
      (RatInterval.width_mono (x.approx_mono (le_max_left _ _))).trans
        (x.width_modulus δ)
    have hy : (y.approx (max (x.modulus δ) (y.modulus δ))).width ≤ δ.1 :=
      (RatInterval.width_mono (y.approx_mono (le_max_right _ _))).trans
        (y.width_modulus δ)
    rw [RatInterval.width_add]
    dsimp [δ] at hx hy ⊢
    linarith

/-- Subtracting certified names adds the first enclosure to the negation of the second. -/
def sub (x y : CertifiedReal) : CertifiedReal := add x (neg y)

/-- Certified subtraction denotes the difference of the two named real values. -/
@[simp]
theorem sub_value (x y : CertifiedReal) : (sub x y).value = x.value - y.value := by
  rfl

/-- Two certified names whose every approximation is shared denote the same real value. -/
theorem value_eq_of_common_approximations (x y : CertifiedReal)
    (hxy : ∀ n, x.approx n = y.approx n) : x.value = y.value := by
  apply le_antisymm
  · by_contra h
    have hlt : y.value < x.value := lt_of_not_ge h
    obtain ⟨ε, hεpos, hεlt⟩ : ∃ ε : ℚ, 0 < ε ∧ (ε : ℝ) < x.value - y.value := by
      exact exists_pos_rat_lt (sub_pos.mpr hlt)
    let n := x.modulus ⟨ε, hεpos⟩
    have hx := x.contains n
    have hy : (x.approx n).Contains y.value := by simpa [hxy n] using y.contains n
    have hw : ((x.approx n).width : ℝ) ≤ ε := by
      exact_mod_cast x.width_modulus ⟨ε, hεpos⟩
    have hspan : x.value - y.value ≤ ((x.approx n).width : ℝ) := by
      simp only [RatInterval.width, Rat.cast_sub]
      linarith [hx.2, hy.1]
    exact (not_lt_of_ge (hspan.trans hw)) hεlt
  · by_contra h
    have hlt : x.value < y.value := lt_of_not_ge h
    obtain ⟨ε, hεpos, hεlt⟩ : ∃ ε : ℚ, 0 < ε ∧ (ε : ℝ) < y.value - x.value := by
      exact exists_pos_rat_lt (sub_pos.mpr hlt)
    let n := x.modulus ⟨ε, hεpos⟩
    have hx := x.contains n
    have hy : (x.approx n).Contains y.value := by simpa [hxy n] using y.contains n
    have hw : ((x.approx n).width : ℝ) ≤ ε := by
      exact_mod_cast x.width_modulus ⟨ε, hεpos⟩
    have hspan : y.value - x.value ≤ ((x.approx n).width : ℝ) := by
      simp only [RatInterval.width, Rat.cast_sub]
      linarith [hy.2, hx.1]
    exact (not_lt_of_ge (hspan.trans hw)) hεlt

end CertifiedReal

end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

