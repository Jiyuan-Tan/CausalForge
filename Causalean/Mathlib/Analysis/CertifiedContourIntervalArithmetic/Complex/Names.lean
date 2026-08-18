import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.Rectangles

/-!
# Certified complex names

This module represents complex values by effectively refining nested rational rectangles and derives certified modulus names from them.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- A certified complex name represents [a complex number](hyp:value) by [a sequence of rational
rectangle enclosures indexed by fuel](hyp:approx) that is [nested — each successive enclosure a
subrectangle of the one before](hyp:nested) — and [always contains the represented
value](hyp:contains), together with [a computable rule selecting, for any requested positive
rational error, a fuel level](hyp:modulus) [whose enclosure meets that coordinate-width
tolerance](hyp:width_modulus). -/
structure CertifiedComplex where
  /-- The unique complex value denoted by the nested name. -/
  value : ℂ
  /-- The rational rectangle returned at each fuel. -/
  approx : ℕ → ComplexRatInterval
  /-- Adjacent fuel values refine by coordinatewise finite intersection. -/
  nested : ∀ n, (approx (n + 1)).Subinterval (approx n)
  /-- Every fuel-indexed rectangle contains the denoted value. -/
  contains : ∀ n, (approx n).Contains value
  /-- The executable fuel selected for a requested positive rational width. -/
  modulus : PosRat → ℕ
  /-- The selected rectangle meets the requested coordinate-width tolerance. -/
  width_modulus : ∀ ε, (approx (modulus ε)).width ≤ ε.1

namespace CertifiedComplex

private theorem approx_mono (z : CertifiedComplex) {m n : ℕ} (hmn : m ≤ n) :
    (z.approx n).Subinterval (z.approx m) := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩
  | succ n hmn ih =>
      exact ⟨RatInterval.subinterval_trans (z.nested n).1 ih.1,
        RatInterval.subinterval_trans (z.nested n).2 ih.2⟩

private theorem rectangle_width_mono {I J : ComplexRatInterval}
    (hIJ : I.Subinterval J) : I.width ≤ J.width := by
  exact max_le_max (RatInterval.width_mono hIJ.1) (RatInterval.width_mono hIJ.2)

/-- A certified complex name refines effectively to a requested rational width. -/
def refine (z : CertifiedComplex) (ε : PosRat) : ComplexRatInterval := z.approx (z.modulus ε)

/-- Effective refinement preserves containment and meets its requested width. -/
theorem refine_spec (z : CertifiedComplex) (ε : PosRat) :
    (z.refine ε).Contains z.value ∧ (z.refine ε).width ≤ ε.1 := by
  exact ⟨z.contains _, z.width_modulus ε⟩

/-- A rational complex point has the constant point rectangle as its certified name. -/
def ofRatPair (x y : ℚ) : CertifiedComplex where
  value := (x : ℝ) + (y : ℝ) * Complex.I
  approx := fun _ => ComplexRatInterval.point x y
  nested := by
    intro n
    exact ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩
  contains := by intro n; exact ComplexRatInterval.point_sound x y
  modulus := fun _ => 0
  width_modulus := by
    intro ε
    simpa [ComplexRatInterval.width, ComplexRatInterval.point,
      RatInterval.width, RatInterval.point] using ε.2.le

/-- Adding certified complex names uses equal-fuel rectangle addition and a
half-tolerance refinement for each operand. -/
def add (z w : CertifiedComplex) : CertifiedComplex where
  value := z.value + w.value
  approx := fun n => (z.approx n).add (w.approx n)
  nested := by
    intro n
    exact ⟨RatInterval.add_mono (z.nested n).1 (w.nested n).1,
      RatInterval.add_mono (z.nested n).2 (w.nested n).2⟩
  contains := by intro n; exact ComplexRatInterval.add_sound (z.contains n) (w.contains n)
  modulus := fun ε =>
    max (z.modulus ⟨ε.1 / 2, div_pos ε.2 (by norm_num)⟩)
      (w.modulus ⟨ε.1 / 2, div_pos ε.2 (by norm_num)⟩)
  width_modulus := by
    intro ε
    let δ : PosRat := ⟨ε.1 / 2, div_pos ε.2 (by norm_num)⟩
    let k := max (z.modulus δ) (w.modulus δ)
    have hz : (z.approx k).width ≤ δ.1 :=
      (rectangle_width_mono (approx_mono z (le_max_left _ _))).trans (z.width_modulus δ)
    have hw : (w.approx k).width ≤ δ.1 :=
      (rectangle_width_mono (approx_mono w (le_max_right _ _))).trans (w.width_modulus δ)
    have hzre : (z.approx k).re.width ≤ δ.1 :=
      (le_max_left _ _).trans hz
    have hzim : (z.approx k).im.width ≤ δ.1 :=
      (le_max_right _ _).trans hz
    have hwre : (w.approx k).re.width ≤ δ.1 :=
      (le_max_left _ _).trans hw
    have hwim : (w.approx k).im.width ≤ δ.1 :=
      (le_max_right _ _).trans hw
    rw [ComplexRatInterval.width_add]
    dsimp [k, δ] at hzre hzim hwre hwim ⊢
    exact max_le (by linarith) (by linarith)

/-- Modulus evaluation on a refining complex name recursively intersects the
current Newton enclosure with every preceding output. -/
def normApprox (z : CertifiedComplex) : ℕ → RatInterval
  | 0 => (z.approx 0).normInterval 0
  | fuel + 1 => (normApprox z fuel).tighten
      ((z.approx (fuel + 1)).normInterval (fuel + 1))

/-- A conservative executable modulus precision includes both input-name
diameter and Newton iteration fuel, including the nondifferentiable origin. -/
def normPrecision (z : CertifiedComplex) (ε : PosRat) : ℕ :=
  let M := (z.approx 0).maxAbs
  let δ : PosRat :=
    ⟨ε.1 ^ 2 / (16 * (M + 1)), by
      have hM : 0 ≤ M := by
        exact le_max_of_le_left ((abs_nonneg _).trans (le_max_left _ _))
      exact div_pos (sq_pos_of_pos ε.2) (by nlinarith)⟩
  max (z.modulus δ) (64 * (ε.1.den + 1) * (M.num.natAbs + 2) ^ 2)

/-- Recursive modulus approximations contain the norm and are adjacent-fuel nested. -/
theorem normApprox_spec (z : CertifiedComplex) (fuel : ℕ) :
    (normApprox z fuel).Contains ‖z.value‖ ∧
      (normApprox z (fuel + 1)).Subinterval (normApprox z fuel) := by
  induction fuel with
  | zero =>
      have h0 := ComplexRatInterval.normInterval_sound (z.contains 0) 0
      have h1 := ComplexRatInterval.normInterval_sound (z.contains 1) 1
      exact ⟨h0, RatInterval.tighten_subinterval_left h0 h1⟩
  | succ fuel ih =>
      have hnew := ComplexRatInterval.normInterval_sound
        (z.contains (fuel + 1)) (fuel + 1)
      have hcur : (normApprox z (fuel + 1)).Contains ‖z.value‖ := by
        rw [normApprox]
        exact RatInterval.tighten_sound ih.1 hnew
      have hnext := ComplexRatInterval.normInterval_sound
        (z.contains (fuel + 2)) (fuel + 2)
      constructor
      · exact hcur
      · rw [show fuel + 1 + 1 = fuel + 2 by omega, normApprox]
        exact RatInterval.tighten_subinterval_left hcur hnext

private theorem tighten_subinterval_right {I J : RatInterval} {x : ℝ}
    (hI : I.Contains x) (hJ : J.Contains x) :
    (I.tighten J).Subinterval J := by
  have hlohi : max I.lo J.lo ≤ min I.hi J.hi := by
    apply max_le
    · apply le_min I.lo_le_hi
      exact_mod_cast hI.1.trans hJ.2
    · apply le_min
      · exact_mod_cast hJ.1.trans hI.2
      · exact J.lo_le_hi
  simp only [RatInterval.tighten, hlohi, dif_pos, RatInterval.Subinterval]
  exact ⟨le_max_right _ _, min_le_right _ _⟩

private theorem normApprox_subinterval_current (z : CertifiedComplex) (fuel : ℕ) :
    (normApprox z fuel).Subinterval ((z.approx fuel).normInterval fuel) := by
  cases fuel with
  | zero => exact RatInterval.subinterval_refl _
  | succ fuel =>
      rw [normApprox]
      exact tighten_subinterval_right (normApprox_spec z fuel).1
        (ComplexRatInterval.normInterval_sound (z.contains (fuel + 1)) (fuel + 1))

/-- For [a certified complex input](hyp:z) and [a requested positive rational tolerance
`ε`](hyp:ε), [evaluating the certified-modulus approximation at the precision level selected
for that tolerance yields an output enclosure whose width is no larger than `ε`](goal). -/
theorem norm_width_at_precision (z : CertifiedComplex) (ε : PosRat) :
    (normApprox z (normPrecision z ε)).width ≤ ε.1 := by
  let M := (z.approx 0).maxAbs
  have hM : 0 ≤ M := by
    exact le_max_of_le_left ((abs_nonneg _).trans (le_max_left _ _))
  let δ : PosRat := ⟨ε.1 ^ 2 / (16 * (M + 1)), by
    exact div_pos (sq_pos_of_pos ε.2) (by nlinarith)⟩
  let N := 64 * (ε.1.den + 1) * (M.num.natAbs + 2) ^ 2
  let k := max (z.modulus δ) N
  change (normApprox z k).width ≤ ε.1
  have hkmod : z.modulus δ ≤ k := le_max_left _ _
  have hkN : N ≤ k := le_max_right _ _
  let K := z.approx k
  let K0 := z.approx 0
  let D := K.normSq
  have hKK0 : K.Subinterval K0 := approx_mono z (Nat.zero_le k)
  have hKw : K.width ≤ δ.1 :=
    (rectangle_width_mono (approx_mono z hkmod)).trans (z.width_modulus δ)
  have hreA : K.re.maxAbs ≤ M :=
    (ComplexRatInterval.rat_maxAbs_mono hKK0.1).trans (le_max_left _ _)
  have himA : K.im.maxAbs ≤ M :=
    (ComplexRatInterval.rat_maxAbs_mono hKK0.2).trans (le_max_right _ _)
  have hrew : K.re.width ≤ δ.1 := (le_max_left _ _).trans hKw
  have himw : K.im.width ≤ δ.1 := (le_max_right _ _).trans hKw
  have hDw : D.width ≤ 4 * M * δ.1 := by
    rw [show D.width = K.re.sq.width + K.im.sq.width by
      simp [D, ComplexRatInterval.normSq, RatInterval.width_add]]
    have hre := ComplexRatInterval.rat_sq_width_le K.re
    have him := ComplexRatInterval.rat_sq_width_le K.im
    have hre0 : 0 ≤ K.re.maxAbs := (abs_nonneg K.re.lo).trans (le_max_left _ _)
    have him0 : 0 ≤ K.im.maxAbs := (abs_nonneg K.im.lo).trans (le_max_left _ _)
    have hδ0 : 0 ≤ δ.1 := δ.2.le
    nlinarith [mul_le_mul hreA hrew (RatInterval.width_nonneg K.re) hM,
      mul_le_mul himA himw (RatInterval.width_nonneg K.im) hM]
  have hDwε : D.width ≤ ε.1 ^ 2 / 4 := by
    refine hDw.trans ?_
    dsimp [δ]
    have hMp : 0 < M + 1 := by linarith
    rw [show 4 * M * (ε.1 ^ 2 / (16 * (M + 1))) =
      (M * ε.1 ^ 2) / (4 * (M + 1)) by
        field_simp [ne_of_gt hMp]
        ring]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 4 * (M + 1))).2
    nlinarith [sq_nonneg ε.1]
  have hDhi : D.hi ≤ 2 * M ^ 2 := by
    change K.re.sq.hi + K.im.sq.hi ≤ 2 * M ^ 2
    have hrehi := ComplexRatInterval.rat_sq_hi_le K.re
    have himhi := ComplexRatInterval.rat_sq_hi_le K.im
    have hre0 : 0 ≤ K.re.maxAbs := (abs_nonneg K.re.lo).trans (le_max_left _ _)
    have him0 : 0 ≤ K.im.maxAbs := (abs_nonneg K.im.lo).trans (le_max_left _ _)
    nlinarith [mul_self_le_mul_self hre0 hreA, mul_self_le_mul_self him0 himA]
  have hMle : M ≤ (M.num.natAbs : ℕ) := by
    have hnum0 : 0 ≤ M.num := Rat.num_nonneg.mpr hM
    calc
      M = (M.num : ℚ) / (M.den : ℕ) := (Rat.num_div_den M).symm
      _ ≤ (M.num : ℚ) := div_le_self (by exact_mod_cast hnum0)
        (by exact_mod_cast Rat.den_pos M)
      _ = (M.num.natAbs : ℕ) := by
        have hi : (M.num.natAbs : ℤ) = M.num := Int.natAbs_of_nonneg hnum0
        exact (congrArg (fun x : ℤ => (x : ℚ)) hi).symm
  have hεden : (1 : ℚ) ≤ ε.1 * (ε.1.den : ℕ) := by
    have hnumpos : 0 < ε.1.num := (Rat.num_pos).2 ε.2
    have hrepr := Rat.num_div_den ε.1
    have hdenpos : (0 : ℚ) < ε.1.den := by exact_mod_cast Rat.den_pos ε.1
    have heq : (ε.1.num : ℚ) = ε.1 * (ε.1.den : ℕ) :=
      (div_eq_iff hdenpos.ne').mp hrepr
    rw [← heq]
    exact_mod_cast hnumpos
  have hrate : (D.hi + 1) / (k + 1) ≤ ε.1 / 4 := by
    have hp0 : (0 : ℚ) ≤ (M.num.natAbs + 2 : ℕ) := by positivity
    have hDcoarse : 4 * (D.hi + 1) ≤ 8 * (M.num.natAbs + 2 : ℕ) ^ 2 := by
      have hp : (M : ℚ) ≤ (M.num.natAbs : ℕ) := hMle
      have hMsq := mul_self_le_mul_self hM hp
      have hMsq' : M ^ 2 ≤ (M.num.natAbs : ℚ) ^ 2 := by
        simpa [pow_two] using hMsq
      calc
        4 * (D.hi + 1) ≤ 4 * (2 * M ^ 2 + 1) := by nlinarith [hDhi]
        _ ≤ 8 * (M.num.natAbs + 2 : ℕ) ^ 2 := by
          push_cast
          nlinarith [hMsq', sq_nonneg (M.num.natAbs : ℚ)]
    have hkcast : (N : ℚ) ≤ k + 1 := by exact_mod_cast hkN.trans (Nat.le_add_right k 1)
    have hεfac : 1 ≤ ε.1 * (ε.1.den + 1 : ℕ) := by
      exact hεden.trans (mul_le_mul_of_nonneg_left (by norm_num) ε.2.le)
    have hNform : (N : ℚ) =
        64 * (ε.1.den + 1 : ℕ) * (M.num.natAbs + 2 : ℕ) ^ 2 := by
      simp [N]
    have hbig : 8 * (M.num.natAbs + 2 : ℕ) ^ 2 ≤ ε.1 * (k + 1) := by
      have hP : (0 : ℚ) ≤ (M.num.natAbs + 2 : ℕ) ^ 2 := by positivity
      have h64 : 64 * (M.num.natAbs + 2 : ℕ) ^ 2 ≤ ε.1 * (N : ℚ) := by
        rw [hNform]
        nlinarith [mul_le_mul_of_nonneg_right hεfac hP]
      nlinarith [mul_le_mul_of_nonneg_left hkcast ε.2.le]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < k + 1)).2
    nlinarith
  have hsqrtspan : (Real.sqrt (D.hi : ℝ) - Real.sqrt (D.lo : ℝ)) ≤ (ε.1 : ℝ) / 2 := by
    have hlo0 : (0 : ℝ) ≤ D.lo := by
      exact_mod_cast ComplexRatInterval.normSq_lo_nonneg K
    have hDcast : (D.lo : ℝ) ≤ D.hi := by exact_mod_cast D.lo_le_hi
    have hhi0 : (0 : ℝ) ≤ D.hi := hlo0.trans hDcast
    have hslo := Real.sq_sqrt hlo0
    have hshi := Real.sq_sqrt hhi0
    have hsord := Real.sqrt_le_sqrt hDcast
    have hw : ((D.hi : ℝ) - D.lo) ≤ (ε.1 : ℝ) ^ 2 / 4 := by exact_mod_cast hDwε
    have hεr : (0 : ℝ) < ε.1 := by exact_mod_cast ε.2
    have hspan0 : 0 ≤ Real.sqrt (D.hi : ℝ) - Real.sqrt (D.lo : ℝ) := sub_nonneg.mpr hsord
    apply (sq_le_sq₀ hspan0 (by positivity : (0 : ℝ) ≤ (ε.1 : ℝ) / 2)).mp
    calc
      (Real.sqrt (D.hi : ℝ) - Real.sqrt (D.lo : ℝ)) ^ 2 ≤
          (D.hi : ℝ) - D.lo := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg (D.lo : ℝ))
          (Real.sqrt_nonneg (D.hi : ℝ))]
      _ ≤ (ε.1 : ℝ) ^ 2 / 4 := hw
      _ = ((ε.1 : ℝ) / 2) ^ 2 := by ring
  have hcurrent : (K.normInterval k).width ≤ ε.1 := by
    rw [ComplexRatInterval.normInterval, RatInterval.sqrtInterval_width]
    have hblo := RatInterval.sqrt_iterates_sound D.lo
      (ComplexRatInterval.normSq_lo_nonneg K) k
    have hbhi := RatInterval.sqrt_iterates_sound D.hi
      ((ComplexRatInterval.normSq_lo_nonneg K).trans D.lo_le_hi) k
    have hrlo := RatInterval.sqrt_gap_rate D.lo
      (ComplexRatInterval.normSq_lo_nonneg K) k
    have hrhi := RatInterval.sqrt_gap_rate D.hi
      ((ComplexRatInterval.normSq_lo_nonneg K).trans D.lo_le_hi) k
    have hrate_lo : (D.lo + 1) / (k + 1) ≤ ε.1 / 4 :=
      (div_le_div_of_nonneg_right (by linarith [D.lo_le_hi]) (by positivity)).trans hrate
    exact_mod_cast (show
      (RatInterval.sqrtUpper D.hi k : ℝ) - RatInterval.sqrtLower D.lo k ≤
        (ε.1 : ℝ) by
      have hrlo' : ((RatInterval.sqrtUpper D.lo k - RatInterval.sqrtLower D.lo k : ℚ) : ℝ) ≤ ε.1 / 4 :=
        by exact_mod_cast hrlo.trans hrate_lo
      have hrhi' : ((RatInterval.sqrtUpper D.hi k - RatInterval.sqrtLower D.hi k : ℚ) : ℝ) ≤ ε.1 / 4 :=
        by exact_mod_cast hrhi.trans hrate
      norm_num at hrlo' hrhi'
      have huhi : (RatInterval.sqrtUpper D.hi k : ℝ) - Real.sqrt D.hi ≤ ε.1 / 4 := by
        linarith [hrhi', hbhi.1]
      have hllo : Real.sqrt D.lo - (RatInterval.sqrtLower D.lo k : ℝ) ≤ ε.1 / 4 := by
        linarith [hrlo', hblo.2]
      linarith [huhi, hllo, hsqrtspan])
  exact (RatInterval.width_mono (normApprox_subinterval_current z k)).trans hcurrent

/-- Complex modulus lifts a refining certified complex name to a certified real name. -/
noncomputable def norm (z : CertifiedComplex) : CertifiedReal where
  value := ‖z.value‖
  approx := normApprox z
  nested := fun fuel => (normApprox_spec z fuel).2
  contains := by intro fuel; exact (normApprox_spec z fuel).1
  modulus := normPrecision z
  width_modulus := norm_width_at_precision z

end CertifiedComplex

end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex
