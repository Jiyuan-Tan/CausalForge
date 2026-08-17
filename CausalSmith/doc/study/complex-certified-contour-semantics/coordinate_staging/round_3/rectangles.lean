import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.Basic

/-!
# Rational complex rectangle operations

This module equips rational complex rectangles with sound arithmetic, guarded division, modulus bounds, and explicit width propagation.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace ComplexRatInterval

/-- The width of a complex rectangle is the larger of its two coordinate widths. -/
def width (I : ComplexRatInterval) : ℚ := max I.re.width I.im.width

/-- The maximum coordinate endpoint magnitude controls arithmetic error amplification. -/
def maxAbs (I : ComplexRatInterval) : ℚ := max I.re.maxAbs I.im.maxAbs

/-- A rational pair determines a point rectangle in the complex plane. -/
def point (x y : ℚ) : ComplexRatInterval :=
  ⟨RatInterval.point x, RatInterval.point y⟩

/-- Complex rectangle negation reverses both coordinate intervals. -/
def neg (I : ComplexRatInterval) : ComplexRatInterval := ⟨I.re.neg, I.im.neg⟩

/-- Complex rectangle subtraction adds the coordinatewise negation. -/
def sub (I J : ComplexRatInterval) : ComplexRatInterval := I.add J.neg

/-- Complex rectangle multiplication evaluates the Cartesian formula with
outward rational real interval operations. -/
def mul (I J : ComplexRatInterval) : ComplexRatInterval :=
  ⟨(I.re.mul J.re).sub (I.im.mul J.im),
    (I.re.mul J.im).add (I.im.mul J.re)⟩

/-- Complex conjugation negates only the imaginary coordinate interval. -/
def conj (I : ComplexRatInterval) : ComplexRatInterval := ⟨I.re, I.im.neg⟩

/-- The squared-modulus interval sums the sign-aware squares of both coordinates. -/
def normSq (I : ComplexRatInterval) : RatInterval := I.re.sq.add I.im.sq

/-- Guarded complex division multiplies by the conjugate and divides both
resulting coordinates by the denominator squared-modulus interval. -/
def div (I J : ComplexRatInterval) (hJ : J.normSq.AwayFromZero) : ComplexRatInterval :=
  let numerator := I.mul J.conj
  ⟨numerator.re.div J.normSq hJ, numerator.im.div J.normSq hJ⟩

/-- Coordinatewise conditional intersection makes a rectangle no larger while
retaining a common enclosed complex value. -/
def tighten (I J : ComplexRatInterval) : ComplexRatInterval :=
  ⟨I.re.tighten J.re, I.im.tighten J.im⟩

/-- The rational point rectangle contains the corresponding complex number. -/
theorem point_sound (x y : ℚ) :
    (point x y).Contains ((x : ℝ) + (y : ℝ) * Complex.I) := by
  constructor
  · simpa [point] using RatInterval.point_sound x
  · simpa [point] using RatInterval.point_sound y

/-- Semantic coordinate bounds and rectangle width give an executable maximum
endpoint-magnitude bound. -/
theorem maxAbs_le_of_contains_width {I : ComplexRatInterval} {z : ℂ}
    {C w : ℚ} (hz : I.Contains z)
    (hzabs : max |z.re| |z.im| ≤ (C : ℝ)) (hw : I.width ≤ w) :
    I.maxAbs ≤ C + w := by
  apply max_le
  · exact RatInterval.maxAbs_le_of_contains_width hz.1
      ((le_max_left _ _).trans hzabs)
      ((le_max_left I.re.width I.im.width).trans hw)
  · exact RatInterval.maxAbs_le_of_contains_width hz.2
      ((le_max_right _ _).trans hzabs)
      ((le_max_right I.re.width I.im.width).trans hw)

/-- Complex rectangle negation encloses negated complex values. -/
theorem neg_sound {I : ComplexRatInterval} {z : ℂ} (hz : I.Contains z) :
    I.neg.Contains (-z) := by
  exact ⟨by simpa [neg] using RatInterval.neg_sound hz.1,
    by simpa [neg] using RatInterval.neg_sound hz.2⟩

/-- Complex rectangle subtraction encloses differences of enclosed values. -/
theorem sub_sound {I J : ComplexRatInterval} {z w : ℂ}
    (hz : I.Contains z) (hw : J.Contains w) : (I.sub J).Contains (z - w) := by
  simpa [sub, sub_eq_add_neg] using add_sound hz (neg_sound hw)

/-- Complex rectangle multiplication encloses products of enclosed values. -/
theorem mul_sound {I J : ComplexRatInterval} {z w : ℂ}
    (hz : I.Contains z) (hw : J.Contains w) : (I.mul J).Contains (z * w) := by
  constructor
  · simpa [mul, Complex.mul_re] using
      RatInterval.sub_sound (RatInterval.mul_sound hz.1 hw.1)
        (RatInterval.mul_sound hz.2 hw.2)
  · simpa [mul, Complex.mul_im] using
      RatInterval.add_sound (RatInterval.mul_sound hz.1 hw.2)
        (RatInterval.mul_sound hz.2 hw.1)

/-- The squared-modulus interval contains the squared complex norm. -/
theorem normSq_sound {I : ComplexRatInterval} {z : ℂ} (hz : I.Contains z) :
    I.normSq.Contains (‖z‖ ^ 2) := by
  rw [Complex.sq_norm]
  simpa [normSq, Complex.normSq_apply, pow_two] using
    RatInterval.add_sound (RatInterval.sq_sound hz.1) (RatInterval.sq_sound hz.2)

/-- Guarded complex rectangle division encloses the quotient of enclosed
values and certifies semantically that the denominator is nonzero. -/
theorem div_sound {I J : ComplexRatInterval} {z w : ℂ}
    (hJ : J.normSq.AwayFromZero) (hz : I.Contains z) (hw : J.Contains w) :
    (I.div J hJ).Contains (z / w) := by
  have hconj : J.conj.Contains (starRingEnd ℂ w) := by
    exact ⟨by simpa [conj] using hw.1,
      by simpa [conj] using RatInterval.neg_sound hw.2⟩
  have hnum : (I.mul J.conj).Contains (z * starRingEnd ℂ w) := mul_sound hz hconj
  have hden := normSq_sound hw
  rw [Complex.sq_norm] at hden
  constructor
  · simpa [div, Complex.div_re, Complex.normSq_apply, div_eq_mul_inv,
      mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using
        RatInterval.div_sound hJ hnum.1 hden
  · simpa [div, Complex.div_im, Complex.normSq_apply, div_eq_mul_inv,
      mul_add, sub_eq_add_neg, add_mul, mul_comm, mul_left_comm, mul_assoc] using
        RatInterval.div_sound hJ hnum.2 hden

/-- Conjugation preserves rectangle width. -/
theorem width_conj (I : ComplexRatInterval) : I.conj.width = I.width := by
  simp [width, conj, RatInterval.width_neg]

/-- Conjugation preserves the maximum coordinate endpoint magnitude. -/
theorem maxAbs_conj (I : ComplexRatInterval) : I.conj.maxAbs = I.maxAbs := by
  simp [maxAbs, conj, RatInterval.maxAbs_neg]

/-- Tightening two rectangles containing a common value preserves that value
and produces a subrectangle of the first argument. -/
theorem tighten_sound_left {I J : ComplexRatInterval} {z : ℂ}
    (hI : I.Contains z) (hJ : J.Contains z) :
    (I.tighten J).Contains z ∧ (I.tighten J).Subinterval I := by
  exact ⟨⟨RatInterval.tighten_sound hI.1 hJ.1,
      RatInterval.tighten_sound hI.2 hJ.2⟩,
    ⟨RatInterval.tighten_subinterval_left hI.1 hJ.1,
      RatInterval.tighten_subinterval_left hI.2 hJ.2⟩⟩

/-- Complex rectangle addition has exactly the maximum of the two summed
coordinate widths. -/
theorem width_add (I J : ComplexRatInterval) :
    (I.add J).width = max (I.re.width + J.re.width) (I.im.width + J.im.width) := by
  simp [width, add, RatInterval.width_add]

/-- Complex rectangle multiplication has twice the product of operand
coordinate magnitude bounds as an executable magnitude bound. -/
theorem mul_maxAbs (I J : ComplexRatInterval) :
    (I.mul J).maxAbs ≤ 2 * I.maxAbs * J.maxAbs := by
  have hIre : I.re.maxAbs ≤ I.maxAbs := le_max_left _ _
  have hIim : I.im.maxAbs ≤ I.maxAbs := le_max_right _ _
  have hJre : J.re.maxAbs ≤ J.maxAbs := le_max_left _ _
  have hJim : J.im.maxAbs ≤ J.maxAbs := le_max_right _ _
  have hI0 : 0 ≤ I.maxAbs := (abs_nonneg I.re.lo).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hJ0 : 0 ≤ J.maxAbs := (abs_nonneg J.re.lo).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hrr := RatInterval.maxAbs_mul I.re J.re
  have hii := RatInterval.maxAbs_mul I.im J.im
  have hri := RatInterval.maxAbs_mul I.re J.im
  have hir := RatInterval.maxAbs_mul I.im J.re
  have hrr' : (I.re.mul J.re).maxAbs ≤ I.maxAbs * J.maxAbs :=
    hrr.trans (mul_le_mul hIre hJre
      ((abs_nonneg J.re.lo).trans (le_max_left _ _)) hI0)
  have hii' : (I.im.mul J.im).maxAbs ≤ I.maxAbs * J.maxAbs :=
    hii.trans (mul_le_mul hIim hJim
      ((abs_nonneg J.im.lo).trans (le_max_left _ _)) hI0)
  have hri' : (I.re.mul J.im).maxAbs ≤ I.maxAbs * J.maxAbs :=
    hri.trans (mul_le_mul hIre hJim
      ((abs_nonneg J.im.lo).trans (le_max_left _ _)) hI0)
  have hir' : (I.im.mul J.re).maxAbs ≤ I.maxAbs * J.maxAbs :=
    hir.trans (mul_le_mul hIim hJre
      ((abs_nonneg J.re.lo).trans (le_max_left _ _)) hI0)
  apply max_le
  · exact (RatInterval.maxAbs_sub _ _).trans (by linarith)
  · exact (RatInterval.maxAbs_add _ _).trans (by linarith)

private theorem interval_product_difference {I J : RatInterval}
    {x x' y y' : ℚ} (hx : I.lo ≤ x ∧ x ≤ I.hi)
    (hx' : I.lo ≤ x' ∧ x' ≤ I.hi) (hy : J.lo ≤ y ∧ y ≤ J.hi)
    (hy' : J.lo ≤ y' ∧ y' ≤ J.hi) :
    |x * y - x' * y'| ≤ I.maxAbs * J.width + J.maxAbs * I.width := by
  have hax : |x| ≤ I.maxAbs := abs_le_max_abs_abs hx.1 hx.2
  have hay' : |y'| ≤ J.maxAbs := abs_le_max_abs_abs hy'.1 hy'.2
  have hdx : |x - x'| ≤ I.width := by
    simpa [RatInterval.width] using
      (abs_sub_le_of_le_of_le hx.1 hx.2 hx'.1 hx'.2)
  have hdy : |y - y'| ≤ J.width := by
    simpa [RatInterval.width] using
      (abs_sub_le_of_le_of_le hy.1 hy.2 hy'.1 hy'.2)
  calc
    |x * y - x' * y'| = |x * (y - y') + (x - x') * y'| := by ring_nf
    _ ≤ |x| * |y - y'| + |x - x'| * |y'| := by
      simpa [abs_mul] using abs_add_le (x * (y - y')) ((x - x') * y')
    _ ≤ I.maxAbs * J.width + J.maxAbs * I.width := by
      have hI0 : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
      have hJ0 : 0 ≤ J.maxAbs := (abs_nonneg J.lo).trans (le_max_left _ _)
      have hwI : 0 ≤ I.width := RatInterval.width_nonneg I
      have hwJ : 0 ≤ J.width := RatInterval.width_nonneg J
      nlinarith [mul_le_mul hax hdy (abs_nonneg (y - y')) hI0,
        mul_le_mul hdx hay' (abs_nonneg y') hwI]

private theorem interval_mul_width_le (I J : RatInterval) :
    (I.mul J).width ≤ I.maxAbs * J.width + J.maxAbs * I.width := by
  let R := I.maxAbs * J.width + J.maxAbs * I.width
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  have hprod : ∀ u ∈ [a, b, c, d], ∀ v ∈ [a, b, c, d], |u - v| ≤ R := by
    intro u hu v hv
    simp at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl <;>
      apply interval_product_difference <;>
      simp [a, b, c, d, I.lo_le_hi, J.lo_le_hi]
  have haa := hprod a (by simp) a (by simp)
  have hab := hprod a (by simp) b (by simp)
  have hac := hprod a (by simp) c (by simp)
  have had := hprod a (by simp) d (by simp)
  have hba := hprod b (by simp) a (by simp)
  have hbb := hprod b (by simp) b (by simp)
  have hbc := hprod b (by simp) c (by simp)
  have hbd := hprod b (by simp) d (by simp)
  have hca := hprod c (by simp) a (by simp)
  have hcb := hprod c (by simp) b (by simp)
  have hcc := hprod c (by simp) c (by simp)
  have hcd := hprod c (by simp) d (by simp)
  have hda := hprod d (by simp) a (by simp)
  have hdb := hprod d (by simp) b (by simp)
  have hdc := hprod d (by simp) c (by simp)
  have hdd := hprod d (by simp) d (by simp)
  rw [abs_le] at haa hab hac had hba hbb hbc hbd hca hcb hcc hcd hda hdb hdc hdd
  rcases haa with ⟨haa₁, haa₂⟩
  rcases hab with ⟨hab₁, hab₂⟩
  rcases hac with ⟨hac₁, hac₂⟩
  rcases had with ⟨had₁, had₂⟩
  rcases hba with ⟨hba₁, hba₂⟩
  rcases hbb with ⟨hbb₁, hbb₂⟩
  rcases hbc with ⟨hbc₁, hbc₂⟩
  rcases hbd with ⟨hbd₁, hbd₂⟩
  rcases hca with ⟨hca₁, hca₂⟩
  rcases hcb with ⟨hcb₁, hcb₂⟩
  rcases hcc with ⟨hcc₁, hcc₂⟩
  rcases hcd with ⟨hcd₁, hcd₂⟩
  rcases hda with ⟨hda₁, hda₂⟩
  rcases hdb with ⟨hdb₁, hdb₂⟩
  rcases hdc with ⟨hdc₁, hdc₂⟩
  rcases hdd with ⟨hdd₁, hdd₂⟩
  simp only [RatInterval.width, RatInterval.mul, a, b, c, d]
  rw [sub_le_iff_le_add]
  simp only [add_min]
  apply max_le <;> apply max_le <;> apply le_min <;> apply le_min <;>
    dsimp [a, b, c, d, R] at * <;>
    simp only [RatInterval.width] at * <;>
    linarith

private theorem rat_sq_subinterval_mul (K : RatInterval) :
    K.sq.Subinterval (K.mul K) := by
  have hlo : (K.mul K).Contains ((K.lo : ℝ) ^ 2) := by
    simpa [pow_two] using RatInterval.mul_sound
      (show K.Contains (K.lo : ℝ) from ⟨le_rfl, by exact_mod_cast K.lo_le_hi⟩)
      (show K.Contains (K.lo : ℝ) from ⟨le_rfl, by exact_mod_cast K.lo_le_hi⟩)
  have hhi : (K.mul K).Contains ((K.hi : ℝ) ^ 2) := by
    simpa [pow_two] using RatInterval.mul_sound
      (show K.Contains (K.hi : ℝ) from ⟨by exact_mod_cast K.lo_le_hi, le_rfl⟩)
      (show K.Contains (K.hi : ℝ) from ⟨by exact_mod_cast K.lo_le_hi, le_rfl⟩)
  rw [RatInterval.sq]
  split_ifs with hneg hpos
  · exact ⟨by exact_mod_cast hhi.1, by exact_mod_cast hlo.2⟩
  · exact ⟨by exact_mod_cast hlo.1, by exact_mod_cast hhi.2⟩
  · have hz : K.Contains (0 : ℝ) := by
      exact ⟨by exact_mod_cast le_of_not_gt hpos, by exact_mod_cast le_of_not_gt hneg⟩
    have hzero : (K.mul K).Contains (0 : ℝ) := by
      simpa using RatInterval.mul_sound hz hz
    exact ⟨by exact_mod_cast hzero.1,
      max_le (by exact_mod_cast hlo.2) (by exact_mod_cast hhi.2)⟩

/-- Squaring an interval has width at most twice its maximum endpoint magnitude times its width. -/
theorem rat_sq_width_le (K : RatInterval) :
    K.sq.width ≤ 2 * K.maxAbs * K.width := by
  exact (RatInterval.width_mono (rat_sq_subinterval_mul K)).trans
    (by simpa [two_mul, add_mul] using interval_mul_width_le K K)

/-- The upper endpoint of a squared interval is bounded by the square of its maximum endpoint magnitude. -/
theorem rat_sq_hi_le (K : RatInterval) : K.sq.hi ≤ K.maxAbs ^ 2 := by
  have hlo : |K.lo| ≤ K.maxAbs := le_max_left _ _
  have hhi : |K.hi| ≤ K.maxAbs := le_max_right _ _
  have hM : 0 ≤ K.maxAbs := (abs_nonneg K.lo).trans hlo
  have hlo' : K.lo ^ 2 ≤ K.maxAbs ^ 2 :=
    (sq_le_sq).2 (by simpa [abs_of_nonneg hM] using hlo)
  have hhi' : K.hi ^ 2 ≤ K.maxAbs ^ 2 :=
    (sq_le_sq).2 (by simpa [abs_of_nonneg hM] using hhi)
  rw [RatInterval.sq]
  split_ifs
  · exact hlo'
  · exact hhi'
  · exact max_le hlo' hhi'

/-- Refining an interval cannot increase its maximum endpoint magnitude. -/
theorem rat_maxAbs_mono {K L : RatInterval} (hKL : K.Subinterval L) :
    K.maxAbs ≤ L.maxAbs := by
  apply max_le
  · exact abs_le_max_abs_abs hKL.1 (K.lo_le_hi.trans hKL.2)
  · exact abs_le_max_abs_abs (hKL.1.trans K.lo_le_hi) hKL.2

/-- Each coordinate width after complex multiplication is bounded explicitly
by the operand widths and endpoint magnitudes. -/
theorem mul_width (I J : ComplexRatInterval) :
    (I.mul J).width ≤
      2 * (I.maxAbs * J.width + J.maxAbs * I.width) := by
  have hIreA : I.re.maxAbs ≤ I.maxAbs := le_max_left _ _
  have hIimA : I.im.maxAbs ≤ I.maxAbs := le_max_right _ _
  have hJreA : J.re.maxAbs ≤ J.maxAbs := le_max_left _ _
  have hJimA : J.im.maxAbs ≤ J.maxAbs := le_max_right _ _
  have hIrew : I.re.width ≤ I.width := le_max_left _ _
  have hIimw : I.im.width ≤ I.width := le_max_right _ _
  have hJrew : J.re.width ≤ J.width := le_max_left _ _
  have hJimw : J.im.width ≤ J.width := le_max_right _ _
  have hIA0 : 0 ≤ I.maxAbs := (abs_nonneg I.re.lo).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hJA0 : 0 ≤ J.maxAbs := (abs_nonneg J.re.lo).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hrr := interval_mul_width_le I.re J.re
  have hii := interval_mul_width_le I.im J.im
  have hri := interval_mul_width_le I.re J.im
  have hir := interval_mul_width_le I.im J.re
  have hrr' : (I.re.mul J.re).width ≤ I.maxAbs * J.width + J.maxAbs * I.width := by
    nlinarith [mul_le_mul hIreA hJrew (RatInterval.width_nonneg J.re)
      hIA0,
      mul_le_mul hJreA hIrew (RatInterval.width_nonneg I.re)
        hJA0]
  have hii' : (I.im.mul J.im).width ≤ I.maxAbs * J.width + J.maxAbs * I.width := by
    nlinarith [mul_le_mul hIimA hJimw (RatInterval.width_nonneg J.im)
      hIA0,
      mul_le_mul hJimA hIimw (RatInterval.width_nonneg I.im)
        hJA0]
  have hri' : (I.re.mul J.im).width ≤ I.maxAbs * J.width + J.maxAbs * I.width := by
    nlinarith [mul_le_mul hIreA hJimw (RatInterval.width_nonneg J.im)
      hIA0,
      mul_le_mul hJimA hIrew (RatInterval.width_nonneg I.re)
        hJA0]
  have hir' : (I.im.mul J.re).width ≤ I.maxAbs * J.width + J.maxAbs * I.width := by
    nlinarith [mul_le_mul hIimA hJrew (RatInterval.width_nonneg J.re)
      hIA0,
      mul_le_mul hJreA hIimw (RatInterval.width_nonneg I.im)
        hJA0]
  change max ((I.re.mul J.re).sub (I.im.mul J.im)).width
      ((I.re.mul J.im).add (I.im.mul J.re)).width ≤
    2 * (I.maxAbs * J.width + J.maxAbs * I.width)
  rw [RatInterval.width_sub, RatInterval.width_add]
  exact max_le (by linarith) (by linarith)

/-- The squared-modulus interval width is controlled by rectangle magnitude
and rectangle width. -/
theorem normSq_width (I : ComplexRatInterval) :
    I.normSq.width ≤ 4 * I.maxAbs * I.width := by
  have hre := rat_sq_width_le I.re
  have him := rat_sq_width_le I.im
  have hA0 : 0 ≤ I.maxAbs := (abs_nonneg I.re.lo).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hreprod : I.re.maxAbs * I.re.width ≤ I.maxAbs * I.width :=
    mul_le_mul (le_max_left _ _) (le_max_left _ _)
      (RatInterval.width_nonneg I.re) hA0
  have himprod : I.im.maxAbs * I.im.width ≤ I.maxAbs * I.width :=
    mul_le_mul (le_max_right _ _) (le_max_right _ _)
      (RatInterval.width_nonneg I.im) hA0
  rw [normSq, RatInterval.width_add]
  nlinarith

/-- If the squared-modulus denominator has positive lower bound δ, guarded
division has maximum coordinate magnitude at most the numerator magnitude
divided by δ. -/
theorem div_maxAbs {I J : ComplexRatInterval} (hJ : J.normSq.AwayFromZero)
    {δ : ℚ} (hδ : 0 < δ) (hsep : δ ≤ J.normSq.lo) :
    (I.div J hJ).maxAbs ≤ (I.mul J.conj).maxAbs / δ := by
  let N := I.mul J.conj
  let D := J.normSq
  have hlo : 0 < D.lo := hδ.trans_le hsep
  have hhi : 0 < D.hi := hlo.trans_le D.lo_le_hi
  have hinvA : (D.inv hJ).maxAbs ≤ 1 / δ := by
    have hinvord : D.hi⁻¹ ≤ D.lo⁻¹ := (inv_le_inv₀ hhi hlo).2 D.lo_le_hi
    simp only [RatInterval.inv, RatInterval.maxAbs,
      abs_of_pos (inv_pos.mpr hhi), abs_of_pos (inv_pos.mpr hlo)]
    rw [max_eq_right hinvord]
    simpa [one_div] using (inv_le_inv₀ hlo hδ).2 hsep
  have hN0 : 0 ≤ N.maxAbs := (abs_nonneg N.re.lo).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hinv0 : 0 ≤ (D.inv hJ).maxAbs :=
    (abs_nonneg (D.inv hJ).lo).trans (le_max_left _ _)
  have hre := RatInterval.maxAbs_mul N.re (D.inv hJ)
  have him := RatInterval.maxAbs_mul N.im (D.inv hJ)
  have hre' : (N.re.mul (D.inv hJ)).maxAbs ≤ N.maxAbs / δ := by
    calc
      _ ≤ N.re.maxAbs * (D.inv hJ).maxAbs := hre
      _ ≤ N.maxAbs * (1 / δ) :=
        mul_le_mul (le_max_left _ _) hinvA hinv0 hN0
      _ = N.maxAbs / δ := by ring
  have him' : (N.im.mul (D.inv hJ)).maxAbs ≤ N.maxAbs / δ := by
    calc
      _ ≤ N.im.maxAbs * (D.inv hJ).maxAbs := him
      _ ≤ N.maxAbs * (1 / δ) :=
        mul_le_mul (le_max_right _ _) hinvA hinv0 hN0
      _ = N.maxAbs / δ := by ring
  change max (N.re.div D hJ).maxAbs (N.im.div D hJ).maxAbs ≤ N.maxAbs / δ
  change max (N.re.mul (D.inv hJ)).maxAbs
    (N.im.mul (D.inv hJ)).maxAbs ≤ N.maxAbs / δ
  exact max_le hre' him'

/-- If the squared-modulus denominator has certified lower bound δ, guarded
division propagates widths with the usual inverse-square factor. -/
theorem div_width {I J : ComplexRatInterval} (hJ : J.normSq.AwayFromZero)
    {δ : ℚ} (hδ : 0 < δ) (hsep : δ ≤ J.normSq.lo) :
    (I.div J hJ).width ≤
      (I.mul J.conj).maxAbs * J.normSq.width / (δ ^ 2) +
        (I.mul J.conj).width / δ := by
  let N := I.mul J.conj
  let D := J.normSq
  have hlo : 0 < D.lo := hδ.trans_le hsep
  have hhi : 0 < D.hi := hlo.trans_le D.lo_le_hi
  have hprod : δ ^ 2 ≤ D.lo * D.hi := by
    have := mul_le_mul hsep (hsep.trans D.lo_le_hi) hδ.le hlo.le
    simpa [pow_two] using this
  have hinvw : (D.inv hJ).width ≤ D.width / δ ^ 2 := by
    have heq : (D.inv hJ).width = D.width / (D.lo * D.hi) := by
      simp only [RatInterval.inv, RatInterval.width]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_left (RatInterval.width_nonneg D)
      (sq_pos_of_pos hδ) hprod
  have hinvA : (D.inv hJ).maxAbs ≤ 1 / δ := by
    have hinvord : D.hi⁻¹ ≤ D.lo⁻¹ := (inv_le_inv₀ hhi hlo).2 D.lo_le_hi
    simp only [RatInterval.inv, RatInterval.maxAbs,
      abs_of_pos (inv_pos.mpr hhi), abs_of_pos (inv_pos.mpr hlo)]
    rw [max_eq_right hinvord]
    simpa [one_div] using (inv_le_inv₀ hlo hδ).2 hsep
  have hNA : 0 ≤ N.maxAbs := (abs_nonneg N.re.lo).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hNW : 0 ≤ N.width := (RatInterval.width_nonneg N.re).trans (le_max_left _ _)
  have hInvA0 : 0 ≤ (D.inv hJ).maxAbs :=
    (abs_nonneg (D.inv hJ).lo).trans (le_max_left _ _)
  have hInvW0 : 0 ≤ (D.inv hJ).width := RatInterval.width_nonneg _
  have hre := interval_mul_width_le N.re (D.inv hJ)
  have him := interval_mul_width_le N.im (D.inv hJ)
  have hreA : N.re.maxAbs ≤ N.maxAbs := le_max_left _ _
  have himA : N.im.maxAbs ≤ N.maxAbs := le_max_right _ _
  have hrew : N.re.width ≤ N.width := le_max_left _ _
  have himw : N.im.width ≤ N.width := le_max_right _ _
  have hre' : (N.re.mul (D.inv hJ)).width ≤
      N.maxAbs * (D.width / δ ^ 2) + (1 / δ) * N.width := by
    nlinarith [mul_le_mul hreA hinvw hInvW0 hNA,
      mul_le_mul hinvA hrew (RatInterval.width_nonneg N.re) (by positivity : (0 : ℚ) ≤ 1 / δ)]
  have him' : (N.im.mul (D.inv hJ)).width ≤
      N.maxAbs * (D.width / δ ^ 2) + (1 / δ) * N.width := by
    nlinarith [mul_le_mul himA hinvw hInvW0 hNA,
      mul_le_mul hinvA himw (RatInterval.width_nonneg N.im) (by positivity : (0 : ℚ) ≤ 1 / δ)]
  change max (N.re.div D hJ).width (N.im.div D hJ).width ≤
    N.maxAbs * D.width / δ ^ 2 + N.width / δ
  change max (N.re.mul (D.inv hJ)).width (N.im.mul (D.inv hJ)).width ≤ _
  apply max_le
  · exact hre'.trans_eq (by ring)
  · exact him'.trans_eq (by ring)

/-- Applying rational square-root bounds to the squared-modulus interval
produces an executable enclosure of the complex norm. -/
theorem normSq_lo_nonneg (I : ComplexRatInterval) : 0 ≤ I.normSq.lo := by
  have hsquare (K : RatInterval) : 0 ≤ K.sq.lo := by
    unfold RatInterval.sq
    split_ifs <;> positivity
  simp only [normSq, RatInterval.add]
  exact add_nonneg (hsquare I.re) (hsquare I.im)

/-- Applying rational square-root bounds to the squared-modulus interval
produces an executable enclosure of the complex norm. -/
def normInterval (I : ComplexRatInterval) (fuel : ℕ) : RatInterval :=
  RatInterval.sqrtInterval I.normSq (normSq_lo_nonneg I) fuel

/-- The executable modulus interval contains the norm of every enclosed complex value. -/
theorem normInterval_sound {I : ComplexRatInterval} {z : ℂ}
    (hz : I.Contains z) (fuel : ℕ) : (I.normInterval fuel).Contains ‖z‖ := by
  have hs := RatInterval.sqrtInterval_sound (normSq_lo_nonneg I)
    (normSq_sound hz) fuel
  simpa [normInterval, Real.sqrt_sq (norm_nonneg z)] using hs

end ComplexRatInterval

end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
