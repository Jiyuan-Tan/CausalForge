import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareAnalytic
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Arm-slice certificates for the fixed hard square

This module proves finiteness by parametrizing the ambient radius circle and
strict positivity by exhibiting short armwise arcs with nontrivial coordinate
projections.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The two-dimensional score space is isometric to the complex plane. -/
-- @node: causalHardScoreComplexEquiv
noncomputable def causalHardScoreComplexEquiv : Score ≃ᵢ ℂ where
  toFun x := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I
  invFun z := scorePoint z.re z.im
  left_inv x := by
    ext i
    fin_cases i
    · simp [scorePoint_apply_zero]
    · simp [scorePoint_apply_one]
  right_inv z := by
    apply Complex.ext <;> simp [scorePoint_apply_zero, scorePoint_apply_one]
  isometry_toFun := by
    intro x y
    simp only [edist_dist]
    rw [dist_eq_norm, dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, Complex.norm_def,
      Complex.normSq_apply, PiLp.sub_apply]
    congr 2 <;> ring

/-- Every radius circle in the score plane has finite one-dimensional
Hausdorff measure. -/
-- @node: causalHardSphere_hausdorffMeasure_lt_top
lemma causalHardSphere_hausdorffMeasure_lt_top (x : Score) (s : ℝ) :
    μH[1] (Metric.sphere x s) < ∞ := by
  by_cases hs : s < 0
  · simp [Metric.sphere_eq_empty_of_neg hs]
  have hsabs : |s| = s := abs_of_nonneg (le_of_not_gt hs)
  let e := causalHardScoreComplexEquiv
  have hcircle : μH[1] (Metric.sphere (e x) s) < ∞ := by
    rw [← hsabs, ← image_circleMap_Ioc]
    refine lt_of_le_of_lt
      ((lipschitzWith_circleMap (e x) s).hausdorffMeasure_image_le (by norm_num) _) ?_
    rw [hausdorffMeasure_real, Real.volume_Ioc]
    simpa only [ENNReal.rpow_one] using
      ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top
  rw [← e.image_sphere x s] at hcircle
  simpa only [e, IsometryEquiv.hausdorffMeasure_image] using hcircle

/-- A score coordinate is one-Lipschitz. -/
-- @node: causalHardScoreCoordinate_lipschitz
lemma causalHardScoreCoordinate_lipschitz (i : Fin 2) :
    LipschitzWith 1 (fun z : Score => z i) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, PiLp.sub_apply]
  rw [Real.le_sqrt (abs_nonneg _) (by positivity)]
  fin_cases i
  · change |x 0 - y 0| ^ 2 ≤ |x 0 - y 0| ^ 2 + |x 1 - y 1| ^ 2
    nlinarith [sq_nonneg |x 1 - y 1|]
  · change |x 1 - y 1| ^ 2 ≤ |x 0 - y 0| ^ 2 + |x 1 - y 1| ^ 2
    nlinarith [sq_nonneg |x 0 - y 0|]

/-- A score set whose coordinate projection contains a nondegenerate interval
has positive one-dimensional Hausdorff measure. -/
-- @node: hausdorffMeasure_pos_of_scoreCoordinate_interval
lemma hausdorffMeasure_pos_of_scoreCoordinate_interval
    {S : Set Score} {i : Fin 2} {a b : ℝ}
    (hab : a < b) (hsub : Icc a b ⊆ (fun z : Score => z i) '' S) :
    0 < μH[1] S := by
  have hI : 0 < μH[1] (Icc a b) := by
    rw [hausdorffMeasure_real, Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  have himage : μH[1] ((fun z : Score => z i) '' S) ≤ μH[1] S := by
    simpa using (causalHardScoreCoordinate_lipschitz i).hausdorffMeasure_image_le
      (by norm_num : (0 : ℝ) ≤ 1) S
  exact hI.trans_le ((measure_mono hsub).trans himage)

/-- A radius-circle arc written as a graph over the second coordinate. -/
-- @node: causalHardArc0
noncomputable def causalHardArc0 (x : Score) (s dn dt r : ℝ) : Score :=
  scorePoint (x 0 + dn * Real.sqrt (s ^ 2 - r ^ 2)) (x 1 + dt * r)

/-- A radius-circle arc written as a graph over the first coordinate. -/
-- @node: causalHardArc1
noncomputable def causalHardArc1 (x : Score) (s dn dt r : ℝ) : Score :=
  scorePoint (x 0 + dt * r) (x 1 + dn * Real.sqrt (s ^ 2 - r ^ 2))

/-- Every admissible graph-over-second-coordinate arc point lies on its
prescribed radius circle. -/
-- @node: causalHardArc0_dist
lemma causalHardArc0_dist {x : Score} {s r dn dt : ℝ} (hs : 0 < s)
    (hr0 : 0 ≤ r) (hr : r ≤ s) (hdn : |dn| = 1) (hdt : |dt| = 1) :
    dist (causalHardArc0 x s dn dt r) x = s := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp only [causalHardArc0, Fin.sum_univ_two, Real.norm_eq_abs,
    PiLp.sub_apply, scorePoint_apply_zero, scorePoint_apply_one]
  have hrad : 0 ≤ s ^ 2 - r ^ 2 := by nlinarith
  simp only [add_sub_cancel_left]
  rw [abs_mul, hdn, one_mul, abs_mul, hdt, one_mul,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hr0,
    Real.sq_sqrt hrad]
  calc
    Real.sqrt (s ^ 2 - r ^ 2 + r ^ 2) = Real.sqrt (s ^ 2) := by ring
    _ = |s| := Real.sqrt_sq_eq_abs s
    _ = s := abs_of_pos hs

/-- Every admissible graph-over-first-coordinate arc point lies on its
prescribed radius circle. -/
-- @node: causalHardArc1_dist
lemma causalHardArc1_dist {x : Score} {s r dn dt : ℝ} (hs : 0 < s)
    (hr0 : 0 ≤ r) (hr : r ≤ s) (hdn : |dn| = 1) (hdt : |dt| = 1) :
    dist (causalHardArc1 x s dn dt r) x = s := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp only [causalHardArc1, Fin.sum_univ_two, Real.norm_eq_abs,
    PiLp.sub_apply, scorePoint_apply_zero, scorePoint_apply_one]
  have hrad : 0 ≤ s ^ 2 - r ^ 2 := by nlinarith
  simp only [add_sub_cancel_left]
  rw [abs_mul, hdt, one_mul, abs_mul, hdn, one_mul,
    abs_of_nonneg hr0, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hrad]
  calc
    Real.sqrt (r ^ 2 + (s ^ 2 - r ^ 2)) = Real.sqrt (s ^ 2) := by ring
    _ = |s| := Real.sqrt_sq_eq_abs s
    _ = s := abs_of_pos hs

/-- The normal displacement of a short quarter arc is positive and at most
the radius. -/
-- @node: causalHardArc_sqrt_bounds
lemma causalHardArc_sqrt_bounds {s r : ℝ} (hs : 0 < s) (hr0 : 0 ≤ r)
    (hr : r ≤ s / 2) :
    0 < Real.sqrt (s ^ 2 - r ^ 2) ∧ Real.sqrt (s ^ 2 - r ^ 2) ≤ s := by
  have hrad : 0 < s ^ 2 - r ^ 2 := by nlinarith
  constructor
  · exact Real.sqrt_pos.2 hrad
  · rw [Real.sqrt_le_iff]
    exact ⟨hs.le, by nlinarith⟩

/-- Every positive radius at most one cuts a positive-length arc from the
fixed treatment rectangle at every frontier point. -/
-- @node: causalHardArmOne_slice_hausdorffMeasure_pos
lemma causalHardArmOne_slice_hausdorffMeasure_pos {x : Score} {s : ℝ}
    (hx : x ∈ frontier causalHardArmOne) (hs : 0 < s) (hs1 : s ≤ 1) :
    0 < μH[1] {z | z ∈ causalHardArmOne ∧ dist z x = s} := by
  have hx' := (mem_frontier_causalHardArmOne_iff x).mp hx
  rcases hx'.2.2.2.2 with hedge | hedge | hedge | hedge
  · by_cases hm : x 1 ≤ 1
    · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 1)
        (a := x 1 + s / 4) (b := x 1 + s / 2) (by linarith)
      intro y hy
      let r := y - x 1
      let z := causalHardArc0 x s 1 1 r
      have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.1]
      have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.2]
      have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
      refine ⟨z, ⟨?_, causalHardArc0_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
      · simp only [causalHardArmOne, mem_setOf_eq, z, causalHardArc0,
          scorePoint_apply_zero, scorePoint_apply_one]
        rw [hedge]
        exact ⟨by linarith, by linarith, by linarith [hx'.2.2.1],
          by linarith [hx'.2.2.2.1]⟩
      · simp [z, causalHardArc0, r, scorePoint_apply_one]
    · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 1)
        (a := x 1 - s / 2) (b := x 1 - s / 4) (by linarith)
      intro y hy
      let r := x 1 - y
      let z := causalHardArc0 x s 1 (-1) r
      have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.2]
      have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.1]
      have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
      refine ⟨z, ⟨?_, causalHardArc0_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
      · simp only [causalHardArmOne, mem_setOf_eq, z, causalHardArc0,
          scorePoint_apply_zero, scorePoint_apply_one]
        rw [hedge]
        exact ⟨by linarith, by linarith, by linarith [hx'.2.2.1],
          by linarith [hx'.2.2.2.1]⟩
      · simp [z, causalHardArc0, r, scorePoint_apply_one]
  · by_cases hm : x 1 ≤ 1
    · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 1)
        (a := x 1 + s / 4) (b := x 1 + s / 2) (by linarith)
      intro y hy
      let r := y - x 1
      let z := causalHardArc0 x s (-1) 1 r
      have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.1]
      have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.2]
      have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
      refine ⟨z, ⟨?_, causalHardArc0_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
      · simp only [causalHardArmOne, mem_setOf_eq, z, causalHardArc0,
          scorePoint_apply_zero, scorePoint_apply_one]
        rw [hedge]
        exact ⟨by linarith, by linarith, by linarith [hx'.2.2.1],
          by linarith [hx'.2.2.2.1]⟩
      · simp [z, causalHardArc0, r, scorePoint_apply_one]
    · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 1)
        (a := x 1 - s / 2) (b := x 1 - s / 4) (by linarith)
      intro y hy
      let r := x 1 - y
      let z := causalHardArc0 x s (-1) (-1) r
      have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.2]
      have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.1]
      have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
      refine ⟨z, ⟨?_, causalHardArc0_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
      · simp only [causalHardArmOne, mem_setOf_eq, z, causalHardArc0,
          scorePoint_apply_zero, scorePoint_apply_one]
        rw [hedge]
        exact ⟨by linarith, by linarith, by linarith [hx'.2.2.1],
          by linarith [hx'.2.2.2.1]⟩
      · simp [z, causalHardArc0, r, scorePoint_apply_one]
  · by_cases hm : x 0 ≤ 0
    · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 0)
        (a := x 0 + s / 4) (b := x 0 + s / 2) (by linarith)
      intro y hy
      let r := y - x 0
      let z := causalHardArc1 x s 1 1 r
      have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.1]
      have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.2]
      have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
      refine ⟨z, ⟨?_, causalHardArc1_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
      · simp only [causalHardArmOne, mem_setOf_eq, z, causalHardArc1,
          scorePoint_apply_zero, scorePoint_apply_one]
        rw [hedge]
        exact ⟨by linarith [hx'.1], by linarith [hx'.2.1],
          by linarith, by linarith⟩
      · simp [z, causalHardArc1, r, scorePoint_apply_zero]
    · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 0)
        (a := x 0 - s / 2) (b := x 0 - s / 4) (by linarith)
      intro y hy
      let r := x 0 - y
      let z := causalHardArc1 x s 1 (-1) r
      have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.2]
      have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.1]
      have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
      refine ⟨z, ⟨?_, causalHardArc1_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
      · simp only [causalHardArmOne, mem_setOf_eq, z, causalHardArc1,
          scorePoint_apply_zero, scorePoint_apply_one]
        rw [hedge]
        exact ⟨by linarith [hx'.1], by linarith [hx'.2.1],
          by linarith, by linarith⟩
      · simp [z, causalHardArc1, r, scorePoint_apply_zero]
  · by_cases hm : x 0 ≤ 0
    · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 0)
        (a := x 0 + s / 4) (b := x 0 + s / 2) (by linarith)
      intro y hy
      let r := y - x 0
      let z := causalHardArc1 x s (-1) 1 r
      have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.1]
      have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.2]
      have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
      refine ⟨z, ⟨?_, causalHardArc1_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
      · simp only [causalHardArmOne, mem_setOf_eq, z, causalHardArc1,
          scorePoint_apply_zero, scorePoint_apply_one]
        rw [hedge]
        exact ⟨by linarith [hx'.1], by linarith [hx'.2.1],
          by linarith, by linarith⟩
      · simp [z, causalHardArc1, r, scorePoint_apply_zero]
    · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 0)
        (a := x 0 - s / 2) (b := x 0 - s / 4) (by linarith)
      intro y hy
      let r := x 0 - y
      let z := causalHardArc1 x s (-1) (-1) r
      have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.2]
      have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.1]
      have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
      refine ⟨z, ⟨?_, causalHardArc1_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
      · simp only [causalHardArmOne, mem_setOf_eq, z, causalHardArc1,
          scorePoint_apply_zero, scorePoint_apply_one]
        rw [hedge]
        exact ⟨by linarith [hx'.1], by linarith [hx'.2.1],
          by linarith, by linarith⟩
      · simp [z, causalHardArc1, r, scorePoint_apply_zero]

/-- Every positive radius at most one cuts a positive-length arc from the
support-side complement of the treatment rectangle. -/
-- @node: causalHardArmZero_slice_hausdorffMeasure_pos
lemma causalHardArmZero_slice_hausdorffMeasure_pos {x : Score} {s : ℝ}
    (hx : x ∈ frontier causalHardArmOne) (hs : 0 < s) (hs1 : s ≤ 1) :
    0 < μH[1] {z | z ∈ causalHardSquare \ causalHardArmOne ∧ dist z x = s} := by
  have hx' := (mem_frontier_causalHardArmOne_iff x).mp hx
  rcases hx'.2.2.2.2 with hedge | hedge | hedge | hedge
  · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 1)
      (a := x 1 + s / 4) (b := x 1 + s / 2) (by linarith)
    intro y hy
    let r := y - x 1
    let z := causalHardArc0 x s (-1) 1 r
    have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.1]
    have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.2]
    have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
    refine ⟨z, ⟨⟨?_, ?_⟩,
      causalHardArc0_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
    · intro i
      fin_cases i
      · change -3 ≤ z 0 ∧ z 0 ≤ 3
        simp only [z, causalHardArc0, scorePoint_apply_zero]
        rw [hedge]
        exact ⟨by linarith, by linarith⟩
      · change -3 ≤ z 1 ∧ z 1 ≤ 3
        simp only [z, causalHardArc0, scorePoint_apply_one]
        exact ⟨by linarith [hx'.2.2.1], by linarith [hx'.2.2.2.1]⟩
    · intro hA
      simp only [causalHardArmOne, mem_setOf_eq] at hA
      simp only [z, causalHardArc0, scorePoint_apply_zero] at hA
      rw [hedge] at hA
      linarith
    · simp [z, causalHardArc0, r, scorePoint_apply_one]
  · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 1)
      (a := x 1 + s / 4) (b := x 1 + s / 2) (by linarith)
    intro y hy
    let r := y - x 1
    let z := causalHardArc0 x s 1 1 r
    have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.1]
    have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.2]
    have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
    refine ⟨z, ⟨⟨?_, ?_⟩,
      causalHardArc0_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
    · intro i
      fin_cases i
      · change -3 ≤ z 0 ∧ z 0 ≤ 3
        simp only [z, causalHardArc0, scorePoint_apply_zero]
        rw [hedge]
        exact ⟨by linarith, by linarith⟩
      · change -3 ≤ z 1 ∧ z 1 ≤ 3
        simp only [z, causalHardArc0, scorePoint_apply_one]
        exact ⟨by linarith [hx'.2.2.1], by linarith [hx'.2.2.2.1]⟩
    · intro hA
      simp only [causalHardArmOne, mem_setOf_eq] at hA
      simp only [z, causalHardArc0, scorePoint_apply_zero] at hA
      rw [hedge] at hA
      linarith
    · simp [z, causalHardArc0, r, scorePoint_apply_one]
  · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 0)
      (a := x 0 + s / 4) (b := x 0 + s / 2) (by linarith)
    intro y hy
    let r := y - x 0
    let z := causalHardArc1 x s (-1) 1 r
    have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.1]
    have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.2]
    have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
    refine ⟨z, ⟨⟨?_, ?_⟩,
      causalHardArc1_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
    · intro i
      fin_cases i
      · change -3 ≤ z 0 ∧ z 0 ≤ 3
        simp only [z, causalHardArc1, scorePoint_apply_zero]
        exact ⟨by linarith [hx'.1], by linarith [hx'.2.1]⟩
      · change -3 ≤ z 1 ∧ z 1 ≤ 3
        simp only [z, causalHardArc1, scorePoint_apply_one]
        rw [hedge]
        exact ⟨by linarith, by linarith⟩
    · intro hA
      simp only [causalHardArmOne, mem_setOf_eq] at hA
      simp only [z, causalHardArc1, scorePoint_apply_one] at hA
      rw [hedge] at hA
      linarith
    · simp [z, causalHardArc1, r, scorePoint_apply_zero]
  · apply hausdorffMeasure_pos_of_scoreCoordinate_interval (i := 0)
      (a := x 0 + s / 4) (b := x 0 + s / 2) (by linarith)
    intro y hy
    let r := y - x 0
    let z := causalHardArc1 x s 1 1 r
    have hr0 : 0 ≤ r := by dsimp [r]; linarith [hy.1]
    have hr : r ≤ s / 2 := by dsimp [r]; linarith [hy.2]
    have hsqrt := causalHardArc_sqrt_bounds hs hr0 hr
    refine ⟨z, ⟨⟨?_, ?_⟩,
      causalHardArc1_dist hs hr0 (hr.trans (by linarith)) (by norm_num) (by norm_num)⟩, ?_⟩
    · intro i
      fin_cases i
      · change -3 ≤ z 0 ∧ z 0 ≤ 3
        simp only [z, causalHardArc1, scorePoint_apply_zero]
        exact ⟨by linarith [hx'.1], by linarith [hx'.2.1]⟩
      · change -3 ≤ z 1 ∧ z 1 ≤ 3
        simp only [z, causalHardArc1, scorePoint_apply_one]
        rw [hedge]
        exact ⟨by linarith, by linarith⟩
    · intro hA
      simp only [causalHardArmOne, mem_setOf_eq] at hA
      simp only [z, causalHardArc1, scorePoint_apply_one] at hA
      rw [hedge] at hA
      linarith
    · simp [z, causalHardArc1, r, scorePoint_apply_zero]

/-- A uniformly positive and bounded density gives finite positive mass to
each positive-length arm slice. -/
-- @node: causalHardDensitySlice_finite_pos
lemma causalHardDensitySlice_finite_pos (P : A1A2Law)
    (hA1 : P.A1 = causalHardArmOne)
    (hA0 : P.A0 = causalHardSquare \ causalHardArmOne)
    (hdensMeas : Measurable P.density)
    (hlower : ∀ z, (1 / 48 : ℝ) ≤ P.density z)
    (hupper : ∀ z, P.density z ≤ (5 / 144 : ℝ))
    (t : Bool) {x : Score} {s : ℝ}
    (hx : x ∈ frontier causalHardArmOne) (hs : 0 < s) (hs1 : s ≤ 1) :
    0 < armSliceDensityMass P t x s ∧ armSliceDensityMass P t x s < ∞ := by
  let S : Set Score := {z | z ∈ (if t then P.A1 else P.A0) ∧ dist z x = s}
  have hSpos : 0 < μH[1] S := by
    cases t with
    | false => simpa [S, hA0] using causalHardArmZero_slice_hausdorffMeasure_pos hx hs hs1
    | true => simpa [S, hA1] using causalHardArmOne_slice_hausdorffMeasure_pos hx hs hs1
  have hSfinite : μH[1] S < ∞ := by
    apply lt_of_le_of_lt (measure_mono ?_) (causalHardSphere_hausdorffMeasure_lt_top x s)
    intro z hz
    exact hz.2
  have hlo : ENNReal.ofReal (1 / 48 : ℝ) * μH[1] S ≤
      ∫⁻ z in S, ENNReal.ofReal (P.density z) ∂μH[1] := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono (ENNReal.measurable_ofReal.comp hdensMeas)
      (fun z _ => ENNReal.ofReal_le_ofReal (hlower z))
  have hup : (∫⁻ z in S, ENNReal.ofReal (P.density z) ∂μH[1]) ≤
      ENNReal.ofReal (5 / 144 : ℝ) * μH[1] S := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono measurable_const
      (fun z _ => ENNReal.ofReal_le_ofReal (hupper z))
  unfold armSliceDensityMass
  change 0 < ∫⁻ z in S, ENNReal.ofReal (P.density z) ∂μH[1] ∧
    (∫⁻ z in S, ENNReal.ofReal (P.density z) ∂μH[1]) < ∞
  constructor
  · exact (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
      hSpos.ne').trans_le hlo
  · exact hup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSfinite)

/-- Every explicit angular hard law satisfies the class's finite-positive
arm-slice condition once the envelope is at least `48`. -/
-- @node: causalHardA1A2Law_slice_certificate
lemma causalHardA1A2Law_slice_certificate {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare)
    {L : ℝ} (hL : 48 ≤ L) :
    let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
      hdelta hw hsep hcell
    ∀ t x s, x ∈ P.boundary → 0 < s → s ≤ L⁻¹ →
      0 < armSliceDensityMass P t x s ∧ armSliceDensityMass P t x s < ∞ := by
  dsimp only
  intro t x s hx hs hsL
  let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
    hdelta hw hsep hcell
  have hgeom := causalHardA1A2Law_geometry b cA delta w centers omega hb
    hscale hcA hdelta hw hsep hcell
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hs1 : s ≤ 1 := hsL.trans ((inv_le_one₀ hLpos).2 (by linarith))
  apply causalHardDensitySlice_finite_pos P hgeom.2.1 hgeom.2.2.1
  · exact (causalHardScoreDensity_continuous centers omega hb hscale).measurable
  · intro z
    exact (causalHardScoreDensity_mem_Icc hcA hdelta hw hsep omega z).1
  · intro z
    exact (causalHardScoreDensity_mem_Icc hcA hdelta hw hsep omega z).2
  · exact hgeom.2.2.2 ▸ hx
  · exact hs
  · exact hs1

end CausalSmith.Stat.BddUniformLogPenalty
