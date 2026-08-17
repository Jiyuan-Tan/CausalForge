import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareGeometry
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.LawClass
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.SquareBoundary

/-!
# Class-level geometry of the fixed assignment rectangle

This module transports the existing explicit square-frontier traversal to the
fixed arm-one rectangle.  It supplies the rectifiability leaf needed by the
hard-square class certificate.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Scale the unit square by two and translate it upward by one. -/
-- @node: causalHardRectangleAffineHomeomorph
noncomputable def causalHardRectangleAffineHomeomorph : Score ≃ₜ Score :=
  (Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num)).trans
    (Homeomorph.addLeft (scorePoint 0 1))

/-- The affine image of the centered unit square is the fixed arm-one
rectangle. -/
-- @node: causalHardRectangleAffineHomeomorph_image
lemma causalHardRectangleAffineHomeomorph_image :
    causalHardRectangleAffineHomeomorph '' scoreCube (1 / 2 : ℝ) =
      causalHardArmOne := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy0 := hy (0 : Fin 2)
    have hy1 := hy (1 : Fin 2)
    rw [abs_le] at hy0 hy1
    simp only [causalHardRectangleAffineHomeomorph, Homeomorph.trans_apply,
      Homeomorph.smulOfNeZero_apply, Homeomorph.coe_addLeft,
      causalHardArmOne, mem_setOf_eq, PiLp.add_apply, PiLp.smul_apply,
      scorePoint_apply_zero, scorePoint_apply_one, smul_eq_mul, zero_add]
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  · intro hx
    simp only [causalHardArmOne, mem_setOf_eq] at hx
    let y : Score := scorePoint (x 0 / 2) ((x 1 - 1) / 2)
    refine ⟨y, ?_, ?_⟩
    · intro i
      change |y i| ≤ 1 / 2
      fin_cases i
      · rw [show y ⟨0, by omega⟩ = x 0 / 2 by
          simpa [y] using
            scorePoint_apply_zero (x 0 / 2) ((x 1 - 1) / 2)]
        rw [abs_le]
        constructor <;> linarith [hx.1, hx.2.1]
      · rw [show y ⟨1, by omega⟩ = (x 1 - 1) / 2 by
          simpa [y] using
            scorePoint_apply_one (x 0 / 2) ((x 1 - 1) / 2)]
        rw [abs_le]
        constructor <;> linarith [hx.2.2.1, hx.2.2.2]
    · ext i
      fin_cases i
      · simp only [causalHardRectangleAffineHomeomorph,
          Homeomorph.trans_apply, Homeomorph.smulOfNeZero_apply,
          Homeomorph.coe_addLeft, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [show (scorePoint 0 1) ⟨0, by omega⟩ = 0 by
          simpa using scorePoint_apply_zero 0 1,
          show y ⟨0, by omega⟩ = x 0 / 2 by
            simpa [y] using
              scorePoint_apply_zero (x 0 / 2) ((x 1 - 1) / 2)]
        norm_num [causalHardRectangleAffineHomeomorph,
          Homeomorph.coe_addLeft]
        ring
      · simp only [causalHardRectangleAffineHomeomorph,
          Homeomorph.trans_apply, Homeomorph.smulOfNeZero_apply,
          Homeomorph.coe_addLeft, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [show (scorePoint 0 1) ⟨1, by omega⟩ = 1 by
          simpa using scorePoint_apply_one 0 1,
          show y ⟨1, by omega⟩ = (x 1 - 1) / 2 by
            simpa [y] using
              scorePoint_apply_one (x 0 / 2) ((x 1 - 1) / 2)]
        norm_num [causalHardRectangleAffineHomeomorph,
          Homeomorph.coe_addLeft]
        ring

/-- The square traversal transported to the fixed assignment rectangle. -/
-- @node: causalHardRectangleFrontierParam
noncomputable def causalHardRectangleFrontierParam (t : ℝ) : Score :=
  causalHardRectangleAffineHomeomorph (squareFrontierParam t)

/-- The fixed assignment frontier is a rectifiable curve. -/
-- @node: causalHardFrontier_rectifiableCurve
lemma causalHardFrontier_rectifiableCurve :
    RectifiableCurve (frontier causalHardArmOne) := by
  refine ⟨16, causalHardRectangleFrontierParam, ?_, ?_⟩
  · have hT : LipschitzWith 2
        (causalHardRectangleAffineHomeomorph : Score → Score) := by
      have hs : LipschitzWith 2 (fun x : Score => (2 : ℝ) • x) := by
        simpa using (lipschitzWith_smul (2 : ℝ) :
          LipschitzWith ‖(2 : ℝ)‖₊ (fun x : Score => (2 : ℝ) • x))
      have ha := (isometry_add_left (scorePoint 0 1)).lipschitz.comp hs
      rw [one_mul] at ha
      exact ha
    have hc := hT.comp squareFrontierParam_lipschitz
    convert hc.lipschitzOnWith using 1 <;>
      first
        | rfl
        | norm_num [causalHardRectangleFrontierParam, Function.comp_def]
  · change (fun t => causalHardRectangleAffineHomeomorph
      (squareFrontierParam t)) '' Icc (0 : ℝ) 1 = _
    rw [← Set.image_image, squareFrontierParam_image,
      causalHardRectangleAffineHomeomorph.image_frontier,
      causalHardRectangleAffineHomeomorph_image]

/-- The hard square has the class's rectangular-support form for every
envelope at least three. -/
-- @node: causalHardSquare_rectangularScoreSupport
lemma causalHardSquare_rectangularScoreSupport {L : ℝ} (hL : 3 ≤ L) :
    RectangularScoreSupport causalHardSquare L := by
  refine ⟨-3, 3, by norm_num, rfl, ?_⟩
  intro x hx i
  apply abs_le.mpr
  constructor
  · linarith [(hx i).1]
  · exact (hx i).2.trans hL

/-- The fixed rectangle frontier has one-dimensional Hausdorff mass between
`1/48` and `48`, the uniform bounds needed by every admissible hard law. -/
-- @node: causalHardFrontier_hausdorff_bounds_fixed
lemma causalHardFrontier_hausdorff_bounds_fixed :
    ENNReal.ofReal (48 : ℝ)⁻¹ ≤
        Measure.hausdorffMeasure 1 (frontier causalHardArmOne) ∧
      Measure.hausdorffMeasure 1 (frontier causalHardArmOne) ≤
        ENNReal.ofReal 48 := by
  have hupper : Measure.hausdorffMeasure 1 (frontier causalHardArmOne) ≤ 16 := by
    have himage : causalHardRectangleFrontierParam '' Icc (0 : ℝ) 1 =
        frontier causalHardArmOne := by
      change (fun t => causalHardRectangleAffineHomeomorph
        (squareFrontierParam t)) '' Icc (0 : ℝ) 1 = _
      rw [← Set.image_image, squareFrontierParam_image,
        causalHardRectangleAffineHomeomorph.image_frontier,
        causalHardRectangleAffineHomeomorph_image]
    rw [← himage]
    have hT : LipschitzWith 2
        (causalHardRectangleAffineHomeomorph : Score → Score) := by
      have hs : LipschitzWith 2 (fun x : Score => (2 : ℝ) • x) := by
        simpa using (lipschitzWith_smul (2 : ℝ) :
          LipschitzWith ‖(2 : ℝ)‖₊ (fun x : Score => (2 : ℝ) • x))
      have ha := (isometry_add_left (scorePoint 0 1)).lipschitz.comp hs
      rw [one_mul] at ha
      exact ha
    have hlip : LipschitzOnWith 16 causalHardRectangleFrontierParam
        (Icc (0 : ℝ) 1) := by
      have hc := hT.comp squareFrontierParam_lipschitz
      convert hc.lipschitzOnWith using 1 <;>
        first
          | rfl
          | norm_num [causalHardRectangleFrontierParam, Function.comp_def]
    have h := hlip.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
    simpa [hausdorffMeasure_real] using h
  have hsegment : segment ℝ (scorePoint (-1) 0) (scorePoint 1 0) ⊆
      frontier causalHardArmOne := by
    rw [segment_eq_image_lineMap]
    rintro z ⟨t, ht, rfl⟩
    let y : Score := scorePoint (t - 1 / 2) (-1 / 2)
    have hy : y ∈ frontier (scoreCube (1 / 2 : ℝ)) := by
      rw [mem_frontier_scoreCube_half_iff]
      refine ⟨?_, ?_, Or.inr ?_⟩
      · rw [show y 0 = t - 1 / 2 by simp [y, scorePoint_apply_zero], abs_le]
        constructor <;> linarith [ht.1, ht.2]
      · rw [show y 1 = -1 / 2 by simp [y, scorePoint_apply_one]]
        norm_num
      · rw [show y 1 = -1 / 2 by simp [y, scorePoint_apply_one]]
        norm_num
    have him : causalHardRectangleAffineHomeomorph y ∈
        frontier causalHardArmOne := by
      rw [← causalHardRectangleAffineHomeomorph_image,
        ← causalHardRectangleAffineHomeomorph.image_frontier]
      exact ⟨y, hy, rfl⟩
    convert him using 1
    ext i
    fin_cases i
    · simp [causalHardRectangleAffineHomeomorph, y, AffineMap.lineMap_apply,
        scorePoint_apply_zero]
      ring
    · simp [causalHardRectangleAffineHomeomorph, y, AffineMap.lineMap_apply,
        scorePoint_apply_one]
      norm_num
  have hlower : (2 : ℝ≥0∞) ≤
      Measure.hausdorffMeasure 1 (frontier causalHardArmOne) := by
    calc
      (2 : ℝ≥0∞) = Measure.hausdorffMeasure 1
          (segment ℝ (scorePoint (-1) 0) (scorePoint 1 0)) := by
        rw [hausdorffMeasure_segment]
        simp [edist_dist, dist_scorePoint_same_second]
        norm_num
      _ ≤ _ := measure_mono hsegment
  constructor
  · exact (by norm_num : ENNReal.ofReal (48 : ℝ)⁻¹ ≤ (2 : ℝ≥0∞)).trans hlower
  · exact hupper.trans (by norm_num)

/-- The fixed frontier Hausdorff bounds remain valid for every class envelope
`L ≥ 48`. -/
-- @node: causalHardFrontier_hausdorff_bounds
lemma causalHardFrontier_hausdorff_bounds {L : ℝ} (hL : 48 ≤ L) :
    ENNReal.ofReal L⁻¹ ≤
        Measure.hausdorffMeasure 1 (frontier causalHardArmOne) ∧
      Measure.hausdorffMeasure 1 (frontier causalHardArmOne) ≤
        ENNReal.ofReal L := by
  have hLpos : 0 < L := (by norm_num : (0 : ℝ) < 48).trans_le hL
  have hinv : L⁻¹ ≤ (48 : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hLpos (by norm_num : (0 : ℝ) < 48)).mpr hL
  exact ⟨(ENNReal.ofReal_le_ofReal hinv).trans
      causalHardFrontier_hausdorff_bounds_fixed.1,
    causalHardFrontier_hausdorff_bounds_fixed.2.trans
      (ENNReal.ofReal_le_ofReal hL)⟩

end CausalSmith.Stat.BddUniformLogPenalty
