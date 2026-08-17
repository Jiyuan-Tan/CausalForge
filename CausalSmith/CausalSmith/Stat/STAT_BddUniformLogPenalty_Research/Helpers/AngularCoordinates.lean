import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularGrid
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.Polar

/-!
# Coordinate bridge for the angular packing

This file relates the Euclidean-space representation of CTY scores to the
ordinary product plane used by Mathlib's polar-coordinate integration lemmas.
-/

open MeasureTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The two ordinary real coordinates of a Euclidean CTY score. -/
-- @node: scoreCoordinates
def scoreCoordinates (x : Score) : ℝ × ℝ :=
  (x 0, x 1)

/-- Coordinate extraction preserves planar Lebesgue measure. -/
-- @node: scoreCoordinates_measurePreserving
lemma scoreCoordinates_measurePreserving :
    MeasurePreserving scoreCoordinates (volume : Measure Score)
      (volume : Measure (ℝ × ℝ)) := by
  exact (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

/-- Coordinate extraction is a measurable embedding as well as
measure-preserving. -/
-- @node: scoreCoordinates_measurableEmbedding
lemma scoreCoordinates_measurableEmbedding :
    MeasurableEmbedding scoreCoordinates := by
  exact ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    (MeasurableEquiv.finTwoArrow (α := ℝ))).measurableEmbedding

/-- Coordinate extraction commutes with subtraction. -/
-- @node: scoreCoordinates_sub
lemma scoreCoordinates_sub (x y : Score) :
    scoreCoordinates (x - y) = scoreCoordinates x - scoreCoordinates y := by
  ext <;> simp [scoreCoordinates]

/-- The explicit planar radius of the coordinate difference is exactly the
Euclidean distance between the corresponding CTY scores. -/
-- @node: planarRadius_scoreCoordinates_sub
lemma planarRadius_scoreCoordinates_sub (x y : Score) :
    planarRadius (scoreCoordinates x - scoreCoordinates y) = dist x y := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp [planarRadius, scoreCoordinates, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs]

/-- Relative to a lower-edge grid center, membership in its Euclidean closed
ball is the same as the corresponding planar-radius inequality. -/
-- @node: mem_angularGrid_closedBall_iff_planarRadius
lemma mem_angularGrid_closedBall_iff_planarRadius
    {M : ℕ} (j : Fin M) (w : ℝ) (x : Score) :
    x ∈ Metric.closedBall (angularGridCenter M j) w ↔
      planarRadius
        (scoreCoordinates x - scoreCoordinates (angularGridCenter M j)) ≤ w := by
  rw [Metric.mem_closedBall, planarRadius_scoreCoordinates_sub]

/-- A sufficiently small ball around a lower-edge grid center is cut by the
packing square exactly along the horizontal diameter: in centered planar
coordinates, its packing cell is the closed upper half-disc. -/
-- @node: mem_angularGrid_packingCell_iff_closedUpperHalfDisc
lemma mem_angularGrid_packingCell_iff_closedUpperHalfDisc
    {M : ℕ} (j : Fin M) {w : ℝ} (hw : w ≤ 1 / 4) (x : Score) :
    x ∈ Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2) ↔
      0 ≤ (scoreCoordinates x - scoreCoordinates (angularGridCenter M j)).2 ∧
      planarRadius
        (scoreCoordinates x - scoreCoordinates (angularGridCenter M j)) ≤ w := by
  rw [mem_inter_iff, mem_angularGrid_closedBall_iff_planarRadius]
  constructor
  · rintro ⟨hr, hsquare⟩
    constructor
    · have hcoord := (abs_le.mp (hsquare (1 : Fin 2))).1
      simp [scoreCoordinates, angularGridCenter_apply_one] at hcoord ⊢
      linarith
    · exact hr
  · rintro ⟨hy, hr⟩
    refine ⟨hr, ?_⟩
    have hdist : dist x (angularGridCenter M j) ≤ w := by
      rw [← planarRadius_scoreCoordinates_sub]
      exact hr
    intro i
    have hnorm : |x i - angularGridCenter M j i| ≤ w := by
      have hle : |x i - angularGridCenter M j i| ≤
          dist x (angularGridCenter M j) := by
        simpa [dist_eq_norm, Real.norm_eq_abs] using
          (PiLp.norm_apply_le (x - angularGridCenter M j) i)
      exact hle.trans hdist
    fin_cases i
    · change |x 0| ≤ (1 / 2 : ℝ)
      have hnorm0 : |x 0 - angularGridCenter M j 0| ≤ w := by
        simpa using hnorm
      have hc := angularGridCenter_first_abs_lt_quarter M j
      rw [abs_le] at hnorm0 ⊢
      rw [abs_lt] at hc
      constructor <;> linarith
    · change |x 1| ≤ (1 / 2 : ℝ)
      have hnorm1 : |x 1 - angularGridCenter M j 1| ≤ w := by
        simpa using hnorm
      rw [angularGridCenter_apply_one] at hnorm1
      rw [abs_le] at hnorm1 ⊢
      change 0 ≤ x 1 - angularGridCenter M j 1 at hy
      rw [angularGridCenter_apply_one] at hy
      constructor <;> linarith

end CausalSmith.Stat.BddUniformLogPenalty
