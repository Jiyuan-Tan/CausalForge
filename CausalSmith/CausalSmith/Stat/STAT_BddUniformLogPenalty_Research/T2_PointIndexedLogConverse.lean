import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.FiniteMaxLowerBound
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.ClassInclusion

/-!
# Point-indexed logarithmic converse

The headline theorem lower-bounds outer-expectation risk over the exact CTY law
class while permitting arbitrary law-independent point-indexed families whose
fixed-point sections are Borel measurable. No joint regularity in the point is
assumed.
-/

open Filter
open scoped ENNReal Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

-- @node: pointIndexedDistanceRisk_eventually_lower
/-- The finite angular packing gives an eventual positive multiple of the
frontier rate uniformly over all point-indexed rules. -/
lemma pointIndexedDistanceRisk_eventually_lower
    (q : ℕ) (L : ℝ) (hq : 1 ≤ q) (hL : 4 ≤ L) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      ENNReal.ofReal (c * frontierRate n) ≤ pointIndexedDistanceRisk n q L := by
  obtain ⟨c, hc, N, hN⟩ := packing_finite_max_lower_bound q L hq hL
  refine ⟨c, hc, N, ?_⟩
  intro n hn
  unfold pointIndexedDistanceRisk
  apply le_iInf
  intro rho
  apply le_iInf
  intro hrho
  obtain ⟨P, M, centers, hP, hcenters, hmeas, hlower⟩ := hN n hn rho hrho
  refine hlower.trans ?_
  have hpoint : finitePackingLoss rho P centers ≤ boundaryLoss rho P := by
    intro w
    unfold finitePackingLoss boundaryLoss
    apply iSup_le
    intro j
    exact le_iSup_of_le (centers j) (le_iSup_of_le (hcenters j) le_rfl)
  have houter :
      (∫⁻ w, finitePackingLoss rho P centers w ∂sampleLaw P n) ≤
        MeasureTheory.outerLIntegral (sampleLaw P n) (boundaryLoss rho P) :=
    MeasureTheory.lintegral_le_outerLIntegral_of_measurable_le hpoint
  exact houter.trans (le_iSup_of_le P (le_iSup_of_le hP le_rfl))

-- @node: thm:point-indexed-distance-log-converse
/-- For every `q ≥ 1` and `L ≥ 4`, the point-indexed outer-expectation minimax
risk has a positive normalized liminf at the logarithmic distance rate.

This is only a lower bound on the full CTY class: no exact constant, matching
upper bound, Assumption-2 upper theorem, or two-sided frontier is asserted. -/
theorem point_indexed_distance_log_converse
    (q : ℕ) (L : ℝ) (hq : 1 ≤ q) (hL : 4 ≤ L) :
    ∃ cPI : ℝ, 0 < cPI ∧
      liminf
          (scaledRisk (fun n => pointIndexedDistanceRisk n q L)) atTop =
        liminf
          (normalizedRisk (fun n => pointIndexedDistanceRisk n q L)) atTop ∧
      ENNReal.ofReal cPI ≤
        liminf
          (normalizedRisk (fun n => pointIndexedDistanceRisk n q L)) atTop := by
  obtain ⟨c, hc, N, hN⟩ := pointIndexedDistanceRisk_eventually_lower q L hq hL
  refine ⟨c, hc, ?_, ?_⟩
  · apply le_antisymm
    · apply Filter.liminf_le_liminf
      · exact scaledRisk_eventually_eq_normalizedRisk _ |>.le
      · isBoundedDefault
      · isBoundedDefault
    · apply Filter.liminf_le_liminf
      · exact scaledRisk_eventually_eq_normalizedRisk _ |>.symm.le
      · isBoundedDefault
      · isBoundedDefault
  · apply le_liminf_of_le
    · isBoundedDefault
    · filter_upwards [eventually_ge_atTop (max N 2)] with n hn
      have hnN : N ≤ n := le_trans (le_max_left _ _) hn
      have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
      have hrate0 : ENNReal.ofReal (frontierRate n) ≠ 0 := by
        simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using frontierRate_pos hn2
      unfold normalizedRisk
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl hrate0) (Or.inl ENNReal.ofReal_ne_top)).2
      rw [← ENNReal.ofReal_mul hc.le]
      exact hN n hnN

end CausalSmith.Stat.BddUniformLogPenalty
