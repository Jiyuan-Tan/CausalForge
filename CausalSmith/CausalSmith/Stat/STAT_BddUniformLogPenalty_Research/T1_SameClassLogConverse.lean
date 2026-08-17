import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.T2_PointIndexedLogConverse
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AnalyticMeasurability
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.FiniteMaxLowerBound

/-!
# CTY common-map same-class logarithmic converse

The inherited common-map result uses the same finite-packing maximum as the
point-indexed theorem. Its identification of completed expectation with outer
expectation uses Causalean's universal measurability of analytic sets.
-/

open Filter
open scoped ENNReal Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

-- @node: thm:cty-same-class-log-converse
/-- The inherited CTY common-map minimax risk has a positive normalized liminf
at the logarithmic distance rate on the same nonparametric law class.

This is a same-class converse, not a matched two-sided frontier: it asserts no
exact asymptotic constant and does not treat the comparator's additional
Assumption-2 upper-theory subclass as a matching upper bound. -/
theorem cty_same_class_log_converse
    (q : ℕ) (L : ℝ) (hq : 1 ≤ q) (hL : 4 ≤ L) :
    ∃ cCTY : ℝ, 0 < cCTY ∧
      liminf (scaledRisk (fun n => ctyDistanceRisk n q L)) atTop =
        liminf (normalizedRisk (fun n => ctyDistanceRisk n q L)) atTop ∧
      ENNReal.ofReal cCTY ≤
        liminf (normalizedRisk (fun n => ctyDistanceRisk n q L)) atTop := by
  obtain ⟨c, hc, _heq, hlower⟩ :=
    point_indexed_distance_log_converse q L hq hL
  refine ⟨c, hc, ?_, hlower.trans ?_⟩
  · apply le_antisymm
    · apply Filter.liminf_le_liminf
      · exact scaledRisk_eventually_eq_normalizedRisk _ |>.le
      · isBoundedDefault
      · isBoundedDefault
    · apply Filter.liminf_le_liminf
      · exact scaledRisk_eventually_eq_normalizedRisk _ |>.symm.le
      · isBoundedDefault
      · isBoundedDefault
  · apply Filter.liminf_le_liminf
    · filter_upwards [] with n
      unfold normalizedRisk
      gcongr
      exact ctyRisk_ge_pointIndexedRisk n q L
    · isBoundedDefault
    · isBoundedDefault

end CausalSmith.Stat.BddUniformLogPenalty
