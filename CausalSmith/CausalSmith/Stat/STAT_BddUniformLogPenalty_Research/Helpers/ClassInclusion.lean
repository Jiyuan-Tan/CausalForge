import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Basic
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularPackingTheorem
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation
import Causalean.Mathlib.CondDistrib
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Strict inclusion of distance decision classes

The common-map class embeds in the point-indexed class by taking every section
equal to the common map. Strictness is witnessed by a coordinate-valued rule on
the square-support product law.
-/

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Every common-map rule is a point-indexed rule with constant sections. -/
lemma ctyClass_subset_piClass (n q : ℕ) (L : ℝ) :
    CtyDistanceDecisionClass n q L ⊆ PointIndexedDecisionClass n q L := by
  rintro rho ⟨T, hT⟩
  refine ⟨{ map := fun _x => T.map, section_measurable := fun _x => T.measurable }, ?_⟩
  intro P hP w x hx
  exact hT P hP w x hx

/-- The point-indexed witness that returns the first coordinate of the query
point, independently of the data. -/
def coordinateWitnessRule (n : ℕ) : RuleFun n :=
  fun _w x => x 0

/-- For an admissible square-support law, the coordinate witness has
measurable fixed sections but cannot be represented by one common distance map. -/
lemma piClass_not_subset_ctyClass
    (n q : ℕ) (L : ℝ) (hn : 1 ≤ n) (hq : 1 ≤ q) (hL : 4 ≤ L) :
    coordinateWitnessRule n ∈ PointIndexedDecisionClass n q L ∧
      coordinateWitnessRule n ∉ CtyDistanceDecisionClass n q L := by
  constructor
  · let T : PIRule n :=
      { map := fun x _w => x 0
        section_measurable := fun _x => measurable_const }
    refine ⟨T, ?_⟩
    intro P hP w x hx
    rfl
  · rintro ⟨T, hT⟩
    obtain ⟨c0, c1, cwLow, cwHigh, cRadial, alpha, hc0, hc1, hcwLow,
      hcwHigh, hcRadial, halpha, halpha8, N, hpack⟩ :=
      cty_support_boundary_angular_packing q L hq hL
    obtain ⟨M, width, mass, centers, laws, values, hM, hwidth,
      hcenters, hsep, hdisjoint, hlaws, hsupports, hmass, hlocal,
      hoff, hvalues, hvalueSep, hradial, houtside, hkl⟩ :=
      hpack (max N 2) (le_max_left _ _)
    let omega : Fin M → Bool := fun _ => false
    let P := laws omega
    let x₀ : Score := scorePoint (-1 / 4) (-1 / 2)
    let x₁ : Score := scorePoint (1 / 4) (-1 / 2)
    let z : Score := scorePoint 0 (-1 / 2)
    let w : Sample n := fun _ => (0, z)
    have hx₀ : x₀ ∈ frontier P.support := by
      rw [hsupports omega]
      exact lowerEdgePoint_mem_frontier _ (by norm_num)
    have hx₁ : x₁ ∈ frontier P.support := by
      rw [hsupports omega]
      exact lowerEdgePoint_mem_frontier _ (by norm_num)
    have heq : distanceData n w x₀ = distanceData n w x₁ := by
      funext i
      apply Prod.ext
      · rfl
      · dsimp [distanceData, w, z, x₀, x₁]
        rw [dist_scorePoint_same_second, dist_scorePoint_same_second]
        norm_num
    have h0 := hT P (hlaws omega) w x₀ hx₀
    have h1 := hT P (hlaws omega) w x₁ hx₁
    rw [heq] at h0
    have : x₀ 0 = x₁ 0 := by
      simpa [coordinateWitnessRule] using h0.trans h1.symm
    norm_num [x₀, x₁, scorePoint_apply_zero] at this

-- @node: lem:common-map-strict-in-point-indexed
/-- For every positive sample size in the stated CTY regime, the inherited
common-map distance class is a proper subset of the sectionwise-Borel
point-indexed class. -/
lemma common_map_strict_in_point_indexed
    (n q : ℕ) (L : ℝ) (hn : 1 ≤ n) (hq : 1 ≤ q) (hL : 4 ≤ L) :
    CtyDistanceDecisionClass n q L ⊂ PointIndexedDecisionClass n q L := by
  refine ⟨ctyClass_subset_piClass n q L, ?_⟩
  intro hreverse
  exact (piClass_not_subset_ctyClass n q L hn hq hL).2
    (hreverse (piClass_not_subset_ctyClass n q L hn hq hL).1)

end CausalSmith.Stat.BddUniformLogPenalty
