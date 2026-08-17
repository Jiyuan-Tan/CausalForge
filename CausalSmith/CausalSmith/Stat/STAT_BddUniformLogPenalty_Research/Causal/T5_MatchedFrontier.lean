import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.T3_A1A2PointIndexedConverse
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.T4_WinsorizedUpper

/-!
# Matched causal frontier

This theorem combines the point-indexed converse with the explicit estimator.
It is about the exact `P₁₂(p,ν,L)` class, not the distinct full
`P_NP(L,q)` support-boundary problem.
-/

open Filter
open scoped ENNReal Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

-- @node: a1a2OuterRisk_le_stabilizedLocalPolynomialOuterRisk
/-- The minimax outer risk is bounded by the outer risk of the explicit
stabilized local-polynomial rule once its frontier bandwidth is positive. -/
lemma a1a2OuterRisk_le_stabilizedLocalPolynomialOuterRisk
    (n p : ℕ) (ν L : ℝ) (hn : 2 ≤ n) :
    a1a2OuterRisk n p ν L ≤ stabilizedLocalPolynomialOuterRisk n p ν L := by
  unfold a1a2OuterRisk stabilizedLocalPolynomialOuterRisk
  refine (iInf_le (fun rho : A1A2RuleFun n =>
    ⨅ (_hrho : rho ∈ A1A2PointIndexedDecisionClass n p ν L),
      ⨆ P : A1A2Law, ⨆ (_hP : A1A2Class p ν L P),
        MeasureTheory.outerLIntegral (causalSampleLaw P n)
          (a1a2BoundaryLoss rho P))
    (stabilizedLocalPolynomial n p L (frontierRate n))).trans ?_
  exact iInf_le_of_le
    (stabilizedLocalPolynomial_mem n p ν L (frontierRate n) (frontierRate_pos hn))
    (le_refl _)

-- @node: stabilizedLocalPolynomial_normalizedRisk_limsup_le
/-- An eventual constant-times-frontier-rate bound for the explicit rule gives
the corresponding normalized limsup bound. -/
lemma stabilizedLocalPolynomial_normalizedRisk_limsup_le
    (p : ℕ) (ν L C : ℝ) (hC : 0 < C) (N : ℕ)
    (hupper : ∀ n : ℕ, N ≤ n →
      stabilizedLocalPolynomialOuterRisk n p ν L ≤
        ENNReal.ofReal (C * frontierRate n)) :
    limsup (normalizedRisk
      (fun n => stabilizedLocalPolynomialOuterRisk n p ν L)) atTop ≤
        ENNReal.ofReal C := by
  apply Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (2 : ℕ)] with n hnN hn2
  unfold normalizedRisk
  calc
    stabilizedLocalPolynomialOuterRisk n p ν L /
        ENNReal.ofReal (frontierRate n) ≤
      ENNReal.ofReal (C * frontierRate n) /
        ENNReal.ofReal (frontierRate n) := by gcongr; exact hupper n hnN
    _ = ENNReal.ofReal C := by
      rw [ENNReal.ofReal_mul hC.le]
      have hr0 : ENNReal.ofReal (frontierRate n) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (frontierRate_pos hn2)).ne'
      rw [ENNReal.mul_div_cancel_right hr0 ENNReal.ofReal_ne_top]

-- @node: thm:cty-a1-a2-winsorized-matched-frontier
/-- The outer-expected minimax rate on the exact Euclidean/uniform-kernel
causal class is `a_n`, for every `L ≥ L₀(p)`.  The three cited CTY interfaces
remain explicit antecedents.  The conclusion contains exactly the lower and
upper frontier for `a1a2OuterRisk` and the explicit stabilized-estimator upper
bound. -/
theorem cty_a1_a2_winsorized_matched_frontier
    (p : ℕ) :
    ∃ L0 : ℝ, 48 ≤ L0 ∧ ∀ ν : ℝ, 2 ≤ ν → ∀ L : ℝ, L0 ≤ L →
      CtyDistanceIdentification p ν L →
      CtyUniformFirstOrderBias p L →
      CtyExpectedLocalPolynomialMaximalBounds p ν L →
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ENNReal.ofReal c ≤
          liminf (normalizedRisk (fun n => a1a2OuterRisk n p ν L)) atTop ∧
        liminf (normalizedRisk (fun n => a1a2OuterRisk n p ν L)) atTop ≤
          limsup (normalizedRisk (fun n => a1a2OuterRisk n p ν L)) atTop ∧
        limsup (normalizedRisk (fun n => a1a2OuterRisk n p ν L)) atTop ≤
          ENNReal.ofReal C ∧
        limsup (normalizedRisk
          (fun n => stabilizedLocalPolynomialOuterRisk n p ν L)) atTop ≤
            ENNReal.ofReal C := by
  rcases cty_a1_a2_point_indexed_log_converse p with ⟨L0, hL0, hconv⟩
  refine ⟨max L0 4, hL0.trans (le_max_left _ _), ?_⟩
  intro ν hν L hL hId hBias hMax
  have hL0L : L0 ≤ L := (le_max_left L0 4).trans hL
  have h4L : 4 ≤ L := (le_max_right L0 4).trans hL
  rcases hconv ν hν L hL0L with ⟨c, hc, _hscale, hlower, _hfixed⟩
  rcases cty_a1_a2_winsorized_expected_outer_upper p ν L hν h4L hId hBias hMax with
    ⟨C0, hC0, N, hupper⟩
  let C := max C0 c
  have hC0C : C0 ≤ C := le_max_left _ _
  have hcC : c ≤ C := le_max_right _ _
  have hexplicit :
      limsup (normalizedRisk
        (fun n => stabilizedLocalPolynomialOuterRisk n p ν L)) atTop ≤
          ENNReal.ofReal C0 :=
    stabilizedLocalPolynomial_normalizedRisk_limsup_le p ν L C0 hC0 N hupper
  have hrisk_eventually :
      (fun n => normalizedRisk (fun m => a1a2OuterRisk m p ν L) n) ≤ᶠ[atTop]
        (fun n => normalizedRisk
          (fun m => stabilizedLocalPolynomialOuterRisk m p ν L) n) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    unfold normalizedRisk
    gcongr
    exact a1a2OuterRisk_le_stabilizedLocalPolynomialOuterRisk n p ν L hn
  have hrisk_explicit :
      limsup (normalizedRisk (fun n => a1a2OuterRisk n p ν L)) atTop ≤
        limsup (normalizedRisk
          (fun n => stabilizedLocalPolynomialOuterRisk n p ν L)) atTop := by
    exact Filter.limsup_le_limsup hrisk_eventually
  refine ⟨c, C, hc, hcC, hlower,
    Filter.liminf_le_limsup, ?_, ?_⟩
  · exact hrisk_explicit.trans (hexplicit.trans (ENNReal.ofReal_le_ofReal hC0C))
  · exact hexplicit.trans (ENNReal.ofReal_le_ofReal hC0C)

end CausalSmith.Stat.BddUniformLogPenalty
