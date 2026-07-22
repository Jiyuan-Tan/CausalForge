import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Projection
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.WeightedFWL
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.PoissonArgmaxDerivative
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Sharp effect-derivative and forbidden-cell sign characterization. -/

open scoped BigOperators

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

/-- The positive residual-energy denominator in the PPML derivative formula. -/
noncomputable def fwlEnergy (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ) : ℝ :=
  ∑ z : SupportedCell T C,
    limitingCellMass T pi z.1.1 * fittedMean T C pi barB gamma delta z.1.1 z.2 *
      (weightedFWLResidual T C hT hC pi barB gamma delta z) ^ 2
  -- @realizes Ecal(delta)(PPML FWL residual-energy denominator)

-- @node: fwlEnergy_pos_of_collapsedDesignRank
/-- Full collapsed rank forces the residualized treatment regressor to have
strictly positive fitted-mean-weighted energy. -/
lemma fwlEnergy_pos_of_collapsedDesignRank (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (hRank : CollapsedDesignRank T C pi) :
    0 < fwlEnergy T C hT hC pi barB gamma delta := by
  classical
  let W := weightedFWLResidual T C hT hC pi barB gamma delta
  let rho := rhoStar T C hT hC pi barB gamma delta
  let a : CollapsedParameter T C := (fun j => -rho j, 1)
  have ha : a ≠ 0 := by
    intro ha0
    have := congrArg Prod.snd ha0
    norm_num [a] at this
  have hnonneg : 0 ≤ fwlEnergy T C hT hC pi barB gamma delta := by
    unfold fwlEnergy
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg
        (mul_nonneg (le_of_lt (div_pos (pi z.1.1).property.1 (by exact_mod_cast hT)))
          (le_of_lt (Real.exp_pos _)))
        (sq_nonneg _)
  by_contra hnpos
  have henergy : fwlEnergy T C hT hC pi barB gamma delta = 0 :=
    le_antisymm (le_of_not_gt hnpos) hnonneg
  have hW (z : SupportedCell T C) : W z = 0 := by
    have hterm :
        limitingCellMass T pi z.1.1 *
            fittedMean T C pi barB gamma delta z.1.1 z.2 * (W z) ^ 2 ≤
          fwlEnergy T C hT hC pi barB gamma delta := by
      unfold fwlEnergy
      change _ * (W z) ^ 2 ≤ ∑ y, _ * (W y) ^ 2
      let f : SupportedCell T C → ℝ := fun y =>
        limitingCellMass T pi y.1.1 *
          fittedMean T C pi barB gamma delta y.1.1 y.2 * (W y) ^ 2
      have hs := Finset.single_le_sum (s := Finset.univ) (f := f)
        (fun y _ => mul_nonneg
          (mul_nonneg (le_of_lt (div_pos (pi y.1.1).property.1 (by exact_mod_cast hT)))
            (le_of_lt (Real.exp_pos _)))
          (sq_nonneg _)) (Finset.mem_univ z)
      simpa [f] using hs
    rw [henergy] at hterm
    have hweight : 0 < limitingCellMass T pi z.1.1 *
        fittedMean T C pi barB gamma delta z.1.1 z.2 :=
      mul_pos (div_pos (pi z.1.1).property.1 (by exact_mod_cast hT)) (Real.exp_pos _)
    have hsquare : (W z) ^ 2 = 0 := by
      apply le_antisymm
      · by_contra hs
        have hp := mul_pos hweight (lt_of_not_ge hs)
        exact (not_lt_of_ge hterm) hp
      · exact sq_nonneg _
    exact sq_eq_zero_iff.mp hsquare
  have hindex (z : SupportedCell T C) :
      collapsedIndex T C (collapsedRegressor T C z.1.1 z.2) a = W z := by
    rw [show W z = weightedFWLResidual T C hT hC pi barB gamma delta z by rfl]
    rw [weightedFWLResidual_eq_rhoStar T C hT hC pi barB gamma delta
      z.1.1 z.1.2 z.2]
    simp only [collapsedIndex, collapsedRegressor, a, rho, mul_one]
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
    ring
  have hrank := hRank a ha
  have hzero :
      (∑ g ∈ C, ∑ t : Fin T,
        limitingCellMass T pi g *
          (collapsedIndex T C (collapsedRegressor T C g t) a) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro g hg
    apply Finset.sum_eq_zero
    intro t ht
    rw [hindex (⟨g, hg⟩, t), hW (⟨g, hg⟩, t)]
    simp
  rw [hzero] at hrank
  exact (lt_irrefl 0) hrank

-- @node: thm:sharp-ppml-forbidden-sign
/-- A treated effect moves beta with exactly the sign of its pseudo-true weighted FWL residual. -/
theorem sharp_ppml_forbidden_sign (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (k : Cohort T) (hk : k ∈ C) (s : Fin T) (hks : treatmentIndicator T k s = 1)
    (hRank : CollapsedDesignRank T C pi) :
    let W := weightedFWLResidual T C hT hC pi barB gamma delta (⟨k, hk⟩, s)
    let denominator := fwlEnergy T C hT hC pi barB gamma delta
    let derivative := limitingCellMass T pi k * untreatedMean T barB gamma k s *
      Real.exp (delta (k, s)) * W / denominator
    HasDerivAt
      (fun x => betaStar T C pi barB gamma (Function.update delta (k, s) x))
      derivative (delta (k, s)) ∧
    0 < denominator ∧
    (derivative < 0 ↔ W < 0) ∧
    (derivative = 0 ↔ W = 0) ∧
    (0 < derivative ↔ 0 < W) := by
  dsimp only
  have hdenominator := fwlEnergy_pos_of_collapsedDesignRank
    T C hT hC pi barB gamma delta hRank
  have hmass : 0 < limitingCellMass T pi k :=
    div_pos (pi k).property.1 (by exact_mod_cast hT)
  have hbaseline : 0 < untreatedMean T barB gamma k s := by
    exact mul_pos (barB k).property (Real.exp_pos _)
  have hprefactor : 0 < limitingCellMass T pi k * untreatedMean T barB gamma k s *
      Real.exp (delta (k, s)) / fwlEnergy T C hT hC pi barB gamma delta :=
    div_pos (mul_pos (mul_pos hmass hbaseline) (Real.exp_pos _)) hdenominator
  refine ⟨?_, hdenominator, ?_, ?_, ?_⟩
  · have henergy : 0 < ∑ z : SupportedCell T C,
        meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
          (weightedFWLResidual T C hT hC pi barB gamma delta z) ^ 2 := by
      simpa [fwlEnergy, meanFWLWeight] using hdenominator
    simpa [fwlEnergy, meanFWLWeight] using
      betaStar_update_hasDerivAt T C hT hC pi barB gamma delta k hk s hks hRank henergy
  · rw [show limitingCellMass T pi k * untreatedMean T barB gamma k s *
        Real.exp (delta (k, s)) *
          weightedFWLResidual T C hT hC pi barB gamma delta (⟨k, hk⟩, s) /
          fwlEnergy T C hT hC pi barB gamma delta =
        (limitingCellMass T pi k * untreatedMean T barB gamma k s *
          Real.exp (delta (k, s)) / fwlEnergy T C hT hC pi barB gamma delta) *
          weightedFWLResidual T C hT hC pi barB gamma delta (⟨k, hk⟩, s) by ring]
    constructor
    · intro hneg
      by_contra hW
      exact (not_lt_of_ge (mul_nonneg hprefactor.le (le_of_not_gt hW))) hneg
    · exact mul_neg_of_pos_of_neg hprefactor
  · rw [show limitingCellMass T pi k * untreatedMean T barB gamma k s *
        Real.exp (delta (k, s)) *
          weightedFWLResidual T C hT hC pi barB gamma delta (⟨k, hk⟩, s) /
          fwlEnergy T C hT hC pi barB gamma delta =
        (limitingCellMass T pi k * untreatedMean T barB gamma k s *
          Real.exp (delta (k, s)) / fwlEnergy T C hT hC pi barB gamma delta) *
          weightedFWLResidual T C hT hC pi barB gamma delta (⟨k, hk⟩, s) by ring]
    exact mul_eq_zero_iff_left (ne_of_gt hprefactor)
  · rw [show limitingCellMass T pi k * untreatedMean T barB gamma k s *
        Real.exp (delta (k, s)) *
          weightedFWLResidual T C hT hC pi barB gamma delta (⟨k, hk⟩, s) /
          fwlEnergy T C hT hC pi barB gamma delta =
        (limitingCellMass T pi k * untreatedMean T barB gamma k s *
          Real.exp (delta (k, s)) / fwlEnergy T C hT hC pi barB gamma delta) *
          weightedFWLResidual T C hT hC pi barB gamma delta (⟨k, hk⟩, s) by ring]
    exact (mul_pos_iff_of_pos_left hprefactor)

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
