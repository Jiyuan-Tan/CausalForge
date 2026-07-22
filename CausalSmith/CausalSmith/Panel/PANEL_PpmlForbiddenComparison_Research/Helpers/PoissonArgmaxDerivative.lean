import Causalean.Stat.MEstimation.FinitePoissonDerivative
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.WeightedFWL

/-! Panel specialization of the shared one-cell finite-Poisson derivative theorem. -/

open scoped BigOperators
open Module Filter Topology
open Causalean.Stat

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

-- @node: betaStar_update_hasDerivAt
/-- Perturbing one treated collapsed cell differentiates the selected PPML
treatment coefficient by its weighted-FWL residual contribution. -/
lemma betaStar_update_hasDerivAt (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hC : C.Nonempty) (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (k : Cohort T) (hk : k ∈ C) (s : Fin T) (hks : treatmentIndicator T k s = 1)
    (hRank : CollapsedDesignRank T C pi)
    (henergy : 0 < ∑ z : SupportedCell T C,
      meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
        (weightedFWLResidual T C hT hC pi barB gamma delta z) ^ 2) :
    HasDerivAt
      (fun x ↦ betaStar T C pi barB gamma (Function.update delta (k, s) x))
      (limitingCellMass T pi k * untreatedMean T barB gamma k s *
        Real.exp (delta (k, s)) *
          weightedFWLResidual T C hT hC pi barB gamma delta (⟨k, hk⟩, s) /
        (∑ z : SupportedCell T C,
          meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
            (weightedFWLResidual T C hT hC pi barB gamma delta z) ^ 2))
      (delta (k, s)) := by
  classical
  let q : SupportedCell T C → ℝ := fun z ↦ limitingCellMass T pi z.1.1
  let m : SupportedCell T C → ℝ := fun z ↦
    observedCohortMean T barB gamma delta z.1.1 z.2
  let A := collapsedDesignMap T C
  let j : SupportedCell T C := (⟨k, hk⟩, s)
  let B := untreatedMean T barB gamma k s
  let betaDot := limitingCellMass T pi k * untreatedMean T barB gamma k s *
    Real.exp (delta (k, s)) *
      weightedFWLResidual T C hT hC pi barB gamma delta (⟨k, hk⟩, s) /
    (∑ z : SupportedCell T C,
      meanFWLWeight T C pi barB gamma delta (z.1.1, z.2) *
        (weightedFWLResidual T C hT hC pi barB gamma delta z) ^ 2)
  letI : Nonempty (SupportedCell T C) :=
    ⟨(⟨hC.choose, hC.choose_spec⟩, ⟨0, hT⟩)⟩
  have hq : ∀ z, 0 < q z := fun z ↦
    div_pos (pi z.1.1).property.1 (by exact_mod_cast hT)
  have hm : ∀ z, 0 < m z := fun z ↦
    mul_pos (mul_pos (barB z.1.1).property (Real.exp_pos _)) (Real.exp_pos _)
  have hB : 0 < B := mul_pos (barB k).property (Real.exp_pos _)
  have hA : Function.Injective A := by
    intro x y hxy
    by_contra hne
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hr := hRank (x - y) hsub
    have hmap : A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hzero :
        (∑ g ∈ C, ∑ t : Fin T,
          limitingCellMass T pi g *
            (collapsedIndex T C (collapsedRegressor T C g t) (x - y)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro g hg
      apply Finset.sum_eq_zero
      intro t ht
      have hz := congrFun hmap (⟨g, hg⟩, t)
      change collapsedIndex T C (collapsedRegressor T C g t) (x - y) = 0 at hz
      rw [hz]
      simp
    linarith
  have hmeans (x : ℝ) :
      (fun z : SupportedCell T C ↦
        observedCohortMean T barB gamma (Function.update delta (k, s) x) z.1.1 z.2) =
      expCellUpdatedMean m j B x := by
    funext z
    by_cases hz : z = j
    · subst z
      simp [observedCohortMean, expCellUpdatedMean, m, j, B, hks]
    · have hcell : (z.1.1, z.2) ≠ (k, s) := by
        intro heq
        rcases z with ⟨⟨g, hg⟩, t⟩
        simp only at heq
        have hgk : g = k := congrArg Prod.fst heq
        have hts : t = s := congrArg Prod.snd heq
        subst g
        subst t
        exact hz rfl
      simp [observedCohortMean, expCellUpdatedMean, m, j, B, hz, hcell]
  have hmean0 : expCellUpdatedMean m j B (delta (k, s)) = m := by
    rw [← hmeans]
    funext z
    simp [m]
  have hprojection0 :
      maximizerOrZero
          (finitePoissonObjective q (expCellUpdatedMean m j B (delta (k, s))) A) =
        collapsedPopulationProjection T C pi barB gamma delta := by
    unfold collapsedPopulationProjection
    apply congrArg maximizerOrZero
    funext theta
    rw [limitingCriterion_eq_finitePoissonObjective]
    simp only [q, A]
    rw [hmean0]
  have hbeta : ∀ v : CollapsedParameter T C,
      (∀ d : CollapsedParameter T C,
        ∑ z, q z * A d z *
          ((if z = j then B * Real.exp (delta (k, s)) else 0) -
            Real.exp
              (A (maximizerOrZero
                (finitePoissonObjective q (expCellUpdatedMean m j B (delta (k, s))) A)) z) *
              A v z) = 0) →
      v.2 = betaDot := by
    intro v hv
    apply linearizedScore_snd_eq_weightedFWL T C hT hC pi barB gamma delta k hk s v
      henergy
    intro d
    have hs := hv d
    simpa [q, A, j, B, betaDot, fittedMean, hprojection0] using hs
  have hg := finitePoissonObjective_expCell_argmax_snd_hasDerivAt
    q m A j B (delta (k, s)) betaDot hq hm hB hA hbeta
  have hfun (x : ℝ) :
      betaStar T C pi barB gamma (Function.update delta (k, s) x) =
        (maximizerOrZero (finitePoissonObjective q (expCellUpdatedMean m j B x) A)).2 := by
    unfold betaStar collapsedPopulationProjection
    apply congrArg (fun f : CollapsedParameter T C → ℝ ↦ (maximizerOrZero f).2)
    funext theta
    rw [limitingCriterion_eq_finitePoissonObjective]
    simp only [q, A]
    rw [hmeans]
  change HasDerivAt _ betaDot (delta (k, s))
  apply hg.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall hfun

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

