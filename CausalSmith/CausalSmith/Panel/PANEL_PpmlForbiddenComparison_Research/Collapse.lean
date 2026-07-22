import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Projection
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.FiniteCollapse

/-! Exact unit-FE collapse and convergence to the limiting collapsed projection. -/

open scoped BigOperators Topology
open Filter
open Causalean.Stat

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

/-- The selected maximizer of the finite collapsed criterion. -/
noncomputable def finiteCollapsedProjection (T : ℕ) (C : Finset (Cohort T)) {N : ℕ}
    (G : Fin N → Cohort T) (b : Fin N → PosReal) (gamma : Fin T → ℝ)
    (delta : Cell T → ℝ) : CollapsedParameter T C :=
  maximizerOrZero (finiteCollapsedCriterion T C G b gamma delta)

-- @node: lem:unit-fe-collapse
/-- The unit-FE and collapsed criteria have the same beta, and these betas converge. -/
lemma unit_fe_collapse (T : ℕ) (C : Finset (Cohort T))
    (hHorizon : ValidPanelHorizon T) -- @realizes T(standing 4 ≤ T premise)
    (hSupport : ValidCohortSupport T C) -- @realizes C(paper cohort-support premise)
    (Omega : ℕ → Type*) (P : ∀ N, SamplingLaw (Omega N))
    (Y : ∀ N, Fin N → Fin T → Fin 2 → Omega N → ℝ)
    (G : ∀ N, Fin N → Cohort T) (b : ∀ N, Fin N → PosReal)
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (hGSupport : ∀ N i, G N i ∈ C) -- @realizes G_i(every deterministic label lies in C)
    (hShare : CohortShareLimit T C G pi)
    (hMean : UnitUntreatedExponentialMean T Omega P Y b gamma)
    (hBaseline : WithinCohortBaselineLimit T C G b barB)
    (hEffects : ProportionalEffects T Omega P Y G delta)
    (hRank : CollapsedDesignRank T C pi) :
    (∀ N, C.card ≤ N →
      IsUniqueGlobalMax (unitCriterion T N (G N) (b N) gamma delta)
        (maximizerOrZero (unitCriterion T N (G N) (b N) gamma delta)) ∧
      IsUniqueGlobalMax (finiteCollapsedCriterion T C (G N) (b N) gamma delta)
        (finiteCollapsedProjection T C (G N) (b N) gamma delta) ∧
      betaNStar T N (G N) (b N) gamma delta =
        (finiteCollapsedProjection T C (G N) (b N) gamma delta).2) ∧
    Tendsto (fun N => betaNStar T N (G N) (b N) gamma delta) atTop
      (nhds (betaStar T C pi barB gamma delta)) ∧
    ∀ N (b' : Fin N → PosReal), C.card ≤ N →
      (∀ g ∈ C, withinCohortBaseline T (G N) b' g =
        withinCohortBaseline T (G N) (b N) g) →
      betaNStar T N (G N) b' gamma delta = betaNStar T N (G N) (b N) gamma delta := by
  classical
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hHorizon
  have hC : C.Nonempty := ⟨⊤, hSupport.1⟩
  have hfinite : ∀ N, C.card ≤ N →
      IsUniqueGlobalMax (unitCriterion T N (G N) (b N) gamma delta)
          (maximizerOrZero (unitCriterion T N (G N) (b N) gamma delta)) ∧
        IsUniqueGlobalMax (finiteCollapsedCriterion T C (G N) (b N) gamma delta)
          (finiteCollapsedProjection T C (G N) (b N) gamma delta) ∧
        betaNStar T N (G N) (b N) gamma delta =
          (finiteCollapsedProjection T C (G N) (b N) gamma delta).2 := by
    intro N hcard
    have harray := hShare.1 N hcard
    simpa [finiteCollapsedProjection, betaNStar] using
      finite_unit_and_collapsed_unique_beta T C (G N) (b N) gamma delta pi
        harray.1 hT hC hSupport.1 (hGSupport N) harray.2 hRank
  refine ⟨hfinite, ?_, ?_⟩
  · have hcollapsed := selectedFiniteCollapsed_tendsto T C G b pi barB gamma delta
      hHorizon hSupport hShare hBaseline hRank
    have hcollapsedBeta : Tendsto
        (fun N => (finiteCollapsedProjection T C (G N) (b N) gamma delta).2)
        atTop (nhds (betaStar T C pi barB gamma delta)) := by
      simpa [finiteCollapsedProjection, betaStar] using
        (continuous_snd.tendsto
          (collapsedPopulationProjection T C pi barB gamma delta)).comp hcollapsed
    apply hcollapsedBeta.congr'
    filter_upwards [Filter.eventually_ge_atTop C.card] with N hcard
    exact (hfinite N hcard).2.2.symm
  · intro N b' hcard hmeans
    have harray := hShare.1 N hcard
    have hcrit : finiteCollapsedCriterion T C (G N) b' gamma delta =
        finiteCollapsedCriterion T C (G N) (b N) gamma delta := by
      funext theta
      unfold finiteCollapsedCriterion
      apply Finset.sum_congr rfl
      intro g hg
      apply Finset.sum_congr rfl
      intro t ht
      rw [show finiteObservedCohortMean T (G N) b' gamma delta g t =
          finiteObservedCohortMean T (G N) (b N) gamma delta g t by
        simp only [finiteObservedCohortMean, finiteUntreatedMean, hmeans g hg]]
    have hselected :
        maximizerOrZero (finiteCollapsedCriterion T C (G N) b' gamma delta) =
          maximizerOrZero (finiteCollapsedCriterion T C (G N) (b N) gamma delta) :=
      congrArg maximizerOrZero hcrit
    have hb' := finite_unit_and_collapsed_unique_beta T C (G N) b' gamma delta pi
      harray.1 hT hC hSupport.1 (hGSupport N) harray.2 hRank
    have hb := finite_unit_and_collapsed_unique_beta T C (G N) (b N) gamma delta pi
      harray.1 hT hC hSupport.1 (hGSupport N) harray.2 hRank
    unfold betaNStar
    calc
      (maximizerOrZero (unitCriterion T N (G N) b' gamma delta)).2 =
          (maximizerOrZero (finiteCollapsedCriterion T C (G N) b' gamma delta)).2 :=
        hb'.2.2
      _ = (maximizerOrZero
          (finiteCollapsedCriterion T C (G N) (b N) gamma delta)).2 := by rw [hselected]
      _ = (maximizerOrZero (unitCriterion T N (G N) (b N) gamma delta)).2 :=
        hb.2.2.symm

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
