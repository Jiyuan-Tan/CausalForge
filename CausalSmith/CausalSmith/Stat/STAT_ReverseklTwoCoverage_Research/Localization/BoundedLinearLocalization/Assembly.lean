import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.Arithmetic

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Assembly for bounded linear localization
-/

namespace CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationExactWrapper

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open CausalSmith.Substrate.MeasurableFiniteLinearERM
open CausalSmith.Stat.ReverseKLTwoCoverage.LinearExactShellTypeFit
open CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationAdapters
open CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationProjection
open CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationZhao
open CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationArithmetic

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

lemma empiricalSqNorm_sampleEvaluation
    (sample : LoggedSample n 𝒳 𝒜)
    (f g : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    empiricalSqNorm
        (sampleEvaluation sample f - sampleEvaluation sample g) =
      empiricalSeminormSq sample (fun x a => f x a - g x a) := by
  rfl

lemma empiricalSqNorm_sub_comm
    (sample : LoggedSample n 𝒳 𝒜)
    (f g : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    empiricalSqNorm
        (sampleEvaluation sample f - sampleEvaluation sample g) =
      empiricalSqNorm
        (sampleEvaluation sample g - sampleEvaluation sample f) := by
  unfold empiricalSqNorm sampleEvaluation
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change
    (f (sample i).context (sample i).action -
      g (sample i).context (sample i).action) ^ 2 =
    (g (sample i).context (sample i).action -
      f (sample i).context (sample i).action) ^ 2
  ring

lemma probability_inter_ge
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (delta : ℝ)
    (hprobA : μ.real A ≥ 1 - delta)
    (hprobB : μ.real B ≥ 1 - delta) :
    μ.real (A ∩ B) ≥ 1 - 2 * delta := by
  have hAc : μ.real Aᶜ ≤ delta := by
    rw [measureReal_compl hA, probReal_univ]
    linarith
  have hBc : μ.real Bᶜ ≤ delta := by
    rw [measureReal_compl hB, probReal_univ]
    linarith
  rw [show A ∩ B = (Aᶜ ∪ Bᶜ)ᶜ by simp,
    measureReal_compl (hA.compl.union hB.compl), probReal_univ]
  have hu := (measureReal_union_le Aᶜ Bᶜ).trans
    (add_le_add hAc hBc)
  linarith

lemma bounded_linear_localization_exact_wrapper
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hn : 0 < n) :
    ∀ c0 : ℝ, 64 ≤ c0 →
      ∃ event : Set (LoggedSample n 𝒳 𝒜),
        MeasurableSet event ∧
        (productLaw E P n).real event ≥ 1 - failureProbability n hn / 2 ∧
        ∀ sample ∈ event,
          linearReward P ∈ confidencePolytope E c0 sample ∧
          ∀ f ∈ confidencePolytope E c0 sample,
            ∑ x, contextMass P x * ∑ a, E.reference x a *
                (f x a - linearReward P x a) ^ 2 ≤
              (4 * c0 + 291) *
                (d * Real.log (Real.exp 1 * n) + Real.log (2 * (n : ℝ) ^ 2)) / n := by
  intro c0 hc0
  let delta := localizationDelta n hn
  let u := localizationU n
  let projectionEvent :=
    projectionGoodEvent (n := n) E P delta
  let comparisonEvent :=
    loggedZhaoEvent (n := n) E P u delta
  let event := projectionEvent ∩ comparisonEvent
  refine ⟨event, ?_, ?_, ?_⟩
  · exact (projectionGoodEvent_measurable (n := n) E P delta).inter
      (loggedZhaoEvent_measurable (n := n) E P u delta)
  · letI : IsProbabilityMeasure (productLaw E P n) :=
      productLaw_isProbability E P
    have hp :=
      projectionGoodEvent_probability (n := n) E P C D delta hshell
        (localizationDelta_pos hn)
    have hz :=
      zhaoEvent_probability (n := n) E P C D u delta hshell hZhao hn
        (localizationU_pos hn) (localizationU_lt_one hn)
        (localizationDelta_pos hn) (localizationDelta_lt_one hn)
    have hinter := probability_inter_ge (productLaw E P n)
      projectionEvent comparisonEvent
      (projectionGoodEvent_measurable (n := n) E P delta)
      (loggedZhaoEvent_measurable (n := n) E P u delta)
      delta hp hz
    have hsplit :
        2 * delta = failureProbability n hn / 2 := by
      unfold delta localizationDelta
      ring
    simpa [event, hsplit] using hinter
  · intro sample hsample
    rcases hsample with ⟨hprojection, hcomparison⟩
    have hrewardPoly :=
      linearReward_mem_predictionPolytope E P C D hshell
    have hprojectionBound :=
      selectedERM_projection_bound_on_good E P C D delta hshell hn
        sample hprojection
    have hprojectionRate :
        empiricalSeminormSq sample
            (fun x a => linearReward P x a - selectedERM E sample x a) ≤
          64 * localizationRate d n / n := by
      rw [← empiricalSqNorm_sampleEvaluation,
        empiricalSqNorm_sub_comm]
      exact hprojectionBound.trans (projection_selected_le_rate E hn)
    have hrateNonneg : 0 ≤ localizationRate d n / n := by
      exact div_nonneg (localizationRate_pos E hn).le (Nat.cast_nonneg n)
    have hrewardRadius :
        empiricalSeminormSq sample
            (fun x a => linearReward P x a - selectedERM E sample x a) ≤
          c0 * localizationRate d n / n := by
      calc
        _ ≤ 64 * localizationRate d n / n := hprojectionRate
        _ ≤ c0 * localizationRate d n / n := by
          have := mul_le_mul_of_nonneg_right hc0 hrateNonneg
          simpa [mul_div_assoc] using this
    refine ⟨⟨hrewardPoly, ?_⟩, ?_⟩
    · simpa [localizationRate] using hrewardRadius
    · intro f hf
      have hemp :
          empiricalSeminormSq sample
              (fun x a => f x a - linearReward P x a) ≤
            (2 * c0 + 128) * localizationRate d n / n := by
        calc
          empiricalSeminormSq sample
              (fun x a => f x a - linearReward P x a) ≤
            2 * empiricalSeminormSq sample
                (fun x a => f x a - selectedERM E sample x a) +
              2 * empiricalSeminormSq sample
                (fun x a => selectedERM E sample x a -
                  linearReward P x a) :=
            empiricalSeminormSq_sub_triangle sample f
              (selectedERM E sample) (linearReward P)
          _ ≤ 2 * (c0 * localizationRate d n / n) +
              2 * (64 * localizationRate d n / n) := by
            gcongr
            · simpa [localizationRate] using hf.2
            · rw [← empiricalSqNorm_sampleEvaluation]
              exact hprojectionBound.trans (projection_selected_le_rate E hn)
          _ = (2 * c0 + 128) * localizationRate d n / n := by ring
      have hzhao := hcomparison f hf.1 (linearReward P) hrewardPoly
      have hrem := zhaoRemainder_le_rate E hn
      rw [finiteContextActionLaw_integral
        (contextMass P) E.reference
        (contextMass_nonneg_local E P) E.reference_isPolicy] at hzhao
      have hpop :
          ∑ x, contextMass P x * ∑ a, E.reference x a *
                (f x a - linearReward P x a) ^ 2 ≤
            2 * empiricalSeminormSq sample
                (fun x a => f x a - linearReward P x a) +
              35 * localizationRate d n / n := by
        calc
          _ ≤ 2 / n * ∑ i,
                (f (loggedDesign sample i).1 (loggedDesign sample i).2 -
                  linearReward P (loggedDesign sample i).1
                    (loggedDesign sample i).2) ^ 2 +
              32 / (3 * n) *
                Real.log
                  (2 * supCoveringNumber (predictionPolytope E) u / delta) +
              10 * u := hzhao
          _ = 2 * empiricalSeminormSq sample
                (fun x a => f x a - linearReward P x a) +
              (32 / (3 * n) *
                Real.log
                  (2 * supCoveringNumber (predictionPolytope E) u / delta) +
                10 * u) := by
              unfold empiricalSeminormSq loggedDesign
              field_simp
              ring
          _ ≤ 2 * empiricalSeminormSq sample
                (fun x a => f x a - linearReward P x a) +
              35 * localizationRate d n / n := by
            gcongr
      calc
        ∑ x, contextMass P x * ∑ a, E.reference x a *
              (f x a - linearReward P x a) ^ 2 ≤
            2 * empiricalSeminormSq sample
                (fun x a => f x a - linearReward P x a) +
              35 * localizationRate d n / n := hpop
        _ ≤ 2 * ((2 * c0 + 128) * localizationRate d n / n) +
              35 * localizationRate d n / n := by gcongr
        _ = (4 * c0 + 291) * localizationRate d n / n := by ring
        _ = (4 * c0 + 291) *
              (d * Real.log (Real.exp 1 * n) +
                Real.log (2 * (n : ℝ) ^ 2)) / n := by
          rfl

end CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationExactWrapper
