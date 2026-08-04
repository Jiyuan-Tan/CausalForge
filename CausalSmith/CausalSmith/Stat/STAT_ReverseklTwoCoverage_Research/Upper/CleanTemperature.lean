import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.Concentration
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Coverage.FeatureDomination
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Gibbs.RegretIdentity
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegion

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
  (E : CommonExperiment d 𝒳 𝒜)

noncomputable def empiricalGibbsRadiusObjective
    (sample : LoggedSample n 𝒳 𝒜)
    (g : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)) : ℝ :=
  sSup {u : ℝ | ∃ f ∈ confidencePolytope E 64 sample,
    u = (n : ℝ)⁻¹ * ∑ i, gibbsRadius E g f (sample i).context}

def IsLexicographicStabilizedSelector
    (sample : LoggedSample n 𝒳 𝒜)
    (g : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)) : Prop :=
  g ∈ confidencePolytope E 64 sample ∧
  (∀ f ∈ confidencePolytope E 64 sample,
    empiricalGibbsRadiusObjective E sample g ≤
      empiricalGibbsRadiusObjective E sample f) ∧
  ∀ f ∈ confidencePolytope E 64 sample,
    empiricalGibbsRadiusObjective E sample f =
      empiricalGibbsRadiusObjective E sample g →
    ¬ PredictionLexLT f g

noncomputable def selectedStabilizedPotential
    (sample : LoggedSample n 𝒳 𝒜) :
    Prediction (𝒳 := 𝒳) (𝒜 := 𝒜) := by
  classical
  exact if h : ∃ g, IsLexicographicStabilizedSelector E sample g
    then Classical.choose h else fun _ _ => 0

noncomputable def stabilizedLearner :
    Learner n (𝒳 := 𝒳) (𝒜 := 𝒜) :=
  fun sample _ x a =>
    E.reference x a *
      Real.exp (E.eta * selectedStabilizedPotential E sample x a) /
      ∑ b, E.reference x b *
        Real.exp (E.eta * selectedStabilizedPotential E sample x b)

noncomputable def cleanComparisonRemainder (d n : ℕ) (eta : ℝ) : ℝ :=
  8 / (3 * n) *
    (Real.log (4 * (n : ℝ) ^ 2) +
      2 * d * Real.log (1 + 4 * n * (eta + 2))) + 3 / n

noncomputable def cleanVarianceRadius (D eta : ℝ) (d n : ℕ) : ℝ :=
  D * (3000 *
    (d * Real.log (Real.exp 1 * n) + Real.log (2 * (n : ℝ) ^ 2)) / n +
      3 * cleanComparisonRemainder d n eta)

noncomputable def cleanQ (d : ℕ) (D eta eps : ℝ) : ℝ :=
  d * D * min (eta / eps) ((eps ^ 2)⁻¹)

noncomputable def cleanLogFactor (d : ℕ) (D eta eps : ℝ) : ℝ :=
  1 + Real.log (Real.exp 1 * cleanQ d D eta eps) +
    Real.log (1 + (1 + eta) * cleanQ d D eta eps)

-- @node: thm:clean-temperature-feature-upper
theorem clean_temperature_feature_upper
    (P0 : BanditLaw E) (C D : ℝ) (hshell : ExactShell E P0 C D)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hMaximum : MeasurableMaximumTheorem) :
    (∀ n, ∀ hn : 0 < n,
      IsMeasurableLearner E (stabilizedLearner (n := n) E) ∧
      ∀ P ∈ exactShellSet E C D,
        learnerRisk E P n (stabilizedLearner (n := n) E) ≤
          min
            (E.eta * cleanVarianceRadius D E.eta d n)
            (Real.sqrt (2 * cleanVarianceRadius D E.eta d n)) +
          failureProbability n hn * min 2 (E.eta / 2)) ∧
    ∀ eps, ∀ heps : eps ∈ Set.Ioo (0 : ℝ) 1,
      (E.eta ≤ 2 * eps → sampleComplexity E eps C D heps.1 heps.2 = 1) ∧
      (2 * eps < E.eta →
        let n0 : ℕ :=
          ⌈(10 : ℝ) ^ 8 * cleanQ d D E.eta eps *
            cleanLogFactor d D E.eta eps⌉₊
        (∀ P ∈ exactShellSet E C D,
          learnerRisk E P n0 (stabilizedLearner (n := n0) E) ≤ eps) ∧
        sampleComplexity E eps C D heps.1 heps.2 ≤ n0) := by
  sorry

end CausalSmith.Stat.ReverseKLTwoCoverage
