import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.ERMPluginAssembly

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]

-- @node: thm:erm-plugin-upper
theorem erm_plugin_upper :
    ∃ K : ℝ, 0 < K ∧
      ∀ (d : ℕ) (𝒳 𝒜 : Type*)
        [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
        [LinearOrder 𝒳] [LinearOrder 𝒜]
        [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
        [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
        (E : CommonExperiment d 𝒳 𝒜) (P0 : BanditLaw E) (C D : ℝ),
        ExactShell E P0 C D →
        ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜) →
        (∀ n, ∀ hn : 0 < n,
          IsMeasurableLearner E (ermGibbsPluginLearner (n := n) E) ∧
          ∀ P ∈ exactShellSet E C D,
            learnerRisk E P n (ermGibbsPluginLearner (n := n) E) ≤
              min
                (600 * kappa E.eta * D * localizationComplexity d n / n)
                (Real.sqrt 600 * (1 + Real.exp (2 * E.eta)) *
                  Real.sqrt (D * localizationComplexity d n / n)) +
              failureProbability n hn / 2 * min 2 (E.eta / 2)) ∧
        ∀ eps, ∀ heps : 0 < eps, ∀ heps_one : eps < 1,
          let qPlugin := (d : ℝ) * D *
            min (kappa E.eta / eps)
              ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2)
          let qEnvelope := (d : ℝ) * D *
            min (d * E.eta / eps)
              (min (d / eps ^ 2)
                (min (kappa E.eta / eps)
                  ((1 + Real.exp (2 * E.eta)) ^ 2 / eps ^ 2)))
          (2 ≤ K * qPlugin * pluginLogFactor E.eta eps qPlugin →
            sampleComplexity E eps C D heps heps_one ≤
              (↑⌈K * qPlugin * pluginLogFactor E.eta eps qPlugin⌉₊ : WithTop ℕ)) ∧
          (2 ≤ K * qEnvelope * pluginLogFactor E.eta eps qEnvelope →
            sampleComplexity E eps C D heps heps_one ≤
              (↑⌈K * qEnvelope * pluginLogFactor E.eta eps qEnvelope⌉₊ : WithTop ℕ)) := by
  exact erm_plugin_upper_proof

end CausalSmith.Stat.ReverseKLTwoCoverage
