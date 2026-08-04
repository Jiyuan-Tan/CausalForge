import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Basic
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Learner.PredictionPolytope
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.Concentration
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Coverage.FeatureDomination
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Gibbs.RegretIdentity
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.DimensionWitness
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.LocalizedDefs
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.LocalizedEnvelopeInversion

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]

-- @node: thm:localized-upper
theorem localized_upper :
    ∃ K : ℝ, 0 < K ∧
      (∀ (d : ℕ) (𝒳 𝒜 : Type*)
        [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
        [LinearOrder 𝒳] [LinearOrder 𝒜]
        [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
        [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
        (E : CommonExperiment d 𝒳 𝒜) (P0 : BanditLaw E) (C D : ℝ),
        ExactShell E P0 C D →
        ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜) →
        ∀ n, ∀ hn : 0 < n,
          IsMeasurableLearner E
            (predictionPolytopeLearner E 64 (by norm_num) (n := n)).deployed ∧
          (∀ P ∈ exactShellSet E C D,
            learnerRisk E P n
              (predictionPolytopeLearner E 64 (by norm_num) (n := n)).deployed ≤
                K * localizedRate E.eta D d n + failureProbability n hn) ∧
          ∀ eps, ∀ heps : 0 < eps, ∀ heps_one : eps < 1,
            let q := (d : ℝ) ^ 2 * D *
              min (E.eta / eps) ((eps ^ 2)⁻¹)
            2 ≤ K * q * localizedLogFactor E.eta eps q →
            sampleComplexity E eps C D heps heps_one ≤
              (↑⌈K * q * localizedLogFactor E.eta eps q⌉₊ : WithTop ℕ)) ∧
      (∃ (experiments :
          ∀ k : DimensionIndex,
            CommonExperiment k.1 (Fin k.1) (Fin 2))
        (laws : ∀ k : DimensionIndex, BanditLaw (experiments k)),
        (∀ k : DimensionIndex, (experiments k).eta = dimensionWitnessEta) ∧
        (∀ k : DimensionIndex,
          ExactShell (experiments k) (laws k)
            dimensionWitnessC dimensionWitnessD) ∧
        (∀ k : DimensionIndex,
          let nd := k.1 ^ 2
          learnerRisk (experiments k) (laws k) nd
              (fun sample _ =>
                lowerEnvelopePolicy (experiments k) 64 sample) ≥
            Real.log (4 / 3) / (8 * Real.log 3) *
              (1 - k.1 * Real.exp
                (-(k.1 : ℝ) * (3 * Real.log 3 - 2)))) ∧
        Filter.Tendsto
          (fun k : DimensionIndex =>
            (k.1 : ℝ) * dimensionWitnessD / (k.1 ^ 2 : ℕ))
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun k : DimensionIndex =>
            Real.sqrt ((k.1 : ℝ) * dimensionWitnessD / (k.1 ^ 2 : ℕ)))
          Filter.atTop (nhds 0)) := by
  refine ⟨(10 : ℝ) ^ 8, by positivity, ?_, ?_⟩
  · intro d 𝒳 𝒜 _ _ _ _ _ _ _ _ _ _ E P0 C D hshell hZhao n hn
    refine ⟨predictionPolytopeLearner_measurable (n := n) E 64 (by norm_num),
      ?_, ?_⟩
    · intro P hP
      have hrisk :=
        lowerEnvelopeRisk_le_localizedRate E P C D hP hZhao hn
      have hrate : 0 ≤ localizedRate E.eta D d n := by
        unfold localizedRate
        apply le_min
        · have hD : 0 ≤ D := hP.featureExactShell.1.le
          have ha :
              0 ≤ (d : ℝ) * Real.log (Real.exp 1 * n) +
                Real.log (2 * (n : ℝ) ^ 2) := by
            have hlog1 : 0 ≤ Real.log (Real.exp 1 * (n : ℝ)) := by
              apply Real.log_nonneg
              have he : 1 ≤ Real.exp 1 := by
                rw [← Real.exp_zero]
                exact Real.exp_le_exp.mpr (by norm_num)
              have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
              nlinarith [mul_le_mul he hn1 (by norm_num : (0 : ℝ) ≤ 1)
                (Real.exp_pos 1).le]
            have hlog2 : 0 ≤ Real.log (2 * (n : ℝ) ^ 2) := by
              apply Real.log_nonneg
              have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
              nlinarith [sq_nonneg ((n : ℝ) - 1)]
            positivity
          exact div_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg E.eta_pos.le (Nat.cast_nonneg d))
                hD)
              ha)
            (Nat.cast_nonneg n)
        · exact Real.sqrt_nonneg _
      exact hrisk.trans (by
        gcongr
        nlinarith)
    · intro eps heps heps_one
      exact lowerEnvelope_sampleComplexity_bound
        E P0 C D eps hshell hZhao heps heps_one
  · obtain ⟨experiments, laws, heta, hshell, hrisk, hlinear, hsqrt⟩ :=
      empirical_ball_dimension_witness
    exact ⟨experiments, laws, heta, fun k => (hshell k).1,
      hrisk, hlinear, hsqrt⟩

end CausalSmith.Stat.ReverseKLTwoCoverage
