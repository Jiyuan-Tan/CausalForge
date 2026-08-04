import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.DimensionWitness.Limits

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped Topology

-- @node: prop:empirical-ball-dimension-witness
theorem empirical_ball_dimension_witness :
    ∃ (experiments :
        ∀ k : DimensionIndex,
          CommonExperiment k.1 (Fin k.1) (Fin 2))
      (laws : ∀ k : DimensionIndex, BanditLaw (experiments k)),
      (∀ k : DimensionIndex, (experiments k).eta = dimensionWitnessEta) ∧
      (∀ k : DimensionIndex,
        ExactShell (experiments k) (laws k) dimensionWitnessC dimensionWitnessD ∧
          ∀ᵐ z ∂(laws k).dataMeasure,
            z.reward = linearReward (laws k) z.context z.action) ∧
      (∀ k : DimensionIndex,
        let n := k.1 ^ 2
        learnerRisk (experiments k) (laws k) n
            (fun sample _ => lowerEnvelopePolicy (experiments k) 64 sample) ≥
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
        Filter.atTop (nhds 0) := by
  let experiments :
      ∀ k : DimensionIndex, CommonExperiment k.1 (Fin k.1) (Fin 2) :=
    fun k => dwExperiment k.1 k.2
  let laws : ∀ k : DimensionIndex, BanditLaw (experiments k) :=
    fun k => dwLaw k.1 k.2
  refine ⟨experiments, laws, ?_, ?_, ?_,
    dw_linear_dimension_limit, dw_sqrt_dimension_limit⟩
  · intro k
    simp [experiments, dimensionWitnessEta, dwExperiment, dwEta]
  · intro k
    constructor
    · simpa [experiments, laws, dimensionWitnessC, dimensionWitnessD,
        dwCoverageC, dwCoverageD] using dw_exactShell k.1 k.2
    · simpa [experiments, laws] using dw_deterministicReward k.1 k.2
  · intro k
    dsimp only
    simpa [experiments, laws, dwLearner] using
      dw_learnerRisk_lower k.1 k.2

end CausalSmith.Stat.ReverseKLTwoCoverage
