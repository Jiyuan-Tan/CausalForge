import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Basic

namespace CausalSmith.Stat.ReverseKLTwoCoverage

abbrev DimensionIndex := {d : ℕ // 4 ≤ d}

noncomputable def dimensionWitnessEta : ℝ := 4 * Real.log 3
noncomputable def dimensionWitnessC : ℝ := 3 / 2
noncomputable def dimensionWitnessD : ℝ := 13 / 10

end CausalSmith.Stat.ReverseKLTwoCoverage
