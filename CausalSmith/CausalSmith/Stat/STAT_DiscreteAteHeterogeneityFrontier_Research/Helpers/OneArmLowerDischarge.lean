import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.CitedGates
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmHeadlineAssembly

/-! # One-arm lower-bound discharge

This module exposes the proved binary one-arm lower bound in the local
heterogeneity-frontier namespace.
-/

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

-- @node: lem:zeng-binary-one-arm-lower
/-- [The proved binary one-arm minimax result discharges the local cited interface](goal). -/
theorem zengOneArmMinimaxLower (epsilon : ℝ) :
    ZengOneArmMinimaxLower epsilon := by
  exact CausalSmith.Stat.DiscreteAteMinimaxLoggap.zengOneArmMinimaxLower epsilon

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
