import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Upper.Localized
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegion

/-!
# Definitions for the ERM Gibbs plug-in upper bound

This module isolates the rate complexity and logarithmic inversion factor so
the finite-sample and inversion helpers form an acyclic import graph.
-/

namespace CausalSmith.Stat.ReverseKLTwoCoverage

noncomputable def localizationComplexity (d n : ℕ) : ℝ :=
  d * Real.log (Real.exp 1 * n) + Real.log (2 * (n : ℝ) ^ 2)

/-- Explicit polylogarithmic inversion factor for the ERM plug-in bounds. -/
noncomputable def pluginLogFactor (eta eps q : ℝ) : ℝ :=
  1 + Real.log (Real.exp 1 * q) + Real.log (1 + (1 + eta) * q / eps)

end CausalSmith.Stat.ReverseKLTwoCoverage
