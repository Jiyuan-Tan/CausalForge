import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Basic

namespace CausalSmith.Stat.ReverseKLTwoCoverage

noncomputable def localizedRate (eta D : ℝ) (d n : ℕ) : ℝ :=
  let a := d * Real.log (Real.exp 1 * n) + Real.log (2 * (n : ℝ) ^ 2)
  min (eta * d * D * a / n) (Real.sqrt (d * D * a / n))

/-- Explicit logarithmic factor hidden by the localized theorem's `\widetilde O`. -/
noncomputable def localizedLogFactor (eta eps q : ℝ) : ℝ :=
  1 + Real.log (Real.exp 1 * q) + Real.log (1 + (1 + eta) * q / eps)

end CausalSmith.Stat.ReverseKLTwoCoverage
