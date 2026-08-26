import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LowerBound

/-!
# Constant assembly for the one-arm minimax rate

This module packages the final elementary step combining separate parametric
and high-dimensional risk lower bounds.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- Two nonnegative component lower bounds combine into a lower bound for
their sum, losing only the universal factor two. -/
lemma half_min_mul_add_le_of_component_bounds
    {a b x y R : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxR : a * x ≤ R) (hyR : b * y ≤ R) :
    (min a b / 2) * (x + y) ≤ R := by
  have hax : min a b * x ≤ R :=
    (mul_le_mul_of_nonneg_right (min_le_left a b) hx).trans hxR
  have hby : min a b * y ≤ R :=
    (mul_le_mul_of_nonneg_right (min_le_right a b) hy).trans hyR
  nlinarith

/-- Specialized assembly for the two summands in `minimaxRate`. -/
lemma minimaxRate_lower_of_two_components
    {n d : ℕ} {a b R : ℝ}
    (hn : 0 < n) (hlog : 0 < Real.log n)
    (hparam : a * (1 / (n : ℝ)) ≤ R)
    (hdim : b * (d ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) ≤ R) :
    (min a b / 2) * minimaxRate n d ≤ R := by
  unfold minimaxRate
  apply half_min_mul_add_le_of_component_bounds
  · positivity
  · positivity
  · exact hparam
  · exact hdim

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
