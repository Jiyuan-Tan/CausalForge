import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.Estimators

/-! # Finite-sample radial transport scale -/

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Set

-- @node: finiteSampleRadial_transportScale
/-- If [the sample is nonempty](hyp:hn) and [the sampling budget satisfies the stated lower
  bound](hyp:hN), [below a fixed sample-size cutoff, the one-arm parametric source bound dominates
  the capped radial term after Bernoulli-channel scaling](goal). -/
lemma finiteSampleRadial_transportScale {n d N : ℕ}
    (hn : 0 < n) (hN : n ≤ N) (M sigma : ℝ) :
    (1 / (800 * (N : ℝ))) * M ^ 2 * sigma ^ 2 *
        min 1 (polynomialComponent n d) ≤
      (M * sigma / 2) ^ 2 * (1 / (200 * (n : ℝ))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le hnR (by exact_mod_cast hN)
  have hrecip : 1 / (N : ℝ) ≤ 1 / (n : ℝ) := by
    exact one_div_le_one_div_of_le hnR (by exact_mod_cast hN)
  have hmin : min 1 (polynomialComponent n d) ≤ 1 := min_le_left _ _
  have hnonneg : 0 ≤ M ^ 2 * sigma ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcoef : 0 ≤ (1 / (800 * (N : ℝ))) * M ^ 2 * sigma ^ 2 := by
    positivity
  calc
    (1 / (800 * (N : ℝ))) * M ^ 2 * sigma ^ 2 *
        min 1 (polynomialComponent n d) ≤
        (1 / (800 * (N : ℝ))) * M ^ 2 * sigma ^ 2 := by
          simpa using mul_le_mul_of_nonneg_left hmin hcoef
    _ ≤ (1 / (800 * (n : ℝ))) * M ^ 2 * sigma ^ 2 := by
      have hc : 1 / (800 * (N : ℝ)) ≤ 1 / (800 * (n : ℝ)) := by
        simpa [one_div, mul_inv_rev] using
          (mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 1 / 800))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (sq_nonneg M)) (sq_nonneg sigma)
    _ = (M * sigma / 2) ^ 2 * (1 / (200 * (n : ℝ))) := by ring

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
