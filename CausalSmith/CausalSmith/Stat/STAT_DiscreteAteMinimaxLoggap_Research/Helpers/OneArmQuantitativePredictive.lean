import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmFullCountCollapse
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmGridPriorLift
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmProductPredictive

/-!
# Quantitative predictive total-variation bounds

This module combines moment matching, the full count-space Poisson tail, and
product tensorization into a directly usable predictive bound.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory Causalean.Stat
open scoped NNReal ENNReal BigOperators

/-- Moment matching through degree `D`, together with a pointwise logarithmic
tail budget, makes the one-cell triple-Poisson predictives `2 / n²`-close. -/
theorem tvDist_mixedTriplePoissonPMF_le_two_inv_sq_of_moments_log_budget
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (ω₀ : PMF ι₀) (ω₁ : PMF ι₁)
    (lam11₀ lam10₀ lam0₀ : ι₀ → ℝ≥0)
    (lam11₁ lam10₁ lam0₁ : ι₁ → ℝ≥0)
    {sampleScale n : ℝ}
    (p₀ pi₀ mu₀ : ι₀ → ℝ) (p₁ pi₁ mu₁ : ι₁ → ℝ)
    (h11₀ : ∀ r, (lam11₀ r : ℝ) = sampleScale * p₀ r * pi₀ r * mu₀ r)
    (h10₀ : ∀ r, (lam10₀ r : ℝ) = sampleScale * p₀ r * pi₀ r * (1 - mu₀ r))
    (h0₀ : ∀ r, (lam0₀ r : ℝ) = sampleScale * p₀ r * (1 - pi₀ r))
    (h11₁ : ∀ r, (lam11₁ r : ℝ) = sampleScale * p₁ r * pi₁ r * mu₁ r)
    (h10₁ : ∀ r, (lam10₁ r : ℝ) = sampleScale * p₁ r * pi₁ r * (1 - mu₁ r))
    (h0₁ : ∀ r, (lam0₁ r : ℝ) = sampleScale * p₁ r * (1 - pi₁ r))
    (hs : 0 ≤ sampleScale) (hn : 0 < n)
    (hp₀ : ∀ r, 0 ≤ p₀ r) (hp₁ : ∀ r, 0 ≤ p₁ r)
    (hpi₀ : ∀ r, pi₀ r ∈ Set.Icc (0 : ℝ) 1)
    (hpi₁ : ∀ r, pi₁ r ∈ Set.Icc (0 : ℝ) 1)
    (hmu₀ : ∀ r, mu₀ r ∈ Set.Icc (0 : ℝ) 1)
    (hmu₁ : ∀ r, mu₁ r ∈ Set.Icc (0 : ℝ) 1)
    (D : ℕ)
    (hmoment : ∀ i j k : ℕ, i + j + k ≤ D →
      ∑ r, (ω₀ r).toReal *
          (p₀ r ^ i * (p₀ r * pi₀ r) ^ j * (p₀ r * pi₀ r * mu₀ r) ^ k) =
        ∑ r, (ω₁ r).toReal *
          (p₁ r ^ i * (p₁ r * pi₁ r) ^ j * (p₁ r * pi₁ r * mu₁ r) ^ k))
    (hbudget₀ : ∀ r, 4 * (sampleScale * p₀ r) + 2 * Real.log n ≤
      ((D + 1 : ℕ) : ℝ) * Real.log 2)
    (hbudget₁ : ∀ r, 4 * (sampleScale * p₁ r) + 2 * Real.log n ≤
      ((D + 1 : ℕ) : ℝ) * Real.log 2) :
    tvDist
        (mixedTriplePoissonPMF ω₀ lam11₀ lam10₀ lam0₀).toMeasure
        (mixedTriplePoissonPMF ω₁ lam11₁ lam10₁ lam0₁).toMeasure ≤
      2 * n⁻¹ ^ 2 := by
  let q₀ := mixedTriplePoissonPMF ω₀ lam11₀ lam10₀ lam0₀
  let q₁ := mixedTriplePoissonPMF ω₁ lam11₁ lam10₁ lam0₁
  have hmass₀ : Summable (mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀) := by
    have hq := pmf_toReal_summable (p := q₀)
    simpa only [q₀, mixedTriplePoissonPMF_toReal_eq_mixedTriplePoissonMass
      ω₀ lam11₀ lam10₀ lam0₀ sampleScale p₀ pi₀ mu₀ h11₀ h10₀ h0₀] using hq
  have hmass₁ : Summable (mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁) := by
    have hq := pmf_toReal_summable (p := q₁)
    simpa only [q₁, mixedTriplePoissonPMF_toReal_eq_mixedTriplePoissonMass
      ω₁ lam11₁ lam10₁ lam0₁ sampleScale p₁ pi₁ mu₁ h11₁ h10₁ h0₁] using hq
  have htotal₀ : ∑' c, mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀ c = 1 := by
    have hq := tsum_pmf_toReal_eq_one q₀
    simpa only [q₀, mixedTriplePoissonPMF_toReal_eq_mixedTriplePoissonMass
      ω₀ lam11₀ lam10₀ lam0₀ sampleScale p₀ pi₀ mu₀ h11₀ h10₀ h0₀] using hq
  have htotal₁ : ∑' c, mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁ c = 1 := by
    have hq := tsum_pmf_toReal_eq_one q₁
    simpa only [q₁, mixedTriplePoissonPMF_toReal_eq_mixedTriplePoissonMass
      ω₁ lam11₁ lam10₁ lam0₁ sampleScale p₁ pi₁ mu₁ h11₁ h10₁ h0₁] using hq
  have htail₀ (r : ι₀) :
      expSeriesTail (2 * (sampleScale * p₀ r)) (D + 1) ≤ n⁻¹ ^ 2 :=
    expSeriesTail_two_mul_le_inv_sq_of_log_budget
      (mul_nonneg hs (hp₀ r)) hn (D + 1) (hbudget₀ r)
  have htail₁ (r : ι₁) :
      expSeriesTail (2 * (sampleScale * p₁ r)) (D + 1) ≤ n⁻¹ ^ 2 :=
    expSeriesTail_two_mul_le_inv_sq_of_log_budget
      (mul_nonneg hs (hp₁ r)) hn (D + 1) (hbudget₁ r)
  have hcollapse := tsum_abs_mixedTriplePoissonMass_sub_le_tails_of_moments
    ω₀ ω₁ p₀ pi₀ mu₀ p₁ pi₁ mu₁ hs hp₀ hp₁ hpi₀ hpi₁ hmu₀ hmu₁ D
    hmoment hmass₀ hmass₁ htotal₀ htotal₁
  have htailSum₀ :
      ∑ r, (ω₀ r).toReal * expSeriesTail (2 * (sampleScale * p₀ r)) (D + 1) ≤
        n⁻¹ ^ 2 := by
    calc
      _ ≤ ∑ r, (ω₀ r).toReal * (n⁻¹ ^ 2) := by
        gcongr with r
        exact htail₀ r
      _ = n⁻¹ ^ 2 := by
        rw [← Finset.sum_mul]
        have hsum : ∑ r, (ω₀ r).toReal = 1 := by
          simpa only [tsum_fintype] using tsum_pmf_toReal_eq_one ω₀
        rw [hsum, one_mul]
  have htailSum₁ :
      ∑ r, (ω₁ r).toReal * expSeriesTail (2 * (sampleScale * p₁ r)) (D + 1) ≤
        n⁻¹ ^ 2 := by
    calc
      _ ≤ ∑ r, (ω₁ r).toReal * (n⁻¹ ^ 2) := by
        gcongr with r
        exact htail₁ r
      _ = n⁻¹ ^ 2 := by
        rw [← Finset.sum_mul]
        have hsum : ∑ r, (ω₁ r).toReal = 1 := by
          simpa only [tsum_fintype] using tsum_pmf_toReal_eq_one ω₁
        rw [hsum, one_mul]
  exact (tvDist_mixedTriplePoissonPMF_le_tsum_abs_mass
    ω₀ ω₁ lam11₀ lam10₀ lam0₀ lam11₁ lam10₁ lam0₁
    sampleScale p₀ pi₀ mu₀ p₁ pi₁ mu₁
    h11₀ h10₀ h0₀ h11₁ h10₁ h0₁).trans
      (hcollapse.trans (by linarith))

/-- The iid `m`-cell predictive products inherit the one-cell bound linearly. -/
theorem tvDist_oneArmCountIidMeasure_le_two_card_mul_inv_sq
    (q₀ q₁ : PMF (Fin 3 → ℕ)) (m : ℕ) {n : ℝ}
    (hone : tvDist q₀.toMeasure q₁.toMeasure ≤ 2 * n⁻¹ ^ 2) :
    tvDist (oneArmCountIidMeasure q₀ m) (oneArmCountIidMeasure q₁ m) ≤
      2 * (m : ℝ) * n⁻¹ ^ 2 := by
  refine (tvDist_pi_le_card_mul q₀.toMeasure q₁.toMeasure m).trans ?_
  exact (mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg m)).trans_eq (by ring)

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
