/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Probability.IidMeanVariance
import Causalean.Stat.Concentration.Chebyshev

/-!
# Kish dispersion and effective sample size

This module develops the empirical second-moment statistic used for weighted
i.i.d. samples. When weights have population mean one, their second moment is
the Kish design effect; dividing the nominal sample size by this design effect
gives the effective sample size. The results below establish its mean, a
variance bound under a fourth-moment envelope, and a lower-tail bound.
-/

namespace Causalean.Stat

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Empirical Kish dispersion is the sample average of the squared observation-level weights. -/
def empiricalKishDispersion {Ω : Type*} (g : Ω → ℝ) (n : ℕ)
    (sample : Fin n → Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, g (sample i) ^ 2

/-- A mean-one square-integrable weight has second moment at least one, so its Kish design effect
cannot improve on an equally weighted sample. -/
lemma one_le_secondMoment_of_mean_one
    {𝒳 : Type*} [MeasurableSpace 𝒳]
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] (w : 𝒳 → ℝ)
    (hw : MemLp w 2 μ) (hmean : (∫ x, w x ∂μ) = 1) :
    1 ≤ ∫ x, w x ^ 2 ∂μ := by
  have hv := variance_nonneg w μ
  rw [variance_eq_sub hw, hmean] at hv
  norm_num at hv ⊢
  linarith

/-- The expected empirical Kish dispersion equals the population second moment of the
observation-level weight statistic. -/
lemma empiricalKishDispersion_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (n : ℕ) (hn : 0 < n)
    (hF : Integrable (fun o => g o ^ 2) μ) :
    (∫ sample : Fin n → Ω, empiricalKishDispersion g n sample
        ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ o, g o ^ 2 ∂μ := by
  simpa [empiricalKishDispersion] using
    Causalean.Mathlib.Probability.iid_average_integral μ n hn
      (fun o => g o ^ 2) hF

/-- If the fourth power of a weight is bounded by four times a squared envelope times its second
power, empirical Kish dispersion has variance at most four times the squared envelope and the
population second moment, divided by sample size. -/
lemma empiricalKishDispersion_variance_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (n : ℕ) (k kappa : ℝ) (hn : 0 < n)
    (hF : MemLp (fun o => g o ^ 2) 2 μ)
    (hkappa : (∫ o, g o ^ 2 ∂μ) = kappa)
    (hfourth : ∀ᵐ o ∂μ, g o ^ 4 ≤ 4 * k ^ 2 * g o ^ 2) :
    variance
        (fun sample : Fin n → Ω => empiricalKishDispersion g n sample)
        (Measure.pi (fun _ : Fin n => μ)) ≤
      4 * k ^ 2 * kappa / n := by
  have hvar := Causalean.Mathlib.Probability.iid_average_variance μ n
    (fun o => g o ^ 2) hF
  have hsingle :
      variance (fun o => g o ^ 2) μ ≤ 4 * k ^ 2 * kappa := by
    calc
      variance (fun o => g o ^ 2) μ ≤
          ∫ o, (g o ^ 2) ^ 2 ∂μ :=
        variance_le_expectation_sq hF.aestronglyMeasurable
      _ = ∫ o, g o ^ 4 ∂μ := by
        apply integral_congr_ae
        filter_upwards with o
        ring
      _ ≤ ∫ o, 4 * k ^ 2 * g o ^ 2 ∂μ := by
        have hleft : Integrable (fun o => g o ^ 4) μ := by
          have hpow : (fun o => g o ^ 4) = fun o => (g o ^ 2) ^ 2 := by
            funext o
            ring
          rw [hpow]
          exact hF.integrable_sq
        exact integral_mono_ae hleft
          (hF.integrable (by norm_num) |>.const_mul _) hfourth
      _ = 4 * k ^ 2 * kappa := by
        rw [integral_const_mul, hkappa]
  change variance
      (fun sample : Fin n → Ω =>
        (n : ℝ)⁻¹ * ∑ i, g (sample i) ^ 2)
      (Measure.pi (fun _ : Fin n => μ)) ≤ _
  rw [hvar]
  calc
    (n : ℝ)⁻¹ * variance (fun o => g o ^ 2) μ ≤
        (n : ℝ)⁻¹ * (4 * k ^ 2 * kappa) := by
      gcongr
    _ = 4 * k ^ 2 * kappa / n := by ring

/-- A positive population Kish dispersion falls below half its mean with probability at most
sixteen times the squared weight envelope divided by sample size and population dispersion. -/
lemma empiricalKishDispersion_lower_tail_le
    {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (Q : Measure (Fin n → Ω)) [IsProbabilityMeasure Q]
    (g : Ω → ℝ) (k kappa : ℝ)
    (hn : 0 < n) (hkappa : 0 < kappa)
    (hF : MemLp (empiricalKishDispersion g n) 2 Q)
    (hmean : (∫ sample, empiricalKishDispersion g n sample ∂Q) = kappa)
    (hvar : variance (empiricalKishDispersion g n) Q ≤
      4 * k ^ 2 * kappa / n) :
    (Q {sample | empiricalKishDispersion g n sample < kappa / 2}).toReal ≤
      16 * k ^ 2 / ((n : ℝ) * kappa) := by
  have hcheb := Causalean.Stat.Concentration.probability_abs_sub_mean_gt_le Q
    (empiricalKishDispersion g n) kappa (4 * k ^ 2 * kappa / n)
      (kappa / 2) hF (half_pos hkappa) hmean hvar
  have hsub :
      {sample | empiricalKishDispersion g n sample < kappa / 2} ⊆
        {sample | kappa / 2 <
          |empiricalKishDispersion g n sample - kappa|} := by
    intro sample hs
    simp only [Set.mem_setOf_eq] at hs ⊢
    rw [abs_of_neg (by linarith)]
    linarith
  calc
    (Q {sample | empiricalKishDispersion g n sample < kappa / 2}).toReal ≤
        (Q {sample | kappa / 2 <
          |empiricalKishDispersion g n sample - kappa|}).toReal :=
      measureReal_mono hsub
    _ ≤ (4 * k ^ 2 * kappa / n) / (kappa / 2) ^ 2 := hcheb
    _ = 16 * k ^ 2 / ((n : ℝ) * kappa) := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp [hnR.ne', hkappa.ne']
      ring

end

end Causalean.Stat
