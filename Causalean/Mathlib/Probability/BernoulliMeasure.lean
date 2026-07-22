/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Analysis.BernoulliKL
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Real-valued Bernoulli measures

This file defines the Bernoulli law on the real line, supported on `0` and
`1`, and proves its basic probability, support, integral, absolute-continuity,
and KL-divergence facts.
-/

namespace Causalean.Mathlib.Probability

open MeasureTheory

/-- The Bernoulli law on `ℝ` with success probability `p`.  Concentrates
`ENNReal.ofReal p` on `1` and `ENNReal.ofReal (1 − p)` on `0`. -/
noncomputable def bernoulliLaw (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac (1 : ℝ)
    + ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)

/-- Two-point integral for the custom `bernoulliLaw`: since
`bernoulliLaw p = ENNReal.ofReal p • dirac 1 + ENNReal.ofReal (1-p) • dirac 0`,
its integral splits via `integral_add_measure` / `integral_smul_measure` /
`integral_dirac` into the two-point weighted sum, with `0 ≤ p ≤ 1` collapsing
the `ENNReal → ℝ` coercions to `p` and `1 - p`. -/
lemma bernoulliLaw_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : ℝ → ℝ) :
    ∫ y, f y ∂(bernoulliLaw p) = p * f 1 + (1 - p) * f 0 := by
  unfold bernoulliLaw
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp [hp0, sub_nonneg.mpr hp1, smul_eq_mul]
  · exact Integrable.smul_measure (μ := Measure.dirac (1 : ℝ))
      (c := ENNReal.ofReal p)
      (integrable_dirac (f := f) (a := (1 : ℝ)) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac (0 : ℝ))
      (c := ENNReal.ofReal (1 - p))
      (integrable_dirac (f := f) (a := (0 : ℝ)) (by simp [enorm])) (by simp)

/-- The custom `bernoulliLaw` is a probability measure for `0 ≤ p ≤ 1`:
its total mass is `p + (1 - p) = 1`. -/
lemma bernoulliLaw_isProbabilityMeasure {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliLaw p) := by
  rw [isProbabilityMeasure_iff]
  unfold bernoulliLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
  norm_num

/-- The Bernoulli law on the real line is almost surely nonnegative, since all
of its mass is placed at `0` and `1`. -/
lemma bernoulliLaw_ae_nonneg {p : ℝ} :
    0 ≤ᵐ[bernoulliLaw p] (fun y : ℝ => y) := by
  change (bernoulliLaw p) {y : ℝ | ¬ 0 ≤ y} = 0
  have hset : {y : ℝ | ¬ 0 ≤ y} = {y | y < 0} := by
    ext y
    simp [not_le]
  rw [hset]
  unfold bernoulliLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp

/-- The Bernoulli law on the real line is almost surely at most one, since all
of its mass is placed at `0` and `1`. -/
lemma bernoulliLaw_ae_le_one {p : ℝ} :
    (fun y : ℝ => y) ≤ᵐ[bernoulliLaw p] fun _ => (1 : ℝ) := by
  change (bernoulliLaw p) {y : ℝ | ¬ y ≤ 1} = 0
  have hset : {y : ℝ | ¬ y ≤ 1} = {y | 1 < y} := by
    ext y
    simp [not_le]
  rw [hset]
  unfold bernoulliLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp

/-- A draw from the real-valued Bernoulli law is almost surely either `0` or
`1`. -/
lemma bernoulliLaw_ae_zero_or_one {p : ℝ} :
    ∀ᵐ y ∂bernoulliLaw p, y = 0 ∨ y = 1 := by
  change (bernoulliLaw p) {y : ℝ | ¬ (y = 0 ∨ y = 1)} = 0
  unfold bernoulliLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp

/-- Alias for the binary-support fact: a draw from the real-valued Bernoulli
law is almost surely either `0` or `1`. -/
lemma bernoulliLaw_ae_binary {p : ℝ} :
    ∀ᵐ y ∂bernoulliLaw p, y = 0 ∨ y = 1 := by
  exact bernoulliLaw_ae_zero_or_one

/-- Bernoulli laws with parameters in the central quarter band are mutually
absolutely continuous in the direction needed for likelihood-ratio and KL
computations. -/
lemma bernoulliLaw_ac_of_mem_quarter_band {p q : ℝ}
    (_hp_lo : (1 : ℝ) / 4 ≤ p) (_hp_hi : p ≤ 3 / 4)
    (hq_lo : (1 : ℝ) / 4 ≤ q) (hq_hi : q ≤ 3 / 4) :
    bernoulliLaw p ≪ bernoulliLaw q := by
  have hq_ne0 : ENNReal.ofReal q ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have h1q_ne0 : ENNReal.ofReal (1 - q) ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  unfold bernoulliLaw at hzero ⊢
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply] at hzero ⊢
  by_cases h1 : (1 : ℝ) ∈ s
  · exfalso
    by_cases h0 : (0 : ℝ) ∈ s
    · simp [h1, h0, hq_ne0] at hzero
    · simp [h1, h0, hq_ne0] at hzero
  · by_cases h0 : (0 : ℝ) ∈ s
    · exfalso
      simp [h1, h0, h1q_ne0] at hzero
    · simp [h1, h0]

/-- The log-likelihood ratio between two central-quarter Bernoulli laws is
integrable under the first Bernoulli law. -/
lemma bernoulliLaw_llr_integrable_of_mem_quarter_band {p q : ℝ}
    (_hp_lo : (1 : ℝ) / 4 ≤ p) (_hp_hi : p ≤ 3 / 4)
    (_hq_lo : (1 : ℝ) / 4 ≤ q) (_hq_hi : q ≤ 3 / 4) :
    Integrable (llr (bernoulliLaw p) (bernoulliLaw q)) (bernoulliLaw p) := by
  unfold bernoulliLaw
  rw [integrable_add_measure]
  constructor
  · exact Integrable.smul_measure (μ := Measure.dirac (1 : ℝ))
      (c := ENNReal.ofReal p)
      (integrable_dirac
        (f := llr (ENNReal.ofReal p • Measure.dirac (1 : ℝ)
          + ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)) (bernoulliLaw q))
        (a := (1 : ℝ)) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac (0 : ℝ))
      (c := ENNReal.ofReal (1 - p))
      (integrable_dirac
        (f := llr (ENNReal.ofReal p • Measure.dirac (1 : ℝ)
          + ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)) (bernoulliLaw q))
        (a := (0 : ℝ)) (by simp [enorm])) (by simp)

/-- For two Bernoulli laws with success probabilities strictly between zero
and one, their KL divergence is the usual two-point Bernoulli expression:
success contribution plus failure contribution. -/
lemma bernoulliLaw_klDiv_toReal {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (InformationTheory.klDiv (bernoulliLaw p) (bernoulliLaw q)).toReal
      = p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  classical
  haveI hp_prob : IsProbabilityMeasure (bernoulliLaw p) :=
    bernoulliLaw_isProbabilityMeasure hp0.le hp1.le
  haveI hq_prob : IsProbabilityMeasure (bernoulliLaw q) :=
    bernoulliLaw_isProbabilityMeasure hq0.le hq1.le
  let g : ℝ → ENNReal :=
    fun x =>
      if x = 1 then ENNReal.ofReal (p / q)
      else ENNReal.ofReal ((1 - p) / (1 - q))
  have hg : Measurable g := by
    dsimp [g]
    exact Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const
  have hq_ne0 : ENNReal.ofReal q ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have h1q_ne0 : ENNReal.ofReal (1 - q) ≠ 0 := by
    intro h
    have hle := ENNReal.ofReal_eq_zero.mp h
    linarith
  have hwd : bernoulliLaw p = (bernoulliLaw q).withDensity g := by
    ext s hs
    rw [withDensity_apply _ hs]
    rw [← lintegral_indicator hs g]
    unfold bernoulliLaw
    dsimp [g]
    rw [lintegral_add_measure]
    rw [lintegral_smul_measure, lintegral_smul_measure]
    simp only [lintegral_dirac]
    by_cases h1 : (1 : ℝ) ∈ s
    · by_cases h0 : (0 : ℝ) ∈ s
      · simp [h1, h0, ENNReal.ofReal_div_of_pos hq0,
          ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1),
          ENNReal.mul_div_cancel hq_ne0 ENNReal.ofReal_ne_top,
          ENNReal.mul_div_cancel h1q_ne0 ENNReal.ofReal_ne_top]
      · simp [h1, h0, ENNReal.ofReal_div_of_pos hq0,
          ENNReal.mul_div_cancel hq_ne0 ENNReal.ofReal_ne_top]
    · by_cases h0 : (0 : ℝ) ∈ s
      · simp [h1, h0, ENNReal.ofReal_div_of_pos (sub_pos.mpr hq1),
          ENNReal.mul_div_cancel h1q_ne0 ENNReal.ofReal_ne_top]
      · simp [h1, h0]
  have hac : bernoulliLaw p ≪ bernoulliLaw q := by
    rw [hwd]
    exact withDensity_absolutelyContinuous (bernoulliLaw q) g
  have hrn : (bernoulliLaw p).rnDeriv (bernoulliLaw q) =ᵐ[bernoulliLaw q] g := by
    rw [hwd]
    exact Measure.rnDeriv_withDensity (bernoulliLaw q) hg
  rw [InformationTheory.toReal_klDiv_eq_integral_klFun hac]
  trans ∫ x, InformationTheory.klFun (g x).toReal ∂(bernoulliLaw q)
  · exact integral_congr_ae <| by
      filter_upwards [hrn] with x hx
      rw [hx]
  rw [bernoulliLaw_integral hq0.le hq1.le]
  dsimp [g]
  have hpq_nonneg : 0 ≤ p / q := div_nonneg hp0.le hq0.le
  have hcp_nonneg : 0 ≤ (1 - p) / (1 - q) :=
    div_nonneg (sub_nonneg.mpr hp1.le) (sub_nonneg.mpr hq1.le)
  simp only [↓reduceIte, zero_ne_one]
  rw [ENNReal.toReal_ofReal hpq_nonneg, ENNReal.toReal_ofReal hcp_nonneg]
  have hqne : q ≠ 0 := hq0.ne'
  have h1qne : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
  have hA :
      q * InformationTheory.klFun (p / q) = p * Real.log (p / q) + q - p := by
    rw [InformationTheory.klFun_apply]
    field_simp [hqne]
  have hB :
      (1 - q) * InformationTheory.klFun ((1 - p) / (1 - q))
        = (1 - p) * Real.log ((1 - p) / (1 - q)) + (1 - q) - (1 - p) := by
    rw [InformationTheory.klFun_apply]
    field_simp [h1qne]
  rw [hA, hB]
  ring

/-- When both Bernoulli success probabilities lie in the middle half of the
unit interval, their KL divergence is at most four times the squared
difference of the probabilities. -/
lemma bernoulliLaw_klDiv_le_four_sq_sub {p q : ℝ}
    (hp_lo : (1 : ℝ) / 4 ≤ p) (hp_hi : p ≤ 3 / 4)
    (hq_lo : (1 : ℝ) / 4 ≤ q) (hq_hi : q ≤ 3 / 4) :
    InformationTheory.klDiv (bernoulliLaw p) (bernoulliLaw q)
      ≤ ENNReal.ofReal (4 * (p - q) ^ 2) := by
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hac : bernoulliLaw p ≪ bernoulliLaw q :=
    bernoulliLaw_ac_of_mem_quarter_band hp_lo hp_hi hq_lo hq_hi
  have hint : Integrable (llr (bernoulliLaw p) (bernoulliLaw q)) (bernoulliLaw p) :=
    bernoulliLaw_llr_integrable_of_mem_quarter_band hp_lo hp_hi hq_lo hq_hi
  have hfinite :
      InformationTheory.klDiv (bernoulliLaw p) (bernoulliLaw q) ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hac hint
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal <| by
    rw [bernoulliLaw_klDiv_toReal hp0 hp1 hq0 hq1]
    exact Causalean.Mathlib.Analysis.bernoulli_kl_le_four_sq_sub_of_mem_quarter_band
      hp_lo hp_hi hq_lo hq_hi

/-- `ℝ≥0∞`/`lintegral` analogue of `bernoulliLaw_integral`: a Bernoulli law
integrates an `ℝ≥0∞`-valued function as the two-point weighted sum. -/
lemma bernoulliLaw_lintegral_ofReal {p : ℝ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (f : ℝ → ENNReal) :
    ∫⁻ y, f y ∂(bernoulliLaw p)
      = ENNReal.ofReal p * f 1 + ENNReal.ofReal (1 - p) * f 0 := by
  unfold bernoulliLaw
  rw [lintegral_add_measure]
  · simp [lintegral_smul_measure, mul_comm]

end Causalean.Mathlib.Probability
