/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Analysis.BernoulliKL
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bernoulli measures

This file defines the Bernoulli law on the real line, supported on `0` and
`1`, and proves its basic probability, support, integral, absolute-continuity,
and KL-divergence facts. It also provides the corresponding Bool-valued law and
its measurability, probability, integral, bind, and map formulas.
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

/-- A Bernoulli law is absolutely continuous with respect to any Bernoulli law
whose success probability is strictly between zero and one. -/
lemma bernoulliLaw_ac_of_reference_interior {p q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
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

/-- The log-likelihood ratio between any two real-parameter Bernoulli laws is
integrable under the first law. -/
lemma bernoulliLaw_llr_integrable {p q : ℝ} :
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

/-- For Bernoulli laws whose first success probability lies in the unit interval
and whose reference probability is strictly between zero and one, their KL divergence
is the usual two-point Bernoulli expression: success contribution plus failure contribution. -/
lemma bernoulliLaw_klDiv_toReal {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (InformationTheory.klDiv (bernoulliLaw p) (bernoulliLaw q)).toReal
      = p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  classical
  haveI hp_prob : IsProbabilityMeasure (bernoulliLaw p) :=
    bernoulliLaw_isProbabilityMeasure hp0 hp1
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
  have hpq_nonneg : 0 ≤ p / q := div_nonneg hp0 hq0.le
  have hcp_nonneg : 0 ≤ (1 - p) / (1 - q) :=
    div_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1.le)
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
    bernoulliLaw_ac_of_reference_interior hq0 hq1
  have hint : Integrable (llr (bernoulliLaw p) (bernoulliLaw q)) (bernoulliLaw p) :=
    bernoulliLaw_llr_integrable
  have hfinite :
      InformationTheory.klDiv (bernoulliLaw p) (bernoulliLaw q) ≠ ⊤ :=
    InformationTheory.klDiv_ne_top hac hint
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal <| by
    rw [bernoulliLaw_klDiv_toReal hp0.le hp1.le hq0 hq1]
    exact Causalean.Mathlib.Analysis.bernoulli_kl_le_four_sq_sub_of_mem_quarter_band
      hp_lo hp_hi hq_lo hq_hi

/-- `ℝ≥0∞`/`lintegral` analogue of `bernoulliLaw_integral`: a Bernoulli law
integrates an `ℝ≥0∞`-valued function as the two-point weighted sum. -/
lemma bernoulliLaw_lintegral_ofReal {p : ℝ} (f : ℝ → ENNReal) :
    ∫⁻ y, f y ∂(bernoulliLaw p)
      = ENNReal.ofReal p * f 1 + ENNReal.ofReal (1 - p) * f 0 := by
  unfold bernoulliLaw
  rw [lintegral_add_measure]
  · simp [lintegral_smul_measure, mul_comm]

/-- The Boolean Bernoulli distribution assigns success probability to truth and failure
probability to falsehood. It is the same two-point law as the existing real-valued Bernoulli
distribution on zero and one, but its Boolean values make it usable as a Markov kernel into
a Boolean coordinate of a potential-outcome tuple.

This is the Bool-valued sibling of `bernoulliLaw`. -/
noncomputable def bernoulliBool (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true +
    ENNReal.ofReal (1 - p) • Measure.dirac false

/-- The Bool-valued Bernoulli distribution varies measurably with its success probability,
so a measurable probability parameter can be used to construct a measurable kernel. -/
lemma measurable_bernoulliBool : Measurable bernoulliBool := by
  unfold bernoulliBool
  fun_prop

/-- A Bool-valued Bernoulli distribution is a probability distribution whenever its
success probability lies between zero and one. -/
lemma bernoulliBool_isProbabilityMeasure {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliBool p) := by
  rw [isProbabilityMeasure_iff]
  unfold bernoulliBool
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
  convert ENNReal.ofReal_one using 2
  all_goals ring

/-- The expectation of a real-valued function of a Bool-valued Bernoulli draw is its value
at success times the success probability plus its value at failure times the failure
probability. -/
lemma bernoulliBool_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Bool → ℝ) :
    ∫ z, f z ∂bernoulliBool p =
      p * f true + (1 - p) * f false := by
  unfold bernoulliBool
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp [hp0, sub_nonneg.mpr hp1, smul_eq_mul]
  · exact Integrable.smul_measure (μ := Measure.dirac true)
      (c := ENNReal.ofReal p)
      (integrable_dirac (f := f) (a := true) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac false)
      (c := ENNReal.ofReal (1 - p))
      (integrable_dirac (f := f) (a := false) (by simp [enorm])) (by simp)

/-- Drawing a Bool-valued Bernoulli variable and then selecting a distribution according to
its value produces the corresponding success-probability mixture of the two distributions. -/
lemma bernoulliBool_bind {β : Type*} [MeasurableSpace β] (p : ℝ)
    (K : Bool → Measure β) :
    (bernoulliBool p).bind K =
      ENNReal.ofReal p • K true + ENNReal.ofReal (1 - p) • K false := by
  ext A hA
  rw [Measure.bind_apply hA (measurable_of_finite _).aemeasurable]
  unfold bernoulliBool
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

/-- Transforming a Bool-valued Bernoulli draw produces a two-point distribution concentrated
on the transformed success and failure values with their original probabilities. -/
lemma bernoulliBool_map {β : Type*} [MeasurableSpace β] (p : ℝ)
    (f : Bool → β) :
    (bernoulliBool p).map f =
      ENNReal.ofReal p • Measure.dirac (f true) +
        ENNReal.ofReal (1 - p) • Measure.dirac (f false) := by
  have hf : Measurable f := measurable_of_finite f
  unfold bernoulliBool
  rw [Measure.map_add _ _ hf, Measure.map_smul, Measure.map_smul]
  rw [Measure.map_dirac' hf, Measure.map_dirac' hf]

end Causalean.Mathlib.Probability
