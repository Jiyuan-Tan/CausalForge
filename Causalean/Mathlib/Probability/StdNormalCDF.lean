/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Standard normal CDF and probit

Self-contained one-dimensional standard-normal analysis. Mathlib provides the
standard-normal measure `gaussianReal 0 1` and density `gaussianPDFReal 0 1`;
this file adds project-level names for the density `stdNormalPDF`, the CDF
`stdNormalCDF`, and the probit inverse `probit`.

The CDF is defined from `ProbabilityTheory.cdf (gaussianReal 0 1)`, so
monotonicity and the `atBot`/`atTop` limits come from the `StieltjesFunction`
API. The file also proves CDF symmetry, continuity, strict monotonicity, the
open range `(0,1)`, and exact inversion for `probit`. -/

import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Standard normal CDF and probit

This file provides self-contained one-dimensional standard-normal analysis. It
names the standard-normal density `stdNormalPDF`, CDF `stdNormalCDF`, and
probit inverse `probit`. It proves CDF symmetry, monotonicity, endpoint
limits, continuity, strict monotonicity, positivity, the strict upper bound by
one, and the two exact inversion identities `stdNormalCDF_probit` and
`probit_stdNormalCDF`.
-/

namespace Causalean.Mathlib

open MeasureTheory ProbabilityTheory Real Filter Topology

/-- The standard-normal density `φ(x) = exp(-x²/2)/√(2π)` (= `gaussianPDFReal 0 1`). -/
noncomputable def stdNormalPDF (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The standard-normal CDF `Φ(x) = P(N(0,1) ≤ x)`, packaged from Mathlib's `cdf`. -/
noncomputable def stdNormalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The named standard-normal density is Mathlib's real Gaussian density with mean zero and
variance one. -/
@[simp] lemma stdNormalPDF_def (x : ℝ) : stdNormalPDF x = gaussianPDFReal 0 1 x := rfl

/-- The named standard-normal CDF is Mathlib's CDF for the standard real Gaussian law. -/
@[simp] lemma stdNormalCDF_def (x : ℝ) : stdNormalCDF x = cdf (gaussianReal 0 1) x := rfl

/-- `Φ` is monotone (inherited from the `StieltjesFunction` structure of `cdf`). -/
lemma stdNormalCDF_monotone : Monotone stdNormalCDF := by
  intro a b hab
  exact (monotone_cdf (gaussianReal 0 1)) hab

/-- `Φ(x) ∈ [0,1]`. -/
lemma stdNormalCDF_nonneg (x : ℝ) : 0 ≤ stdNormalCDF x := cdf_nonneg _ x

/-- The standard-normal CDF is at most one at every real point. -/
lemma stdNormalCDF_le_one (x : ℝ) : stdNormalCDF x ≤ 1 := cdf_le_one _ x

/-- **Symmetry of the standard normal CDF:** `Φ(−t) = 1 − Φ(t)`, from the reflection symmetry
of the Gaussian law and its atomlessness. -/
lemma stdNormalCDF_neg (t : ℝ) : stdNormalCDF (-t) = 1 - stdNormalCDF t := by
  have hreal : ∀ s : ℝ, stdNormalCDF s = (gaussianReal 0 1).real (Set.Iic s) := by
    intro s; rw [stdNormalCDF_def]; exact cdf_eq_real _ s
  set μ : Measure ℝ := gaussianReal 0 1 with hμ
  haveI : NoAtoms μ := noAtoms_gaussianReal (v := 1) one_ne_zero
  -- Reflection symmetry of the law: `Φ(-t) = μ.real (Ici t)`.
  have hmap : μ.map (fun x => -x) = μ := by rw [hμ, gaussianReal_map_neg, neg_zero]
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Iic (-t) = Set.Ici t := by ext x; simp
  have step1 : stdNormalCDF (-t) = μ.real (Set.Ici t) := by
    rw [hreal (-t)]
    conv_lhs => rw [← hmap]
    rw [MeasureTheory.map_measureReal_apply measurable_neg measurableSet_Iic, hpre]
  rw [step1, ← Set.compl_Iio, MeasureTheory.measureReal_compl measurableSet_Iio,
    MeasureTheory.measureReal_congr MeasureTheory.Iio_ae_eq_Iic, MeasureTheory.probReal_univ,
    hreal t]

/-- `Φ → 0` at `-∞`. -/
lemma stdNormalCDF_tendsto_atBot : Tendsto stdNormalCDF atBot (𝓝 0) := tendsto_cdf_atBot _

/-- `Φ → 1` at `+∞`. -/
lemma stdNormalCDF_tendsto_atTop : Tendsto stdNormalCDF atTop (𝓝 1) := tendsto_cdf_atTop _

/-- `Φ` is continuous: the standard normal has no atoms. -/
lemma stdNormalCDF_continuous : Continuous stdNormalCDF := by
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (v := 1) one_ne_zero
  set f := cdf (gaussianReal 0 1) with hf
  rw [show stdNormalCDF = f from by ext x; simp [stdNormalCDF, hf]]
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine (f.mono.continuousAt_iff_leftLim_eq_rightLim).2 ?_
  rw [f.rightLim_eq x]
  have hjump : f.measure {x} = ENNReal.ofReal (f x - Function.leftLim (f : ℝ → ℝ) x) :=
    f.measure_singleton x
  have hμx : f.measure {x} = 0 := by
    rw [hf, ProbabilityTheory.measure_cdf]
    exact measure_singleton x
  rw [hμx, eq_comm, ENNReal.ofReal_eq_zero] at hjump
  have hle : Function.leftLim (f : ℝ → ℝ) x ≤ f x :=
    f.mono.leftLim_le (le_refl x)
  linarith [hjump, hle]

/-- `Φ` is strictly monotone: the standard normal has full support. -/
lemma stdNormalCDF_strictMono : StrictMono stdNormalCDF := by
  intro a b hab
  have hfi : IntervalIntegrable (gaussianPDFReal 0 1) volume a b :=
    (integrable_gaussianPDFReal 0 1).intervalIntegrable
  have hposInt : 0 < ∫ x in a..b, gaussianPDFReal 0 1 x :=
    intervalIntegral.intervalIntegral_pos_of_pos hfi
      (fun x => gaussianPDFReal_pos 0 1 x one_ne_zero) hab
  have hposSet : 0 < ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x := by
    simpa [intervalIntegral.integral_of_le hab.le] using hposInt
  have hμpos : 0 < (gaussianReal 0 1) (Set.Ioc a b) := by
    rw [gaussianReal_apply_eq_integral (μ := 0) (v := 1) one_ne_zero]
    exact ENNReal.ofReal_pos.mpr hposSet
  have hmeasure : (gaussianReal 0 1) (Set.Ioc a b) =
      ENNReal.ofReal (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) := by
    calc
      (gaussianReal 0 1) (Set.Ioc a b)
          = (cdf (gaussianReal 0 1)).measure (Set.Ioc a b) := by
              rw [ProbabilityTheory.measure_cdf (gaussianReal 0 1)]
      _ = ENNReal.ofReal (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) := by
              rw [StieltjesFunction.measure_Ioc]
  have hdiff : 0 < cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a := by
    exact ENNReal.ofReal_pos.mp (by simpa [hmeasure] using hμpos)
  exact sub_pos.mp hdiff

/-- `0 < Φ(x)` for every real `x` (full support of the Gaussian). -/
lemma stdNormalCDF_pos (x : ℝ) : 0 < stdNormalCDF x := by
  have hlt := stdNormalCDF_strictMono (by linarith : x - 1 < x)
  have hnon := stdNormalCDF_nonneg (x - 1)
  linarith

/-- `Φ(x) < 1` for every real `x`. -/
lemma stdNormalCDF_lt_one (x : ℝ) : stdNormalCDF x < 1 := by
  have hlt := stdNormalCDF_strictMono (by linarith : x < x + 1)
  have hle := stdNormalCDF_le_one (x + 1)
  linarith

/-- The **probit** `Φ⁻¹(p)`: the standard-normal quantile, the generalized inverse of `Φ`. -/
noncomputable def probit (p : ℝ) : ℝ := sInf {x : ℝ | p ≤ stdNormalCDF x}

/-- `Φ(Φ⁻¹(p)) = p` for `p ∈ (0,1)` (exact inversion, using continuity + strict monotonicity). -/
lemma stdNormalCDF_probit {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    stdNormalCDF (probit p) = p := by
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.mp
    (stdNormalCDF_tendsto_atBot.eventually_lt_const h0)
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp
    (stdNormalCDF_tendsto_atTop.eventually_const_lt h1)
  have hab : a < b := by
    by_contra hnot
    have hba : b ≤ a := le_of_not_gt hnot
    have hmono := stdNormalCDF_monotone hba
    linarith [ha a le_rfl, hb b le_rfl, hmono]
  have hpIcc : p ∈ Set.Icc (stdNormalCDF a) (stdNormalCDF b) :=
    ⟨(ha a le_rfl).le, (hb b le_rfl).le⟩
  have hpimage : p ∈ stdNormalCDF '' Set.Icc a b :=
    intermediate_value_Icc hab.le stdNormalCDF_continuous.continuousOn hpIcc
  rcases hpimage with ⟨x, _hxI, hxeq⟩
  have hset : {y : ℝ | p ≤ stdNormalCDF y} = Set.Ici x := by
    ext y
    change p ≤ stdNormalCDF y ↔ x ≤ y
    rw [← hxeq]
    exact stdNormalCDF_strictMono.le_iff_le
  have hprobit : probit p = x := by
    rw [probit, hset, csInf_Ici]
  rw [hprobit, hxeq]

/-- `Φ⁻¹` inverts `Φ`: `Φ⁻¹(Φ(x)) = x`. -/
lemma probit_stdNormalCDF (x : ℝ) : probit (stdNormalCDF x) = x := by
  rw [probit]
  have hset : {y : ℝ | stdNormalCDF x ≤ stdNormalCDF y} = Set.Ici x := by
    ext y
    exact stdNormalCDF_strictMono.le_iff_le
  rw [hset, csInf_Ici]

end Causalean.Mathlib
