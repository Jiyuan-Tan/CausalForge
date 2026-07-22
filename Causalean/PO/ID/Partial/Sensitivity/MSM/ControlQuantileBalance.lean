/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlCutoff

/-! # Marginal Sensitivity Model — control-arm quantile balancing

This file mirrors the treated-arm quantile-balancing closed form for the control arm: calibrated
feasible control propensities are dominated by the control cutoff propensity, so the calibrated
control upper bound is attained at that cutoff.

The theorem `cutoff_optimal0` proves optimality of a calibrated control cutoff
against every member of `MSMSetCalib0`. The theorem `msmUpperCalib0_eq_cutoff`
then identifies the sharp calibrated control upper bound with the cutoff
candidate mean.
-/

namespace Causalean.PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- The control quantile-cutoff weight maximizes the calibrated control candidate mean. -/
theorem cutoff_optimal0 (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c) (hc_int : Integrable c P.μ)
    (hcut_mem : S.cutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ)
    (henv : Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ)
    (hweight_env : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hc_env : Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    {etilde : P.Ω → ℝ} (hmem : etilde ∈ S.MSMSetCalib0 Λ)
    (hmeas : AEMeasurable etilde P.μ) :
    S.candMean0 etilde ≤ S.candMean0 (S.cutoffProp0 Λ c) := by
  classical
  have _ : Integrable c P.μ := hc_int
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  set A : P.Ω → ℝ := S.dVar.indicator false with hA_def
  set Y : P.Ω → ℝ := S.factualY with hY_def
  set e : P.Ω → ℝ := S.propScore false with he_def
  set wE : P.Ω → ℝ := fun ω => 1 / etilde ω with hwE_def
  set wC : P.Ω → ℝ :=
    fun ω => if c ω < Y ω then S.wMax0 Λ ω else S.wMin0 Λ ω with hwC_def
  have hOR_box : ∀ {e et : ℝ}, 0 < e → e < 1 → 0 < et → et < 1 →
      ((1 / Λ ≤ OR et e ∧ OR et e ≤ Λ)
        ↔ (1 + (1 - e) / (Λ * e) ≤ 1 / et
          ∧ 1 / et ≤ 1 + Λ * (1 - e) / e)) := by
    intro e0 et he0 he1 het0 het1
    have h1e : 0 < 1 - e0 := by linarith
    have h1et : 0 < 1 - et := by linarith
    have hOReq : OR et e0 = et * (1 - e0) / ((1 - et) * e0) := by
      rw [OR, div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm, mul_div_mul_comm]
      ring_nf
    rw [hOReq]
    have hMax : (1 / Λ ≤ et * (1 - e0) / ((1 - et) * e0))
        ↔ (1 / et ≤ 1 + Λ * (1 - e0) / e0) := by
      rw [div_le_div_iff₀ hΛ0 (by positivity : (0 : ℝ) < (1 - et) * e0),
        show (1 : ℝ) + Λ * (1 - e0) / e0 = (e0 + Λ * (1 - e0)) / e0 by
          field_simp,
        div_le_div_iff₀ het0 he0]
      constructor <;> intro h <;> nlinarith [h, mul_pos hΛ0 he0]
    have hMin : (et * (1 - e0) / ((1 - et) * e0) ≤ Λ)
        ↔ (1 + (1 - e0) / (Λ * e0) ≤ 1 / et) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 - et) * e0),
        show (1 : ℝ) + (1 - e0) / (Λ * e0) = (Λ * e0 + (1 - e0)) / (Λ * e0) by
          field_simp,
        div_le_div_iff₀ (by positivity : (0 : ℝ) < Λ * e0) het0]
      constructor <;> intro h <;> nlinarith [h, mul_pos hΛ0 he0]
    rw [hMax, hMin, and_comm]
  have hAm : Measurable A := by
    rw [hA_def]
    exact S.dVar.measurable_indicator false
  have hYm : Measurable Y := by
    rw [hY_def]
    exact S.measurable_factualY
  have hem : Measurable e := by
    rw [he_def]
    unfold POBackdoorSystem.propScore
    exact (stronglyMeasurable_condExp.mono S.sigmaX_le).measurable
  have hwMax0m : Measurable (S.wMax0 Λ) := by
    unfold POBackdoorSystem.wMax0
    exact (measurable_const.add
      ((measurable_const.mul (measurable_const.sub hem)).div hem))
  have hwMin0m : Measurable (S.wMin0 Λ) := by
    unfold POBackdoorSystem.wMin0
    exact (measurable_const.add
      ((measurable_const.sub hem).div (measurable_const.mul hem)))
  have hwCm : Measurable wC := by
    rw [hwC_def]
    exact Measurable.ite (measurableSet_lt (hc_meas.mono S.sigmaX_le le_rfl) hYm)
      hwMax0m hwMin0m
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => by
    rcases S.dVar.indicator_eq_one_or_zero false ω with h | h <;> simp [hA_def, h]
  have hae : ∀ᵐ ω ∂P.μ, (1 : ℝ) < S.wMin0 Λ ω ∧ S.wMin0 Λ ω ≤ S.wMax0 Λ ω := by
    filter_upwards [hoverlap] with ω hω
    obtain ⟨he0ω, he1ω⟩ := hω
    have h1e : 0 < 1 - e ω := by rw [he_def] at *; linarith
    have he0' : 0 < e ω := by rw [he_def] at *; exact he0ω
    refine ⟨?_, ?_⟩
    · have : 0 < (1 - e ω) / (Λ * e ω) := by positivity
      simp only [POBackdoorSystem.wMin0, ← he_def]
      linarith
    · simp only [POBackdoorSystem.wMin0, POBackdoorSystem.wMax0, ← he_def]
      have hd1 : (1 - e ω) / (Λ * e ω) ≤ Λ * (1 - e ω) / e ω := by
        rw [div_le_div_iff₀ (by positivity) he0']
        nlinarith [hΛ, mul_pos h1e he0', mul_pos hΛ0 he0',
          mul_nonneg (mul_nonneg (le_of_lt h1e) (le_of_lt he0')) (sub_nonneg.mpr hΛ)]
      linarith
  have hboxE : ∀ᵐ ω ∂P.μ,
      S.wMin0 Λ ω ≤ wE ω ∧ wE ω ≤ S.wMax0 Λ ω := by
    obtain ⟨hinterior, hor⟩ := hmem.1
    filter_upwards [hoverlap, hinterior, hor] with ω hov het hOR
    obtain ⟨he0ω, he1ω⟩ := hov
    obtain ⟨het0, het1⟩ := het
    have hbox := (hOR_box he0ω he1ω het0 het1).mp hOR
    simpa [POBackdoorSystem.wMin0, POBackdoorSystem.wMax0, he_def, hwE_def] using hbox
  have hboxC : ∀ᵐ ω ∂P.μ,
      S.wMin0 Λ ω ≤ wC ω ∧ wC ω ≤ S.wMax0 Λ ω ∧ 0 < wC ω := by
    filter_upwards [hae] with ω hω
    obtain ⟨hmin1, hminmax⟩ := hω
    rw [hwC_def]
    by_cases hcy : c ω < Y ω
    · simp only [if_pos hcy]
      exact ⟨hminmax, le_rfl, lt_of_lt_of_le (by linarith) hminmax⟩
    · simp only [if_neg hcy]
      exact ⟨le_rfl, hminmax, by linarith⟩
  have hYE_int : Integrable (fun ω => A ω * Y ω * wE ω) P.μ := by
    have hwE_aem : AEMeasurable wE P.μ := by
      rw [hwE_def]
      exact aemeasurable_const.div hmeas
    refine Integrable.mono' henv
      (((hAm.mul hYm).aemeasurable.mul hwE_aem).aestronglyMeasurable) ?_
    filter_upwards [hboxE, hmem.1.1] with ω hbox hint
    obtain ⟨_, hmax⟩ := hbox
    obtain ⟨het0, _⟩ := hint
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hA0 ω), hwE_def,
      abs_of_nonneg (by positivity : 0 ≤ 1 / etilde ω), mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hA0 ω)
    exact mul_le_mul_of_nonneg_left hmax (abs_nonneg _)
  have hYC_int : Integrable (fun ω => A ω * Y ω * wC ω) P.μ := by
    refine Integrable.mono' henv
      (((hAm.mul hYm).mul hwCm).aestronglyMeasurable) ?_
    filter_upwards [hboxC] with ω hbox
    obtain ⟨_, hmax, hpos⟩ := hbox
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hA0 ω),
      abs_of_nonneg (le_of_lt hpos), mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hA0 ω)
    exact mul_le_mul_of_nonneg_left hmax (abs_nonneg _)
  have hXE_int : Integrable (fun ω => A ω / etilde ω) P.μ := by
    refine Integrable.mono' hweight_env
      ((hAm.aemeasurable.div hmeas).aestronglyMeasurable) ?_
    filter_upwards [hboxE, hmem.1.1] with ω hbox hint
    obtain ⟨_, hmax⟩ := hbox
    obtain ⟨het0, _⟩ := hint
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (hA0 ω), abs_of_pos het0,
      div_eq_mul_inv, ← one_div, hA_def]
    simpa [hA_def, hwE_def] using mul_le_mul_of_nonneg_left hmax (hA0 ω)
  have hXC_int : Integrable (fun ω => A ω / S.cutoffProp0 Λ c ω) P.μ := by
    have hAwC_int : Integrable (fun ω => A ω * wC ω) P.μ := by
      refine Integrable.mono' hweight_env ((hAm.mul hwCm).aestronglyMeasurable) ?_
      filter_upwards [hboxC] with ω hbox
      obtain ⟨_, hmax, hpos⟩ := hbox
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hA0 ω), abs_of_nonneg (le_of_lt hpos)]
      exact mul_le_mul_of_nonneg_left hmax (hA0 ω)
    refine hAwC_int.congr ?_
    filter_upwards [hboxC] with ω hbox
    change A ω * wC ω =
      A ω / (1 / (if c ω < S.factualY ω then S.wMax0 Λ ω else S.wMin0 Λ ω))
    rw [hwC_def, hY_def, div_div_eq_mul_div, div_one]
  have hcE_int : Integrable (fun ω => c ω * A ω * wE ω) P.μ := by
    have hwE_aem : AEMeasurable wE P.μ := by
      rw [hwE_def]
      exact aemeasurable_const.div hmeas
    refine Integrable.mono' hc_env
      (((hc_meas.mono S.sigmaX_le le_rfl).mul hAm).aemeasurable.mul hwE_aem).aestronglyMeasurable ?_
    filter_upwards [hboxE, hmem.1.1] with ω hbox hint
    obtain ⟨_, hmax⟩ := hbox
    obtain ⟨het0, _⟩ := hint
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hA0 ω), hwE_def,
      abs_of_nonneg (by positivity : 0 ≤ 1 / etilde ω), mul_assoc, mul_assoc]
    simpa [mul_assoc, hwE_def, one_div] using
      mul_le_mul_of_nonneg_left hmax (mul_nonneg (abs_nonneg (c ω)) (hA0 ω))
  have hcC_int : Integrable (fun ω => c ω * A ω * wC ω) P.μ := by
    refine Integrable.mono' hc_env
      (((hc_meas.mono S.sigmaX_le le_rfl).mul hAm).mul hwCm).aestronglyMeasurable ?_
    filter_upwards [hboxC] with ω hbox
    obtain ⟨_, hmax, hpos⟩ := hbox
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hA0 ω),
      abs_of_nonneg (le_of_lt hpos), mul_assoc, mul_assoc]
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hmax (mul_nonneg (abs_nonneg (c ω)) (hA0 ω))
  have hfirstE_int : Integrable (fun ω => A ω * (Y ω - c ω) * wE ω) P.μ := by
    refine (hYE_int.sub hcE_int).congr (Filter.Eventually.of_forall ?_)
    intro ω
    change A ω * Y ω * wE ω - c ω * A ω * wE ω = A ω * (Y ω - c ω) * wE ω
    ring
  have hfirstC_int : Integrable (fun ω => A ω * (Y ω - c ω) * wC ω) P.μ := by
    refine (hYC_int.sub hcC_int).congr (Filter.Eventually.of_forall ?_)
    intro ω
    change A ω * Y ω * wC ω - c ω * A ω * wC ω = A ω * (Y ω - c ω) * wC ω
    ring
  have hctermE_eq : ∫ ω, c ω * A ω * wE ω ∂P.μ = ∫ ω, c ω ∂P.μ := by
    have hprod_int : Integrable (fun ω => c ω * (A ω / etilde ω)) P.μ := by
      refine hcE_int.congr (Filter.Eventually.of_forall ?_)
      intro ω
      change c ω * A ω * (1 / etilde ω) = c ω * (A ω / etilde ω)
      rw [div_eq_mul_inv]
      ring
    have hpull :
        P.μ[fun ω => c ω * (A ω / etilde ω) | S.sigmaX]
          =ᵐ[P.μ] (fun ω => c ω * P.μ[fun ω => A ω / etilde ω | S.sigmaX] ω) := by
      exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := S.sigmaX) (μ := P.μ) hc_meas.stronglyMeasurable hprod_int hXE_int
    have hcal : P.μ[fun ω => A ω / etilde ω | S.sigmaX] =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
      simpa [POBackdoorSystem.Calibrated0, hA_def] using hmem.2
    have hmain : ∫ ω, c ω * (A ω / etilde ω) ∂P.μ = ∫ ω, c ω ∂P.μ := by
      have hcond :
          ∫ ω, P.μ[fun ω => c ω * (A ω / etilde ω) | S.sigmaX] ω ∂P.μ
            = ∫ ω, c ω * (A ω / etilde ω) ∂P.μ :=
        MeasureTheory.integral_condExp S.sigmaX_le
      rw [← hcond]
      calc
        ∫ ω, P.μ[fun ω => c ω * (A ω / etilde ω) | S.sigmaX] ω ∂P.μ
            = ∫ ω, c ω * P.μ[fun ω => A ω / etilde ω | S.sigmaX] ω ∂P.μ :=
          integral_congr_ae hpull
        _ = ∫ ω, c ω * 1 ∂P.μ := by
          refine integral_congr_ae ?_
          filter_upwards [hcal] with ω hω
          rw [hω]
        _ = ∫ ω, c ω ∂P.μ := by simp
    rw [← hmain]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    change c ω * A ω * (1 / etilde ω) = c ω * (A ω / etilde ω)
    rw [div_eq_mul_inv]
    ring
  have hctermC_eq : ∫ ω, c ω * A ω * wC ω ∂P.μ = ∫ ω, c ω ∂P.μ := by
    have hprod_int : Integrable (fun ω => c ω * (A ω / S.cutoffProp0 Λ c ω)) P.μ := by
      refine hcC_int.congr ?_
      filter_upwards [hboxC] with ω hbox
      change c ω * A ω * wC ω =
        c ω * (A ω / (1 / (if c ω < S.factualY ω then S.wMax0 Λ ω else S.wMin0 Λ ω)))
      rw [hwC_def, hY_def, div_div_eq_mul_div, div_one]
      ring
    have hpull :
        P.μ[fun ω => c ω * (A ω / S.cutoffProp0 Λ c ω) | S.sigmaX]
          =ᵐ[P.μ] (fun ω =>
            c ω * P.μ[fun ω => A ω / S.cutoffProp0 Λ c ω | S.sigmaX] ω) := by
      exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := S.sigmaX) (μ := P.μ) hc_meas.stronglyMeasurable hprod_int hXC_int
    have hcal :
        P.μ[fun ω => A ω / S.cutoffProp0 Λ c ω | S.sigmaX]
          =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
      simpa [POBackdoorSystem.Calibrated0, hA_def] using hcut_mem.2
    have hmain :
        ∫ ω, c ω * (A ω / S.cutoffProp0 Λ c ω) ∂P.μ = ∫ ω, c ω ∂P.μ := by
      have hcond :
          ∫ ω, P.μ[fun ω => c ω * (A ω / S.cutoffProp0 Λ c ω) | S.sigmaX] ω ∂P.μ
            = ∫ ω, c ω * (A ω / S.cutoffProp0 Λ c ω) ∂P.μ :=
        MeasureTheory.integral_condExp S.sigmaX_le
      rw [← hcond]
      calc
        ∫ ω, P.μ[fun ω => c ω * (A ω / S.cutoffProp0 Λ c ω) | S.sigmaX] ω ∂P.μ
            = ∫ ω, c ω *
                P.μ[fun ω => A ω / S.cutoffProp0 Λ c ω | S.sigmaX] ω ∂P.μ :=
          integral_congr_ae hpull
        _ = ∫ ω, c ω * 1 ∂P.μ := by
          refine integral_congr_ae ?_
          filter_upwards [hcal] with ω hω
          rw [hω]
        _ = ∫ ω, c ω ∂P.μ := by simp
    rw [← hmain]
    refine integral_congr_ae ?_
    filter_upwards [hboxC] with ω hbox
    change c ω * A ω * wC ω =
      c ω * (A ω / (1 / (if c ω < S.factualY ω then S.wMax0 Λ ω else S.wMin0 Λ ω)))
    rw [hwC_def, hY_def, div_div_eq_mul_div, div_one]
    ring
  have hfirst_le :
      ∫ ω, A ω * (Y ω - c ω) * wE ω ∂P.μ
        ≤ ∫ ω, A ω * (Y ω - c ω) * wC ω ∂P.μ := by
    refine integral_mono_ae hfirstE_int hfirstC_int ?_
    filter_upwards [hboxE] with ω hbox
    obtain ⟨hminE, hmaxE⟩ := hbox
    rw [hwC_def]
    by_cases hcy : c ω < Y ω
    · simp only [if_pos hcy]
      have hcoef_nonneg : 0 ≤ A ω * (Y ω - c ω) := by
        exact mul_nonneg (hA0 ω) (sub_nonneg.mpr (le_of_lt hcy))
      exact mul_le_mul_of_nonneg_left hmaxE hcoef_nonneg
    · simp only [if_neg hcy]
      have hcoef_nonpos : A ω * (Y ω - c ω) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (hA0 ω) (sub_nonpos.mpr (le_of_not_gt hcy))
      exact mul_le_mul_of_nonpos_left hminE hcoef_nonpos
  have hcandE :
      S.candMean0 etilde =
        ∫ ω, A ω * (Y ω - c ω) * wE ω ∂P.μ
          + ∫ ω, c ω * A ω * wE ω ∂P.μ := by
    unfold POBackdoorSystem.candMean0
    rw [← integral_add hfirstE_int hcE_int]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    change S.dVar.indicator false ω * S.factualY ω / etilde ω =
      S.dVar.indicator false ω * (S.factualY ω - c ω) * (1 / etilde ω) +
        c ω * S.dVar.indicator false ω * (1 / etilde ω)
    rw [div_eq_mul_inv, one_div]
    ring
  have hcandC :
      S.candMean0 (S.cutoffProp0 Λ c) =
        ∫ ω, A ω * (Y ω - c ω) * wC ω ∂P.μ
          + ∫ ω, c ω * A ω * wC ω ∂P.μ := by
    unfold POBackdoorSystem.candMean0
    rw [← integral_add hfirstC_int hcC_int]
    refine integral_congr_ae ?_
    filter_upwards [hboxC] with ω hbox
    change S.dVar.indicator false ω * S.factualY ω /
        (1 / (if c ω < S.factualY ω then S.wMax0 Λ ω else S.wMin0 Λ ω))
      = A ω * (Y ω - c ω) * wC ω + c ω * A ω * wC ω
    rw [hwC_def, hA_def, hY_def, div_div_eq_mul_div, div_one]
    ring
  rw [hcandE, hcandC, hctermE_eq, hctermC_eq]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right hfirst_le (∫ ω, c ω ∂P.μ)

/-- The sharp calibrated control upper bound equals the control cutoff candidate mean. -/
theorem msmUpperCalib0_eq_cutoff (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c) (hc_int : Integrable c P.μ)
    (hcut_mem : S.cutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ)
    (henv : Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ)
    (hweight_env : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hc_env : Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hmeas : ∀ etilde ∈ S.MSMSetCalib0 Λ, AEMeasurable etilde P.μ) :
    S.msmUpperCalib0 Λ = S.candMean0 (S.cutoffProp0 Λ c) := by
  classical
  have hne : (S.candMean0 '' S.MSMSetCalib0 Λ).Nonempty :=
    ⟨S.candMean0 (S.cutoffProp0 Λ c), Set.mem_image_of_mem _ hcut_mem⟩
  have hle_all :
      ∀ x ∈ S.candMean0 '' S.MSMSetCalib0 Λ,
        x ≤ S.candMean0 (S.cutoffProp0 Λ c) := by
    rintro x ⟨etilde, hmem, rfl⟩
    exact S.cutoff_optimal0 Λ hΛ hoverlap c hc_meas hc_int hcut_mem henv hweight_env hc_env
      hmem (hmeas etilde hmem)
  have hbdd : BddAbove (S.candMean0 '' S.MSMSetCalib0 Λ) :=
    ⟨S.candMean0 (S.cutoffProp0 Λ c), hle_all⟩
  refine le_antisymm ?_ ?_
  · unfold POBackdoorSystem.msmUpperCalib0
    exact csSup_le hne hle_all
  · unfold POBackdoorSystem.msmUpperCalib0
    exact le_csSup hbdd (Set.mem_image_of_mem _ hcut_mem)

end POBackdoorSystem

end Causalean.PO
