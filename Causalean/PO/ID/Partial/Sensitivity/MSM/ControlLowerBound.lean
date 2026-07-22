/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

-/

import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlCutoffConstruct

/-! # Marginal Sensitivity Model — control sharp lower bound

This file gives the control-arm `sInf` lower bound for the Marginal Sensitivity Model. It mirrors
the treated lower-bound construction with the control propensity, untreated indicator, and control
cutoff-survival equation.

It defines the lower-cutoff candidate `lowerCutoffProp0`, the lower survival
target `survTargetLower0`, and the quantile level `calibLevelLower0`. The main
results are `cutoff_optimal0_lower`, `msmLowerCalib0_eq_cutoff`,
`lowerControl_calibValue_eq`, feasibility lemmas for the lower cutoff, the
existence theorem `exists_calibrating_cutoff0_lower`, and the unconditional
closed form `msmLowerCalib0_eq_cutoff_unconditional`.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- The **lower quantile-cutoff complete propensity**: the candidate whose inverse weight is `wMin0`
above the cutoff and `wMax0` at or below it, `1 / (wMin0 if Y > c(X) else wMax0)` — the minimizing
worst case (opposite of `cutoffProp`). -/
noncomputable def lowerCutoffProp0 (Λ : ℝ) (c : P.Ω → ℝ) (ω : P.Ω) : ℝ :=
  1 / (if c ω < S.factualY ω then S.wMin0 Λ ω else S.wMax0 Λ ω)

/-- The **lower target survival** that calibrates the lower cutoff:
`survTargetLower0 = (wMax0·e − 1)/(wMax0 − wMin0)` (equal to `e − survTarget`). -/
noncomputable def survTargetLower0 (Λ : ℝ) (ω : P.Ω) : ℝ :=
  (S.wMax0 Λ ω * S.propScore false ω - 1) / (S.wMax0 Λ ω - S.wMin0 Λ ω)

/-- The **lower calibration quantile level** `1 − survTargetLower0/e` (= `survTarget/e`). -/
noncomputable def calibLevelLower0 (Λ : ℝ) (ω : P.Ω) : ℝ :=
  1 - S.survTargetLower0 Λ ω / S.propScore false ω

/-- **Optimality of the lower quantile-cutoff weight.** Among all calibrated candidates the lower
cutoff weight MINIMIZES the candidate mean: for any `ẽ ∈ MSMSetCalib0 Λ`,
`candMean0 (lowerCutoffProp0 Λ c) ≤ candMean0 ẽ`. The `≥`-mirror of `cutoff_optimal`. -/
theorem cutoff_optimal0_lower (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c) (hc_int : Integrable c P.μ)
    (hcut_mem : S.lowerCutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ)
    (henv : Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ)
    (hweight_env : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hc_env : Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    {etilde : P.Ω → ℝ} (hmem : etilde ∈ S.MSMSetCalib0 Λ)
    (hmeas : AEMeasurable etilde P.μ) :
    S.candMean0 (S.lowerCutoffProp0 Λ c) ≤ S.candMean0 etilde := by
  classical
  have _ : Integrable c P.μ := hc_int
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  set A : P.Ω → ℝ := S.dVar.indicator false with hA_def
  set Y : P.Ω → ℝ := S.factualY with hY_def
  set e : P.Ω → ℝ := S.propScore false with he_def
  set wE : P.Ω → ℝ := fun ω => 1 / etilde ω with hwE_def
  set wC : P.Ω → ℝ :=
    fun ω => if c ω < Y ω then S.wMin0 Λ ω else S.wMax0 Λ ω with hwC_def
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
  have hwMaxm : Measurable (S.wMax0 Λ) := by
    unfold POBackdoorSystem.wMax0
    exact (measurable_const.add
      ((measurable_const.mul (measurable_const.sub hem)).div hem))
  have hwMinm : Measurable (S.wMin0 Λ) := by
    unfold POBackdoorSystem.wMin0
    exact (measurable_const.add
      ((measurable_const.sub hem).div (measurable_const.mul hem)))
  have hwCm : Measurable wC := by
    rw [hwC_def]
    exact Measurable.ite (measurableSet_lt (hc_meas.mono S.sigmaX_le le_rfl) hYm)
      hwMinm hwMaxm
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
      exact ⟨le_rfl, hminmax, by linarith⟩
    · simp only [if_neg hcy]
      exact ⟨hminmax, le_rfl, lt_of_lt_of_le (by linarith) hminmax⟩
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
  have hXC_int : Integrable (fun ω => A ω / S.lowerCutoffProp0 Λ c ω) P.μ := by
    have hAwC_int : Integrable (fun ω => A ω * wC ω) P.μ := by
      refine Integrable.mono' hweight_env ((hAm.mul hwCm).aestronglyMeasurable) ?_
      filter_upwards [hboxC] with ω hbox
      obtain ⟨_, hmax, hpos⟩ := hbox
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hA0 ω), abs_of_nonneg (le_of_lt hpos)]
      exact mul_le_mul_of_nonneg_left hmax (hA0 ω)
    refine hAwC_int.congr ?_
    filter_upwards [hboxC] with ω hbox
    change A ω * wC ω =
      A ω / (1 / (if c ω < S.factualY ω then S.wMin0 Λ ω else S.wMax0 Λ ω))
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
    have hprod_int : Integrable (fun ω => c ω * (A ω / S.lowerCutoffProp0 Λ c ω)) P.μ := by
      refine hcC_int.congr ?_
      filter_upwards [hboxC] with ω hbox
      change c ω * A ω * wC ω =
        c ω * (A ω / (1 / (if c ω < S.factualY ω then S.wMin0 Λ ω else S.wMax0 Λ ω)))
      rw [hwC_def, hY_def, div_div_eq_mul_div, div_one]
      ring
    have hpull :
        P.μ[fun ω => c ω * (A ω / S.lowerCutoffProp0 Λ c ω) | S.sigmaX]
          =ᵐ[P.μ] (fun ω =>
            c ω * P.μ[fun ω => A ω / S.lowerCutoffProp0 Λ c ω | S.sigmaX] ω) := by
      exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := S.sigmaX) (μ := P.μ) hc_meas.stronglyMeasurable hprod_int hXC_int
    have hcal :
        P.μ[fun ω => A ω / S.lowerCutoffProp0 Λ c ω | S.sigmaX]
          =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
      simpa [POBackdoorSystem.Calibrated0, hA_def] using hcut_mem.2
    have hmain :
        ∫ ω, c ω * (A ω / S.lowerCutoffProp0 Λ c ω) ∂P.μ = ∫ ω, c ω ∂P.μ := by
      have hcond :
          ∫ ω, P.μ[fun ω => c ω * (A ω / S.lowerCutoffProp0 Λ c ω) | S.sigmaX] ω ∂P.μ
            = ∫ ω, c ω * (A ω / S.lowerCutoffProp0 Λ c ω) ∂P.μ :=
        MeasureTheory.integral_condExp S.sigmaX_le
      rw [← hcond]
      calc
        ∫ ω, P.μ[fun ω => c ω * (A ω / S.lowerCutoffProp0 Λ c ω) | S.sigmaX] ω ∂P.μ
            = ∫ ω, c ω *
                P.μ[fun ω => A ω / S.lowerCutoffProp0 Λ c ω | S.sigmaX] ω ∂P.μ :=
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
      c ω * (A ω / (1 / (if c ω < S.factualY ω then S.wMin0 Λ ω else S.wMax0 Λ ω)))
    rw [hwC_def, hY_def, div_div_eq_mul_div, div_one]
    ring
  have hfirst_le :
      ∫ ω, A ω * (Y ω - c ω) * wC ω ∂P.μ
        ≤ ∫ ω, A ω * (Y ω - c ω) * wE ω ∂P.μ := by
    refine integral_mono_ae hfirstC_int hfirstE_int ?_
    filter_upwards [hboxE] with ω hbox
    obtain ⟨hminE, hmaxE⟩ := hbox
    rw [hwC_def]
    by_cases hcy : c ω < Y ω
    · simp only [if_pos hcy]
      have hcoef_nonneg : 0 ≤ A ω * (Y ω - c ω) := by
        exact mul_nonneg (hA0 ω) (sub_nonneg.mpr (le_of_lt hcy))
      exact mul_le_mul_of_nonneg_left hminE hcoef_nonneg
    · simp only [if_neg hcy]
      have hcoef_nonpos : A ω * (Y ω - c ω) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (hA0 ω) (sub_nonpos.mpr (le_of_not_gt hcy))
      exact mul_le_mul_of_nonpos_left hmaxE hcoef_nonpos
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
      S.candMean0 (S.lowerCutoffProp0 Λ c) =
        ∫ ω, A ω * (Y ω - c ω) * wC ω ∂P.μ
          + ∫ ω, c ω * A ω * wC ω ∂P.μ := by
    unfold POBackdoorSystem.candMean0
    rw [← integral_add hfirstC_int hcC_int]
    refine integral_congr_ae ?_
    filter_upwards [hboxC] with ω hbox
    change S.dVar.indicator false ω * S.factualY ω /
        (1 / (if c ω < S.factualY ω then S.wMin0 Λ ω else S.wMax0 Λ ω))
      = A ω * (Y ω - c ω) * wC ω + c ω * A ω * wC ω
    rw [hwC_def, hA_def, hY_def, div_div_eq_mul_div, div_one]
    ring
  rw [hcandE, hcandC, hctermE_eq, hctermC_eq]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right hfirst_le (∫ ω, c ω ∂P.μ)

/-- **The sharp lower bound has the quantile-balancing closed form.** Given a calibrating lower
cutoff, `msmLowerCalib0 Λ = candMean0 (lowerCutoffProp0 Λ c)`. -/
theorem msmLowerCalib0_eq_cutoff (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c) (hc_int : Integrable c P.μ)
    (hcut_mem : S.lowerCutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ)
    (henv : Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ)
    (hweight_env : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hc_env : Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hmeas : ∀ etilde ∈ S.MSMSetCalib0 Λ, AEMeasurable etilde P.μ) :
    S.msmLowerCalib0 Λ = S.candMean0 (S.lowerCutoffProp0 Λ c) := by
  classical
  have hne : (S.candMean0 '' S.MSMSetCalib0 Λ).Nonempty :=
    ⟨S.candMean0 (S.lowerCutoffProp0 Λ c), Set.mem_image_of_mem _ hcut_mem⟩
  have hle_all :
      ∀ x ∈ S.candMean0 '' S.MSMSetCalib0 Λ,
        S.candMean0 (S.lowerCutoffProp0 Λ c) ≤ x := by
    rintro x ⟨etilde, hmem, rfl⟩
    exact S.cutoff_optimal0_lower Λ hΛ hoverlap c hc_meas hc_int hcut_mem henv hweight_env
      hc_env hmem (hmeas etilde hmem)
  have hbdd : BddBelow (S.candMean0 '' S.MSMSetCalib0 Λ) :=
    ⟨S.candMean0 (S.lowerCutoffProp0 Λ c), hle_all⟩
  refine le_antisymm ?_ ?_
  · unfold POBackdoorSystem.msmLowerCalib0
    exact csInf_le hbdd (Set.mem_image_of_mem _ hcut_mem)
  · unfold POBackdoorSystem.msmLowerCalib0
    exact le_csInf hne hle_all

/-- **Decomposition of the lower-cutoff calibration value.**
`E[(1-Z)/lowerCutoffProp0 Λ c | σ(X)] = wMax0·e₀ − (wMax0 − wMin0)·G(c)`, with
`G(c) = controlSurv c`. -/
theorem lowerControl_calibValue_eq (Λ : ℝ) (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c)
    (hint : Integrable (fun ω => S.dVar.indicator false ω / S.lowerCutoffProp0 Λ c ω) P.μ)
    (hint1 : Integrable (fun ω =>
      S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ)
    (hmax_int : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hdiff_int : Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
      (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ) :
    P.μ[fun ω => S.dVar.indicator false ω / S.lowerCutoffProp0 Λ c ω | S.sigmaX]
      =ᵐ[P.μ] (fun ω => S.wMax0 Λ ω * S.propScore false ω
        - (S.wMax0 Λ ω - S.wMin0 Λ ω) * S.controlSurv c ω) := by
  classical
  have _hc_meas_used := hc_meas
  have _hint_used := hint
  set A : P.Ω → ℝ := S.dVar.indicator false with hA_def
  set I : P.Ω → ℝ := fun ω => if c ω < S.factualY ω then (1 : ℝ) else 0 with hI_def
  have hprop_meas : Measurable[S.sigmaX] (S.propScore false) := by
    unfold POBackdoorSystem.propScore
    exact stronglyMeasurable_condExp.measurable
  have hwMin_smeas : StronglyMeasurable[S.sigmaX] (S.wMin0 Λ) := by
    unfold POBackdoorSystem.wMin0
    exact (measurable_const.add
      ((measurable_const.sub hprop_meas).div (measurable_const.mul hprop_meas))).stronglyMeasurable
  have hwMax_smeas : StronglyMeasurable[S.sigmaX] (S.wMax0 Λ) := by
    unfold POBackdoorSystem.wMax0
    exact (measurable_const.add
      ((measurable_const.mul (measurable_const.sub hprop_meas)).div hprop_meas)).stronglyMeasurable
  have hdiff_smeas : StronglyMeasurable[S.sigmaX] (fun ω => S.wMax0 Λ ω - S.wMin0 Λ ω) :=
    (hwMax_smeas.measurable.sub hwMin_smeas.measurable).stronglyMeasurable
  have hA_int : Integrable A P.μ := by
    rw [hA_def]
    exact S.dVar.integrable_indicator false
  have hI_int : Integrable (fun ω => A ω * I ω) P.μ := by
    rw [hA_def, hI_def]
    exact hint1
  have hmax_int' : Integrable (fun ω => S.wMax0 Λ ω * A ω) P.μ := by
    refine hmax_int.congr (Filter.Eventually.of_forall ?_)
    intro ω
    rw [hA_def]
    exact mul_comm _ _
  have hpoint :
      (fun ω => S.dVar.indicator false ω / S.lowerCutoffProp0 Λ c ω)
        =ᵐ[P.μ] (fun ω => S.wMax0 Λ ω * A ω
          - (S.wMax0 Λ ω - S.wMin0 Λ ω) * (A ω * I ω)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    rw [hA_def, hI_def]
    by_cases hcy : c ω < S.factualY ω
    · simp only [POBackdoorSystem.lowerCutoffProp0, if_pos hcy]
      rw [div_div_eq_mul_div, div_one]
      ring
    · simp only [POBackdoorSystem.lowerCutoffProp0, if_neg hcy]
      rw [div_div_eq_mul_div, div_one]
      ring
  refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := P.μ) hpoint).trans ?_
  have hsplit :
      P.μ[fun ω => S.wMax0 Λ ω * A ω
          - (S.wMax0 Λ ω - S.wMin0 Λ ω) * (A ω * I ω) | S.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => S.wMax0 Λ ω * A ω | S.sigmaX]
            - P.μ[fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) * (A ω * I ω) | S.sigmaX] :=
    MeasureTheory.condExp_sub hmax_int' hdiff_int S.sigmaX
  have hpullMax :
      P.μ[fun ω => S.wMax0 Λ ω * A ω | S.sigmaX]
        =ᵐ[P.μ] (fun ω => S.wMax0 Λ ω * S.propScore false ω) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaX) (μ := P.μ) hwMax_smeas hmax_int' hA_int
    exact h.trans (Filter.EventuallyEq.of_eq (by
      funext ω
      rfl))
  have hpullDiff :
      P.μ[fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) * (A ω * I ω) | S.sigmaX]
        =ᵐ[P.μ] (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) * S.controlSurv c ω) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaX) (μ := P.μ) hdiff_smeas hdiff_int hI_int
    exact h.trans (Filter.EventuallyEq.of_eq (by
      funext ω
      rfl))
  filter_upwards [hsplit, hpullMax, hpullDiff] with ω hsplitω hmaxω hdiffω
  rw [hsplitω]
  change P.μ[fun ω => S.wMax0 Λ ω * A ω | S.sigmaX] ω
      - P.μ[fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) * (A ω * I ω) | S.sigmaX] ω
    = S.wMax0 Λ ω * S.propScore false ω - (S.wMax0 Λ ω - S.wMin0 Λ ω) * S.controlSurv c ω
  rw [hmaxω, hdiffω]

/-- **Lower-cutoff calibration from the survival equation.** -/
theorem lowerCutoffProp0_calibrated_of_survival (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c)
    (hint : Integrable (fun ω => S.dVar.indicator false ω / S.lowerCutoffProp0 Λ c ω) P.μ)
    (hint1 : Integrable (fun ω =>
      S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ)
    (hmax_int : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hdiff_int : Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
      (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ)
    (hsurv : S.controlSurv c =ᵐ[P.μ] S.survTargetLower0 Λ) :
    S.Calibrated0 (S.lowerCutoffProp0 Λ c) := by
  unfold POBackdoorSystem.Calibrated0
  have hΛ0 : 0 < Λ := lt_trans zero_lt_one hΛ
  refine (S.lowerControl_calibValue_eq Λ c hc_meas hint hint1 hmax_int hdiff_int).trans ?_
  filter_upwards [hoverlap, hsurv] with ω hω hsurvω
  rw [hsurvω]
  set e : ℝ := S.propScore false ω with he_def
  have he0 : 0 < e := by simpa [he_def] using hω.1
  have he1 : e < 1 := by simpa [he_def] using hω.2
  have hdiff_pos : 0 < S.wMax0 Λ ω - S.wMin0 Λ ω := by
    simp only [POBackdoorSystem.wMax0, POBackdoorSystem.wMin0, ← he_def]
    have h1e : 0 < 1 - e := by linarith
    have hΛsq : 0 < Λ * Λ - 1 := by nlinarith
    field_simp [hΛ0.ne', he0.ne']
    nlinarith [h1e, hΛsq, hΛ0, he0]
  have hdiff_ne : S.wMax0 Λ ω - S.wMin0 Λ ω ≠ 0 := hdiff_pos.ne'
  unfold POBackdoorSystem.survTargetLower0
  field_simp [hdiff_ne]
  ring

/-- **The lower cutoff propensity is always in the odds-ratio box.** -/
theorem lowerCutoffProp0_mem_MSMSet0 (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) :
    S.lowerCutoffProp0 Λ c ∈ S.MSMSet0 Λ := by
  classical
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hOR_box : ∀ {e et : ℝ}, 0 < e → e < 1 → 0 < et → et < 1 →
      ((1 / Λ ≤ OR et e ∧ OR et e ≤ Λ)
        ↔ (1 + (1 - e) / (Λ * e) ≤ 1 / et
          ∧ 1 / et ≤ 1 + Λ * (1 - e) / e)) := by
    intro e et he0 he1 het0 het1
    have h1e : 0 < 1 - e := by linarith
    have h1et : 0 < 1 - et := by linarith
    have hOReq : OR et e = et * (1 - e) / ((1 - et) * e) := by
      rw [OR, div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm, mul_div_mul_comm]
      ring_nf
    rw [hOReq]
    have hMax : (1 / Λ ≤ et * (1 - e) / ((1 - et) * e))
        ↔ (1 / et ≤ 1 + Λ * (1 - e) / e) := by
      rw [div_le_div_iff₀ hΛ0 (by positivity : (0 : ℝ) < (1 - et) * e),
        show (1 : ℝ) + Λ * (1 - e) / e = (e + Λ * (1 - e)) / e by
          field_simp,
        div_le_div_iff₀ het0 he0]
      constructor <;> intro h <;> nlinarith [h, mul_pos hΛ0 he0]
    have hMin : (et * (1 - e) / ((1 - et) * e) ≤ Λ)
        ↔ (1 + (1 - e) / (Λ * e) ≤ 1 / et) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 - et) * e),
        show (1 : ℝ) + (1 - e) / (Λ * e) = (Λ * e + (1 - e)) / (Λ * e) by
          field_simp,
        div_le_div_iff₀ (by positivity : (0 : ℝ) < Λ * e) het0]
      constructor <;> intro h <;> nlinarith [h, mul_pos hΛ0 he0]
    rw [hMax, hMin, and_comm]
  have hae : ∀ᵐ ω ∂P.μ, (1 : ℝ) < S.wMin0 Λ ω ∧ S.wMin0 Λ ω ≤ S.wMax0 Λ ω := by
    filter_upwards [hoverlap] with ω hω
    set e : ℝ := S.propScore false ω with he_def
    have he0 : 0 < e := by simpa [he_def] using hω.1
    have he1 : e < 1 := by simpa [he_def] using hω.2
    have h1e : 0 < 1 - e := by linarith
    refine ⟨?_, ?_⟩
    · have : 0 < (1 - e) / (Λ * e) := by positivity
      simp only [POBackdoorSystem.wMin0, ← he_def]
      linarith
    · simp only [POBackdoorSystem.wMin0, POBackdoorSystem.wMax0, ← he_def]
      have hd1 : (1 - e) / (Λ * e) ≤ Λ * (1 - e) / e := by
        rw [div_le_div_iff₀ (by positivity) he0]
        nlinarith [hΛ, mul_pos h1e he0, mul_pos hΛ0 he0,
          mul_nonneg (mul_nonneg (le_of_lt h1e) (le_of_lt he0)) (sub_nonneg.mpr hΛ)]
      linarith
  have hboxC : ∀ᵐ ω ∂P.μ,
      S.wMin0 Λ ω ≤ (if c ω < S.factualY ω then S.wMin0 Λ ω else S.wMax0 Λ ω)
        ∧ (if c ω < S.factualY ω then S.wMin0 Λ ω else S.wMax0 Λ ω) ≤ S.wMax0 Λ ω
        ∧ 1 < (if c ω < S.factualY ω then S.wMin0 Λ ω else S.wMax0 Λ ω) := by
    filter_upwards [hae] with ω hω
    obtain ⟨hmin1, hminmax⟩ := hω
    by_cases hcy : c ω < S.factualY ω
    · simp only [if_pos hcy]
      exact ⟨le_rfl, hminmax, hmin1⟩
    · simp only [if_neg hcy]
      exact ⟨hminmax, le_rfl, lt_of_lt_of_le hmin1 hminmax⟩
  refine ⟨?_, ?_⟩
  · filter_upwards [hboxC] with ω hω
    obtain ⟨_, _, hwgt⟩ := hω
    unfold POBackdoorSystem.lowerCutoffProp0
    constructor
    · positivity
    · rw [div_lt_one (by linarith)]
      linarith
  · filter_upwards [hoverlap, hboxC] with ω hov hw
    obtain ⟨he0, he1⟩ := hov
    obtain ⟨hmin, hmax, hwgt⟩ := hw
    set wC : ℝ := if c ω < S.factualY ω then S.wMin0 Λ ω else S.wMax0 Λ ω with hwC_def
    have hcut : S.lowerCutoffProp0 Λ c ω = 1 / wC := by
      rw [POBackdoorSystem.lowerCutoffProp0, hwC_def]
    have het0 : 0 < S.lowerCutoffProp0 Λ c ω := by
      rw [hcut]
      positivity
    have het1 : S.lowerCutoffProp0 Λ c ω < 1 := by
      rw [hcut, div_lt_one (by linarith)]
      linarith
    rw [(hOR_box he0 he1 het0 het1)]
    have hinv : 1 / S.lowerCutoffProp0 Λ c ω = wC := by
      rw [hcut, one_div_one_div]
    rw [hinv]
    simpa [POBackdoorSystem.wMin0, POBackdoorSystem.wMax0, hwC_def] using ⟨hmin, hmax⟩

/-- **The lower cutoff is calibrated-feasible given the survival equation.** -/
theorem lowerCutoffProp0_mem_MSMSetCalib0_of_survival (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c)
    (hint : Integrable (fun ω => S.dVar.indicator false ω / S.lowerCutoffProp0 Λ c ω) P.μ)
    (hint1 : Integrable (fun ω =>
      S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ)
    (hmax_int : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hdiff_int : Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
      (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ)
    (hsurv : S.controlSurv c =ᵐ[P.μ] S.survTargetLower0 Λ) :
    S.lowerCutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ := by
  exact
    ⟨S.lowerCutoffProp0_mem_MSMSet0 Λ (le_of_lt hΛ) hoverlap c,
     S.lowerCutoffProp0_calibrated_of_survival Λ hΛ hoverlap c hc_meas hint hint1
       hmax_int hdiff_int hsurv⟩

/-- **Existence of a calibrating lower cutoff.** The `survTargetLower0` analogue of
`exists_calibrating_cutoff`: a `σ(X)`-measurable `c` with `controlSurv c =ᵐ survTargetLower0 Λ`. -/
theorem exists_calibrating_cutoff0_lower (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (hatomless : ∀ a : γ, Continuous (condCDF S.controlXYLaw a))
    (hlevel : ∀ᵐ ω ∂P.μ, 0 < S.calibLevelLower0 Λ ω ∧ S.calibLevelLower0 Λ ω < 1) :
    ∃ c : P.Ω → ℝ, Measurable[S.sigmaX] c ∧ S.controlSurv c =ᵐ[P.μ] S.survTargetLower0 Λ := by
  classical
  have _hΛ_used := hΛ
  have hprop_meas : Measurable[S.sigmaX] (S.propScore false) := by
    unfold POBackdoorSystem.propScore
    exact stronglyMeasurable_condExp.measurable
  have hwMin_meas : Measurable[S.sigmaX] (S.wMin0 Λ) := by
    unfold POBackdoorSystem.wMin0
    exact measurable_const.add
      ((measurable_const.sub hprop_meas).div (measurable_const.mul hprop_meas))
  have hwMax_meas : Measurable[S.sigmaX] (S.wMax0 Λ) := by
    unfold POBackdoorSystem.wMax0
    exact measurable_const.add
      ((measurable_const.mul (measurable_const.sub hprop_meas)).div hprop_meas)
  have hsurvTarget_meas : Measurable[S.sigmaX] (S.survTargetLower0 Λ) := by
    unfold POBackdoorSystem.survTargetLower0
    exact ((hwMax_meas.mul hprop_meas).sub measurable_const).div
      (hwMax_meas.sub hwMin_meas)
  have hlevel_meas : Measurable[S.sigmaX] (S.calibLevelLower0 Λ) := by
    unfold POBackdoorSystem.calibLevelLower0
    exact measurable_const.sub (hsurvTarget_meas.div hprop_meas)
  obtain ⟨g, hg, hg_eq⟩ := S.exists_factor_through_factualX hlevel_meas
  let τ : γ → ℝ := fun a => if 0 < g a ∧ g a < 1 then g a else (1 / 2 : ℝ)
  have hτ_meas : Measurable τ := by
    dsimp [τ]
    refine Measurable.ite ?_ hg measurable_const
    exact (measurableSet_lt measurable_const hg).inter (measurableSet_lt hg measurable_const)
  have hτ0 : ∀ a, 0 < τ a := by
    intro a
    dsimp [τ]
    by_cases ha : 0 < g a ∧ g a < 1
    · simp [ha]
    · simp [ha]
  have hτ1 : ∀ a, τ a < 1 := by
    intro a
    dsimp [τ]
    by_cases ha : 0 < g a ∧ g a < 1
    · simp [ha]
    · simp only [ha, ↓reduceIte]
      norm_num
  haveI : IsFiniteMeasure S.controlXYLaw := by
    unfold POBackdoorSystem.controlXYLaw
    infer_instance
  obtain ⟨hq_meas, hq_attain⟩ :=
    Causalean.Mathlib.measurable_condQuantile_and_attains
      S.controlXYLaw τ hτ_meas hτ0 hτ1 hatomless
  let c : P.Ω → ℝ := fun ω =>
    Causalean.Mathlib.condQuantile S.controlXYLaw τ (S.factualX ω)
  have hc_meas : Measurable[S.sigmaX] c := by
    rw [POBackdoorSystem.sigmaX]
    exact hq_meas.comp (comap_measurable S.factualX)
  refine ⟨c, hc_meas, ?_⟩
  have hτ_eq_level : ∀ᵐ ω ∂P.μ, τ (S.factualX ω) = S.calibLevelLower0 Λ ω := by
    filter_upwards [hlevel] with ω hω
    have hgx : g (S.factualX ω) = S.calibLevelLower0 Λ ω := by
      exact (congrFun hg_eq ω).symm
    dsimp [τ]
    rw [hgx]
    simp [hω]
  have hsurv := S.controlSurv_eq c hc_meas
  filter_upwards [hsurv, hτ_eq_level, hoverlap] with ω hsurvω hτω hoverlapω
  rw [hsurvω]
  have hcdf :
      S.controlCondCDF ω (c ω) = τ (S.factualX ω) := by
    unfold POBackdoorSystem.controlCondCDF c
    exact hq_attain (S.factualX ω)
  rw [hcdf, hτω]
  unfold POBackdoorSystem.calibLevelLower0
  have hpos : S.propScore false ω ≠ 0 := ne_of_gt hoverlapω.1
  field_simp [hpos]
  ring

/-- **The sharp lower bound, unconditionally.** The `sInf`-mirror of
`msmUpperCalib_eq_cutoff_unconditional`: the Dorn–Guo sharp lower bound has the quantile-balancing
closed form with the calibrating-cutoff hypothesis discharged. -/
theorem msmLowerCalib0_eq_cutoff_unconditional (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (hatomless : ∀ a : γ, Continuous (condCDF S.controlXYLaw a))
    (hlevel : ∀ᵐ ω ∂P.μ, 0 < S.calibLevelLower0 Λ ω ∧ S.calibLevelLower0 Λ ω < 1)
    (hmeas : ∀ etilde ∈ S.MSMSetCalib0 Λ, AEMeasurable etilde P.μ)
    (hreg : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω / S.lowerCutoffProp0 Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
        (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ) :
    ∃ c : P.Ω → ℝ, Measurable[S.sigmaX] c ∧
      S.lowerCutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ ∧
      S.msmLowerCalib0 Λ = S.candMean0 (S.lowerCutoffProp0 Λ c) := by
  obtain ⟨c, hc_meas, hsurv⟩ :=
    S.exists_calibrating_cutoff0_lower Λ hΛ hoverlap hatomless hlevel
  obtain ⟨hc_int, hint, hint1, hmax_int, hdiff_int,
    henv, hc_env⟩ := hreg c hc_meas
  have hcut_mem : S.lowerCutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ :=
    S.lowerCutoffProp0_mem_MSMSetCalib0_of_survival Λ hΛ hoverlap c hc_meas
      hint hint1 hmax_int hdiff_int hsurv
  have heq : S.msmLowerCalib0 Λ = S.candMean0 (S.lowerCutoffProp0 Λ c) :=
    S.msmLowerCalib0_eq_cutoff Λ (le_of_lt hΛ) hoverlap c hc_meas
      hc_int hcut_mem henv hmax_int hc_env hmeas
  exact ⟨c, hc_meas, hcut_mem, heq⟩

end POBackdoorSystem

end PO
end Causalean
