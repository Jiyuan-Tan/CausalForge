/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlSharp

/-! # Marginal Sensitivity Model — control cutoff calibration

This file is the control-arm mirror of the treated cutoff-selection and calibration-bracket
development: the cutoff propensity uses the untreated indicator and the control propensity
`P[D=0 | X]`, decomposes its conditional calibration value into a minimum-weight term plus a
conditional control-survival term, and reduces calibrated membership in the sharp control MSM set to
the corresponding conditional-survival equation.

It defines the control endpoint weights `wMin0` and `wMax0`, the upper-cutoff
candidate `cutoffProp0`, the survival target `survTarget0`, and the conditional
survival functional `controlSurv`. The main theorems are the calibration
bracket lemmas, `control_calibValue_eq`, `controlCutoffProp_calibrated_of_survival`,
`cutoffProp0_mem_MSMSet0`, and `cutoffProp0_mem_MSMSetCalib0_of_survival`.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- The smallest admissible inverse-propensity weight for untreated units is the lower endpoint of
the control odds-ratio box. -/
noncomputable def wMin0 (Λ : ℝ) (ω : P.Ω) : ℝ :=
  1 + (1 - S.propScore false ω) / (Λ * S.propScore false ω)

/-- The largest admissible inverse-propensity weight for untreated units is the upper endpoint of
the control odds-ratio box. -/
noncomputable def wMax0 (Λ : ℝ) (ω : P.Ω) : ℝ :=
  1 + Λ * (1 - S.propScore false ω) / S.propScore false ω

/-- The control quantile-cutoff complete propensity uses the upper weight above the cutoff and the
lower weight at or below it. -/
noncomputable def cutoffProp0 (Λ : ℝ) (c : P.Ω → ℝ) (ω : P.Ω) : ℝ :=
  1 / (if c ω < S.factualY ω then S.wMax0 Λ ω else S.wMin0 Λ ω)

/-- The conditional control-survival at a cutoff is the conditional mean of untreated units whose
outcome lies above the cutoff. -/
noncomputable def controlSurv (c : P.Ω → ℝ) : P.Ω → ℝ :=
  P.μ[fun ω => S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0) | S.sigmaX]

/-- The target control survival is the conditional survival value that makes the cutoff
calibrated. -/
noncomputable def survTarget0 (Λ : ℝ) (ω : P.Ω) : ℝ :=
  (1 - S.wMin0 Λ ω * S.propScore false ω) / (S.wMax0 Λ ω - S.wMin0 Λ ω)

/-- The lower control calibration bracket is at most one under overlap and sensitivity level at
least one. -/
theorem wMin0_mul_propScore_le_one (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1) :
    ∀ᵐ ω ∂P.μ, S.wMin0 Λ ω * S.propScore false ω ≤ 1 := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  filter_upwards [hoverlap] with ω hω
  set e : ℝ := S.propScore false ω with he_def
  have he0 : 0 < e := by simpa [he_def] using hω.1
  have he1 : e < 1 := by simpa [he_def] using hω.2
  have hw :
      S.wMin0 Λ ω * S.propScore false ω = e + (1 - e) / Λ := by
    simp only [POBackdoorSystem.wMin0, ← he_def]
    field_simp [hΛ0.ne', he0.ne']
  have hdiv : (1 - e) / Λ ≤ 1 - e := by
    rw [div_le_iff₀ hΛ0]
    nlinarith [hΛ, le_of_lt he1]
  calc
    S.wMin0 Λ ω * S.propScore false ω = e + (1 - e) / Λ := hw
    _ ≤ e + (1 - e) := by linarith
    _ = 1 := by ring

/-- The upper control calibration bracket is at least one under overlap and sensitivity level at
least one. -/
theorem one_le_wMax0_mul_propScore (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1) :
    ∀ᵐ ω ∂P.μ, 1 ≤ S.wMax0 Λ ω * S.propScore false ω := by
  filter_upwards [hoverlap] with ω hω
  set e : ℝ := S.propScore false ω with he_def
  have he0 : 0 < e := by simpa [he_def] using hω.1
  have he1 : e < 1 := by simpa [he_def] using hω.2
  have hw :
      S.wMax0 Λ ω * S.propScore false ω = e + Λ * (1 - e) := by
    simp only [POBackdoorSystem.wMax0, ← he_def]
    field_simp [he0.ne']
  have hmul : 1 - e ≤ Λ * (1 - e) := by
    nlinarith [hΛ, le_of_lt he1]
  calc
    1 = e + (1 - e) := by ring
    _ ≤ e + Λ * (1 - e) := by linarith
    _ = S.wMax0 Λ ω * S.propScore false ω := hw.symm

/-- The all-lower-weight control conditional calibration value equals the lower weight times the
control propensity. -/
theorem condExp_control_wMin0_eq (Λ : ℝ)
    (hint : Integrable (fun ω => S.dVar.indicator false ω * S.wMin0 Λ ω) P.μ) :
    P.μ[fun ω => S.dVar.indicator false ω * S.wMin0 Λ ω | S.sigmaX]
      =ᵐ[P.μ] (fun ω => S.wMin0 Λ ω * S.propScore false ω) := by
  have hprop_meas : Measurable[S.sigmaX] (S.propScore false) := by
    unfold POBackdoorSystem.propScore
    exact stronglyMeasurable_condExp.measurable
  have hw_smeas : StronglyMeasurable[S.sigmaX] (S.wMin0 Λ) := by
    unfold POBackdoorSystem.wMin0
    exact (measurable_const.add
      ((measurable_const.sub hprop_meas).div (measurable_const.mul hprop_meas))).stronglyMeasurable
  have hind_int : Integrable (S.dVar.indicator false) P.μ :=
    S.dVar.integrable_indicator false
  have hcomm :
      (fun ω => S.dVar.indicator false ω * S.wMin0 Λ ω)
        = (fun ω => S.wMin0 Λ ω * S.dVar.indicator false ω) := by
    funext ω
    exact mul_comm _ _
  refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := P.μ)
    (Filter.EventuallyEq.of_eq hcomm)).trans ?_
  have hpull :
      P.μ[fun ω => S.wMin0 Λ ω * S.dVar.indicator false ω | S.sigmaX]
        =ᵐ[P.μ] (fun ω => S.wMin0 Λ ω * P.μ[S.dVar.indicator false | S.sigmaX] ω) :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaX) (μ := P.μ) hw_smeas (hint.congr (Filter.EventuallyEq.of_eq hcomm))
      hind_int
  exact hpull.trans (Filter.EventuallyEq.of_eq (by
    funext ω
    rfl))

/-- The all-upper-weight control conditional calibration value equals the upper weight times the
control propensity. -/
theorem condExp_control_wMax0_eq (Λ : ℝ)
    (hint : Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ) :
    P.μ[fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω | S.sigmaX]
      =ᵐ[P.μ] (fun ω => S.wMax0 Λ ω * S.propScore false ω) := by
  have hprop_meas : Measurable[S.sigmaX] (S.propScore false) := by
    unfold POBackdoorSystem.propScore
    exact stronglyMeasurable_condExp.measurable
  have hw_smeas : StronglyMeasurable[S.sigmaX] (S.wMax0 Λ) := by
    unfold POBackdoorSystem.wMax0
    exact (measurable_const.add
      ((measurable_const.mul (measurable_const.sub hprop_meas)).div hprop_meas)).stronglyMeasurable
  have hind_int : Integrable (S.dVar.indicator false) P.μ :=
    S.dVar.integrable_indicator false
  have hcomm :
      (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω)
        = (fun ω => S.wMax0 Λ ω * S.dVar.indicator false ω) := by
    funext ω
    exact mul_comm _ _
  refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := P.μ)
    (Filter.EventuallyEq.of_eq hcomm)).trans ?_
  have hpull :
      P.μ[fun ω => S.wMax0 Λ ω * S.dVar.indicator false ω | S.sigmaX]
        =ᵐ[P.μ] (fun ω => S.wMax0 Λ ω * P.μ[S.dVar.indicator false | S.sigmaX] ω) :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaX) (μ := P.μ) hw_smeas (hint.congr (Filter.EventuallyEq.of_eq hcomm))
      hind_int
  exact hpull.trans (Filter.EventuallyEq.of_eq (by
    funext ω
    rfl))

/-- The cutoff control calibration value decomposes into the lower bracket plus the weight spread
times the conditional control survival. -/
theorem control_calibValue_eq (Λ : ℝ) (c : P.Ω → ℝ) (_hc_meas : Measurable[S.sigmaX] c)
    (_hint : Integrable (fun ω => S.dVar.indicator false ω / S.cutoffProp0 Λ c ω) P.μ)
    (hint1 : Integrable (fun ω =>
      S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ)
    (hmin_int : Integrable (fun ω => S.dVar.indicator false ω * S.wMin0 Λ ω) P.μ)
    (hdiff_int : Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
      (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ) :
    P.μ[fun ω => S.dVar.indicator false ω / S.cutoffProp0 Λ c ω | S.sigmaX]
      =ᵐ[P.μ] (fun ω => S.wMin0 Λ ω * S.propScore false ω
        + (S.wMax0 Λ ω - S.wMin0 Λ ω) * S.controlSurv c ω) := by
  classical
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
  have hmin_int' : Integrable (fun ω => S.wMin0 Λ ω * A ω) P.μ := by
    refine hmin_int.congr (Filter.Eventually.of_forall ?_)
    intro ω
    rw [hA_def]
    exact mul_comm _ _
  have hpoint :
      (fun ω => S.dVar.indicator false ω / S.cutoffProp0 Λ c ω)
        =ᵐ[P.μ] (fun ω => S.wMin0 Λ ω * A ω
          + (S.wMax0 Λ ω - S.wMin0 Λ ω) * (A ω * I ω)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    rw [hA_def, hI_def]
    by_cases hcy : c ω < S.factualY ω
    · simp only [POBackdoorSystem.cutoffProp0, if_pos hcy]
      rw [div_div_eq_mul_div, div_one]
      ring
    · simp only [POBackdoorSystem.cutoffProp0, if_neg hcy]
      rw [div_div_eq_mul_div, div_one]
      ring
  refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := P.μ) hpoint).trans ?_
  have hsplit :
      P.μ[fun ω => S.wMin0 Λ ω * A ω
          + (S.wMax0 Λ ω - S.wMin0 Λ ω) * (A ω * I ω) | S.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => S.wMin0 Λ ω * A ω | S.sigmaX]
            + P.μ[fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) * (A ω * I ω) | S.sigmaX] :=
    MeasureTheory.condExp_add hmin_int' hdiff_int S.sigmaX
  have hpullMin :
      P.μ[fun ω => S.wMin0 Λ ω * A ω | S.sigmaX]
        =ᵐ[P.μ] (fun ω => S.wMin0 Λ ω * S.propScore false ω) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaX) (μ := P.μ) hwMin_smeas hmin_int' hA_int
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
  filter_upwards [hsplit, hpullMin, hpullDiff] with ω hsplitω hminω hdiffω
  rw [hsplitω]
  change P.μ[fun ω => S.wMin0 Λ ω * A ω | S.sigmaX] ω
      + P.μ[fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) * (A ω * I ω) | S.sigmaX] ω
    = S.wMin0 Λ ω * S.propScore false ω + (S.wMax0 Λ ω - S.wMin0 Λ ω) * S.controlSurv c ω
  rw [hminω, hdiffω]

/-- A cutoff satisfying the target control-survival equation is calibrated. -/
theorem controlCutoffProp_calibrated_of_survival (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c)
    (hint : Integrable (fun ω => S.dVar.indicator false ω / S.cutoffProp0 Λ c ω) P.μ)
    (hint1 : Integrable (fun ω =>
      S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ)
    (hmin_int : Integrable (fun ω => S.dVar.indicator false ω * S.wMin0 Λ ω) P.μ)
    (hdiff_int : Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
      (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ)
    (hsurv : S.controlSurv c =ᵐ[P.μ] S.survTarget0 Λ) :
    S.Calibrated0 (S.cutoffProp0 Λ c) := by
  unfold POBackdoorSystem.Calibrated0
  have hΛ0 : 0 < Λ := lt_trans zero_lt_one hΛ
  refine (S.control_calibValue_eq Λ c hc_meas hint hint1 hmin_int hdiff_int).trans ?_
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
  unfold POBackdoorSystem.survTarget0
  field_simp [hdiff_ne]
  ring

/-- The control cutoff propensity always lies inside the control odds-ratio box. -/
theorem cutoffProp0_mem_MSMSet0 (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) :
    S.cutoffProp0 Λ c ∈ S.MSMSet0 Λ := by
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
      S.wMin0 Λ ω ≤ (if c ω < S.factualY ω then S.wMax0 Λ ω else S.wMin0 Λ ω)
        ∧ (if c ω < S.factualY ω then S.wMax0 Λ ω else S.wMin0 Λ ω) ≤ S.wMax0 Λ ω
        ∧ 1 < (if c ω < S.factualY ω then S.wMax0 Λ ω else S.wMin0 Λ ω) := by
    filter_upwards [hae] with ω hω
    obtain ⟨hmin1, hminmax⟩ := hω
    by_cases hcy : c ω < S.factualY ω
    · simp only [if_pos hcy]
      exact ⟨hminmax, le_rfl, lt_of_lt_of_le hmin1 hminmax⟩
    · simp only [if_neg hcy]
      exact ⟨le_rfl, hminmax, hmin1⟩
  refine ⟨?_, ?_⟩
  · filter_upwards [hboxC] with ω hω
    obtain ⟨_, _, hwgt⟩ := hω
    unfold POBackdoorSystem.cutoffProp0
    constructor
    · positivity
    · rw [div_lt_one (by linarith)]
      linarith
  · filter_upwards [hoverlap, hboxC] with ω hov hw
    obtain ⟨he0, he1⟩ := hov
    obtain ⟨hmin, hmax, hwgt⟩ := hw
    set wC : ℝ := if c ω < S.factualY ω then S.wMax0 Λ ω else S.wMin0 Λ ω with hwC_def
    have hcut : S.cutoffProp0 Λ c ω = 1 / wC := by
      rw [POBackdoorSystem.cutoffProp0, hwC_def]
    have het0 : 0 < S.cutoffProp0 Λ c ω := by
      rw [hcut]
      positivity
    have het1 : S.cutoffProp0 Λ c ω < 1 := by
      rw [hcut, div_lt_one (by linarith)]
      linarith
    rw [(hOR_box he0 he1 het0 het1)]
    have hinv : 1 / S.cutoffProp0 Λ c ω = wC := by
      rw [hcut, one_div_one_div]
    rw [hinv]
    simpa [POBackdoorSystem.wMin0, POBackdoorSystem.wMax0, hwC_def] using ⟨hmin, hmax⟩

/-- The cutoff belongs to the calibrated control MSM set whenever it solves the target
control-survival equation. -/
theorem cutoffProp0_mem_MSMSetCalib0_of_survival (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c)
    (hint : Integrable (fun ω => S.dVar.indicator false ω / S.cutoffProp0 Λ c ω) P.μ)
    (hint1 : Integrable (fun ω =>
      S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ)
    (hmin_int : Integrable (fun ω => S.dVar.indicator false ω * S.wMin0 Λ ω) P.μ)
    (hdiff_int : Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
      (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ)
    (hsurv : S.controlSurv c =ᵐ[P.μ] S.survTarget0 Λ) :
    S.cutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ :=
    ⟨S.cutoffProp0_mem_MSMSet0 Λ (le_of_lt hΛ) hoverlap c,
   S.controlCutoffProp_calibrated_of_survival Λ hΛ hoverlap c hc_meas hint hint1
     hmin_int hdiff_int hsurv⟩

end POBackdoorSystem

end PO
end Causalean
