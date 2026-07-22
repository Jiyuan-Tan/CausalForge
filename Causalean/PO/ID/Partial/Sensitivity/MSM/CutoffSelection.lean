/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — reducing the cutoff calibration to a conditional-quantile equation

The sharp quantile-balancing bound (`QuantileBalance.msmUpperCalib_eq_cutoff`) needs the cutoff
propensity `cutoffProp Λ c` to be *calibrated* and feasible (`hcut_mem : cutoffProp Λ c ∈ MSMSetCalib Λ`).
This file reduces that hypothesis to a single explicit **conditional-survival** equation on the cutoff.

Writing `G(c) = E[Z·1{Y > c(X)} | σ(X)]` for the conditional treated-survival, the cutoff's calibration
value decomposes exactly:

    E[Z / cutoffProp Λ c | σ(X)] = wMin·e + (wMax − wMin)·G(c)      (`cutoff_calibValue_eq`)

(pulling the `σ(X)`-measurable weights `wMin`, `wMax` out of the conditional expectation). Hence the cutoff
is calibrated **iff** `G(c) = (1 − wMin·e)/(wMax − wMin) =: survTarget` (`cutoffProp_calibrated_of_survival`).
Together with the fact that the cutoff is always in the odds-ratio box (`cutoffProp_mem_MSMSet`), this gives
`cutoffProp_mem_MSMSetCalib_of_survival`: the calibrated-feasibility hypothesis `hcut_mem` holds as soon as the cutoff
`c` solves the conditional-survival equation.

**Scope.** This file supplies the calibration algebra used by the cutoff-construction files. It shows
that a `σ(X)`-measurable cutoff solving `G(c) = survTarget` immediately yields a calibrated feasible
cutoff propensity; the conditional-quantile construction of such cutoffs is handled downstream by the
MSM cutoff-construction development.
-/

import Causalean.PO.ID.Partial.Sensitivity.MSM.CutoffExists
import Causalean.PO.ID.Partial.Sensitivity.MSM.Sharp
import Causalean.PO.ID.Partial.Sensitivity.MSM.QuantileBalance

/-! # Sharp treated-arm upper bound from calibrated cutoffs

This file reduces calibrated feasibility of the upper MSM cutoff to one
conditional-survival equation. It defines `treatedSurv` and `survTarget`, proves
the calibration decomposition `cutoff_calibValue_eq`, derives
`cutoffProp_calibrated_of_survival`, proves every cutoff propensity lies in the
odds-ratio box via `cutoffProp_mem_MSMSet`, and packages both facts as
`cutoffProp_mem_MSMSetCalib_of_survival`.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- The **conditional treated-survival** at cutoff `c`: `G(c) = E[Z·1{Y > c(X)} | σ(X)]`. -/
noncomputable def treatedSurv (c : P.Ω → ℝ) : P.Ω → ℝ :=
  P.μ[fun ω => S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0) | S.sigmaX]

/-- The **target survival** that calibrates the cutoff: `(1 − wMin·e)/(wMax − wMin)`. -/
noncomputable def survTarget (Λ : ℝ) (ω : P.Ω) : ℝ :=
  (1 - S.wMin Λ ω * S.propScore true ω) / (S.wMax Λ ω - S.wMin Λ ω)

/-- **Decomposition of the cutoff calibration value.** Pulling the `σ(X)`-measurable weights out
of the conditional expectation gives
`E[Z/cutoffProp Λ c | σ(X)] = wMin·e + (wMax − wMin)·G(c)`. -/
theorem cutoff_calibValue_eq (Λ : ℝ) (c : P.Ω → ℝ) (_hc_meas : Measurable[S.sigmaX] c)
    (_hint : Integrable (fun ω => S.dVar.indicator true ω / S.cutoffProp Λ c ω) P.μ)
    (hint1 : Integrable (fun ω =>
      S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ)
    (hmin_int : Integrable (fun ω => S.dVar.indicator true ω * S.wMin Λ ω) P.μ)
    (hdiff_int : Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
      (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ) :
    P.μ[fun ω => S.dVar.indicator true ω / S.cutoffProp Λ c ω | S.sigmaX]
      =ᵐ[P.μ] (fun ω => S.wMin Λ ω * S.propScore true ω
        + (S.wMax Λ ω - S.wMin Λ ω) * S.treatedSurv c ω) := by
  classical
  set A : P.Ω → ℝ := S.dVar.indicator true with hA_def
  set I : P.Ω → ℝ := fun ω => if c ω < S.factualY ω then (1 : ℝ) else 0 with hI_def
  have hprop_meas : Measurable[S.sigmaX] (S.propScore true) := by
    unfold POBackdoorSystem.propScore
    exact stronglyMeasurable_condExp.measurable
  have hwMin_smeas : StronglyMeasurable[S.sigmaX] (S.wMin Λ) := by
    unfold POBackdoorSystem.wMin
    exact (measurable_const.add
      ((measurable_const.sub hprop_meas).div (measurable_const.mul hprop_meas))).stronglyMeasurable
  have hwMax_smeas : StronglyMeasurable[S.sigmaX] (S.wMax Λ) := by
    unfold POBackdoorSystem.wMax
    exact (measurable_const.add
      ((measurable_const.mul (measurable_const.sub hprop_meas)).div hprop_meas)).stronglyMeasurable
  have hdiff_smeas : StronglyMeasurable[S.sigmaX] (fun ω => S.wMax Λ ω - S.wMin Λ ω) :=
    (hwMax_smeas.measurable.sub hwMin_smeas.measurable).stronglyMeasurable
  have hA_int : Integrable A P.μ := by
    rw [hA_def]
    exact S.dVar.integrable_indicator true
  have hI_int : Integrable (fun ω => A ω * I ω) P.μ := by
    rw [hA_def, hI_def]
    exact hint1
  have hmin_int' : Integrable (fun ω => S.wMin Λ ω * A ω) P.μ := by
    refine hmin_int.congr (Filter.Eventually.of_forall ?_)
    intro ω
    rw [hA_def]
    exact mul_comm _ _
  have hpoint :
      (fun ω => S.dVar.indicator true ω / S.cutoffProp Λ c ω)
        =ᵐ[P.μ] (fun ω => S.wMin Λ ω * A ω
          + (S.wMax Λ ω - S.wMin Λ ω) * (A ω * I ω)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    rw [hA_def, hI_def]
    by_cases hcy : c ω < S.factualY ω
    · simp only [POBackdoorSystem.cutoffProp, if_pos hcy]
      rw [div_div_eq_mul_div, div_one]
      ring
    · simp only [POBackdoorSystem.cutoffProp, if_neg hcy]
      rw [div_div_eq_mul_div, div_one]
      ring
  refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := P.μ) hpoint).trans ?_
  have hsplit :
      P.μ[fun ω => S.wMin Λ ω * A ω
          + (S.wMax Λ ω - S.wMin Λ ω) * (A ω * I ω) | S.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => S.wMin Λ ω * A ω | S.sigmaX]
            + P.μ[fun ω => (S.wMax Λ ω - S.wMin Λ ω) * (A ω * I ω) | S.sigmaX] :=
    MeasureTheory.condExp_add hmin_int' hdiff_int S.sigmaX
  have hpullMin :
      P.μ[fun ω => S.wMin Λ ω * A ω | S.sigmaX]
        =ᵐ[P.μ] (fun ω => S.wMin Λ ω * S.propScore true ω) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaX) (μ := P.μ) hwMin_smeas hmin_int' hA_int
    exact h.trans (Filter.EventuallyEq.of_eq (by
      funext ω
      rfl))
  have hpullDiff :
      P.μ[fun ω => (S.wMax Λ ω - S.wMin Λ ω) * (A ω * I ω) | S.sigmaX]
        =ᵐ[P.μ] (fun ω => (S.wMax Λ ω - S.wMin Λ ω) * S.treatedSurv c ω) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaX) (μ := P.μ) hdiff_smeas hdiff_int hI_int
    exact h.trans (Filter.EventuallyEq.of_eq (by
      funext ω
      rfl))
  filter_upwards [hsplit, hpullMin, hpullDiff] with ω hsplitω hminω hdiffω
  rw [hsplitω]
  change P.μ[fun ω => S.wMin Λ ω * A ω | S.sigmaX] ω
      + P.μ[fun ω => (S.wMax Λ ω - S.wMin Λ ω) * (A ω * I ω) | S.sigmaX] ω
    = S.wMin Λ ω * S.propScore true ω + (S.wMax Λ ω - S.wMin Λ ω) * S.treatedSurv c ω
  rw [hminω, hdiffω]

/-- **Calibration from the survival equation.** If the conditional treated-survival of the cutoff
equals the target, the cutoff is calibrated. -/
theorem cutoffProp_calibrated_of_survival (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c)
    (hint : Integrable (fun ω => S.dVar.indicator true ω / S.cutoffProp Λ c ω) P.μ)
    (hint1 : Integrable (fun ω =>
      S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ)
    (hmin_int : Integrable (fun ω => S.dVar.indicator true ω * S.wMin Λ ω) P.μ)
    (hdiff_int : Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
      (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ)
    (hsurv : S.treatedSurv c =ᵐ[P.μ] S.survTarget Λ) :
    S.Calibrated (S.cutoffProp Λ c) := by
  unfold POBackdoorSystem.Calibrated
  have hΛ0 : 0 < Λ := lt_trans zero_lt_one hΛ
  refine (S.cutoff_calibValue_eq Λ c hc_meas hint hint1 hmin_int hdiff_int).trans ?_
  filter_upwards [hoverlap, hsurv] with ω hω hsurvω
  rw [hsurvω]
  set e : ℝ := S.propScore true ω with he_def
  have he0 : 0 < e := by simpa [he_def] using hω.1
  have he1 : e < 1 := by simpa [he_def] using hω.2
  have hdiff_pos : 0 < S.wMax Λ ω - S.wMin Λ ω := by
    simp only [POBackdoorSystem.wMax, POBackdoorSystem.wMin, ← he_def]
    have h1e : 0 < 1 - e := by linarith
    have hΛsq : 0 < Λ * Λ - 1 := by nlinarith
    field_simp [hΛ0.ne', he0.ne']
    nlinarith [h1e, hΛsq, hΛ0, he0]
  have hdiff_ne : S.wMax Λ ω - S.wMin Λ ω ≠ 0 := hdiff_pos.ne'
  unfold POBackdoorSystem.survTarget
  field_simp [hdiff_ne]
  ring

/-- **The cutoff propensity is always in the odds-ratio box.** For any cutoff `c`, the cutoff
weight is `wMin` or `wMax` (the box endpoints), so `cutoffProp Λ c ∈ MSMSet Λ`. -/
theorem cutoffProp_mem_MSMSet (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (c : P.Ω → ℝ) :
    S.cutoffProp Λ c ∈ S.MSMSet Λ := by
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
  have hae : ∀ᵐ ω ∂P.μ, (1 : ℝ) < S.wMin Λ ω ∧ S.wMin Λ ω ≤ S.wMax Λ ω := by
    filter_upwards [hoverlap] with ω hω
    set e : ℝ := S.propScore true ω with he_def
    have he0 : 0 < e := by simpa [he_def] using hω.1
    have he1 : e < 1 := by simpa [he_def] using hω.2
    have h1e : 0 < 1 - e := by linarith
    refine ⟨?_, ?_⟩
    · have : 0 < (1 - e) / (Λ * e) := by positivity
      simp only [POBackdoorSystem.wMin, ← he_def]
      linarith
    · simp only [POBackdoorSystem.wMin, POBackdoorSystem.wMax, ← he_def]
      have hd1 : (1 - e) / (Λ * e) ≤ Λ * (1 - e) / e := by
        rw [div_le_div_iff₀ (by positivity) he0]
        nlinarith [hΛ, mul_pos h1e he0, mul_pos hΛ0 he0,
          mul_nonneg (mul_nonneg (le_of_lt h1e) (le_of_lt he0)) (sub_nonneg.mpr hΛ)]
      linarith
  have hboxC : ∀ᵐ ω ∂P.μ,
      S.wMin Λ ω ≤ (if c ω < S.factualY ω then S.wMax Λ ω else S.wMin Λ ω)
        ∧ (if c ω < S.factualY ω then S.wMax Λ ω else S.wMin Λ ω) ≤ S.wMax Λ ω
        ∧ 1 < (if c ω < S.factualY ω then S.wMax Λ ω else S.wMin Λ ω) := by
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
    unfold POBackdoorSystem.cutoffProp
    constructor
    · positivity
    · rw [div_lt_one (by linarith)]
      linarith
  · filter_upwards [hoverlap, hboxC] with ω hov hw
    obtain ⟨he0, he1⟩ := hov
    obtain ⟨hmin, hmax, hwgt⟩ := hw
    set wC : ℝ := if c ω < S.factualY ω then S.wMax Λ ω else S.wMin Λ ω with hwC_def
    have hcut : S.cutoffProp Λ c ω = 1 / wC := by
      rw [POBackdoorSystem.cutoffProp, hwC_def]
    have het0 : 0 < S.cutoffProp Λ c ω := by
      rw [hcut]
      positivity
    have het1 : S.cutoffProp Λ c ω < 1 := by
      rw [hcut, div_lt_one (by linarith)]
      linarith
    rw [(hOR_box he0 he1 het0 het1)]
    have hinv : 1 / S.cutoffProp Λ c ω = wC := by
      rw [hcut, one_div_one_div]
    rw [hinv]
    simpa [POBackdoorSystem.wMin, POBackdoorSystem.wMax, hwC_def] using ⟨hmin, hmax⟩

/-- **Calibrated feasibility reduces to the survival equation.** If the cutoff `c` solves the
conditional treated-survival equation `G(c) = survTarget`, then
`cutoffProp Λ c ∈ MSMSetCalib Λ`, discharging the `hcut_mem` hypothesis of
`msmUpperCalib_eq_cutoff`. -/
theorem cutoffProp_mem_MSMSetCalib_of_survival (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c)
    (hint : Integrable (fun ω => S.dVar.indicator true ω / S.cutoffProp Λ c ω) P.μ)
    (hint1 : Integrable (fun ω =>
      S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ)
    (hmin_int : Integrable (fun ω => S.dVar.indicator true ω * S.wMin Λ ω) P.μ)
    (hdiff_int : Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
      (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ)
    (hsurv : S.treatedSurv c =ᵐ[P.μ] S.survTarget Λ) :
    S.cutoffProp Λ c ∈ S.MSMSetCalib Λ :=
    ⟨S.cutoffProp_mem_MSMSet Λ (le_of_lt hΛ) hoverlap c,
   S.cutoffProp_calibrated_of_survival Λ hΛ hoverlap c hc_meas hint hint1
     hmin_int hdiff_int hsurv⟩

end POBackdoorSystem

end PO
end Causalean
