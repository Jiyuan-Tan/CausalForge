/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — quantile balancing (Dorn–Guo sharp upper bound)

The sharp (calibrated) upper bound `msmUpperCalib Λ` of `Bounds.lean`/`Sharp.lean` is attained by a
**quantile-cutoff** complete propensity (Dorn–Guo 2022): the worst-case inverse-propensity weight is

    w_c(ω) = wMax(ω)   if  Y(ω) > c(X(ω)),     wMin(ω)   if  Y(ω) ≤ c(X(ω)),

where the cutoff `c` is `σ(X)`-measurable and chosen so that the resulting candidate is *calibrated*
(`E[Z/(1/w_c) | σ(X)] = 1`); under continuous outcomes `c(X)` is the conditional quantile
`Q_{Λ/(Λ+1)}(X)` of `Y` among the treated. This file proves the **optimality** of that cutoff weight by
the Neyman–Pearson / Dantzig–Wald exchange argument: for any calibrated feasible candidate `ẽ`,

    candMean(ẽ) − candMean(1/w_c)
      = ∫ A·(Y − c)·(w_ẽ − w_c)        (the `c`-term cancels because both are calibrated)
      ≤ 0,                              (pointwise: `(Y − c)(w_ẽ − w_c) ≤ 0` by the box bound + cutoff sign)

so `candMean(ẽ) ≤ candMean(1/w_c)`, and hence `msmUpperCalib Λ = candMean(1/w_c)` — the sharp bound has
the quantile-balancing closed form.

**Scope.** This is the optimality / closed-form characterization given a calibrated cutoff. The
construction of `c` (the conditional quantile making `1/w_c` calibrated) is intentionally outside this
file and is discharged by the cutoff-selection and cutoff-construction modules.
-/

import Causalean.PO.ID.Partial.Sensitivity.MSM.Bounds
import Causalean.PO.ID.Partial.Sensitivity.MSM.Sharp

/-! # Quantile balancing for sharp MSM upper bounds

This file proves the Neyman-Pearson exchange argument behind the sharp treated
upper bound in the marginal sensitivity model. It defines the quantile-cutoff
complete propensity `cutoffProp`, proves the optimality theorem
`cutoff_optimal`, and derives `msmUpperCalib_eq_cutoff`: once the cutoff
candidate is calibrated and feasible, the sharp upper endpoint is exactly its
candidate mean.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- The **quantile-cutoff complete propensity** at cutoff function `c`: the candidate whose inverse
weight is `wMax` above the cutoff and `wMin` at or below it,
`1 / (wMax if Y > c(X) else wMin)`. -/
noncomputable def cutoffProp (Λ : ℝ) (c : P.Ω → ℝ) (ω : P.Ω) : ℝ :=
  1 / (if c ω < S.factualY ω then S.wMax Λ ω else S.wMin Λ ω)

/-- **Optimality of the quantile-cutoff weight (Neyman–Pearson exchange).** Among all calibrated,
data-compatible candidates, the cutoff weight maximizes the candidate mean: for any
`ẽ ∈ MSMSetCalib Λ`, `candMean ẽ ≤ candMean (cutoffProp Λ c)`.

Hypotheses: `1 ≤ Λ`; overlap; `c` is `σ(X)`-measurable; the cutoff candidate is itself feasible and
calibrated (`hcut_mem : cutoffProp Λ c ∈ MSMSetCalib Λ` — this is where the conditional-quantile
construction enters); and the envelope-integrability that makes all candidate means finite. -/
theorem cutoff_optimal (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c) (hc_int : Integrable c P.μ)
    (hcut_mem : S.cutoffProp Λ c ∈ S.MSMSetCalib Λ)
    (henv : Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ)
    (hweight_env : Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hc_env : Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    {etilde : P.Ω → ℝ} (hmem : etilde ∈ S.MSMSetCalib Λ)
    (hmeas : AEMeasurable etilde P.μ) :
    S.candMean etilde ≤ S.candMean (S.cutoffProp Λ c) := by
  classical
  have _ : Integrable c P.μ := hc_int
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  set A : P.Ω → ℝ := S.dVar.indicator true with hA_def
  set Y : P.Ω → ℝ := S.factualY with hY_def
  set e : P.Ω → ℝ := S.propScore true with he_def
  set wE : P.Ω → ℝ := fun ω => 1 / etilde ω with hwE_def
  set wC : P.Ω → ℝ :=
    fun ω => if c ω < Y ω then S.wMax Λ ω else S.wMin Λ ω with hwC_def
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
    exact S.dVar.measurable_indicator true
  have hYm : Measurable Y := by
    rw [hY_def]
    exact S.measurable_factualY
  have hem : Measurable e := by
    rw [he_def]
    unfold POBackdoorSystem.propScore
    exact (stronglyMeasurable_condExp.mono S.sigmaX_le).measurable
  have hwMaxm : Measurable (S.wMax Λ) := by
    unfold POBackdoorSystem.wMax
    exact (measurable_const.add
      ((measurable_const.mul (measurable_const.sub hem)).div hem))
  have hwMinm : Measurable (S.wMin Λ) := by
    unfold POBackdoorSystem.wMin
    exact (measurable_const.add
      ((measurable_const.sub hem).div (measurable_const.mul hem)))
  have hwCm : Measurable wC := by
    rw [hwC_def]
    exact Measurable.ite (measurableSet_lt (hc_meas.mono S.sigmaX_le le_rfl) hYm)
      hwMaxm hwMinm
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => by
    rcases S.dVar.indicator_eq_one_or_zero true ω with h | h <;> simp [hA_def, h]
  have hae : ∀ᵐ ω ∂P.μ, (1 : ℝ) < S.wMin Λ ω ∧ S.wMin Λ ω ≤ S.wMax Λ ω := by
    filter_upwards [hoverlap] with ω hω
    obtain ⟨he0ω, he1ω⟩ := hω
    have h1e : 0 < 1 - e ω := by rw [he_def] at *; linarith
    have he0' : 0 < e ω := by rw [he_def] at *; exact he0ω
    refine ⟨?_, ?_⟩
    · have : 0 < (1 - e ω) / (Λ * e ω) := by positivity
      simp only [POBackdoorSystem.wMin, ← he_def]
      linarith
    · simp only [POBackdoorSystem.wMin, POBackdoorSystem.wMax, ← he_def]
      have hd1 : (1 - e ω) / (Λ * e ω) ≤ Λ * (1 - e ω) / e ω := by
        rw [div_le_div_iff₀ (by positivity) he0']
        nlinarith [hΛ, mul_pos h1e he0', mul_pos hΛ0 he0',
          mul_nonneg (mul_nonneg (le_of_lt h1e) (le_of_lt he0')) (sub_nonneg.mpr hΛ)]
      linarith
  have hboxE : ∀ᵐ ω ∂P.μ,
      S.wMin Λ ω ≤ wE ω ∧ wE ω ≤ S.wMax Λ ω := by
    obtain ⟨hinterior, hor⟩ := hmem.1
    filter_upwards [hoverlap, hinterior, hor] with ω hov het hOR
    obtain ⟨he0ω, he1ω⟩ := hov
    obtain ⟨het0, het1⟩ := het
    have hbox := (hOR_box he0ω he1ω het0 het1).mp hOR
    simpa [POBackdoorSystem.wMin, POBackdoorSystem.wMax, he_def, hwE_def] using hbox
  have hboxC : ∀ᵐ ω ∂P.μ,
      S.wMin Λ ω ≤ wC ω ∧ wC ω ≤ S.wMax Λ ω ∧ 0 < wC ω := by
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
  have hXC_int : Integrable (fun ω => A ω / S.cutoffProp Λ c ω) P.μ := by
    have hAwC_int : Integrable (fun ω => A ω * wC ω) P.μ := by
      refine Integrable.mono' hweight_env ((hAm.mul hwCm).aestronglyMeasurable) ?_
      filter_upwards [hboxC] with ω hbox
      obtain ⟨_, hmax, hpos⟩ := hbox
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hA0 ω), abs_of_nonneg (le_of_lt hpos)]
      exact mul_le_mul_of_nonneg_left hmax (hA0 ω)
    refine hAwC_int.congr ?_
    filter_upwards [hboxC] with ω hbox
    change A ω * wC ω =
      A ω / (1 / (if c ω < S.factualY ω then S.wMax Λ ω else S.wMin Λ ω))
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
      simpa [POBackdoorSystem.Calibrated, hA_def] using hmem.2
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
    have hprod_int : Integrable (fun ω => c ω * (A ω / S.cutoffProp Λ c ω)) P.μ := by
      refine hcC_int.congr ?_
      filter_upwards [hboxC] with ω hbox
      change c ω * A ω * wC ω =
        c ω * (A ω / (1 / (if c ω < S.factualY ω then S.wMax Λ ω else S.wMin Λ ω)))
      rw [hwC_def, hY_def, div_div_eq_mul_div, div_one]
      ring
    have hpull :
        P.μ[fun ω => c ω * (A ω / S.cutoffProp Λ c ω) | S.sigmaX]
          =ᵐ[P.μ] (fun ω =>
            c ω * P.μ[fun ω => A ω / S.cutoffProp Λ c ω | S.sigmaX] ω) := by
      exact MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := S.sigmaX) (μ := P.μ) hc_meas.stronglyMeasurable hprod_int hXC_int
    have hcal :
        P.μ[fun ω => A ω / S.cutoffProp Λ c ω | S.sigmaX]
          =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
      simpa [POBackdoorSystem.Calibrated, hA_def] using hcut_mem.2
    have hmain :
        ∫ ω, c ω * (A ω / S.cutoffProp Λ c ω) ∂P.μ = ∫ ω, c ω ∂P.μ := by
      have hcond :
          ∫ ω, P.μ[fun ω => c ω * (A ω / S.cutoffProp Λ c ω) | S.sigmaX] ω ∂P.μ
            = ∫ ω, c ω * (A ω / S.cutoffProp Λ c ω) ∂P.μ :=
        MeasureTheory.integral_condExp S.sigmaX_le
      rw [← hcond]
      calc
        ∫ ω, P.μ[fun ω => c ω * (A ω / S.cutoffProp Λ c ω) | S.sigmaX] ω ∂P.μ
            = ∫ ω, c ω *
                P.μ[fun ω => A ω / S.cutoffProp Λ c ω | S.sigmaX] ω ∂P.μ :=
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
      c ω * (A ω / (1 / (if c ω < S.factualY ω then S.wMax Λ ω else S.wMin Λ ω)))
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
      S.candMean etilde =
        ∫ ω, A ω * (Y ω - c ω) * wE ω ∂P.μ
          + ∫ ω, c ω * A ω * wE ω ∂P.μ := by
    unfold POBackdoorSystem.candMean
    rw [← integral_add hfirstE_int hcE_int]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    change S.dVar.indicator true ω * S.factualY ω / etilde ω =
      S.dVar.indicator true ω * (S.factualY ω - c ω) * (1 / etilde ω) +
        c ω * S.dVar.indicator true ω * (1 / etilde ω)
    rw [div_eq_mul_inv, one_div]
    ring
  have hcandC :
      S.candMean (S.cutoffProp Λ c) =
        ∫ ω, A ω * (Y ω - c ω) * wC ω ∂P.μ
          + ∫ ω, c ω * A ω * wC ω ∂P.μ := by
    unfold POBackdoorSystem.candMean
    rw [← integral_add hfirstC_int hcC_int]
    refine integral_congr_ae ?_
    filter_upwards [hboxC] with ω hbox
    change S.dVar.indicator true ω * S.factualY ω /
        (1 / (if c ω < S.factualY ω then S.wMax Λ ω else S.wMin Λ ω))
      = A ω * (Y ω - c ω) * wC ω + c ω * A ω * wC ω
    rw [hwC_def, hA_def, hY_def, div_div_eq_mul_div, div_one]
    ring
  rw [hcandE, hcandC, hctermE_eq, hctermC_eq]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right hfirst_le (∫ ω, c ω ∂P.μ)

/-- **The sharp upper bound has the quantile-balancing closed form.** Given a calibrating cutoff
`c`, `msmUpperCalib Λ = candMean (cutoffProp Λ c)`: the cutoff candidate is feasible (so its mean is
`≤` the sup) and optimal (so the sup is `≤` its mean). -/
theorem msmUpperCalib_eq_cutoff (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (c : P.Ω → ℝ) (hc_meas : Measurable[S.sigmaX] c) (hc_int : Integrable c P.μ)
    (hcut_mem : S.cutoffProp Λ c ∈ S.MSMSetCalib Λ)
    (henv : Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ)
    (hweight_env : Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hc_env : Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hmeas : ∀ etilde ∈ S.MSMSetCalib Λ, AEMeasurable etilde P.μ) :
    S.msmUpperCalib Λ = S.candMean (S.cutoffProp Λ c) := by
  classical
  have hne : (S.candMean '' S.MSMSetCalib Λ).Nonempty :=
    ⟨S.candMean (S.cutoffProp Λ c), Set.mem_image_of_mem _ hcut_mem⟩
  have hle_all :
      ∀ x ∈ S.candMean '' S.MSMSetCalib Λ,
        x ≤ S.candMean (S.cutoffProp Λ c) := by
    rintro x ⟨etilde, hmem, rfl⟩
    exact S.cutoff_optimal Λ hΛ hoverlap c hc_meas hc_int hcut_mem henv hweight_env hc_env
      hmem (hmeas etilde hmem)
  have hbdd : BddAbove (S.candMean '' S.MSMSetCalib Λ) :=
    ⟨S.candMean (S.cutoffProp Λ c), hle_all⟩
  refine le_antisymm ?_ ?_
  · unfold POBackdoorSystem.msmUpperCalib
    exact csSup_le hne hle_all
  · unfold POBackdoorSystem.msmUpperCalib
    exact le_csSup hbdd (Set.mem_image_of_mem _ hcut_mem)

end POBackdoorSystem

end PO
end Causalean
