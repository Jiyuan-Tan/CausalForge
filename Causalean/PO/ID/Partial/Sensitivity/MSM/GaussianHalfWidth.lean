/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — the Gaussian sharp half-width (Dorn–Guo corollary, closed form)

The headline Dorn–Guo Gaussian number. Under a conditional-Gaussian treated outcome law `Y | X ~
N(m(X), σ(X)²)`, the sharp upper bound on `E[Y(1)]` evaluates in closed form:

    msmUpperCalib Λ = ∫ m(X) dμ  +  (Λ²−1)/Λ · φ(Φ⁻¹(Λ/(Λ+1))) · ∫ (1 − e(X))·σ(X) dμ,

the point-identified (NUC) mean `∫ m(X)` plus the half-width with factor `gaussianMSMHalfWidthFactor`.

The evaluation uses `msmUpperCalib_gaussian` (the bound is `candMean` at the explicit Gaussian quantile
cutoff `c = m + σ·Φ⁻¹(Λ/(Λ+1))`), then the two Gaussian conditional moments — the conditional mean
`E[A·Y|σX] = e·m` and the conditional truncated mean `E[A·Y·1{Y>c}|σX] = e·(m·(1−Φ) + σ·φ)`
(`GaussianOutcomeModel`, the faithful "conditionally Gaussian outcomes" premise, with the truncated mean
in the form of `GaussianMoments.integral_Ioi_id_gaussianReal`) — and the per-stratum algebra
`wMin·e + (wMax−wMin)·e/(Λ+1) = 1`, `(wMax−wMin)·e = (1−e)(Λ²−1)/Λ`, at the cutoff where
`(c−m)/σ = Φ⁻¹(Λ/(Λ+1))`. -/

import Causalean.PO.ID.Partial.Sensitivity.MSM.Gaussian
import Causalean.Mathlib.Probability.GaussianMoments

/-! # Gaussian MSM half-width formula

This file evaluates the calibrated Gaussian MSM upper endpoint in closed form.
It defines the scalar `gaussianMSMHalfWidthFactor`, strengthens the CDF-only
Gaussian cutoff model to `GaussianOutcomeModel` with conditional mean and
truncated-mean identities, and proves `msmUpperCalib_gaussian_halfWidth`: the
sharp upper bound is the point-identified conditional mean plus the Dorn-Guo
half-width contribution.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- **Dorn–Guo Gaussian half-width factor.** For `τ = Λ/(Λ+1)` with `Λ ≥ 1`, the per-stratum
MSM sharp half-width factor is `(Λ²−1)/Λ · φ(Φ⁻¹(τ))`. This packages the scalar appearing in
the Gaussian ATE interval `[ψ ± (Λ²−1)/Λ · φ(Φ⁻¹(Λ/(Λ+1))) · E[σ(X)]]`. -/
noncomputable def gaussianMSMHalfWidthFactor (Λ : ℝ) : ℝ :=
  (Λ ^ 2 - 1) / Λ * Causalean.Mathlib.stdNormalPDF
    (Causalean.Mathlib.probit (Λ / (Λ + 1)))

private lemma gaussian_halfWidth_scalar (Λ e M s φ : ℝ) (hΛ : 1 < Λ)
    (he0 : 0 < e) (_he1 : e < 1) :
    (1 + (1 - e) / (Λ * e)) * (e * M) +
      ((1 + Λ * (1 - e) / e) - (1 + (1 - e) / (Λ * e))) *
        (e * (M * (1 / (Λ + 1)) + s * φ)) =
      M + ((Λ ^ 2 - 1) / Λ * φ) * ((1 - e) * s) := by
  have hΛ0 : Λ ≠ 0 := by linarith
  have he0' : e ≠ 0 := by linarith
  have hΛp : Λ + 1 ≠ 0 := by linarith
  field_simp [hΛ0, he0', hΛp]
  ring

private lemma integral_mul_condExp_eq {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} {m0 : MeasurableSpace Ω} (hm0 : m0 ≤ mΩ)
    [SigmaFinite (μ.trim hm0)] {h f : Ω → ℝ}
    (hh : StronglyMeasurable[m0] h)
    (hf : Integrable f μ) (hhf : Integrable (h * f) μ) :
    ∫ ω, h ω * f ω ∂μ = ∫ ω, h ω * μ[f | m0] ω ∂μ := by
  have hpull : μ[h * f | m0] =ᵐ[μ] h * μ[f | m0] :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := m0) (μ := μ) hh hhf hf
  have hcond : ∫ ω, μ[h * f | m0] ω ∂μ = ∫ ω, (h * f) ω ∂μ :=
    MeasureTheory.integral_condExp hm0
  change ∫ ω, (h * f) ω ∂μ = ∫ ω, (h * μ[f | m0]) ω ∂μ
  rw [← hcond]
  exact integral_congr_ae hpull

private lemma gaussianCutoff_standardized {m σ : γ → ℝ}
    (hmodel : S.GaussianTreatedModel m σ) (Λ : ℝ) (ω : P.Ω) :
    (S.gaussianCutoff m σ Λ ω - m (S.factualX ω)) / σ (S.factualX ω) =
      Causalean.Mathlib.probit (Λ / (Λ + 1)) := by
  have hσne : σ (S.factualX ω) ≠ 0 := ne_of_gt (hmodel.σ_pos (S.factualX ω))
  unfold POBackdoorSystem.gaussianCutoff
  field_simp [hσne]
  ring

private lemma integrable_treatedY_of_wMax_envelope (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (henv : Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ) :
    Integrable (fun ω => S.dVar.indicator true ω * S.factualY ω) P.μ := by
  have hA_nonneg : ∀ ω, 0 ≤ S.dVar.indicator true ω := by
    intro ω
    rcases S.dVar.indicator_eq_one_or_zero true ω with h | h <;> simp [h]
  have hwMax_ge_one : ∀ᵐ ω ∂P.μ, 1 ≤ S.wMax Λ ω := by
    filter_upwards [hoverlap] with ω hω
    unfold POBackdoorSystem.wMax
    have hΛpos : 0 < Λ := by linarith
    have hnum : 0 < 1 - S.propScore true ω := by linarith [hω.2]
    have hterm : 0 ≤ Λ * (1 - S.propScore true ω) / S.propScore true ω :=
      div_nonneg (mul_nonneg (le_of_lt hΛpos) (le_of_lt hnum)) (le_of_lt hω.1)
    linarith
  refine Integrable.mono' henv
    ((S.dVar.measurable_indicator true).mul S.measurable_factualY).aestronglyMeasurable ?_
  filter_upwards [hwMax_ge_one] with ω hw
  rw [Real.norm_eq_abs, abs_mul]
  have hAabs : |S.dVar.indicator true ω| = S.dVar.indicator true ω :=
    abs_of_nonneg (hA_nonneg ω)
  rw [hAabs]
  have hbase : 0 ≤ S.dVar.indicator true ω * |S.factualY ω| :=
    mul_nonneg (hA_nonneg ω) (abs_nonneg _)
  calc
    S.dVar.indicator true ω * |S.factualY ω|
        = S.dVar.indicator true ω * |S.factualY ω| * 1 := by ring
    _ ≤ S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω :=
      mul_le_mul_of_nonneg_left hw hbase

private lemma integrable_treatedY_trunc_of_wMax_envelope (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (c : P.Ω → ℝ) (hc : Measurable[S.sigmaX] c)
    (henv : Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ) :
    Integrable (fun ω => S.dVar.indicator true ω * S.factualY ω *
      (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ := by
  have hA_nonneg : ∀ ω, 0 ≤ S.dVar.indicator true ω := by
    intro ω
    rcases S.dVar.indicator_eq_one_or_zero true ω with h | h <;> simp [h]
  have hI_nonneg : ∀ ω, 0 ≤ (if c ω < S.factualY ω then (1 : ℝ) else 0) := by
    intro ω
    split <;> positivity
  have hI_le_one : ∀ ω, (if c ω < S.factualY ω then (1 : ℝ) else 0) ≤ 1 := by
    intro ω
    split <;> norm_num
  have hwMax_ge_one : ∀ᵐ ω ∂P.μ, 1 ≤ S.wMax Λ ω := by
    filter_upwards [hoverlap] with ω hω
    unfold POBackdoorSystem.wMax
    have hΛpos : 0 < Λ := by linarith
    have hnum : 0 < 1 - S.propScore true ω := by linarith [hω.2]
    have hterm : 0 ≤ Λ * (1 - S.propScore true ω) / S.propScore true ω :=
      div_nonneg (mul_nonneg (le_of_lt hΛpos) (le_of_lt hnum)) (le_of_lt hω.1)
    linarith
  have hImeas : Measurable (fun ω => if c ω < S.factualY ω then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lt (hc.mono S.sigmaX_le le_rfl) S.measurable_factualY)
      measurable_const measurable_const
  refine Integrable.mono' henv
    (((S.dVar.measurable_indicator true).mul S.measurable_factualY).mul hImeas).aestronglyMeasurable ?_
  filter_upwards [hwMax_ge_one] with ω hw
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have hAabs : |S.dVar.indicator true ω| = S.dVar.indicator true ω :=
    abs_of_nonneg (hA_nonneg ω)
  have hIabs : |(if c ω < S.factualY ω then (1 : ℝ) else 0)| =
      (if c ω < S.factualY ω then (1 : ℝ) else 0) :=
    abs_of_nonneg (hI_nonneg ω)
  rw [hAabs, hIabs]
  have hbase : 0 ≤ S.dVar.indicator true ω * |S.factualY ω| :=
    mul_nonneg (hA_nonneg ω) (abs_nonneg _)
  calc
    S.dVar.indicator true ω * |S.factualY ω| *
        (if c ω < S.factualY ω then (1 : ℝ) else 0)
        ≤ S.dVar.indicator true ω * |S.factualY ω| * 1 :=
      mul_le_mul_of_nonneg_left (hI_le_one ω) hbase
    _ = S.dVar.indicator true ω * |S.factualY ω| := by ring
    _ ≤ S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω := by
      calc
        S.dVar.indicator true ω * |S.factualY ω|
            = S.dVar.indicator true ω * |S.factualY ω| * 1 := by ring
        _ ≤ S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω :=
          mul_le_mul_of_nonneg_left hw hbase

/-- **The conditional-Gaussian outcome model.** Strengthens `GaussianTreatedModel` (conditional
CDF `Φ((·−m)/σ)`) with the two conditional moments it implies: the treated conditional mean
`E[A·Y|σX] = e(X)·m(X)` and the truncated mean above any `σ(X)`-measurable cutoff.
This is the faithful "treated outcomes are conditionally Gaussian `N(m(X), σ(X)²)`" premise
of the Dorn–Guo corollary. -/
structure GaussianOutcomeModel (m σ : γ → ℝ) : Prop extends S.GaussianTreatedModel m σ where
  condMean_eq :
    P.μ[fun ω => S.dVar.indicator true ω * S.factualY ω | S.sigmaX]
      =ᵐ[P.μ] fun ω => S.propScore true ω * m (S.factualX ω)
  condTruncMean_eq : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
    P.μ[fun ω => S.dVar.indicator true ω * S.factualY ω *
        (if c ω < S.factualY ω then (1 : ℝ) else 0) | S.sigmaX]
      =ᵐ[P.μ] fun ω => S.propScore true ω *
        (m (S.factualX ω) *
            (1 - Causalean.Mathlib.stdNormalCDF ((c ω - m (S.factualX ω)) / σ (S.factualX ω)))
          + σ (S.factualX ω) *
            Causalean.Mathlib.stdNormalPDF ((c ω - m (S.factualX ω)) / σ (S.factualX ω)))

/-- **The Dorn–Guo Gaussian sharp upper bound, closed form.** Under the conditional-Gaussian
outcome model, the sharp upper bound on `E[Y(1)]` equals the point-identified mean
`∫ m(X)` plus the half-width
`(Λ²−1)/Λ · φ(Φ⁻¹(Λ/(Λ+1))) · ∫ (1 − e(X))·σ(X)`. -/
theorem msmUpperCalib_gaussian_halfWidth (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    {m σ : γ → ℝ} (hmodel : S.GaussianOutcomeModel m σ)
    (hmeas : ∀ etilde ∈ S.MSMSetCalib Λ, AEMeasurable etilde P.μ)
    (hint_m : Integrable (fun ω => m (S.factualX ω)) P.μ)
    (hint_σ : Integrable (fun ω => (1 - S.propScore true ω) * σ (S.factualX ω)) P.μ)
    (hreg : Integrable (S.gaussianCutoff m σ Λ) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω / S.cutoffProp Λ (S.gaussianCutoff m σ Λ) ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω *
        (if S.gaussianCutoff m σ Λ ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMin Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (S.dVar.indicator true ω *
          (if S.gaussianCutoff m σ Λ ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => |S.gaussianCutoff m σ Λ ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hint_candMin : Integrable (fun ω => S.wMin Λ ω *
      (S.dVar.indicator true ω * S.factualY ω)) P.μ)
    (hint_candTrunc : Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
      (S.dVar.indicator true ω * S.factualY ω *
        (if S.gaussianCutoff m σ Λ ω < S.factualY ω then (1 : ℝ) else 0))) P.μ) :
    S.msmUpperCalib Λ
      = (∫ ω, m (S.factualX ω) ∂P.μ)
        + gaussianMSMHalfWidthFactor Λ
          * ∫ ω, (1 - S.propScore true ω) * σ (S.factualX ω) ∂P.μ := by
  classical
  let c : P.Ω → ℝ := S.gaussianCutoff m σ Λ
  let A : P.Ω → ℝ := S.dVar.indicator true
  let Y : P.Ω → ℝ := S.factualY
  let e : P.Ω → ℝ := S.propScore true
  let M : P.Ω → ℝ := fun ω => m (S.factualX ω)
  let sig : P.Ω → ℝ := fun ω => σ (S.factualX ω)
  let z : ℝ := Causalean.Mathlib.probit (Λ / (Λ + 1))
  let K : ℝ := (Λ ^ 2 - 1) / Λ * Causalean.Mathlib.stdNormalPDF z
  have hc : Measurable[S.sigmaX] c := by
    simpa [c] using S.measurable_gaussianCutoff hmodel.measurable_m hmodel.measurable_σ Λ
  have hreg_all := hreg
  obtain ⟨_hc_int, _hcut_int, _hI_int, _hmin_int, _hdiff_int,
    henvY, _hweight_env, _hc_env⟩ := hreg
  have hAY_int : Integrable (fun ω => A ω * Y ω) P.μ := by
    simpa [A, Y] using
      S.integrable_treatedY_of_wMax_envelope Λ hΛ hoverlap henvY
  have hAYI_int : Integrable
      (fun ω => A ω * Y ω * (if c ω < Y ω then (1 : ℝ) else 0)) P.μ := by
    simpa [A, Y, c] using
      S.integrable_treatedY_trunc_of_wMax_envelope Λ hΛ hoverlap c hc henvY
  have hprop_meas : Measurable[S.sigmaX] (S.propScore true) := by
    unfold POBackdoorSystem.propScore
    exact stronglyMeasurable_condExp.measurable
  have hwMin_smeas : StronglyMeasurable[S.sigmaX] (S.wMin Λ) := by
    unfold POBackdoorSystem.wMin
    exact (measurable_const.add
      ((measurable_const.sub hprop_meas).div
        (measurable_const.mul hprop_meas))).stronglyMeasurable
  have hwMax_smeas : StronglyMeasurable[S.sigmaX] (S.wMax Λ) := by
    unfold POBackdoorSystem.wMax
    exact (measurable_const.add
      ((measurable_const.mul (measurable_const.sub hprop_meas)).div
        hprop_meas)).stronglyMeasurable
  have hdiff_smeas :
      StronglyMeasurable[S.sigmaX] (fun ω => S.wMax Λ ω - S.wMin Λ ω) :=
    (hwMax_smeas.measurable.sub hwMin_smeas.measurable).stronglyMeasurable
  have hmain :
      S.msmUpperCalib Λ = S.candMean (S.cutoffProp Λ c) := by
    simpa [c] using
      S.msmUpperCalib_gaussian Λ hΛ hoverlap hmodel.toGaussianTreatedModel hmeas hreg_all
  have hcand_split :
      S.candMean (S.cutoffProp Λ c) =
        ∫ ω, S.wMin Λ ω * (A ω * Y ω) ∂P.μ +
          ∫ ω, (S.wMax Λ ω - S.wMin Λ ω) *
            (A ω * Y ω * (if c ω < Y ω then (1 : ℝ) else 0)) ∂P.μ := by
    unfold POBackdoorSystem.candMean
    rw [← integral_add hint_candMin hint_candTrunc]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    by_cases hcy : c ω < Y ω
    · have hcy' : S.gaussianCutoff m σ Λ ω < S.factualY ω := by
        simpa [c, Y] using hcy
      simp only [c, A, Y, POBackdoorSystem.cutoffProp, if_pos hcy, if_pos hcy']
      rw [div_div_eq_mul_div, div_one]
      ring
    · have hcy' : ¬S.gaussianCutoff m σ Λ ω < S.factualY ω := by
        simpa [c, Y] using hcy
      simp only [c, A, Y, POBackdoorSystem.cutoffProp, if_neg hcy, if_neg hcy']
      rw [div_div_eq_mul_div, div_one]
      ring
  have hint_candTrunc_prod :
      Integrable
        ((fun ω => S.wMax Λ ω - S.wMin Λ ω) *
          fun ω => A ω * Y ω * (if c ω < Y ω then (1 : ℝ) else 0)) P.μ := by
    refine hint_candTrunc.congr (Filter.Eventually.of_forall ?_)
    intro ω
    by_cases hcy : c ω < Y ω
    · simp [A, Y, c, hcy]
    · simp [A, Y, c, hcy]
  have hmin_pull :
      ∫ ω, S.wMin Λ ω * (A ω * Y ω) ∂P.μ =
        ∫ ω, S.wMin Λ ω *
          P.μ[fun ω => A ω * Y ω | S.sigmaX] ω ∂P.μ := by
    simpa [Pi.mul_apply] using
      integral_mul_condExp_eq (μ := P.μ) (m0 := S.sigmaX) S.sigmaX_le
        hwMin_smeas hAY_int (by simpa [A, Y] using hint_candMin)
  have hmin_ae :
      (fun ω => S.wMin Λ ω *
          P.μ[fun ω => A ω * Y ω | S.sigmaX] ω)
        =ᵐ[P.μ] fun ω => S.wMin Λ ω * (e ω * M ω) := by
    filter_upwards [hmodel.condMean_eq] with ω hω
    simpa [A, Y, e, M] using congrArg (fun t => S.wMin Λ ω * t) hω
  have hmin_int_eval : Integrable (fun ω => S.wMin Λ ω * (e ω * M ω)) P.μ := by
    have hpull :
        P.μ[fun ω => S.wMin Λ ω * (A ω * Y ω) | S.sigmaX]
          =ᵐ[P.μ] fun ω => S.wMin Λ ω *
            P.μ[fun ω => A ω * Y ω | S.sigmaX] ω :=
      MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := S.sigmaX) (μ := P.μ) hwMin_smeas
        (by simpa [A, Y] using hint_candMin) hAY_int
    exact (MeasureTheory.integrable_condExp
      (μ := P.μ) (m := S.sigmaX)
      (f := fun ω => S.wMin Λ ω * (A ω * Y ω))).congr
        (hpull.trans hmin_ae)
  have hmin_eval :
      ∫ ω, S.wMin Λ ω * (A ω * Y ω) ∂P.μ =
        ∫ ω, S.wMin Λ ω * (e ω * M ω) ∂P.μ := by
    rw [hmin_pull]
    exact integral_congr_ae hmin_ae
  have htrunc_pull :
      ∫ ω, (S.wMax Λ ω - S.wMin Λ ω) *
            (A ω * Y ω * (if c ω < Y ω then (1 : ℝ) else 0)) ∂P.μ =
        ∫ ω, (S.wMax Λ ω - S.wMin Λ ω) *
          P.μ[fun ω => A ω * Y ω * (if c ω < Y ω then (1 : ℝ) else 0) |
            S.sigmaX] ω ∂P.μ := by
    simpa [Pi.mul_apply] using
      integral_mul_condExp_eq (μ := P.μ) (m0 := S.sigmaX) S.sigmaX_le
        hdiff_smeas hAYI_int hint_candTrunc_prod
  have htrunc_ae :
      (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
          P.μ[fun ω => A ω * Y ω * (if c ω < Y ω then (1 : ℝ) else 0) |
            S.sigmaX] ω)
        =ᵐ[P.μ] fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
          (e ω * (M ω *
              (1 - Causalean.Mathlib.stdNormalCDF ((c ω - M ω) / sig ω))
            + sig ω *
              Causalean.Mathlib.stdNormalPDF ((c ω - M ω) / sig ω))) := by
    filter_upwards [hmodel.condTruncMean_eq c hc] with ω hω
    simpa [A, Y, e, M, sig] using
      congrArg (fun t => (S.wMax Λ ω - S.wMin Λ ω) * t) hω
  have htrunc_int_eval : Integrable
      (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (e ω * (M ω *
            (1 - Causalean.Mathlib.stdNormalCDF ((c ω - M ω) / sig ω))
          + sig ω *
            Causalean.Mathlib.stdNormalPDF ((c ω - M ω) / sig ω)))) P.μ := by
    have hpull :
        P.μ[fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
            (A ω * Y ω * (if c ω < Y ω then (1 : ℝ) else 0)) | S.sigmaX]
          =ᵐ[P.μ] fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
            P.μ[fun ω => A ω * Y ω *
              (if c ω < Y ω then (1 : ℝ) else 0) | S.sigmaX] ω :=
      MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := S.sigmaX) (μ := P.μ) hdiff_smeas
        hint_candTrunc_prod hAYI_int
    exact (MeasureTheory.integrable_condExp
      (μ := P.μ) (m := S.sigmaX)
      (f := fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (A ω * Y ω * (if c ω < Y ω then (1 : ℝ) else 0)))).congr
        (hpull.trans htrunc_ae)
  have htrunc_eval :
      ∫ ω, (S.wMax Λ ω - S.wMin Λ ω) *
            (A ω * Y ω * (if c ω < Y ω then (1 : ℝ) else 0)) ∂P.μ =
        ∫ ω, (S.wMax Λ ω - S.wMin Λ ω) *
          (e ω * (M ω *
              (1 - Causalean.Mathlib.stdNormalCDF ((c ω - M ω) / sig ω))
            + sig ω *
              Causalean.Mathlib.stdNormalPDF ((c ω - M ω) / sig ω))) ∂P.μ := by
    rw [htrunc_pull]
    exact integral_congr_ae htrunc_ae
  have hp0 : 0 < Λ / (Λ + 1) := by positivity
  have hp1 : Λ / (Λ + 1) < 1 := by
    have hΛp : 0 < Λ + 1 := by linarith
    rw [div_lt_one hΛp]
    linarith
  have honeMinus : 1 - Λ / (Λ + 1) = 1 / (Λ + 1) := by
    have hΛp : Λ + 1 ≠ 0 := by linarith
    field_simp [hΛp]
    ring
  have hscalar_ae :
      (fun ω => S.wMin Λ ω * (e ω * M ω) +
        (S.wMax Λ ω - S.wMin Λ ω) *
          (e ω * (M ω *
              (1 - Causalean.Mathlib.stdNormalCDF ((c ω - M ω) / sig ω))
            + sig ω *
              Causalean.Mathlib.stdNormalPDF ((c ω - M ω) / sig ω))))
        =ᵐ[P.μ] fun ω => M ω + K * ((1 - e ω) * sig ω) := by
    filter_upwards [hoverlap] with ω hω
    have harg :
        (c ω - M ω) / sig ω = z := by
      simpa [c, M, sig, z] using
        S.gaussianCutoff_standardized hmodel.toGaussianTreatedModel Λ ω
    have hcdf :
        Causalean.Mathlib.stdNormalCDF ((c ω - M ω) / sig ω) = Λ / (Λ + 1) := by
      rw [harg]
      exact Causalean.Mathlib.stdNormalCDF_probit hp0 hp1
    have hpdf :
        Causalean.Mathlib.stdNormalPDF ((c ω - M ω) / sig ω) =
          Causalean.Mathlib.stdNormalPDF z := by
      rw [harg]
    have hscalar := gaussian_halfWidth_scalar Λ (e ω) (M ω) (sig ω)
      (Causalean.Mathlib.stdNormalPDF z) hΛ hω.1 hω.2
    unfold POBackdoorSystem.wMin POBackdoorSystem.wMax
    rw [hcdf, hpdf, honeMinus]
    simpa [e, K, z, mul_assoc, mul_left_comm, mul_comm] using hscalar
  have hcombined :
      (∫ ω, S.wMin Λ ω * (e ω * M ω) ∂P.μ) +
        ∫ ω, (S.wMax Λ ω - S.wMin Λ ω) *
          (e ω * (M ω *
              (1 - Causalean.Mathlib.stdNormalCDF ((c ω - M ω) / sig ω))
            + sig ω *
              Causalean.Mathlib.stdNormalPDF ((c ω - M ω) / sig ω))) ∂P.μ =
        ∫ ω, M ω + K * ((1 - e ω) * sig ω) ∂P.μ := by
    rw [← integral_add hmin_int_eval htrunc_int_eval]
    exact integral_congr_ae hscalar_ae
  have hsplit_final :
      ∫ ω, M ω + K * ((1 - e ω) * sig ω) ∂P.μ =
        (∫ ω, M ω ∂P.μ) + K * ∫ ω, (1 - e ω) * sig ω ∂P.μ := by
    have hM_int : Integrable M P.μ := by
      simpa [M] using hint_m
    have hσ_int : Integrable (fun ω => (1 - e ω) * sig ω) P.μ := by
      simpa [e, sig] using hint_σ
    rw [integral_add hM_int (hσ_int.const_mul K)]
    rw [integral_const_mul]
  calc
    S.msmUpperCalib Λ = S.candMean (S.cutoffProp Λ c) := hmain
    _ = (∫ ω, S.wMin Λ ω * (A ω * Y ω) ∂P.μ) +
          ∫ ω, (S.wMax Λ ω - S.wMin Λ ω) *
            (A ω * Y ω * (if c ω < Y ω then (1 : ℝ) else 0)) ∂P.μ := hcand_split
    _ = (∫ ω, S.wMin Λ ω * (e ω * M ω) ∂P.μ) +
          ∫ ω, (S.wMax Λ ω - S.wMin Λ ω) *
            (e ω * (M ω *
                (1 - Causalean.Mathlib.stdNormalCDF ((c ω - M ω) / sig ω))
              + sig ω *
                Causalean.Mathlib.stdNormalPDF ((c ω - M ω) / sig ω))) ∂P.μ := by
      rw [hmin_eval, htrunc_eval]
    _ = ∫ ω, M ω + K * ((1 - e ω) * sig ω) ∂P.μ := hcombined
    _ = (∫ ω, M ω ∂P.μ) + K * ∫ ω, (1 - e ω) * sig ω ∂P.μ := hsplit_final
    _ = (∫ ω, m (S.factualX ω) ∂P.μ)
        + gaussianMSMHalfWidthFactor Λ
          * ∫ ω, (1 - S.propScore true ω) * σ (S.factualX ω) ∂P.μ := by
      simp [M, e, sig, K, z, gaussianMSMHalfWidthFactor]

end POBackdoorSystem

end PO
end Causalean
