/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — the Gaussian special case (Dorn–Guo corollary)

When the treated conditional outcome law `Y | X` (among the treated) is Gaussian `N(m(X), σ(X)²)`, the
calibrating quantile cutoff is fully explicit. Two ingredients:

* **The calibration level is exactly `Λ/(Λ+1)`, independent of the propensity.** Algebra:
  `survTarget = (1 − wMin·e)/(wMax − wMin) = e/(Λ+1)`, hence `calibLevel = 1 − survTarget/e = Λ/(Λ+1)`
  (and `calibLevelLower = 1/(Λ+1)`). So the sharp-bound cutoff is the `Λ/(Λ+1)` conditional quantile.

* **Under the Gaussian conditional law the cutoff is `c(X) = m(X) + σ(X)·Φ⁻¹(Λ/(Λ+1))`** — the explicit
  Gaussian quantile (`probit = Φ⁻¹` from `Mathlib/Probability/StdNormalCDF.lean`). It solves the survival
  equation `treatedSurv c =ᵐ survTarget Λ`, so the sharp upper bound is attained at this explicit cutoff.

This sidesteps the general measurable-selection: the quantile is closed-form. The subsequent
`GaussianHalfWidth.lean` file evaluates `candMean (cutoffProp Λ c)` to the closed-form half-width
`(Λ²−1)/Λ · φ(Φ⁻¹(Λ/(Λ+1))) · E[(1-e(X))σ(X)]` using the truncated Gaussian moment. -/

import Causalean.PO.ID.Partial.Sensitivity.MSM.CutoffConstruct
import Causalean.Mathlib.Probability.StdNormalCDF
import Causalean.Mathlib.Probability.StdNormalMoments

/-! # Gaussian treated-arm MSM cutoff formula

This file specializes the treated-arm calibrated MSM upper bound to conditional
Gaussian outcome laws. It proves the propensity-free calibration level
`calibLevel_eq`, introduces the conditional-Gaussian CDF assumption
`GaussianTreatedModel`, defines the explicit quantile cutoff `gaussianCutoff`,
proves `gaussianCutoff_calibrates`, and concludes with `msmUpperCalib_gaussian`:
the sharp calibrated upper endpoint is the candidate mean at that explicit
Gaussian cutoff. The separate half-width file evaluates that candidate mean in
closed form.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

private lemma survTarget_eq_prop_div (Λ : ℝ) (hΛ : 1 < Λ) {ω : P.Ω}
    (hω : 0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    S.survTarget Λ ω = S.propScore true ω / (Λ + 1) := by
  unfold POBackdoorSystem.survTarget POBackdoorSystem.wMin POBackdoorSystem.wMax
  set e := S.propScore true ω
  have he0pos : 0 < e := by simpa [e] using hω.1
  have he1 : e < 1 := by simpa [e] using hω.2
  have h1e : 0 < 1 - e := by linarith
  have hΛ0pos : 0 < Λ := by linarith
  have hΛmpos : 0 < Λ - 1 := by linarith
  have hΛppos : 0 < Λ + 1 := by linarith
  have he0 : e ≠ 0 := ne_of_gt he0pos
  have hΛ0 : Λ ≠ 0 := ne_of_gt hΛ0pos
  have hΛm : Λ - 1 ≠ 0 := ne_of_gt hΛmpos
  have hΛp : Λ + 1 ≠ 0 := ne_of_gt hΛppos
  have hnum : 1 - (1 + (1 - e) / (Λ * e)) * e = (1 - e) * (Λ - 1) / Λ := by
    field_simp [he0, hΛ0]
    ring
  have hdeneq :
      1 + Λ * (1 - e) / e - (1 + (1 - e) / (Λ * e)) =
        (1 - e) * (Λ - 1) * (Λ + 1) / (Λ * e) := by
    field_simp [he0, hΛ0]
    ring
  rw [hnum, hdeneq]
  field_simp [he0, hΛ0, hΛm, hΛp, ne_of_gt h1e]

/-- **The calibration level is exactly `Λ/(Λ+1)`.** Under overlap and `1 < Λ`, the sharp-upper-bound
quantile level `calibLevel = 1 − survTarget/e` equals `Λ/(Λ+1)` a.e., independent of the propensity
`e(X)` — because `survTarget = e/(Λ+1)`. Pure algebra from `wMin`, `wMax`. -/
theorem calibLevel_eq (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    ∀ᵐ ω ∂P.μ, S.calibLevel Λ ω = Λ / (Λ + 1) := by
  filter_upwards [hoverlap] with ω hω
  unfold POBackdoorSystem.calibLevel
  rw [S.survTarget_eq_prop_div Λ hΛ hω]
  have he0 : S.propScore true ω ≠ 0 := ne_of_gt hω.1
  have hΛp : Λ + 1 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < Λ + 1)
  field_simp [he0, hΛp]
  ring

/-- **The conditional-Gaussian treated-outcome model.** The treated conditional law of `Y` given
`X` is `N(m(X), σ(X)²)`: a measurable mean `m` and positive standard deviation `σ`
with `condCDF treatedXYLaw a t = Φ((t − m a)/σ a)` for all `a, t`. -/
structure GaussianTreatedModel (m σ : γ → ℝ) : Prop where
  measurable_m : Measurable m
  measurable_σ : Measurable σ
  σ_pos : ∀ a, 0 < σ a
  condCDF_eq : ∀ a t, condCDF S.treatedXYLaw a t
    = Causalean.Mathlib.stdNormalCDF ((t - m a) / σ a)

/-- The **explicit Gaussian cutoff** `c(X) = m(X) + σ(X)·Φ⁻¹(Λ/(Λ+1))`, the `Λ/(Λ+1)` conditional
quantile of the treated Gaussian outcome law. -/
noncomputable def gaussianCutoff (m σ : γ → ℝ) (Λ : ℝ) (ω : P.Ω) : ℝ :=
  m (S.factualX ω) + σ (S.factualX ω) * Causalean.Mathlib.probit (Λ / (Λ + 1))

/-- The explicit Gaussian cutoff is `σ(X)`-measurable. -/
theorem measurable_gaussianCutoff {m σ : γ → ℝ} (hm : Measurable m) (hσ : Measurable σ) (Λ : ℝ) :
    Measurable[S.sigmaX] (S.gaussianCutoff m σ Λ) := by
  unfold POBackdoorSystem.gaussianCutoff
  change Measurable[MeasurableSpace.comap S.factualX inferInstance]
    (fun ω => m (S.factualX ω) +
      σ (S.factualX ω) * Causalean.Mathlib.probit (Λ / (Λ + 1)))
  exact (hm.comp (comap_measurable S.factualX)).add
    ((hσ.comp (comap_measurable S.factualX)).mul measurable_const)

/-- **The explicit Gaussian cutoff calibrates.** Under the conditional-Gaussian model, the cutoff
`m(X) + σ(X)·Φ⁻¹(Λ/(Λ+1))` solves the survival equation `treatedSurv c =ᵐ survTarget Λ`. -/
theorem gaussianCutoff_calibrates (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    {m σ : γ → ℝ} (hmodel : S.GaussianTreatedModel m σ) :
    S.treatedSurv (S.gaussianCutoff m σ Λ) =ᵐ[P.μ] S.survTarget Λ := by
  have hc : Measurable[S.sigmaX] (S.gaussianCutoff m σ Λ) :=
    S.measurable_gaussianCutoff hmodel.measurable_m hmodel.measurable_σ Λ
  have hsurv := S.treatedSurv_eq (S.gaussianCutoff m σ Λ) hc
  filter_upwards [hsurv, hoverlap] with ω hsurvω hω
  rw [hsurvω]
  have hσpos : 0 < σ (S.factualX ω) := hmodel.σ_pos (S.factualX ω)
  have hσne : σ (S.factualX ω) ≠ 0 := ne_of_gt hσpos
  have hp0 : 0 < Λ / (Λ + 1) := by positivity
  have hp1 : Λ / (Λ + 1) < 1 := by
    have hΛp : 0 < Λ + 1 := by linarith
    rw [div_lt_one hΛp]
    linarith
  have hcdf : S.treatedCondCDF ω (S.gaussianCutoff m σ Λ ω) = Λ / (Λ + 1) := by
    unfold POBackdoorSystem.treatedCondCDF
    rw [hmodel.condCDF_eq]
    have harg :
        (S.gaussianCutoff m σ Λ ω - m (S.factualX ω)) / σ (S.factualX ω) =
          Causalean.Mathlib.probit (Λ / (Λ + 1)) := by
      unfold POBackdoorSystem.gaussianCutoff
      field_simp [hσne]
      ring
    rw [harg]
    exact Causalean.Mathlib.stdNormalCDF_probit hp0 hp1
  rw [hcdf, S.survTarget_eq_prop_div Λ hΛ hω]
  have hΛp_ne : Λ + 1 ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < Λ + 1)
  field_simp [hΛp_ne]
  ring

/-- **The sharp upper bound at the explicit Gaussian cutoff.** Under the conditional-Gaussian
model, the Dorn–Guo sharp upper bound is the quantile-balancing candidate mean at the explicit
Gaussian quantile cutoff:
`msmUpperCalib Λ = candMean (cutoffProp Λ (m(X) + σ(X)·Φ⁻¹(Λ/(Λ+1))))`. -/
theorem msmUpperCalib_gaussian (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    {m σ : γ → ℝ} (hmodel : S.GaussianTreatedModel m σ)
    (hmeas : ∀ etilde ∈ S.MSMSetCalib Λ, AEMeasurable etilde P.μ)
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
      Integrable (fun ω => |S.gaussianCutoff m σ Λ ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ) :
    S.msmUpperCalib Λ = S.candMean (S.cutoffProp Λ (S.gaussianCutoff m σ Λ)) := by
  let c := S.gaussianCutoff m σ Λ
  have hc : Measurable[S.sigmaX] c :=
    S.measurable_gaussianCutoff hmodel.measurable_m hmodel.measurable_σ Λ
  have hsurv : S.treatedSurv c =ᵐ[P.μ] S.survTarget Λ := by
    simpa [c] using S.gaussianCutoff_calibrates Λ hΛ hoverlap hmodel
  obtain ⟨hc_int, hint, hint1, hmin_int, hdiff_int,
    henv, hweight_env, hc_env⟩ := hreg
  have hcut_mem : S.cutoffProp Λ c ∈ S.MSMSetCalib Λ :=
    S.cutoffProp_mem_MSMSetCalib_of_survival Λ hΛ hoverlap c hc
      hint hint1 hmin_int hdiff_int hsurv
  exact S.msmUpperCalib_eq_cutoff Λ (le_of_lt hΛ) hoverlap c hc
    hc_int hcut_mem henv hweight_env hc_env hmeas

end POBackdoorSystem

end PO
end Causalean
