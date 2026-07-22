/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — calibration brackets for the quantile cutoff

The quantile-balancing closed form `msmUpperCalib_eq_cutoff` (in `QuantileBalance.lean`) takes as a
hypothesis that a *calibrating cutoff* `c` exists — a `σ(X)`-measurable function for which the
cutoff propensity `cutoffProp Λ c` is calibrated (`E[Z/cutoffProp Λ c | σ(X)] = 1`). The cutoff is
the conditional quantile `Q_{Λ/(Λ+1)}(X)` of `Y` among the treated, and its construction is a
conditional-quantile / measurable-selection argument (Mathlib `condCDF` + an intermediate-value step).

This file proves the **analytic foundation** for that construction: the conditional calibration value
of the cutoff propensity is monotone in the cutoff and, at the two extremes (`c → ±∞`, i.e. the all-`wMax`
and all-`wMin` weights), takes the values `wMax·e` and `wMin·e`, which **bracket** the target `1`:

    wMin(X)·e(X) = e + (1−e)/Λ ≤ 1 ≤ e + Λ(1−e) = wMax(X)·e(X)    (Λ ≥ 1, 0 < e(X) < 1).

Since `E[Z·wMin | σ(X)] = wMin·e ≤ 1 ≤ wMax·e = E[Z·wMax | σ(X)]`, these lemmas
provide the bracket used by the cutoff-selection and quantile-balancing modules.
-/

import Causalean.PO.ID.Partial.Sensitivity.MSM.Bounds

/-! # Existence interface for calibrated MSM cutoffs

This file isolates the existence and regularity assumptions for treated-arm
calibrating cutoffs. It packages the facts needed to turn a conditional-quantile
cutoff into a calibrated candidate weight for the sharp MSM upper bound.

The public results are the endpoint bracket inequalities
`wMin_mul_propScore_le_one` and `one_le_wMax_mul_propScore`, together with the
conditional-expectation pullout identities `condExp_treat_wMin_eq` and
`condExp_treat_wMax_eq`.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- **Lower calibration bracket (algebraic).** With `Λ ≥ 1` and overlap
`0 < e(X) < 1`, the all-`wMin` calibration value satisfies
`wMin(X)·e(X) = e + (1−e)/Λ ≤ 1`. -/
theorem wMin_mul_propScore_le_one (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    ∀ᵐ ω ∂P.μ, S.wMin Λ ω * S.propScore true ω ≤ 1 := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  filter_upwards [hoverlap] with ω hω
  set e : ℝ := S.propScore true ω with he_def
  have he0 : 0 < e := by simpa [he_def] using hω.1
  have he1 : e < 1 := by simpa [he_def] using hω.2
  have hw :
      S.wMin Λ ω * S.propScore true ω = e + (1 - e) / Λ := by
    simp only [POBackdoorSystem.wMin, ← he_def]
    field_simp [hΛ0.ne', he0.ne']
  have hdiv : (1 - e) / Λ ≤ 1 - e := by
    rw [div_le_iff₀ hΛ0]
    nlinarith [hΛ, le_of_lt he1]
  calc
    S.wMin Λ ω * S.propScore true ω = e + (1 - e) / Λ := hw
    _ ≤ e + (1 - e) := by linarith
    _ = 1 := by ring

/-- **Upper calibration bracket (algebraic).** With `Λ ≥ 1` and overlap, the all-`wMax` calibration
value satisfies `1 ≤ wMax(X)·e(X) = e + Λ(1−e)`. -/
theorem one_le_wMax_mul_propScore (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    ∀ᵐ ω ∂P.μ, 1 ≤ S.wMax Λ ω * S.propScore true ω := by
  filter_upwards [hoverlap] with ω hω
  set e : ℝ := S.propScore true ω with he_def
  have he0 : 0 < e := by simpa [he_def] using hω.1
  have he1 : e < 1 := by simpa [he_def] using hω.2
  have hw :
      S.wMax Λ ω * S.propScore true ω = e + Λ * (1 - e) := by
    simp only [POBackdoorSystem.wMax, ← he_def]
    field_simp [he0.ne']
  have hmul : 1 - e ≤ Λ * (1 - e) := by
    nlinarith [hΛ, le_of_lt he1]
  calc
    1 = e + (1 - e) := by ring
    _ ≤ e + Λ * (1 - e) := by linarith
    _ = S.wMax Λ ω * S.propScore true ω := hw.symm

/-- **The all-`wMin` conditional calibration value is `wMin·e`.**
Pulling the `σ(X)`-measurable weight out of the conditional expectation:
`E[Z·wMin | σ(X)] = wMin·E[Z | σ(X)] = wMin·e`. -/
theorem condExp_treat_wMin_eq (Λ : ℝ)
    (hint : Integrable (fun ω => S.dVar.indicator true ω * S.wMin Λ ω) P.μ) :
    P.μ[fun ω => S.dVar.indicator true ω * S.wMin Λ ω | S.sigmaX]
      =ᵐ[P.μ] (fun ω => S.wMin Λ ω * S.propScore true ω) := by
  have hprop_meas : Measurable[S.sigmaX] (S.propScore true) := by
    unfold POBackdoorSystem.propScore
    exact stronglyMeasurable_condExp.measurable
  have hw_smeas : StronglyMeasurable[S.sigmaX] (S.wMin Λ) := by
    unfold POBackdoorSystem.wMin
    exact (measurable_const.add
      ((measurable_const.sub hprop_meas).div (measurable_const.mul hprop_meas))).stronglyMeasurable
  have hind_int : Integrable (S.dVar.indicator true) P.μ :=
    S.dVar.integrable_indicator true
  have hcomm :
      (fun ω => S.dVar.indicator true ω * S.wMin Λ ω)
        = (fun ω => S.wMin Λ ω * S.dVar.indicator true ω) := by
    funext ω
    exact mul_comm _ _
  refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := P.μ)
    (Filter.EventuallyEq.of_eq hcomm)).trans ?_
  have hpull :
      P.μ[fun ω => S.wMin Λ ω * S.dVar.indicator true ω | S.sigmaX]
        =ᵐ[P.μ] (fun ω => S.wMin Λ ω * P.μ[S.dVar.indicator true | S.sigmaX] ω) :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaX) (μ := P.μ) hw_smeas (hint.congr (Filter.EventuallyEq.of_eq hcomm))
      hind_int
  exact hpull.trans (Filter.EventuallyEq.of_eq (by
    funext ω
    rfl))

/-- **The all-`wMax` conditional calibration value is `wMax·e`.** -/
theorem condExp_treat_wMax_eq (Λ : ℝ)
    (hint : Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ) :
    P.μ[fun ω => S.dVar.indicator true ω * S.wMax Λ ω | S.sigmaX]
      =ᵐ[P.μ] (fun ω => S.wMax Λ ω * S.propScore true ω) := by
  have hprop_meas : Measurable[S.sigmaX] (S.propScore true) := by
    unfold POBackdoorSystem.propScore
    exact stronglyMeasurable_condExp.measurable
  have hw_smeas : StronglyMeasurable[S.sigmaX] (S.wMax Λ) := by
    unfold POBackdoorSystem.wMax
    exact (measurable_const.add
      ((measurable_const.mul (measurable_const.sub hprop_meas)).div hprop_meas)).stronglyMeasurable
  have hind_int : Integrable (S.dVar.indicator true) P.μ :=
    S.dVar.integrable_indicator true
  have hcomm :
      (fun ω => S.dVar.indicator true ω * S.wMax Λ ω)
        = (fun ω => S.wMax Λ ω * S.dVar.indicator true ω) := by
    funext ω
    exact mul_comm _ _
  refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := P.μ)
    (Filter.EventuallyEq.of_eq hcomm)).trans ?_
  have hpull :
      P.μ[fun ω => S.wMax Λ ω * S.dVar.indicator true ω | S.sigmaX]
        =ᵐ[P.μ] (fun ω => S.wMax Λ ω * P.μ[S.dVar.indicator true | S.sigmaX] ω) :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := S.sigmaX) (μ := P.μ) hw_smeas (hint.congr (Filter.EventuallyEq.of_eq hcomm))
      hind_int
  exact hpull.trans (Filter.EventuallyEq.of_eq (by
    funext ω
    rfl))

end POBackdoorSystem

end PO
end Causalean
