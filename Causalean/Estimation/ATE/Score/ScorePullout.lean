/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Score pull-out lemmas for AIPW proofs

Shared helper lemmas that rewrite score-weighted residual terms and remove
indicators inside integrals. These are used by both the mean-zero proof
(`MeanZero.lean`) and the remainder expansion (`Remainder*.lean`).
-/

import Causalean.Estimation.ATE.Score.AIPWMoment

/-! # AIPW Score Pull-Out Lemmas

This file provides conditional-expectation and integral identities that remove
score factors and treatment indicators from augmented inverse-probability
weighted residual terms. These lemmas are shared by the mean-zero proof and
the second-order remainder expansion for the back-door average treatment
effect.

The main declarations define the label-specific value-space propensity
`e_val_label`, prove `propScore_eq_e_val_label_ae`, and provide the integral
helpers `weighted_residual_integral_zero` and
`indicator_to_propScore_integral`.
-/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- Value-space propensity for label `d`: `e_val` for `d = true`,
`1 − e_val` for `d = false`. -/
noncomputable def e_val_label (S : BackdoorEstimationSystem P γ)
    (d : Bool) (x : γ) : ℝ :=
  if d then S.e_val x else 1 - S.e_val x

/-- The value-space propensity for any treatment label is measurable. -/
lemma measurable_e_val_label (S : BackdoorEstimationSystem P γ) (d : Bool) :
    Measurable (S.e_val_label d) := by
  cases d
  · simpa [e_val_label] using measurable_const.sub S.e_meas
  · simpa [e_val_label] using S.e_meas

/-- `propScore false =ᵐ 1 - propScore true` under back-door assumptions.
The indicator-pair sums to one pointwise, conditional expectation is linear,
and preserves constants. -/
lemma propScore_false_ae (S : BackdoorEstimationSystem P γ)
    (_hA : S.toPOBackdoorSystem.Assumptions) :
    S.toPOBackdoorSystem.propScore false
      =ᵐ[P.μ]
        (fun ω => 1 - S.toPOBackdoorSystem.propScore true ω) := by
  have hindD_integrable :
      ∀ e : Bool, Integrable (S.toPOBackdoorSystem.dVar.indicator e) P.μ :=
    fun e => S.toPOBackdoorSystem.dVar.integrable_indicator e
  have hsum_ptwise :
      (fun ω => S.toPOBackdoorSystem.dVar.indicator true ω +
        S.toPOBackdoorSystem.dVar.indicator false ω)
        = (fun _ : P.Ω => (1 : ℝ)) := by
    funext ω
    exact S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
  have hsum :
      P.μ[fun ω => S.toPOBackdoorSystem.dVar.indicator true ω +
          S.toPOBackdoorSystem.dVar.indicator false ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ] (fun _ => (1 : ℝ)) := by
    rw [hsum_ptwise]
    exact Filter.EventuallyEq.of_eq
      (MeasureTheory.condExp_const S.toPOBackdoorSystem.sigmaX_le (1 : ℝ))
  have hadd :
      P.μ[fun ω => S.toPOBackdoorSystem.dVar.indicator true ω +
          S.toPOBackdoorSystem.dVar.indicator false ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[S.toPOBackdoorSystem.dVar.indicator true |
            S.toPOBackdoorSystem.sigmaX]
              + P.μ[S.toPOBackdoorSystem.dVar.indicator false |
                S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_add (hindD_integrable true) (hindD_integrable false)
      S.toPOBackdoorSystem.sigmaX
  filter_upwards [hsum, hadd] with ω h1 h2
  have hsum_ω :
      P.μ[S.toPOBackdoorSystem.dVar.indicator true |
            S.toPOBackdoorSystem.sigmaX] ω
        + P.μ[S.toPOBackdoorSystem.dVar.indicator false |
            S.toPOBackdoorSystem.sigmaX] ω = 1 := by
    rw [← Pi.add_apply, ← h2, h1]
  unfold POBackdoorSystem.propScore
  linarith

/-- The σ(X)-conditional expectation of `1_{D=d}` is `e_val_label d (X)` a.s. -/
lemma propScore_eq_e_val_label_ae
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) (d : Bool) :
    S.toPOBackdoorSystem.propScore d
      =ᵐ[P.μ]
        (fun ω => S.e_val_label d (S.toPOBackdoorSystem.factualX ω)) := by
  cases d
  · -- `d = false`
    filter_upwards [propScore_false_ae S hA, S.e_compat] with ω hf hc
    simp [e_val_label, hf, hc]
  · -- `d = true`
    filter_upwards [S.e_compat] with ω hc
    simp [e_val_label, hc]

/-- AIPW weighted residual integral.
Whenever `g : γ → ℝ` is measurable and the resulting product is integrable,
`∫ g(X) · 1_{D=d} · (Y - μ_val(d, X)) dμ = 0`, by pulling `g(X)` out of
conditional expectation and using `h_residual_ce_zero`.

This is the helper used twice in `aipw_factualZ_integral_zero`.
-/
lemma weighted_residual_integral_zero
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) (d : Bool)
    (g : γ → ℝ) (hg_meas : Measurable g)
    (h_int : Integrable
      (fun ω => g (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator d ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val d (S.toPOBackdoorSystem.factualX ω)))) P.μ)
    (h_residual_ce_zero :
      P.μ[fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
        (S.toPOBackdoorSystem.factualY ω -
          S.μ_val d (S.toPOBackdoorSystem.factualX ω)) | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ] (fun _ => (0 : ℝ))) :
    ∫ ω, g (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator d ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val d (S.toPOBackdoorSystem.factualX ω))) ∂P.μ = 0 := by
  have hg_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => g (S.toPOBackdoorSystem.factualX ω)) := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => g (S.toPOBackdoorSystem.factualX ω))
    exact (hg_meas.comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  have hYind_int : Integrable
      (fun ω => S.toPOBackdoorSystem.factualY ω *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_mul_indicator d hA.integrable_factualY
      S.toPOBackdoorSystem.measurable_factualY
  have hμx_int :
      Integrable (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) P.μ := by
    have hcate_int : Integrable (S.toPOBackdoorSystem.CATE d) P.μ := by
      unfold POBackdoorSystem.CATE
      exact MeasureTheory.integrable_condExp
    exact hcate_int.congr (S.μ_compat hA d)
  have hμx_meas :
      Measurable (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) :=
    (S.μ_meas d).comp S.toPOBackdoorSystem.measurable_factualX
  have hμind_int : Integrable
      (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω) *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_mul_indicator d hμx_int hμx_meas
  have hresid_int : Integrable
      (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
        (S.toPOBackdoorSystem.factualY ω -
          S.μ_val d (S.toPOBackdoorSystem.factualX ω))) P.μ := by
    have hYind_int' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
          S.toPOBackdoorSystem.factualY ω) P.μ := by
      simpa [mul_comm] using hYind_int
    have hμind_int' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
          S.μ_val d (S.toPOBackdoorSystem.factualX ω)) P.μ := by
      simpa [mul_comm] using hμind_int
    have hsub := hYind_int'.sub hμind_int'
    refine hsub.congr ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    change S.toPOBackdoorSystem.dVar.indicator d ω *
          S.toPOBackdoorSystem.factualY ω -
        S.toPOBackdoorSystem.dVar.indicator d ω *
          S.μ_val d (S.toPOBackdoorSystem.factualX ω)
        = S.toPOBackdoorSystem.dVar.indicator d ω *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ_val d (S.toPOBackdoorSystem.factualX ω))
    ring
  have hcondexp_pull :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hg_sm h_int hresid_int
  have hgresid_ce_zero :
      P.μ[fun ω => g (S.toPOBackdoorSystem.factualX ω) *
            (S.toPOBackdoorSystem.dVar.indicator d ω *
              (S.toPOBackdoorSystem.factualY ω -
                S.μ_val d (S.toPOBackdoorSystem.factualX ω))) |
            S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ]
          (fun _ => (0 : ℝ)) := by
    refine hcondexp_pull.trans ?_
    filter_upwards [h_residual_ce_zero] with ω hω
    have : ((fun ω' => g (S.toPOBackdoorSystem.factualX ω')) *
        P.μ[fun ω' => S.toPOBackdoorSystem.dVar.indicator d ω' *
            (S.toPOBackdoorSystem.factualY ω' -
              S.μ_val d (S.toPOBackdoorSystem.factualX ω')) |
            S.toPOBackdoorSystem.sigmaX]) ω = 0 := by
      rw [Pi.mul_apply, hω, mul_zero]
    exact this
  calc
    ∫ ω, g (S.toPOBackdoorSystem.factualX ω) *
          (S.toPOBackdoorSystem.dVar.indicator d ω *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ_val d (S.toPOBackdoorSystem.factualX ω))) ∂P.μ
      = ∫ ω, P.μ[fun ω => g (S.toPOBackdoorSystem.factualX ω) *
            (S.toPOBackdoorSystem.dVar.indicator d ω *
              (S.toPOBackdoorSystem.factualY ω -
                S.μ_val d (S.toPOBackdoorSystem.factualX ω))) |
            S.toPOBackdoorSystem.sigmaX] ω ∂P.μ := by
        rw [MeasureTheory.integral_condExp S.toPOBackdoorSystem.sigmaX_le]
    _ = ∫ _, (0 : ℝ) ∂P.μ :=
          MeasureTheory.integral_congr_ae hgresid_ce_zero
    _ = 0 := MeasureTheory.integral_zero _ _

/-- Companion to `weighted_residual_integral_zero`:
replaces `1_{D=d}` by the value-space propensity `e_val_label d (X)` inside an
integral against `P.μ`. -/
lemma indicator_to_propScore_integral
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) (d : Bool)
    (f : γ → ℝ) (hf_meas : Measurable f)
    (hf_ind_int : Integrable
      (fun ω => f (S.toPOBackdoorSystem.factualX ω) *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ) :
    ∫ ω, f (S.toPOBackdoorSystem.factualX ω) *
        S.toPOBackdoorSystem.dVar.indicator d ω ∂P.μ
      = ∫ ω, f (S.toPOBackdoorSystem.factualX ω) *
          S.e_val_label d (S.toPOBackdoorSystem.factualX ω) ∂P.μ := by
  have hf_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => f (S.toPOBackdoorSystem.factualX ω)) := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => f (S.toPOBackdoorSystem.factualX ω))
    exact (hf_meas.comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  have hind_int : Integrable (S.toPOBackdoorSystem.dVar.indicator d) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_indicator d
  have hCE_pull :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hf_sm hf_ind_int hind_int
  have hCE_replace :
      P.μ[fun ω => f (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ]
          (fun ω => f (S.toPOBackdoorSystem.factualX ω) *
            S.e_val_label d (S.toPOBackdoorSystem.factualX ω)) := by
    refine hCE_pull.trans ?_
    filter_upwards [propScore_eq_e_val_label_ae S hA d] with ω hω
    have hω' :
        P.μ[S.toPOBackdoorSystem.dVar.indicator d |
            S.toPOBackdoorSystem.sigmaX] ω
          = S.e_val_label d (S.toPOBackdoorSystem.factualX ω) := hω
    rw [Pi.mul_apply, hω']
  calc
    ∫ ω, f (S.toPOBackdoorSystem.factualX ω) *
          S.toPOBackdoorSystem.dVar.indicator d ω ∂P.μ
      = ∫ ω, P.μ[fun ω => f (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX] ω ∂P.μ :=
        (MeasureTheory.integral_condExp S.toPOBackdoorSystem.sigmaX_le).symm
    _ = ∫ ω, f (S.toPOBackdoorSystem.factualX ω) *
            S.e_val_label d (S.toPOBackdoorSystem.factualX ω) ∂P.μ :=
        MeasureTheory.integral_congr_ae hCE_replace

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean
