/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mean zero of the ATT AIPW moment — `lem:est-aipw-mean-zero-att`

Headline lemma `aipw_mean_zero_ATT`.

The ATT AIPW moment decomposes (via `aipwMomentATT`) into three pieces:

* `A · (Y − μ₀(X))`                                        — treated arm.
* `−(1 − A) · (e(X) / (1 − e(X))) · (Y − μ₀(X))`           — IPW correction.
* `−A · θ₀`                                                — constant in `θ`.

Mean-zero proof composes:

* the **treated-arm term** `∫ A · (Y − μ₀(X)) dμ` is, by definition, the
  numerator of `adjustedATT` (control-regression form using only `μ₀(X)`);
* the **IPW vanishing** lemma `weighted_residual_false_integral_zero` from
  `ScorePullout.lean`;
* the constant `−E[A · θ₀] = −π_T · θ₀` cancels the treated arm because
  `θ₀ = adjustedATT = E[A · (Y − μ₀)] / π_T`.

The `hIPW` hypothesis below is the same one carried in the PO-level
`adjustedATT_eq_aipwForm`; downstream we want to appeal to that identity, so
the same hypothesis must be threaded through here.
-/

import Causalean.Estimation.ATT.Score.ScorePullout
import Causalean.Tactic.IntegralLinearity

/-!
Proves the population centering facts for the ATT AIPW score. The measurable
helpers `measurable_ψ_ATT` and `measurable_aipwMomentATT_at_θ₀` support
integration against the observed data law, and the headline theorem
`aipw_mean_zero_ATT` shows that the truth moment has expectation zero under
`P_Z`.

The proof combines the PO-level adjusted-ATT identity, the control-arm weighted
residual pull-out lemma, and the constant term `π_T * θ₀`, giving the centering
input for ATT influence-function and DML results.
-/

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO
open Causalean.Estimation.ATE.BackdoorEstimationSystem (projX projA projY indA)

namespace TreatedEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## Measurability -/

/-- Measurability of the ATT influence function `ψ_ATT`. -/
-- Outline: unfold `ψ_ATT`, `aipwMomentATT`, `indA`, `projX`, `projA`, `projY`;
-- combine with measurability of `S.μ₀_val`, `S.e_val`, the indicator
-- `if · = true then 1 else 0` on `Bool`, and the projections.  Same recipe as
-- `BackdoorEstimationSystem.measurable_ψ_AIPW`.
@[fun_prop]
lemma measurable_ψ_ATT (S : TreatedEstimationSystem P γ) :
    Measurable S.ψ_ATT := by
  unfold TreatedEstimationSystem.ψ_ATT
  exact ((measurable_aipwMomentATTFunctional S.η₀ 0).const_mul (1 / S.π_val)).sub
    measurable_const

/-- Measurability of `aipwMomentATT z η₀ θ₀` as a function of `z`. -/
-- Outline: this is `measurable_aipwMomentATTFunctional S.η₀ S.θ₀` after
-- unfolding `aipwMomentATTFunctional` and `η₀`.
@[fun_prop]
lemma measurable_aipwMomentATT_at_θ₀
    (S : TreatedEstimationSystem P γ) :
    Measurable (fun z => aipwMomentATT z S.μ₀_val S.e_val S.θ₀) := by
  simpa [aipwMomentATTFunctional, TreatedEstimationSystem.η₀] using
    measurable_aipwMomentATTFunctional S.η₀ S.θ₀

@[fun_prop]
private lemma measurable_adjustedCE
    (S : TreatedEstimationSystem P γ) (d : Bool) :
    Measurable (S.toPOBackdoorSystem.adjustedCE d) := by
  unfold POBackdoorSystem.adjustedCE POBackdoorSystem.propScore
  have hsm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => P.μ[fun ω' => S.toPOBackdoorSystem.factualY ω' *
          S.toPOBackdoorSystem.dVar.indicator d ω' |
          S.toPOBackdoorSystem.sigmaX] ω /
        P.μ[S.toPOBackdoorSystem.dVar.indicator d |
          S.toPOBackdoorSystem.sigmaX] ω) :=
    ((MeasureTheory.stronglyMeasurable_condExp
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX)
      (f := fun ω' => S.toPOBackdoorSystem.factualY ω' *
        S.toPOBackdoorSystem.dVar.indicator d ω')).measurable.div
      (MeasureTheory.stronglyMeasurable_condExp
        (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX)
        (f := S.toPOBackdoorSystem.dVar.indicator d)).measurable).stronglyMeasurable
  exact (hsm.mono S.toPOBackdoorSystem.sigmaX_le).measurable

private lemma integrable_adjustedCE
    (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions) :
    Integrable (S.toPOBackdoorSystem.adjustedCE false) P.μ := by
  have hcate_int : Integrable (S.toPOBackdoorSystem.CATE false) P.μ := by
    unfold POBackdoorSystem.CATE
    exact MeasureTheory.integrable_condExp
  exact hcate_int.congr (S.control_cate_backdoor hA)

/-! ## Mean-zero theorem -/

/-- **Mean zero of the ATT AIPW moment.** Under [the one-sided back-door ATT
assumptions](hyp:hA), [a strictly positive marginal treatment probability](hyp:hπ_pos),
and [integrability of the control-arm inverse-propensity-weighted residual correction
`(1 − 1{D=1}) · (e(X)/(1 − e(X))) · (Y − μ₀(X))`](hyp:hIPW), [the ATT AIPW moment
evaluated at the truth has mean zero under the joint law of the covariates, treatment,
and outcome](goal).

Proof outline:

* Push the integral from `P_Z` back to `P.μ` via `integral_map`.
* Decompose into three integrals:
  - `∫ A · (Y − μ₀(X)) dμ`,
  - `∫ (1 − A) · (e/(1−e)) · (Y − μ₀(X)) dμ`,
  - `∫ A · θ₀ dμ = θ₀ · π_T`.
* The middle integral is `0` by `weighted_residual_false_integral_zero`
  (combined with `propScore_eq_e_val_ae` to convert `e(X)` between the
  σ(X)-measurable `propScore true` and the value-space `e_val ∘ factualX`).
* The first integral equals `π_T · adjustedATT = π_T · θ₀` directly, since
  `∫ A · (Y − μ₀(X)) dμ` is the numerator of `adjustedATT` by definition.
* The two `π_T · θ₀` terms cancel.

The `hIPW` hypothesis matches the one in `adjustedATT_eq_aipwForm`. -/
theorem aipw_mean_zero_ATT
    (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (hπ_pos : 0 < S.π_val)
    (hIPW : Integrable (fun ω =>
        (1 - S.toPOBackdoorSystem.dVar.indicator true ω)
          * (S.toPOBackdoorSystem.propScore true ω
              / (1 - S.toPOBackdoorSystem.propScore true ω))
          * (S.toPOBackdoorSystem.factualY ω
              - S.toPOBackdoorSystem.adjustedCE false ω)) P.μ) :
    ∫ z, aipwMomentATT z S.μ₀_val S.e_val S.θ₀ ∂(S.P_Z) = 0 := by
  let A : P.Ω → ℝ := fun ω => S.toPOBackdoorSystem.dVar.indicator true ω
  let R : P.Ω → ℝ := fun ω =>
    S.toPOBackdoorSystem.factualY ω - S.toPOBackdoorSystem.adjustedCE false ω
  let W : P.Ω → ℝ := fun ω =>
    S.toPOBackdoorSystem.propScore true ω /
      (1 - S.toPOBackdoorSystem.propScore true ω)
  let N : ℝ := ∫ ω, A ω * R ω - (1 - A ω) * W ω * R ω ∂P.μ
  have hadj :
      S.θ₀ = N / S.π_val := by
    have h := S.toPOBackdoorSystem.adjustedATT_eq_aipwForm hA hIPW
    simpa [TreatedEstimationSystem.θ₀, TreatedEstimationSystem.π_val,
      N, A, R, W] using h
  have hπ_ne : S.π_val ≠ 0 := ne_of_gt hπ_pos
  have hN_eq : N = S.π_val * S.θ₀ := by
    calc
      N = S.π_val * (N / S.π_val) := by
        field_simp [hπ_ne]
      _ = S.π_val * S.θ₀ := by rw [← hadj]
  have htreated_int : Integrable (fun ω => A ω * R ω) P.μ := by
    have hY_int : Integrable S.toPOBackdoorSystem.factualY P.μ :=
      S.toPOBackdoorSystem.integrable_factualY_of_consistency
        hA.consistency hA.integrable_Y1 hA.integrable_Y0
    have hYind_int : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator true ω *
          S.toPOBackdoorSystem.factualY ω) P.μ := by
      have h := S.toPOBackdoorSystem.dVar.integrable_mul_indicator true
        (measurableSet_singleton true) hY_int
      exact h.congr (Filter.Eventually.of_forall (fun ω => by ring))
    have hAdjind_int : Integrable
          (fun ω => S.toPOBackdoorSystem.dVar.indicator true ω *
            S.toPOBackdoorSystem.adjustedCE false ω) P.μ := by
      have h :=
        S.toPOBackdoorSystem.dVar.integrable_mul_indicator true
          (measurableSet_singleton true) (integrable_adjustedCE S hA)
      exact h.congr (Filter.Eventually.of_forall (fun ω => by ring))
    have hsub := hYind_int.sub hAdjind_int
    refine hsub.congr ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    unfold A R
    rw [Pi.sub_apply]
    ring
  have hN_int : Integrable
      (fun ω => A ω * R ω - (1 - A ω) * W ω * R ω) P.μ := by
    exact htreated_int.sub (by simpa [A, R, W] using hIPW)
  have hAθ_int : Integrable (fun ω => A ω * S.θ₀) P.μ := by
    have hA_int : Integrable A P.μ := by
      simpa [A] using S.toPOBackdoorSystem.dVar.integrable_indicator true
    have h := hA_int.const_mul S.θ₀
    exact h.congr (Filter.Eventually.of_forall (fun ω => by
      unfold A
      ring))
  have hmap :
      ∫ z, aipwMomentATT z S.μ₀_val S.e_val S.θ₀ ∂(S.P_Z)
        = ∫ ω, aipwMomentATT (S.factualZ ω) S.μ₀_val S.e_val S.θ₀ ∂P.μ := by
    rw [TreatedEstimationSystem.P_Z]
    exact MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
      (measurable_aipwMomentATT_at_θ₀ S).aestronglyMeasurable
  rw [hmap]
  have hrewrite :
      (fun ω => aipwMomentATT (S.factualZ ω) S.μ₀_val S.e_val S.θ₀)
        =ᵐ[P.μ] (fun ω => A ω * R ω - (1 - A ω) * W ω * R ω
          - A ω * S.θ₀) := by
    filter_upwards [S.μ₀_compat hA, S.e_compat,
      S.control_cate_backdoor hA] with ω hμ he hcat
    have hμ_eq : S.μ₀_val (S.toPOBackdoorSystem.factualX ω)
        = S.toPOBackdoorSystem.adjustedCE false ω := by
      have hcate_eq : S.toPOBackdoorSystem.CATE false ω
          = S.μ₀_val (S.toPOBackdoorSystem.factualX ω) := by
        simpa [POBackdoorSystem.CATE] using hμ
      rw [← hcate_eq, hcat]
    have he_eq : S.e_val (S.toPOBackdoorSystem.factualX ω)
        = S.toPOBackdoorSystem.propScore true ω := he.symm
    have hindA_true : indA (S.factualZ ω) = A ω := by
      by_cases hD : S.toPOBackdoorSystem.factualD ω = true
      · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 1 :=
          S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
        simp [TreatedEstimationSystem.factualZ, A, indA, projA, hD, hInd]
      · have hF : S.toPOBackdoorSystem.factualD ω = false := by
          cases h' : S.toPOBackdoorSystem.factualD ω <;> simp [h'] at hD ⊢
        have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 0 :=
          S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
        simp [TreatedEstimationSystem.factualZ, A, indA, projA, hD, hInd]
    unfold aipwMomentATT R W
    rw [hindA_true]
    simp [TreatedEstimationSystem.factualZ, projX, projY, hμ_eq, he_eq]
  calc
    ∫ ω, aipwMomentATT (S.factualZ ω) S.μ₀_val S.e_val S.θ₀ ∂P.μ
        = ∫ ω, A ω * R ω - (1 - A ω) * W ω * R ω - A ω * S.θ₀ ∂P.μ :=
          MeasureTheory.integral_congr_ae hrewrite
    _ = N - ∫ ω, A ω * S.θ₀ ∂P.μ := by
      exact MeasureTheory.integral_sub hN_int hAθ_int
    _ = N - S.θ₀ * S.π_val := by
      have hAconst :
          ∫ ω, A ω * S.θ₀ ∂P.μ = S.θ₀ * ∫ ω, A ω ∂P.μ := by
        integral_linearity
        ring
      rw [hAconst]
      simp [TreatedEstimationSystem.π_val, POBackdoorSystem.propTreated, A]
    _ = 0 := by
      rw [hN_eq]
      ring

end TreatedEstimationSystem

end ATT
end Estimation
end Causalean
