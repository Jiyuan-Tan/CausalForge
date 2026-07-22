/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW second-order remainder identity

The AIPW moment functional `m_AIPW(η, z, θ₀)` from `AIPWMoment.lean` is
Neyman-orthogonal at `(η₀, θ₀)` (`Neyman.lean`), meaning the directional
derivative of `η ↦ ∫ m(η, z, θ₀) dP_Z` at `η₀` vanishes on `H_ε`.  The DML
asymptotic-linearity proof needs the *second-order* consequence. This file
proves the exact integrated identity that rewrites the population moment at
`η` as a product of outcome-regression and propensity-score errors; the
quantitative L² bound and stochastic product-rate corollary are in
`Remainder/Bound.lean`.

The plug-in remainder is a degenerate one-factor case (no `ê`-error) and uses
only the constant-case Cauchy–Schwarz bound from
`Causalean/Stat/ConditionalOp.lean`; we collect it here too for symmetry.
-/

import Causalean.Estimation.ATE.Score.AIPWMoment
import Causalean.Estimation.ATE.Score.MeanZero
import Causalean.Estimation.ATE.Score.ScorePullout
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Orthogonality.ConditionalOp
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
Establishes the exact second-order AIPW remainder identity for back-door
average treatment effect estimation.

The file records the plug-in bias bound `plugin_bias_le_eLpNorm`, the
remainder constant `aipw_rem_const`, measurability of
`aipwMomentFunctional`, and the headline identity `aipw_remainder_identity`.
The identity pushes the population AIPW moment from the observed-data law
`P_Z` to the covariate law `P_X` and expresses it as the product of nuisance
errors in `μ` and `e`; `Remainder/Bound.lean` then turns this identity into an
L² product bound and an `o_p(n^{-1/2})` corollary.
-/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## Plug-in (degenerate) remainder

The plug-in moment `ψ_plugin(z) − (μ̂(1,x) − μ̂(0,x) − θ₀)` integrates to
`∫ (μ̂(a,·) − μ_val(a,·)) dP_X`, which by Cauchy–Schwarz is bounded by the
L²-norm of the nuisance error. -/

/-- **Plug-in bias bound.** The integrated plug-in bias in component `a`
satisfies `|∫ (μ̂(a,·) − μ_val(a,·)) dP_X| ≤ ‖μ̂(a,·) − μ_val(a,·)‖_{L²(P_X)}`.

Direct corollary of `abs_integral_le_eLpNorm_two` since `P_X` is a
probability measure. -/
theorem plugin_bias_le_eLpNorm
    (S : BackdoorEstimationSystem P γ) [IsProbabilityMeasure P.μ]
    {μ_fn : Bool → γ → ℝ} (hμ_meas : ∀ a, Measurable (μ_fn a))
    (hμ_memLp : ∀ a, MemLp (fun x => μ_fn a x - S.μ_val a x) 2 S.P_X)
    (a : Bool) :
    |∫ x, (μ_fn a x - S.μ_val a x) ∂(S.P_X)|
      ≤ (eLpNorm (fun x => μ_fn a x - S.μ_val a x) 2 S.P_X).toReal := by
  have _ := hμ_meas
  haveI : IsProbabilityMeasure S.P_X := by
    unfold BackdoorEstimationSystem.P_X
    exact Measure.isProbabilityMeasure_map S.toPOBackdoorSystem.measurable_factualX.aemeasurable
  exact abs_integral_le_eLpNorm_two (hμ_memLp a)

/-! ## AIPW second-order remainder

Algebraic identity: at any `η = (μ_fn, e_fn) ∈ H_ε`, expanding the AIPW
moment around `η₀` in `(μ_fn − μ_val, e_fn − e_val)` and integrating against
`dP_Z` cancels the linear term (Neyman orthogonality, `aipw_neyman` part B)
and leaves a quadratic remainder of the form

    Σ_{a ∈ {0,1}} ∫ Δμ_a(x) · Δe_a(x) · w_a(x; η, η₀) dP_X(x),

where `w_a` is uniformly bounded by `2/(ε(1−ε))` on `H_ε`.  Cauchy–Schwarz
on each summand then gives the product-rate bound.

The statement below packages the conclusion directly; the proof body
performs the expansion and applies `integral_abs_mul_le_eLpNorm_mul_eLpNorm`
componentwise. -/

/-- The AIPW remainder constant is the uniform strict-overlap weight bound
used in the second-order remainder estimate. -/
noncomputable def aipw_rem_const (ε : ℝ) : ℝ := 2 / (ε * (1 - ε))

/-- The AIPW moment functional is measurable in the observed data triple for
any fixed nuisance vector and target value. -/
lemma measurable_aipwMomentFunctional
    (η : NuisanceVec γ) (θ : ℝ) :
    Measurable (fun z : γ × Bool × ℝ => aipwMomentFunctional η z θ) := by
  unfold aipwMomentFunctional aipwMoment indA projX projA projY
  have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
  have hy : Measurable (fun z : γ × Bool × ℝ => z.2.2) := by measurability
  have hμt : Measurable (fun z : γ × Bool × ℝ => η.μ_fn true z.1) :=
    (η.μ_meas true).comp hx
  have hμf : Measurable (fun z : γ × Bool × ℝ => η.μ_fn false z.1) :=
    (η.μ_meas false).comp hx
  have he : Measurable (fun z : γ × Bool × ℝ => η.e_fn z.1) :=
    η.e_meas.comp hx
  have hind : Measurable (fun z : γ × Bool × ℝ =>
      if z.2.1 = true then (1 : ℝ) else 0) := by
    have ha : Measurable (fun z : γ × Bool × ℝ => z.2.1) := by measurability
    exact (Measurable.of_discrete
      (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
  exact ((((hμt.sub hμf).add ((hind.div he).mul (hy.sub hμt))).sub
    (((measurable_const.sub hind).div (measurable_const.sub he)).mul
      (hy.sub hμf))).sub measurable_const)

/-- **Integrated AIPW remainder identity.**

Expanding the population AIPW moment around the true nuisance `S.η₀` cancels
the zeroth and first-order terms, leaving the two cross-products between the
outcome-regression error and propensity-score error. -/
lemma aipw_remainder_identity
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (η : NuisanceVec γ) (hη : η ∈ H_ε_aeL2 S ε)
    (hΔμ_memLp :
      ∀ a, MemLp (fun x => η.μ_fn a x - S.μ_val a x) 2 S.P_X) :
    ∫ z, aipwMomentFunctional η z S.θ₀ ∂(S.P_Z)
      =
    ∫ x,
      (η.e_fn x - S.e_val x) *
      ((η.μ_fn true x - S.μ_val true x) / η.e_fn x +
        (η.μ_fn false x - S.μ_val false x) / (1 - η.e_fn x))
      ∂(S.P_X) := by
  let X : P.Ω → γ := S.toPOBackdoorSystem.factualX
  let Y : P.Ω → ℝ := S.toPOBackdoorSystem.factualY
  let indT : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator true
  let indF : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator false
  let dμT : P.Ω → ℝ := fun ω => η.μ_fn true (X ω) - S.μ_val true (X ω)
  let dμF : P.Ω → ℝ := fun ω => η.μ_fn false (X ω) - S.μ_val false (X ω)
  let wT : P.Ω → ℝ := fun ω => indT ω / η.e_fn (X ω)
  let wF : P.Ω → ℝ := fun ω => indF ω / (1 - η.e_fn (X ω))
  let base : P.Ω → ℝ := fun ω =>
    S.μ_val true (X ω) - S.μ_val false (X ω) - S.θ₀
  let rT : P.Ω → ℝ := fun ω => wT ω * (Y ω - S.μ_val true (X ω))
  let rF : P.Ω → ℝ := fun ω => wF ω * (Y ω - S.μ_val false (X ω))
  let iT : P.Ω → ℝ := fun ω => wT ω * dμT ω
  let iF : P.Ω → ℝ := fun ω => wF ω * dμF ω
  let pT : P.Ω → ℝ := fun ω =>
    (dμT ω / η.e_fn (X ω)) * S.e_val_label true (X ω)
  let pF : P.Ω → ℝ := fun ω =>
    (dμF ω / (1 - η.e_fn (X ω))) * S.e_val_label false (X ω)
  let crossInd : P.Ω → ℝ := fun ω => dμT ω - dμF ω - iT ω + iF ω
  let crossProp : P.Ω → ℝ := fun ω => dμT ω - dμF ω - pT ω + pF ω
  let remΩ : P.Ω → ℝ := fun ω =>
    (η.e_fn (X ω) - S.e_val (X ω)) *
      (dμT ω / η.e_fn (X ω) + dμF ω / (1 - η.e_fn (X ω)))
  let remX : γ → ℝ := fun x =>
    (η.e_fn x - S.e_val x) *
      ((η.μ_fn true x - S.μ_val true x) / η.e_fn x +
        (η.μ_fn false x - S.μ_val false x) / (1 - η.e_fn x))
  have hindA_true : ∀ ω, indA (S.factualZ ω) = indT ω := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : indT ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [BackdoorEstimationSystem.factualZ, indA, projA, indT, hD, hInd]
    · have hF : S.toPOBackdoorSystem.factualD ω = false := by
        cases h' : S.toPOBackdoorSystem.factualD ω <;> simp [h'] at hD ⊢
      have hInd : indT ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [BackdoorEstimationSystem.factualZ, indA, projA, indT, hD, hInd]
  have hindA_false : ∀ ω, 1 - indA (S.factualZ ω) = indF ω := by
    intro ω
    have hsum : indT ω + indF ω = 1 := by
      simpa [indT, indF] using
        S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
    calc
      1 - indA (S.factualZ ω) = 1 - indT ω := by rw [hindA_true ω]
      _ = indF ω := by linarith
  have hη_X : ∀ᵐ ω ∂P.μ,
      ε ≤ η.e_fn (X ω) ∧ η.e_fn (X ω) ≤ 1 - ε := by
    simpa [X] using H_ε_aeL2_overlap_factualX S hη
  have hY_L2 : MemLp Y 2 P.μ := by
    dsimp [Y]
    exact
      (memLp_two_iff_integrable_sq
        S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hμ_L2 : ∀ d : Bool, MemLp
      (fun ω => S.μ_val d (X ω)) 2 P.μ := by
    intro d
    have hYd_L2 : MemLp (S.toPOBackdoorSystem.YofD d) 2 P.μ := by
      exact
        (memLp_two_iff_integrable_sq
          (S.toPOBackdoorSystem.measurable_YofD d).aestronglyMeasurable).2 (h_yd2 d)
    have hcond_L2 :
        MemLp (P.μ[S.toPOBackdoorSystem.YofD d |
          S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
      hYd_L2.condExp
    exact hcond_L2.ae_eq (by
      simpa [X] using S.μ_compat hA d)
  have hdμ_L2 : ∀ d : Bool, MemLp
      (fun ω => η.μ_fn d (X ω) - S.μ_val d (X ω)) 2 P.μ := by
    intro d
    have hd : MemLp (fun x => η.μ_fn d x - S.μ_val d x) 2 S.P_X :=
      hΔμ_memLp d
    simpa [X] using
      MemLp.comp_of_map (f := S.toPOBackdoorSystem.factualX) hd
        S.toPOBackdoorSystem.measurable_factualX.aemeasurable
  have hwT_bound : ∀ᵐ ω ∂P.μ, ‖wT ω‖ ≤ ε⁻¹ := by
    filter_upwards [hη_X] with ω hηω
    have hη_pos_ω : 0 < η.e_fn (X ω) := lt_of_lt_of_le h_overlap.1 hηω.1
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : indT ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      have hle : (η.e_fn (X ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hη_pos_ω h_overlap.1).2 hηω.1
      simpa [wT, hInd, one_div, Real.norm_eq_abs, abs_of_pos hη_pos_ω] using hle
    · have hInd : indT ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
      simpa [wT, hInd] using hεinv_nonneg
  have hwF_bound : ∀ᵐ ω ∂P.μ, ‖wF ω‖ ≤ ε⁻¹ := by
    filter_upwards [hη_X] with ω hηω
    have hη_false_pos_ω : 0 < 1 - η.e_fn (X ω) := by
      have : ε ≤ 1 - η.e_fn (X ω) := by linarith [hηω.2]
      exact lt_of_lt_of_le h_overlap.1 this
    by_cases hD : S.toPOBackdoorSystem.factualD ω = false
    · have hInd : indF ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      have hden : ε ≤ 1 - η.e_fn (X ω) := by linarith [hηω.2]
      have hle : (1 - η.e_fn (X ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hη_false_pos_ω h_overlap.1).2 hden
      simpa [wF, hInd, one_div, Real.norm_eq_abs,
        abs_of_pos hη_false_pos_ω] using hle
    · have hInd : indF ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := false) hD
      have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
      simpa [wF, hInd] using hεinv_nonneg
  have hwT_Linf : MemLp wT ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ hwT_bound
    apply Measurable.aestronglyMeasurable
    exact S.toPOBackdoorSystem.dVar.measurable_indicator true |>.div
      (η.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)
  have hwF_Linf : MemLp wF ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ hwF_bound
    apply Measurable.aestronglyMeasurable
    exact S.toPOBackdoorSystem.dVar.measurable_indicator false |>.div
      (measurable_const.sub (η.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))
  have hrT_int : Integrable rT P.μ := by
    have hL2 : MemLp rT 2 P.μ := by
      simpa [rT, Y, X, wT] using
        (hY_L2.sub (hμ_L2 true)).mul hwT_Linf
    exact hL2.integrable (by norm_num)
  have hrF_int : Integrable rF P.μ := by
    have hL2 : MemLp rF 2 P.μ := by
      simpa [rF, Y, X, wF] using
        (hY_L2.sub (hμ_L2 false)).mul hwF_Linf
    exact hL2.integrable (by norm_num)
  have hiT_int : Integrable iT P.μ := by
    have hL2 : MemLp iT 2 P.μ := by
      simpa [iT, dμT, X, wT] using
        (hdμ_L2 true).mul hwT_Linf
    exact hL2.integrable (by norm_num)
  have hiF_int : Integrable iF P.μ := by
    have hL2 : MemLp iF 2 P.μ := by
      simpa [iF, dμF, X, wF] using
        (hdμ_L2 false).mul hwF_Linf
    exact hL2.integrable (by norm_num)
  have hdμT_int : Integrable dμT P.μ :=
    (hdμ_L2 true).integrable (by norm_num)
  have hdμF_int : Integrable dμF P.μ :=
    (hdμ_L2 false).integrable (by norm_num)
  have hbase_int : Integrable base P.μ := by
    have hdiff : Integrable (fun ω => S.μ_val true (X ω) - S.μ_val false (X ω)) P.μ :=
      ((hμ_L2 true).sub (hμ_L2 false)).integrable (by norm_num)
    simpa [base, sub_eq_add_neg] using hdiff.sub (integrable_const (S.θ₀))
  have hcrossInd_int : Integrable crossInd P.μ := by
    simpa [crossInd, sub_eq_add_neg, add_assoc] using
      ((hdμT_int.sub hdμF_int).sub hiT_int).add hiF_int
  have hbase_zero : ∫ ω, base ω ∂P.μ = 0 := by
    have hθ : S.θ₀ = ∫ ω, S.μ_val true (X ω) - S.μ_val false (X ω) ∂P.μ := by
      simpa [X] using theta_zero_factualX_integral S
    have hdiff : Integrable (fun ω => S.μ_val true (X ω) - S.μ_val false (X ω)) P.μ :=
      ((hμ_L2 true).sub (hμ_L2 false)).integrable (by norm_num)
    have hconst : (∫ _ : P.Ω, S.θ₀ ∂P.μ) = S.θ₀ := by
      haveI : IsProbabilityMeasure P.μ := inferInstance
      simp
    calc
      ∫ ω, base ω ∂P.μ
          = (∫ ω, S.μ_val true (X ω) - S.μ_val false (X ω) ∂P.μ) -
              ∫ _ : P.Ω, S.θ₀ ∂P.μ := by
            rw [show base = (fun ω => (S.μ_val true (X ω) -
                S.μ_val false (X ω)) - S.θ₀) from rfl]
            rw [integral_sub]
            · exact hdiff
            · exact integrable_const (S.θ₀)
      _ = S.θ₀ - S.θ₀ := by rw [← hθ, hconst]
      _ = 0 := by ring
  have hrT_zero : ∫ ω, rT ω ∂P.μ = 0 := by
    have hg_meas : Measurable (fun x => 1 / η.e_fn x) :=
      measurable_const.div η.e_meas
    have h_int : Integrable
        (fun ω => (1 / η.e_fn (X ω)) *
          (indT ω * (Y ω - S.μ_val true (X ω)))) P.μ := by
      refine hrT_int.congr ?_
      exact Filter.Eventually.of_forall fun ω => by
        simp [rT, wT, X, Y, indT]
        ring
    calc
      ∫ ω, rT ω ∂P.μ
          = ∫ ω, (1 / η.e_fn (X ω)) *
              (indT ω * (Y ω - S.μ_val true (X ω))) ∂P.μ := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall fun ω => by
              simp [rT, wT, X, Y, indT]
              ring
      _ = 0 := by
            simpa [X, Y, indT] using
              weighted_residual_integral_zero S hA true (fun x => 1 / η.e_fn x)
                hg_meas h_int (cond_exp_residual_zero S hA true)
  have hrF_zero : ∫ ω, rF ω ∂P.μ = 0 := by
    have hg_meas : Measurable (fun x => 1 / (1 - η.e_fn x)) :=
      measurable_const.div (measurable_const.sub η.e_meas)
    have h_int : Integrable
        (fun ω => (1 / (1 - η.e_fn (X ω))) *
          (indF ω * (Y ω - S.μ_val false (X ω)))) P.μ := by
      refine hrF_int.congr ?_
      exact Filter.Eventually.of_forall fun ω => by
        simp [rF, wF, X, Y, indF]
        ring
    calc
      ∫ ω, rF ω ∂P.μ
          = ∫ ω, (1 / (1 - η.e_fn (X ω))) *
              (indF ω * (Y ω - S.μ_val false (X ω))) ∂P.μ := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall fun ω => by
              simp [rF, wF, X, Y, indF]
              ring
      _ = 0 := by
            simpa [X, Y, indF] using
              weighted_residual_integral_zero S hA false
                (fun x => 1 / (1 - η.e_fn x)) hg_meas h_int
                (cond_exp_residual_zero S hA false)
  have hmoment_eq : (fun ω => aipwMomentFunctional η (S.factualZ ω) S.θ₀)
      =ᵐ[P.μ] (fun ω => base ω + rT ω - rF ω + crossInd ω) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    change aipwMomentFunctional η (S.factualZ ω) S.θ₀ =
      base ω + rT ω - rF ω + crossInd ω
    unfold aipwMomentFunctional aipwMoment base rT rF crossInd iT iF wT wF dμT dμF X Y
    have hnot_indT : 1 - indT ω = indF ω := by
      rw [← hindA_true ω]
      exact hindA_false ω
    rw [hindA_true ω, hnot_indT]
    simp [BackdoorEstimationSystem.factualZ, projX, projY]
    ring
  have hpushZ :
      ∫ z, aipwMomentFunctional η z S.θ₀ ∂(S.P_Z)
        = ∫ ω, aipwMomentFunctional η (S.factualZ ω) S.θ₀ ∂P.μ := by
    unfold BackdoorEstimationSystem.P_Z
    rw [MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
      (measurable_aipwMomentFunctional η S.θ₀).aestronglyMeasurable]
  have hΩ_to_cross :
      ∫ ω, aipwMomentFunctional η (S.factualZ ω) S.θ₀ ∂P.μ
        = ∫ ω, crossInd ω ∂P.μ := by
    calc
      ∫ ω, aipwMomentFunctional η (S.factualZ ω) S.θ₀ ∂P.μ
          = ∫ ω, base ω + rT ω - rF ω + crossInd ω ∂P.μ :=
            MeasureTheory.integral_congr_ae hmoment_eq
      _ = (∫ ω, base ω ∂P.μ) + (∫ ω, rT ω ∂P.μ) -
            (∫ ω, rF ω ∂P.μ) + (∫ ω, crossInd ω ∂P.μ) := by
            have hbr : Integrable (fun ω => base ω + rT ω) P.μ :=
              hbase_int.add hrT_int
            have hbrf : Integrable (fun ω => base ω + rT ω - rF ω) P.μ :=
              hbr.sub hrF_int
            rw [show (fun ω => base ω + rT ω - rF ω + crossInd ω) =
                (fun ω => (base ω + rT ω - rF ω) + crossInd ω) from rfl]
            rw [integral_add hbrf hcrossInd_int]
            rw [integral_sub hbr hrF_int]
            rw [integral_add hbase_int hrT_int]
      _ = ∫ ω, crossInd ω ∂P.μ := by rw [hbase_zero, hrT_zero, hrF_zero]; ring
  have hpT_int : Integrable pT P.μ := by
    have hpT_meas : AEStronglyMeasurable pT P.μ := by
      apply Measurable.aestronglyMeasurable
      dsimp [pT, dμT, X]
      exact ((((η.μ_meas true).comp S.toPOBackdoorSystem.measurable_factualX).sub
        ((S.μ_meas true).comp S.toPOBackdoorSystem.measurable_factualX)).div
          (η.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)).mul
            ((S.measurable_e_val_label true).comp S.toPOBackdoorSystem.measurable_factualX)
    refine ((hdμT_int.norm.mul_const ε⁻¹).mono' hpT_meas ?_)
    filter_upwards [hη_X] with ω hηω
    have hη_pos_ω : 0 < η.e_fn (X ω) := lt_of_lt_of_le h_overlap.1 hηω.1
    have hden_abs : |η.e_fn (X ω)| = η.e_fn (X ω) :=
      abs_of_pos hη_pos_ω
    have he_abs_le : |S.e_val (X ω)| ≤ 1 := by
      rw [abs_of_pos (S.e_pos (X ω))]
      exact (S.e_lt_one (X ω)).le
    have hinv_le : (η.e_fn (X ω))⁻¹ ≤ ε⁻¹ :=
      (inv_le_inv₀ hη_pos_ω h_overlap.1).2 hηω.1
    have hratio_le : |S.e_val (X ω)| * (η.e_fn (X ω))⁻¹ ≤ ε⁻¹ := by
      calc
        |S.e_val (X ω)| * (η.e_fn (X ω))⁻¹
            ≤ 1 * (η.e_fn (X ω))⁻¹ := by
              exact mul_le_mul_of_nonneg_right he_abs_le
                (inv_nonneg.mpr hη_pos_ω.le)
        _ ≤ 1 * ε⁻¹ := by
              exact mul_le_mul_of_nonneg_left hinv_le zero_le_one
        _ = ε⁻¹ := by ring
    calc
      ‖pT ω‖ = |dμT ω / η.e_fn (X ω) * S.e_val_label true (X ω)| := by
        change ‖dμT ω / η.e_fn (X ω) * S.e_val_label true (X ω)‖ =
          |dμT ω / η.e_fn (X ω) * S.e_val_label true (X ω)|
        exact Real.norm_eq_abs _
      _ = |dμT ω / η.e_fn (X ω)| * |S.e_val_label true (X ω)| := by
        exact abs_mul _ _
      _ = |dμT ω| / |η.e_fn (X ω)| * |S.e_val_label true (X ω)| := by
        have hdivabs : |dμT ω / η.e_fn (X ω)| =
            |dμT ω| / |η.e_fn (X ω)| := abs_div _ _
        rw [hdivabs]
      _ ≤ |dμT ω| * ε⁻¹ := by
        simp only [e_val_label, hden_abs]
        calc
          |η.μ_fn true (X ω) - S.μ_val true (X ω)| / η.e_fn (X ω) *
              |S.e_val (X ω)|
              = |η.μ_fn true (X ω) - S.μ_val true (X ω)| *
                  (|S.e_val (X ω)| * (η.e_fn (X ω))⁻¹) := by
                rw [div_eq_mul_inv]
                ring
          _ ≤ |η.μ_fn true (X ω) - S.μ_val true (X ω)| * ε⁻¹ :=
                mul_le_mul_of_nonneg_left hratio_le (abs_nonneg _)
          _ = |dμT ω| * ε⁻¹ := by ring
      _ = ‖dμT ω‖ * ε⁻¹ := by simp [Real.norm_eq_abs]
  have hpF_int : Integrable pF P.μ := by
    have hpF_meas : AEStronglyMeasurable pF P.μ := by
      apply Measurable.aestronglyMeasurable
      dsimp [pF, dμF, X]
      exact ((((η.μ_meas false).comp S.toPOBackdoorSystem.measurable_factualX).sub
        ((S.μ_meas false).comp S.toPOBackdoorSystem.measurable_factualX)).div
          (measurable_const.sub
            (η.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))).mul
            ((S.measurable_e_val_label false).comp S.toPOBackdoorSystem.measurable_factualX)
    refine ((hdμF_int.norm.mul_const ε⁻¹).mono' hpF_meas ?_)
    filter_upwards [hη_X] with ω hηω
    have hη_false_pos_ω : 0 < 1 - η.e_fn (X ω) := by
      have : ε ≤ 1 - η.e_fn (X ω) := by linarith [hηω.2]
      exact lt_of_lt_of_le h_overlap.1 this
    have hden_abs : |1 - η.e_fn (X ω)| = 1 - η.e_fn (X ω) :=
      abs_of_pos hη_false_pos_ω
    have helabel_abs_le : |S.e_val_label false (X ω)| ≤ 1 := by
      simp only [e_val_label, Bool.false_eq_true, ↓reduceIte]
      have hnonneg : 0 ≤ 1 - S.e_val (X ω) := by linarith [S.e_lt_one (X ω)]
      rw [abs_of_nonneg hnonneg]
      linarith [S.e_pos (X ω)]
    have hden : ε ≤ 1 - η.e_fn (X ω) := by linarith [hηω.2]
    have hinv_le : (1 - η.e_fn (X ω))⁻¹ ≤ ε⁻¹ :=
      (inv_le_inv₀ hη_false_pos_ω h_overlap.1).2 hden
    have hratio_le :
        |S.e_val_label false (X ω)| * (1 - η.e_fn (X ω))⁻¹ ≤ ε⁻¹ := by
      calc
        |S.e_val_label false (X ω)| * (1 - η.e_fn (X ω))⁻¹
            ≤ 1 * (1 - η.e_fn (X ω))⁻¹ := by
              exact mul_le_mul_of_nonneg_right helabel_abs_le
                (inv_nonneg.mpr hη_false_pos_ω.le)
        _ ≤ 1 * ε⁻¹ := by
              exact mul_le_mul_of_nonneg_left hinv_le zero_le_one
        _ = ε⁻¹ := by ring
    calc
      ‖pF ω‖ = |dμF ω / (1 - η.e_fn (X ω)) * S.e_val_label false (X ω)| := by
        change ‖dμF ω / (1 - η.e_fn (X ω)) * S.e_val_label false (X ω)‖ =
          |dμF ω / (1 - η.e_fn (X ω)) * S.e_val_label false (X ω)|
        exact Real.norm_eq_abs _
      _ = |dμF ω / (1 - η.e_fn (X ω))| * |S.e_val_label false (X ω)| := by
        exact abs_mul _ _
      _ = |dμF ω| / |1 - η.e_fn (X ω)| * |S.e_val_label false (X ω)| := by
        have hdivabs : |dμF ω / (1 - η.e_fn (X ω))| =
            |dμF ω| / |1 - η.e_fn (X ω)| := abs_div _ _
        rw [hdivabs]
      _ ≤ |dμF ω| * ε⁻¹ := by
        simp only [hden_abs]
        calc
          |η.μ_fn false (X ω) - S.μ_val false (X ω)| / (1 - η.e_fn (X ω)) *
              |S.e_val_label false (X ω)|
              = |η.μ_fn false (X ω) - S.μ_val false (X ω)| *
                  (|S.e_val_label false (X ω)| * (1 - η.e_fn (X ω))⁻¹) := by
                rw [div_eq_mul_inv]
                ring
          _ ≤ |η.μ_fn false (X ω) - S.μ_val false (X ω)| * ε⁻¹ :=
                mul_le_mul_of_nonneg_left hratio_le (abs_nonneg _)
          _ = |dμF ω| * ε⁻¹ := by ring
      _ = ‖dμF ω‖ * ε⁻¹ := by simp [Real.norm_eq_abs]
  have hcrossProp_int : Integrable crossProp P.μ := by
    simpa [crossProp, sub_eq_add_neg, add_assoc] using
      ((hdμT_int.sub hdμF_int).sub hpT_int).add hpF_int
  have hcross_to_prop :
      ∫ ω, crossInd ω ∂P.μ = ∫ ω, crossProp ω ∂P.μ := by
    have hIT_prop : ∫ ω, iT ω ∂P.μ = ∫ ω, pT ω ∂P.μ := by
      have hf_meas : Measurable (fun x => (η.μ_fn true x - S.μ_val true x) / η.e_fn x) :=
        ((η.μ_meas true).sub (S.μ_meas true)).div η.e_meas
      have hf_ind_int : Integrable
          (fun ω => ((η.μ_fn true (X ω) - S.μ_val true (X ω)) / η.e_fn (X ω)) *
            indT ω) P.μ := by
        refine hiT_int.congr ?_
        exact Filter.Eventually.of_forall fun ω => by
          simp [iT, wT, dμT, X, indT]
          ring
      calc
        ∫ ω, iT ω ∂P.μ
            = ∫ ω, ((η.μ_fn true (X ω) - S.μ_val true (X ω)) /
                η.e_fn (X ω)) * indT ω ∂P.μ := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall fun ω => by
                simp [iT, wT, dμT, X, indT]
                ring
        _ = ∫ ω, ((η.μ_fn true (X ω) - S.μ_val true (X ω)) /
                η.e_fn (X ω)) * S.e_val_label true (X ω) ∂P.μ :=
              indicator_to_propScore_integral S hA true
                (fun x => (η.μ_fn true x - S.μ_val true x) / η.e_fn x)
                hf_meas hf_ind_int
        _ = ∫ ω, pT ω ∂P.μ := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall fun ω => by simp [pT, dμT, X]
    have hIF_prop : ∫ ω, iF ω ∂P.μ = ∫ ω, pF ω ∂P.μ := by
      have hf_meas : Measurable
          (fun x => (η.μ_fn false x - S.μ_val false x) / (1 - η.e_fn x)) :=
        ((η.μ_meas false).sub (S.μ_meas false)).div (measurable_const.sub η.e_meas)
      have hf_ind_int : Integrable
          (fun ω => ((η.μ_fn false (X ω) - S.μ_val false (X ω)) /
            (1 - η.e_fn (X ω))) * indF ω) P.μ := by
        refine hiF_int.congr ?_
        exact Filter.Eventually.of_forall fun ω => by
          simp [iF, wF, dμF, X, indF]
          ring
      calc
        ∫ ω, iF ω ∂P.μ
            = ∫ ω, ((η.μ_fn false (X ω) - S.μ_val false (X ω)) /
                (1 - η.e_fn (X ω))) * indF ω ∂P.μ := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall fun ω => by
                simp [iF, wF, dμF, X, indF]
                ring
        _ = ∫ ω, ((η.μ_fn false (X ω) - S.μ_val false (X ω)) /
                (1 - η.e_fn (X ω))) * S.e_val_label false (X ω) ∂P.μ :=
              indicator_to_propScore_integral S hA false
                (fun x => (η.μ_fn false x - S.μ_val false x) / (1 - η.e_fn x))
                hf_meas hf_ind_int
        _ = ∫ ω, pF ω ∂P.μ := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall fun ω => by simp [pF, dμF, X]
    calc
      ∫ ω, crossInd ω ∂P.μ
          = (∫ ω, dμT ω ∂P.μ) - (∫ ω, dμF ω ∂P.μ) -
              (∫ ω, iT ω ∂P.μ) + (∫ ω, iF ω ∂P.μ) := by
            have hsplit :
                ∫ ω, (dμT ω - dμF ω - iT ω) + iF ω ∂P.μ =
                  (∫ ω, dμT ω ∂P.μ) - (∫ ω, dμF ω ∂P.μ) -
                    (∫ ω, iT ω ∂P.μ) + (∫ ω, iF ω ∂P.μ) := by
              rw [show (fun ω => dμT ω - dμF ω - iT ω + iF ω) =
                  (fun ω => dμT ω - dμF ω - iT ω) + iF by
                funext ω
                rfl]
              change ∫ ω, (dμT - dμF - iT) ω + iF ω ∂P.μ =
                (∫ ω, dμT ω ∂P.μ) - (∫ ω, dμF ω ∂P.μ) -
                  (∫ ω, iT ω ∂P.μ) + (∫ ω, iF ω ∂P.μ)
              rw [integral_add ((hdμT_int.sub hdμF_int).sub hiT_int) hiF_int]
              change (∫ ω, (dμT - dμF) ω - iT ω ∂P.μ) +
                  (∫ ω, iF ω ∂P.μ) =
                (∫ ω, dμT ω ∂P.μ) - (∫ ω, dμF ω ∂P.μ) -
                  (∫ ω, iT ω ∂P.μ) + (∫ ω, iF ω ∂P.μ)
              rw [integral_sub (hdμT_int.sub hdμF_int) hiT_int]
              change ((∫ ω, dμT ω - dμF ω ∂P.μ) - ∫ ω, iT ω ∂P.μ) +
                  (∫ ω, iF ω ∂P.μ) =
                (∫ ω, dμT ω ∂P.μ) - (∫ ω, dμF ω ∂P.μ) -
                  (∫ ω, iT ω ∂P.μ) + (∫ ω, iF ω ∂P.μ)
              rw [integral_sub hdμT_int hdμF_int]
            exact hsplit
      _ = (∫ ω, dμT ω ∂P.μ) - (∫ ω, dμF ω ∂P.μ) -
              (∫ ω, pT ω ∂P.μ) + (∫ ω, pF ω ∂P.μ) := by
            rw [hIT_prop, hIF_prop]
      _ = ∫ ω, crossProp ω ∂P.μ := by
            have hsplit :
                ∫ ω, (dμT ω - dμF ω - pT ω) + pF ω ∂P.μ =
                  (∫ ω, dμT ω ∂P.μ) - (∫ ω, dμF ω ∂P.μ) -
                    (∫ ω, pT ω ∂P.μ) + (∫ ω, pF ω ∂P.μ) := by
              rw [show (fun ω => dμT ω - dμF ω - pT ω + pF ω) =
                  (fun ω => dμT ω - dμF ω - pT ω) + pF by
                funext ω
                rfl]
              change ∫ ω, (dμT - dμF - pT) ω + pF ω ∂P.μ =
                (∫ ω, dμT ω ∂P.μ) - (∫ ω, dμF ω ∂P.μ) -
                  (∫ ω, pT ω ∂P.μ) + (∫ ω, pF ω ∂P.μ)
              rw [integral_add ((hdμT_int.sub hdμF_int).sub hpT_int) hpF_int]
              change (∫ ω, (dμT - dμF) ω - pT ω ∂P.μ) +
                  (∫ ω, pF ω ∂P.μ) =
                (∫ ω, dμT ω ∂P.μ) - (∫ ω, dμF ω ∂P.μ) -
                  (∫ ω, pT ω ∂P.μ) + (∫ ω, pF ω ∂P.μ)
              rw [integral_sub (hdμT_int.sub hdμF_int) hpT_int]
              change ((∫ ω, dμT ω - dμF ω ∂P.μ) - ∫ ω, pT ω ∂P.μ) +
                  (∫ ω, pF ω ∂P.μ) =
                (∫ ω, dμT ω ∂P.μ) - (∫ ω, dμF ω ∂P.μ) -
                  (∫ ω, pT ω ∂P.μ) + (∫ ω, pF ω ∂P.μ)
              rw [integral_sub hdμT_int hdμF_int]
            exact hsplit.symm
  have hcrossProp_eq_rem : crossProp =ᵐ[P.μ] remΩ := by
    filter_upwards [hη_X] with ω hηω
    have hη_pos_ω : 0 < η.e_fn (X ω) := lt_of_lt_of_le h_overlap.1 hηω.1
    have hη_false_pos_ω : 0 < 1 - η.e_fn (X ω) := by
      have : ε ≤ 1 - η.e_fn (X ω) := by linarith [hηω.2]
      exact lt_of_lt_of_le h_overlap.1 this
    have hdenT : η.e_fn (X ω) ≠ 0 := hη_pos_ω.ne'
    have hdenF : 1 - η.e_fn (X ω) ≠ 0 := hη_false_pos_ω.ne'
    have hdenT' : η.e_fn (S.toPOBackdoorSystem.factualX ω) ≠ 0 := by
      simpa [X] using hdenT
    have hdenF' : 1 - η.e_fn (S.toPOBackdoorSystem.factualX ω) ≠ 0 := by
      simpa [X] using hdenF
    simp [crossProp, remΩ, pT, pF, dμT, dμF, X, e_val_label]
    field_simp [hdenT', hdenF']
    ring
  have hremX_meas : Measurable remX := by
    dsimp [remX]
    exact ((η.e_meas.sub S.e_meas).mul
      ((((η.μ_meas true).sub (S.μ_meas true)).div η.e_meas).add
        (((η.μ_meas false).sub (S.μ_meas false)).div
          (measurable_const.sub η.e_meas))))
  have hrem_push :
      ∫ ω, remΩ ω ∂P.μ = ∫ x, remX x ∂(S.P_X) := by
    unfold BackdoorEstimationSystem.P_X
    rw [MeasureTheory.integral_map S.toPOBackdoorSystem.measurable_factualX.aemeasurable
      hremX_meas.aestronglyMeasurable]
  calc
    ∫ z, aipwMomentFunctional η z S.θ₀ ∂(S.P_Z)
        = ∫ ω, aipwMomentFunctional η (S.factualZ ω) S.θ₀ ∂P.μ := hpushZ
    _ = ∫ ω, crossInd ω ∂P.μ := hΩ_to_cross
    _ = ∫ ω, crossProp ω ∂P.μ := hcross_to_prop
    _ = ∫ ω, remΩ ω ∂P.μ := MeasureTheory.integral_congr_ae hcrossProp_eq_rem
    _ = ∫ x, remX x ∂(S.P_X) := hrem_push

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean
