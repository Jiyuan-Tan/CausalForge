import Causalean.Estimation.ATT.Score.AIPWMoment

/-!
Provides conditioning and reweighting identities for ATT AIPW scores. The
lemmas pull treatment indicators and propensity weights through conditional
expectations to isolate treated and control contributions.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Score pull-out lemmas for ATT AIPW proofs

Helper lemmas that move σ(X)-measurable factors past `μ[·|σ(X)]` and rewrite
the IPW indicator weights for the ATT setting.  Parallels
`Estimation/ATE/Score/ScorePullout.lean`, but only the `(1−A)·e/(1−e)` weight and the
treated-arm `A` indicator appear.  Used by `MeanZero.lean`.
-/

/-!
This file provides the conditioning and reweighting identities needed to handle
the treated and control arms in augmented inverse-probability weighted
estimation of the average treatment effect on the treated.

It defines the value-space control-arm weight `ipwWeight_false`, proves the
propensity identities `propScore_false_ae`, `propScore_eq_e_val_ae`, and
`propScore_false_eq_one_minus_e_val_ae`, establishes the residual identity
`residual_false_condExp_zero`, and exposes the two integral tools
`weighted_residual_false_integral_zero` and `indicator_to_propScore_integral`.
-/

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace TreatedEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- Value-space IPW weight `e(x) / (1 − e(x))` used in the ATT correction. -/
noncomputable def ipwWeight_false (S : TreatedEstimationSystem P γ) (x : γ) :
    ℝ :=
  S.e_val x / (1 - S.e_val x)

/-- Measurability of the value-space IPW weight `e/(1−e)`. -/
lemma measurable_ipwWeight_false (S : TreatedEstimationSystem P γ) :
    Measurable S.ipwWeight_false :=
  S.e_meas.div (measurable_const.sub S.e_meas)

/-- `propScore false =ᵐ 1 − propScore true`.  The indicator pair sums to one
pointwise, conditional expectation is linear and preserves constants. -/
-- Outline: mirror `BackdoorEstimationSystem.propScore_false_ae` from
-- `Estimation/ATE/Score/ScorePullout.lean`.  Uses `dVar.indicator_add_indicator_not`
-- + `condExp_const` + `condExp_add` + `linarith` on the pointwise sum.
lemma propScore_false_ae (S : TreatedEstimationSystem P γ)
    (_hA : S.toPOBackdoorSystem.ATTAssumptions) :
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

/-- The treated-arm propensity `propScore true` factors through `factualX` via
the value-space `e_val`.  Direct restatement of `S.e_compat`. -/
lemma propScore_eq_e_val_ae (S : TreatedEstimationSystem P γ)
    (_hA : S.toPOBackdoorSystem.ATTAssumptions) :
    S.toPOBackdoorSystem.propScore true
      =ᵐ[P.μ]
        (fun ω => S.e_val (S.toPOBackdoorSystem.factualX ω)) :=
  S.e_compat

/-- Control-arm propensity factors through `factualX` as `1 − e_val`. -/
-- Outline: combine `propScore_false_ae` with `S.e_compat`; pointwise rewrite
-- `1 − propScore true ω = 1 − e_val (factualX ω)`.
lemma propScore_false_eq_one_minus_e_val_ae
    (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions) :
    S.toPOBackdoorSystem.propScore false
      =ᵐ[P.μ]
        (fun ω => 1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) := by
  filter_upwards [propScore_false_ae S hA, S.e_compat] with ω hf hc
  simp [hf, hc]

private lemma propScore_false_ne_zero (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions) :
    ∀ᵐ ω ∂P.μ, S.toPOBackdoorSystem.propScore false ω ≠ 0 :=
  hA.propScore_false_ne

/-- The σ(X)-conditional expectation of `1_{D=false}·(Y − μ₀(X))` vanishes a.s.
The witness `Y(false) =ᵐ μ₀_val ∘ factualX` comes from `μ₀_compat` together
with consistency on `{D = false}`. -/
-- Outline: mirror `cond_exp_residual_zero` (ATE/MeanZero) for `d = false`.
-- Use consistency to replace `factualY` by `YofD false` on `{D=false}`,
-- factor σ(X)-measurables out of conditional expectation, and apply
-- `μ₀_compat`.
lemma residual_false_condExp_zero (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions) :
    P.μ[fun ω =>
        S.toPOBackdoorSystem.dVar.indicator false ω
          * (S.toPOBackdoorSystem.factualY ω
              - S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) |
            S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
  have hY_int : Integrable S.toPOBackdoorSystem.factualY P.μ :=
    S.toPOBackdoorSystem.integrable_factualY_of_consistency
      hA.consistency hA.integrable_Y1 hA.integrable_Y0
  have hYind_int : Integrable
      (fun ω => S.toPOBackdoorSystem.factualY ω *
        S.toPOBackdoorSystem.dVar.indicator false ω) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_mul_indicator false hY_int
      S.toPOBackdoorSystem.measurable_factualY
  have hμ₀x_int :
      Integrable (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) P.μ := by
    have hcate_int : Integrable (S.toPOBackdoorSystem.CATE false) P.μ := by
      unfold POBackdoorSystem.CATE
      exact MeasureTheory.integrable_condExp
    exact hcate_int.congr (S.μ₀_compat hA)
  have hμ₀x_meas :
      Measurable (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) :=
    S.μ₀_meas.comp S.toPOBackdoorSystem.measurable_factualX
  have hμ₀ind_int : Integrable
      (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω) *
        S.toPOBackdoorSystem.dVar.indicator false ω) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_mul_indicator false hμ₀x_int hμ₀x_meas
  have hres_eq :
      (fun ω => S.toPOBackdoorSystem.dVar.indicator false ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ₀_val (S.toPOBackdoorSystem.factualX ω)))
        = (fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator false ω -
          S.μ₀_val (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator false ω) := by
    funext ω
    ring
  have hsub :
      P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator false ω -
          S.μ₀_val (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator false ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator false ω |
            S.toPOBackdoorSystem.sigmaX]
          - P.μ[fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator false ω |
            S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_sub hYind_int hμ₀ind_int S.toPOBackdoorSystem.sigmaX
  have hYce :
      P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
          S.toPOBackdoorSystem.dVar.indicator false ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          S.toPOBackdoorSystem.propScore false * S.toPOBackdoorSystem.CATE false := by
    have hcate := S.control_cate_backdoor hA
    filter_upwards [hcate, propScore_false_ne_zero S hA] with ω hcat hneω
    unfold POBackdoorSystem.adjustedCE at hcat
    rw [Pi.mul_apply, hcat]
    field_simp [hneω]
  have hμ₀x_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω))
    exact (S.μ₀_meas.comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  have hind_int : Integrable (S.toPOBackdoorSystem.dVar.indicator false) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_indicator false
  have hμce :
      P.μ[fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω) *
          S.toPOBackdoorSystem.dVar.indicator false ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) *
            S.toPOBackdoorSystem.propScore false := by
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hμ₀x_sm hμ₀ind_int hind_int
    simpa [POBackdoorSystem.propScore] using hpull
  rw [hres_eq]
  refine hsub.trans ?_
  filter_upwards [hYce, hμce, S.μ₀_compat hA] with ω hy hmu hcompat
  have hcate_comp : S.toPOBackdoorSystem.CATE false ω =
      S.μ₀_val (S.toPOBackdoorSystem.factualX ω) := by
    simpa [POBackdoorSystem.CATE] using hcompat
  rw [Pi.sub_apply, hy, hmu, Pi.mul_apply, Pi.mul_apply, hcate_comp]
  ring

/-- AIPW weighted residual integral (control arm).  For any measurable
`g : γ → ℝ` whose product with the residual is integrable,
`∫ g(X) · 1_{D=false} · (Y − μ₀(X)) dμ = 0`.  One-sided analogue of
`weighted_residual_integral_zero` in `Estimation/ATE/Score/ScorePullout.lean`. -/
-- Outline: pull `g(X)` out of `μ[·|σ(X)]` via
-- `condExp_mul_of_stronglyMeasurable_left`, then apply
-- `residual_false_condExp_zero` and `integral_condExp`.
lemma weighted_residual_false_integral_zero
    (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (g : γ → ℝ) (hg_meas : Measurable g)
    (h_int : Integrable
      (fun ω => g (S.toPOBackdoorSystem.factualX ω)
        * (S.toPOBackdoorSystem.dVar.indicator false ω
            * (S.toPOBackdoorSystem.factualY ω
                - S.μ₀_val (S.toPOBackdoorSystem.factualX ω)))) P.μ) :
    ∫ ω, g (S.toPOBackdoorSystem.factualX ω)
        * (S.toPOBackdoorSystem.dVar.indicator false ω
            * (S.toPOBackdoorSystem.factualY ω
                - S.μ₀_val (S.toPOBackdoorSystem.factualX ω))) ∂P.μ = 0 := by
  have hg_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => g (S.toPOBackdoorSystem.factualX ω)) := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => g (S.toPOBackdoorSystem.factualX ω))
    exact (hg_meas.comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  have hY_int : Integrable S.toPOBackdoorSystem.factualY P.μ :=
    S.toPOBackdoorSystem.integrable_factualY_of_consistency
      hA.consistency hA.integrable_Y1 hA.integrable_Y0
  have hYind_int : Integrable
      (fun ω => S.toPOBackdoorSystem.factualY ω *
        S.toPOBackdoorSystem.dVar.indicator false ω) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_mul_indicator false hY_int
      S.toPOBackdoorSystem.measurable_factualY
  have hμ₀x_int :
      Integrable (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) P.μ := by
    have hcate_int : Integrable (S.toPOBackdoorSystem.CATE false) P.μ := by
      unfold POBackdoorSystem.CATE
      exact MeasureTheory.integrable_condExp
    exact hcate_int.congr (S.μ₀_compat hA)
  have hμ₀x_meas :
      Measurable (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) :=
    S.μ₀_meas.comp S.toPOBackdoorSystem.measurable_factualX
  have hμ₀ind_int : Integrable
      (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω) *
        S.toPOBackdoorSystem.dVar.indicator false ω) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_mul_indicator false hμ₀x_int hμ₀x_meas
  have hresid_int : Integrable
      (fun ω => S.toPOBackdoorSystem.dVar.indicator false ω *
        (S.toPOBackdoorSystem.factualY ω -
          S.μ₀_val (S.toPOBackdoorSystem.factualX ω))) P.μ := by
    have hYind_int' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator false ω *
          S.toPOBackdoorSystem.factualY ω) P.μ := by
      simpa [mul_comm] using hYind_int
    have hμ₀ind_int' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator false ω *
          S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) P.μ := by
      simpa [mul_comm] using hμ₀ind_int
    have hsub := hYind_int'.sub hμ₀ind_int'
    refine hsub.congr ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    change S.toPOBackdoorSystem.dVar.indicator false ω *
          S.toPOBackdoorSystem.factualY ω -
        S.toPOBackdoorSystem.dVar.indicator false ω *
          S.μ₀_val (S.toPOBackdoorSystem.factualX ω)
        = S.toPOBackdoorSystem.dVar.indicator false ω *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ₀_val (S.toPOBackdoorSystem.factualX ω))
    ring
  have hcondexp_pull :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hg_sm h_int hresid_int
  have hgresid_ce_zero :
      P.μ[fun ω => g (S.toPOBackdoorSystem.factualX ω) *
            (S.toPOBackdoorSystem.dVar.indicator false ω *
              (S.toPOBackdoorSystem.factualY ω -
                S.μ₀_val (S.toPOBackdoorSystem.factualX ω))) |
            S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ]
          (fun _ => (0 : ℝ)) := by
    refine hcondexp_pull.trans ?_
    filter_upwards [residual_false_condExp_zero S hA] with ω hω
    have : ((fun ω' => g (S.toPOBackdoorSystem.factualX ω')) *
        P.μ[fun ω' => S.toPOBackdoorSystem.dVar.indicator false ω' *
            (S.toPOBackdoorSystem.factualY ω' -
              S.μ₀_val (S.toPOBackdoorSystem.factualX ω')) |
            S.toPOBackdoorSystem.sigmaX]) ω = 0 := by
      rw [Pi.mul_apply, hω, mul_zero]
    exact this
  calc
    ∫ ω, g (S.toPOBackdoorSystem.factualX ω) *
          (S.toPOBackdoorSystem.dVar.indicator false ω *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ₀_val (S.toPOBackdoorSystem.factualX ω))) ∂P.μ
      = ∫ ω, P.μ[fun ω => g (S.toPOBackdoorSystem.factualX ω) *
            (S.toPOBackdoorSystem.dVar.indicator false ω *
              (S.toPOBackdoorSystem.factualY ω -
                S.μ₀_val (S.toPOBackdoorSystem.factualX ω))) |
            S.toPOBackdoorSystem.sigmaX] ω ∂P.μ := by
        rw [MeasureTheory.integral_condExp S.toPOBackdoorSystem.sigmaX_le]
    _ = ∫ _, (0 : ℝ) ∂P.μ :=
          MeasureTheory.integral_congr_ae hgresid_ce_zero
    _ = 0 := MeasureTheory.integral_zero _ _

/-- Replace `1_{D=d}` by the value-space propensity inside an integral against
`P.μ`.  Same shape as the ATE `indicator_to_propScore_integral`. -/
-- Outline: same proof recipe as the ATE counterpart. Pull `f(X)` out of
-- `μ[·|σ(X)]`, apply the appropriate `propScore_eq_e_val_ae` /
-- `propScore_false_eq_one_minus_e_val_ae` substitution, and re-integrate.
lemma indicator_to_propScore_integral
    (S : TreatedEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.ATTAssumptions) (d : Bool)
    (f : γ → ℝ) (hf_meas : Measurable f)
    (hf_ind_int : Integrable
      (fun ω => f (S.toPOBackdoorSystem.factualX ω)
        * S.toPOBackdoorSystem.dVar.indicator d ω) P.μ) :
    ∫ ω, f (S.toPOBackdoorSystem.factualX ω)
        * S.toPOBackdoorSystem.dVar.indicator d ω ∂P.μ
      = ∫ ω, f (S.toPOBackdoorSystem.factualX ω)
          * (if d = true then S.e_val (S.toPOBackdoorSystem.factualX ω)
             else 1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) ∂P.μ := by
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
  have hprop :
      S.toPOBackdoorSystem.propScore d
        =ᵐ[P.μ]
          (fun ω => if d = true then S.e_val (S.toPOBackdoorSystem.factualX ω)
             else 1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) := by
    cases d
    · simpa using propScore_false_eq_one_minus_e_val_ae S hA
    · simpa using propScore_eq_e_val_ae S hA
  have hCE_replace :
      P.μ[fun ω => f (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ]
          (fun ω => f (S.toPOBackdoorSystem.factualX ω) *
            (if d = true then S.e_val (S.toPOBackdoorSystem.factualX ω)
             else 1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) := by
    refine hCE_pull.trans ?_
    filter_upwards [hprop] with ω hω
    have hω' :
        P.μ[S.toPOBackdoorSystem.dVar.indicator d |
            S.toPOBackdoorSystem.sigmaX] ω
          = (if d = true then S.e_val (S.toPOBackdoorSystem.factualX ω)
             else 1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) := hω
    rw [Pi.mul_apply, hω']
  calc
    ∫ ω, f (S.toPOBackdoorSystem.factualX ω) *
          S.toPOBackdoorSystem.dVar.indicator d ω ∂P.μ
      = ∫ ω, P.μ[fun ω => f (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX] ω ∂P.μ :=
        (MeasureTheory.integral_condExp S.toPOBackdoorSystem.sigmaX_le).symm
    _ = ∫ ω, f (S.toPOBackdoorSystem.factualX ω) *
            (if d = true then S.e_val (S.toPOBackdoorSystem.factualX ω)
             else 1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) ∂P.μ :=
        MeasureTheory.integral_congr_ae hCE_replace

end TreatedEstimationSystem

end ATT
end Estimation
end Causalean
