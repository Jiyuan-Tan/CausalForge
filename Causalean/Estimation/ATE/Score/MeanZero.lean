/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mean zero of the AIPW influence function — `lem:est-aipw-mean-zero`

Helpers and headline lemma `aipw_mean_zero`.

Decomposition of `ψ_AIPW(factualZ ω)` into four pieces:

* `(μ_val 1 - μ_val 0)`                       — gives `θ₀` after integration.
* `(ind_true / e_val(X)) (Y - μ_val 1)`       — IPW correction (true).
* `-(ind_false / (1 - e_val(X))) (Y - μ_val 0)` — IPW correction (false).
* `-θ₀`                                       — constant.

The two IPW corrections vanish via `weighted_residual_integral_zero` (a
σ(X)-pull-out lemma based on `cond_exp_residual_zero`). The other two cancel.
-/

import Causalean.Estimation.ATE.Score.AIPWMoment

/-!
Proves measurability and mean-zero properties of the AIPW influence function
for back-door average treatment effect estimation.

The file establishes `measurable_ψ_AIPW`, residual and propensity-score
pull-out lemmas used by the proof, the source-level mean-zero theorem
`aipw_mean_zero`, and the square-integrability corollary
`aipw_mean_zero_of_square_integrable` that derives the weighted residual
integrability gates from strict overlap and second moments.
-/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## Measurability of `ψ_AIPW` -/

/-- The AIPW influence function is measurable as a function of the observed data triple. -/
lemma measurable_ψ_AIPW (S : BackdoorEstimationSystem P γ) :
    Measurable S.ψ_AIPW := by
  unfold BackdoorEstimationSystem.ψ_AIPW aipwMoment indA projX projA projY
  have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
  have hy : Measurable (fun z : γ × Bool × ℝ => z.2.2) := by measurability
  have hμt : Measurable (fun z : γ × Bool × ℝ => S.μ_val true z.1) :=
    (S.μ_meas true).comp hx
  have hμf : Measurable (fun z : γ × Bool × ℝ => S.μ_val false z.1) :=
    (S.μ_meas false).comp hx
  have he : Measurable (fun z : γ × Bool × ℝ => S.e_val z.1) :=
    S.e_meas.comp hx
  have hind : Measurable (fun z : γ × Bool × ℝ =>
      if z.2.1 = true then (1 : ℝ) else 0) := by
    have ha : Measurable (fun z : γ × Bool × ℝ => z.2.1) := by measurability
    exact (Measurable.of_discrete
      (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
  exact ((((hμt.sub hμf).add ((hind.div he).mul (hy.sub hμt))).sub
    (((measurable_const.sub hind).div (measurable_const.sub he)).mul
      (hy.sub hμf))).sub measurable_const)

/-! ## Helpers for `aipw_mean_zero` -/

/-- The conditional treatment probability for either treatment label is
nonzero almost surely under the back-door assumptions. -/
lemma propScore_ne_zero (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) (d : Bool) :
    ∀ᵐ ω ∂P.μ, S.toPOBackdoorSystem.propScore d ω ≠ 0 := by
  cases d
  · have hindD_integrable :
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
    filter_upwards [hsum, hadd, hA.overlap] with ω h1 h2 hT
    have heq : S.toPOBackdoorSystem.propScore true ω +
        S.toPOBackdoorSystem.propScore false ω = 1 := by
      have :
          P.μ[S.toPOBackdoorSystem.dVar.indicator true |
                S.toPOBackdoorSystem.sigmaX] ω
            + P.μ[S.toPOBackdoorSystem.dVar.indicator false |
                S.toPOBackdoorSystem.sigmaX] ω = 1 := by
        rw [← Pi.add_apply, ← h2, h1]
      unfold POBackdoorSystem.propScore
      exact this
    have hps_false : S.toPOBackdoorSystem.propScore false ω =
        1 - S.toPOBackdoorSystem.propScore true ω := by
      linarith
    rw [hps_false]
    linarith [hT.2]
  · filter_upwards [hA.overlap] with ω hω
    exact ne_of_gt hω.1

/-- Conditional expectation of the residual `ind_d · (Y − μ_val d X)` given σ(X)
is zero a.s. — the σ(X)-cleared form of `lem:est-aipw-mean-zero`. -/
lemma cond_exp_residual_zero (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) (d : Bool) :
    P.μ[fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
           (S.toPOBackdoorSystem.factualY ω -
             S.μ_val d (S.toPOBackdoorSystem.factualX ω))
        | S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
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
  have hres_eq :
      (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val d (S.toPOBackdoorSystem.factualX ω)))
        = (fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator d ω -
          S.μ_val d (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω) := by
    funext ω
    ring
  have hsub :
      P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator d ω -
          S.μ_val d (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX]
          - P.μ[fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_sub hYind_int hμind_int S.toPOBackdoorSystem.sigmaX
  have hYce :
      P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
          S.toPOBackdoorSystem.dVar.indicator d ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          S.toPOBackdoorSystem.propScore d * S.toPOBackdoorSystem.CATE d := by
    have hcate := S.toPOBackdoorSystem.cate_backdoor hA d
    filter_upwards [hcate, propScore_ne_zero S hA d] with ω hcat hneω
    unfold POBackdoorSystem.adjustedCE at hcat
    rw [Pi.mul_apply, hcat]
    field_simp [hneω]
  have hμx_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω))
    exact ((S.μ_meas d).comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  have hind_int : Integrable (S.toPOBackdoorSystem.dVar.indicator d) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_indicator d
  have hμce :
      P.μ[fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω) *
          S.toPOBackdoorSystem.dVar.indicator d ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) *
            S.toPOBackdoorSystem.propScore d := by
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hμx_sm hμind_int hind_int
    simpa [POBackdoorSystem.propScore] using hpull
  rw [hres_eq]
  refine hsub.trans ?_
  filter_upwards [hYce, hμce, S.μ_compat hA d] with ω hy hmu hcompat
  have hcate_comp : S.toPOBackdoorSystem.CATE d ω =
      S.μ_val d (S.toPOBackdoorSystem.factualX ω) := by
    simpa [POBackdoorSystem.CATE] using hcompat
  rw [Pi.sub_apply, hy, hmu, Pi.mul_apply, Pi.mul_apply, hcate_comp]
  ring

/-- `propScore false =ᵐ 1 - propScore true` under the back-door assumptions:
the indicator-pair sums to one pointwise, conditional expectation is linear and
preserves constants, so the two propensity scores sum to one a.s. -/
private lemma propScore_false_ae (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) :
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
  have _ := hA
  filter_upwards [hsum, hadd] with ω h1 h2
  have hsum_ω :
      P.μ[S.toPOBackdoorSystem.dVar.indicator true |
            S.toPOBackdoorSystem.sigmaX] ω
        + P.μ[S.toPOBackdoorSystem.dVar.indicator false |
            S.toPOBackdoorSystem.sigmaX] ω = 1 := by
    rw [← Pi.add_apply, ← h2, h1]
  unfold POBackdoorSystem.propScore
  linarith

/-- The estimand `θ₀ = ∫ x, (μ_val(1,x) − μ_val(0,x)) ∂P_X` lifts back to the
ambient measure via `factualX`. -/
lemma theta_zero_factualX_integral
    (S : BackdoorEstimationSystem P γ) :
    S.θ₀ = ∫ ω, S.μ_val true (S.toPOBackdoorSystem.factualX ω) -
        S.μ_val false (S.toPOBackdoorSystem.factualX ω) ∂P.μ := by
  unfold BackdoorEstimationSystem.θ₀ BackdoorEstimationSystem.P_X
  have hmeas_diff :
      Measurable (fun x => S.μ_val true x - S.μ_val false x) :=
    (S.μ_meas true).sub (S.μ_meas false)
  rw [MeasureTheory.integral_map
    S.toPOBackdoorSystem.measurable_factualX.aemeasurable
    hmeas_diff.aestronglyMeasurable]

/-- AIPW weighted-residual integral. Whenever the weight `g : γ → ℝ` is measurable
and the resulting product is integrable, the integral against `μ` of
`g(X(ω)) · 1_{D=d}(ω) · (Y(ω) − μ_val(d, X(ω)))` is zero, by pulling `g(X)` out of
conditional expectation (it is `σ(X)`-measurable) and using `cond_exp_residual_zero`.

Both IPW correction terms in `aipw_factualZ_integral_zero` reduce to this via
`g := fun x => 1 / e_val x` and `g := fun x => 1 / (1 - e_val x)`. -/
private lemma weighted_residual_integral_zero
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) (d : Bool)
    (g : γ → ℝ) (hg_meas : Measurable g)
    (h_int : Integrable
      (fun ω => g (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator d ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val d (S.toPOBackdoorSystem.factualX ω)))) P.μ) :
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
  have hresid_ce_zero := cond_exp_residual_zero S hA d
  have hgresid_ce_zero :
      P.μ[fun ω => g (S.toPOBackdoorSystem.factualX ω) *
            (S.toPOBackdoorSystem.dVar.indicator d ω *
              (S.toPOBackdoorSystem.factualY ω -
                S.μ_val d (S.toPOBackdoorSystem.factualX ω))) |
            S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    refine hcondexp_pull.trans ?_
    filter_upwards [hresid_ce_zero] with ω hω
    have : ((fun ω' => g (S.toPOBackdoorSystem.factualX ω')) *
        P.μ[fun ω' => S.toPOBackdoorSystem.dVar.indicator d ω' *
            (S.toPOBackdoorSystem.factualY ω' -
              S.μ_val d (S.toPOBackdoorSystem.factualX ω')) |
            S.toPOBackdoorSystem.sigmaX]) ω = 0 := by
      rw [Pi.mul_apply, hω, mul_zero]
    exact this
  calc ∫ ω, g (S.toPOBackdoorSystem.factualX ω) *
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

/-! ## Indicator-to-propensity score pull-out

Companion to `weighted_residual_integral_zero`: replaces the indicator
`1_{D=d}` by the value-space propensity `e_val_label d (X)` inside an
integral against `P.μ`.  Used in `Remainder.aipw_remainder_identity` to
collapse the cross terms `(1_{D=d} / η.e_fn) · Δμ_d(X)` to their
`e_val`-weighted form. -/

/-- Value-space propensity for label `d`: `e_val` for `d = true`,
`1 − e_val` for `d = false`. -/
private noncomputable def e_val_label (S : BackdoorEstimationSystem P γ)
    (d : Bool) (x : γ) : ℝ :=
  if d then S.e_val x else 1 - S.e_val x

private lemma measurable_e_val_label (S : BackdoorEstimationSystem P γ) (d : Bool) :
    Measurable (S.e_val_label d) := by
  cases d
  · simpa [e_val_label] using measurable_const.sub S.e_meas
  · simpa [e_val_label] using S.e_meas

/-- The σ(X)-conditional expectation of `1_{D=d}` is `e_val_label d (X)`
a.s.  Combines `e_compat` (for `d = true`) with `propScore_false_ae`
(for `d = false`). -/
private lemma propScore_eq_e_val_label_ae
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

/-- **Indicator-to-propensity rewrite.**  For any measurable
`f : γ → ℝ`, the integral of `f(X) · 1_{D=d}` equals the integral of
`f(X) · e_val_label d (X)` against `P.μ`.

Proof: condition on `σ(X)`; pull `f(X)` out (it is `σ(X)`-measurable);
replace `μ[1_{D=d} | σ(X)] = propScore d` by `e_val_label d (X)` via
`propScore_eq_e_val_label_ae`. -/
private lemma indicator_to_propScore_integral
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
            S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => f (S.toPOBackdoorSystem.factualX ω) *
            S.e_val_label d (S.toPOBackdoorSystem.factualX ω)) := by
    refine hCE_pull.trans ?_
    filter_upwards [propScore_eq_e_val_label_ae S hA d] with ω hω
    have hω' :
        P.μ[S.toPOBackdoorSystem.dVar.indicator d |
            S.toPOBackdoorSystem.sigmaX] ω
          = S.e_val_label d (S.toPOBackdoorSystem.factualX ω) := hω
    rw [Pi.mul_apply, hω']
  calc ∫ ω, f (S.toPOBackdoorSystem.factualX ω) *
          S.toPOBackdoorSystem.dVar.indicator d ω ∂P.μ
      = ∫ ω, P.μ[fun ω => f (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX] ω ∂P.μ :=
        (MeasureTheory.integral_condExp S.toPOBackdoorSystem.sigmaX_le).symm
    _ = ∫ ω, f (S.toPOBackdoorSystem.factualX ω) *
            S.e_val_label d (S.toPOBackdoorSystem.factualX ω) ∂P.μ :=
        MeasureTheory.integral_congr_ae hCE_replace

/-! ## Headline lemma -/

private lemma aipw_factualZ_integral_zero (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (hB_int : Integrable
      (fun ω => (1 / S.e_val (S.toPOBackdoorSystem.factualX ω)) *
        (S.toPOBackdoorSystem.dVar.indicator true ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val true (S.toPOBackdoorSystem.factualX ω)))) P.μ)
    (hC_int : Integrable
      (fun ω => (1 / (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) *
        (S.toPOBackdoorSystem.dVar.indicator false ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω)))) P.μ) :
    (∫ ω, S.ψ_AIPW (S.factualZ ω) ∂P.μ) = 0 := by
  let base : P.Ω → ℝ := fun ω =>
    S.μ_val true (S.toPOBackdoorSystem.factualX ω) -
      S.μ_val false (S.toPOBackdoorSystem.factualX ω)
  let B : P.Ω → ℝ := fun ω =>
    indA (S.factualZ ω) / S.e_val (S.toPOBackdoorSystem.factualX ω) *
      (S.toPOBackdoorSystem.factualY ω -
        S.μ_val true (S.toPOBackdoorSystem.factualX ω))
  let C : P.Ω → ℝ := fun ω =>
    (1 - indA (S.factualZ ω)) /
      (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) *
      (S.toPOBackdoorSystem.factualY ω -
        S.μ_val false (S.toPOBackdoorSystem.factualX ω))
  let B' : P.Ω → ℝ := fun ω =>
    (1 / S.e_val (S.toPOBackdoorSystem.factualX ω)) *
      (S.toPOBackdoorSystem.dVar.indicator true ω *
        (S.toPOBackdoorSystem.factualY ω -
          S.μ_val true (S.toPOBackdoorSystem.factualX ω)))
  let C' : P.Ω → ℝ := fun ω =>
    (1 / (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) *
      (S.toPOBackdoorSystem.dVar.indicator false ω *
        (S.toPOBackdoorSystem.factualY ω -
          S.μ_val false (S.toPOBackdoorSystem.factualX ω)))
  have hindA_true : ∀ ω, indA (S.factualZ ω) =
      S.toPOBackdoorSystem.dVar.indicator true ω := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [BackdoorEstimationSystem.factualZ, indA, projA, hD, hInd]
    · have hF : S.toPOBackdoorSystem.factualD ω = false := by
        cases h' : S.toPOBackdoorSystem.factualD ω <;> simp [h'] at hD ⊢
      have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [BackdoorEstimationSystem.factualZ, indA, projA, hD, hInd]
  have hindA_false : ∀ ω, 1 - indA (S.factualZ ω) =
      S.toPOBackdoorSystem.dVar.indicator false ω := by
    intro ω
    have hsum : S.toPOBackdoorSystem.dVar.indicator true ω +
        S.toPOBackdoorSystem.dVar.indicator false ω = 1 :=
      S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
    calc
      1 - indA (S.factualZ ω) = 1 - S.toPOBackdoorSystem.dVar.indicator true ω := by
        rw [hindA_true ω]
      _ = S.toPOBackdoorSystem.dVar.indicator false ω := by linarith
  have hψ_eq :
      (fun ω => S.ψ_AIPW (S.factualZ ω))
          =ᵐ[P.μ] (fun ω => base ω + B ω - C ω - S.θ₀) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    unfold base B C BackdoorEstimationSystem.ψ_AIPW BackdoorEstimationSystem.aipwMoment
    simp [BackdoorEstimationSystem.factualZ, projX, projY, mul_comm, sub_eq_add_neg,
      add_assoc, add_comm]
  have hEqB : B' =ᵐ[P.μ] B := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    calc
      (1 / S.e_val (S.toPOBackdoorSystem.factualX ω)) *
          (S.toPOBackdoorSystem.dVar.indicator true ω *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ_val true (S.toPOBackdoorSystem.factualX ω)))
          = (S.toPOBackdoorSystem.dVar.indicator true ω /
              S.e_val (S.toPOBackdoorSystem.factualX ω)) *
              (S.toPOBackdoorSystem.factualY ω -
                S.μ_val true (S.toPOBackdoorSystem.factualX ω)) := by
            ring
      _ = (indA (S.factualZ ω) /
            S.e_val (S.toPOBackdoorSystem.factualX ω)) *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ_val true (S.toPOBackdoorSystem.factualX ω)) := by
            rw [hindA_true ω]
  have hB_int' : Integrable B P.μ := hB_int.congr hEqB
  have hEqC : C' =ᵐ[P.μ] C := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    calc
      (1 / (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) *
          (S.toPOBackdoorSystem.dVar.indicator false ω *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ_val false (S.toPOBackdoorSystem.factualX ω)))
          = (S.toPOBackdoorSystem.dVar.indicator false ω /
              (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) *
              (S.toPOBackdoorSystem.factualY ω -
                S.μ_val false (S.toPOBackdoorSystem.factualX ω)) := by
            ring
      _ = ((1 - indA (S.factualZ ω)) /
          (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ_val false (S.toPOBackdoorSystem.factualX ω)) := by
            rw [hindA_false ω]
  have hC_int' : Integrable C P.μ := hC_int.congr hEqC
  have hB_zero : ∫ ω, B' ω ∂P.μ = 0 := by
    have hg_meas : Measurable (fun x => 1 / S.e_val x) :=
      measurable_const.div S.e_meas
    exact weighted_residual_integral_zero S hA true (fun x => 1 / S.e_val x)
      hg_meas hB_int
  have hC_zero : ∫ ω, C' ω ∂P.μ = 0 := by
    have hg_meas : Measurable (fun x => 1 / (1 - S.e_val x)) :=
      measurable_const.div (measurable_const.sub S.e_meas)
    exact weighted_residual_integral_zero S hA false
      (fun x => 1 / (1 - S.e_val x)) hg_meas hC_int
  have hB_zero' : ∫ ω, B ω ∂P.μ = 0 := by
    rw [MeasureTheory.integral_congr_ae hEqB.symm]
    exact hB_zero
  have hC_zero' : ∫ ω, C ω ∂P.μ = 0 := by
    rw [MeasureTheory.integral_congr_ae hEqC.symm]
    exact hC_zero
  have hbase_int : Integrable base P.μ := by
    have hcate : ∀ d, Integrable (S.toPOBackdoorSystem.CATE d) P.μ := fun d => by
      unfold POBackdoorSystem.CATE
      exact MeasureTheory.integrable_condExp
    have h1 :
        Integrable (fun ω => S.μ_val true (S.toPOBackdoorSystem.factualX ω)) P.μ :=
      (hcate true).congr (S.μ_compat hA true)
    have h0 :
        Integrable (fun ω => S.μ_val false (S.toPOBackdoorSystem.factualX ω)) P.μ :=
      (hcate false).congr (S.μ_compat hA false)
    exact h1.sub h0
  have hθ0 : (∫ ω, base ω ∂P.μ) = S.θ₀ := (theta_zero_factualX_integral S).symm
  calc
    (∫ ω, S.ψ_AIPW (S.factualZ ω) ∂P.μ)
        = ∫ ω, base ω + B ω - C ω - S.θ₀ ∂P.μ := by
          exact MeasureTheory.integral_congr_ae hψ_eq
    _ = (∫ ω, base ω ∂P.μ) + (∫ ω, B ω ∂P.μ) - (∫ ω, C ω ∂P.μ) - S.θ₀ := by
      have hBmC_int : Integrable (fun ω => B ω - C ω) P.μ :=
        hB_int'.sub hC_int'
      have htmp : Integrable (fun ω => base ω + (B ω - C ω)) P.μ :=
        hbase_int.add hBmC_int
      have h_inner_int : Integrable (fun ω => base ω + B ω - C ω) P.μ := by
        refine htmp.congr (Filter.EventuallyEq.of_eq (by
          funext ω
          ring))
      have hEq_outer :
          (fun ω => base ω + B ω - C ω - S.θ₀) = (fun ω => (base ω + B ω - C ω) - S.θ₀) := by
        funext ω
        ring
      have hEq_inner :
          (fun ω => base ω + B ω - C ω) = (fun ω => base ω + (B ω - C ω)) := by
        funext ω
        ring
      have hθ_int : Integrable (fun _ : P.Ω => (S.θ₀ : ℝ)) P.μ :=
        integrable_const _
      have hθ_const : (∫ (a : P.Ω), (S.θ₀ : ℝ) ∂P.μ) = S.θ₀ := by
        haveI : IsProbabilityMeasure P.μ := inferInstance
        simp
      rw [show (fun ω => base ω + B ω - C ω - S.θ₀) =
          (fun ω => (base ω + B ω - C ω) - S.θ₀) from hEq_outer]
      rw [integral_sub h_inner_int hθ_int]
      rw [show (fun ω => base ω + B ω - C ω) = (fun ω => base ω + (B ω - C ω)) from hEq_inner]
      rw [integral_add hbase_int hBmC_int]
      rw [integral_sub hB_int' hC_int']
      rw [hθ_const]
      ring
    _ = S.θ₀ + 0 - 0 - S.θ₀ := by
      rw [hθ0, hB_zero', hC_zero']
    _ = 0 := by ring

/-- **Mean zero of `ψ_AIPW`** — `lem:est-aipw-mean-zero`.

Under the back-door assumptions, the AIPW influence function has mean zero
provided the two weighted observed residual corrections are integrable.  The
integrability gates are exactly the treated and control IPW residual terms
appearing in the score:
`e(X)⁻¹ 1{D=1}(Y - μ(1,X))` and
`(1 - e(X))⁻¹ 1{D=0}(Y - μ(0,X))`.

This is the source-level mean-zero statement: strict overlap and second moments
are sufficient ways to prove the gates, but they are not part of the headline
identity. -/
theorem aipw_mean_zero (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (hB_int : Integrable
      (fun ω => (1 / S.e_val (S.toPOBackdoorSystem.factualX ω)) *
        (S.toPOBackdoorSystem.dVar.indicator true ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val true (S.toPOBackdoorSystem.factualX ω)))) P.μ)
    (hC_int : Integrable
      (fun ω => (1 / (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) *
        (S.toPOBackdoorSystem.dVar.indicator false ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω)))) P.μ) :
    (∫ z, S.ψ_AIPW z ∂(S.P_Z)) = 0 := by
  rw [BackdoorEstimationSystem.P_Z]
  rw [MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
    (measurable_ψ_AIPW S).aestronglyMeasurable]
  exact aipw_factualZ_integral_zero S hA hB_int hC_int

/-- A stronger sufficient-condition corollary for `aipw_mean_zero`.

Strict overlap, a factual second moment, and counterfactual second moments imply
the two weighted residual integrability gates used by the source-level
mean-zero theorem. -/
theorem aipw_mean_zero_of_square_integrable (S : BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    (∫ z, S.ψ_AIPW z ∂(S.P_Z)) = 0 := by
  have hindA_true : ∀ ω, indA (S.factualZ ω) =
      S.toPOBackdoorSystem.dVar.indicator true ω := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [BackdoorEstimationSystem.factualZ, indA, projA, hD, hInd]
    · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [BackdoorEstimationSystem.factualZ, indA, projA, hD, hInd]
  have hindA_false : ∀ ω, 1 - indA (S.factualZ ω) =
      S.toPOBackdoorSystem.dVar.indicator false ω := by
    intro ω
    have hsum : S.toPOBackdoorSystem.dVar.indicator true ω +
        S.toPOBackdoorSystem.dVar.indicator false ω = 1 :=
      S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
    calc
      1 - indA (S.factualZ ω) =
          1 - S.toPOBackdoorSystem.dVar.indicator true ω := by
        rw [hindA_true ω]
      _ = S.toPOBackdoorSystem.dVar.indicator false ω := by linarith
  have hY_L2 : MemLp S.toPOBackdoorSystem.factualY 2 P.μ :=
    (memLp_two_iff_integrable_sq
      S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hμ_L2 : ∀ d : Bool, MemLp
      (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) 2 P.μ := by
    intro d
    have hYd_L2 : MemLp (S.toPOBackdoorSystem.YofD d) 2 P.μ :=
      (memLp_two_iff_integrable_sq
        (S.toPOBackdoorSystem.measurable_YofD d).aestronglyMeasurable).2 (h_yd2 d)
    have hcond_L2 :
        MemLp (P.μ[S.toPOBackdoorSystem.YofD d |
          S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
      hYd_L2.condExp
    exact hcond_L2.ae_eq (S.μ_compat hA d)
  have he_lower :
      ∀ᵐ ω ∂P.μ, ε ≤ S.e_val (S.toPOBackdoorSystem.factualX ω) := by
    filter_upwards [h_overlap.2.2, S.e_compat] with ω hprop hcomp
    simpa [hcomp] using hprop.1
  have he_upper :
      ∀ᵐ ω ∂P.μ, S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
    filter_upwards [h_overlap.2.2, S.e_compat] with ω hprop hcomp
    simpa [hcomp] using hprop.2
  have hw_true_bound :
      ∀ᵐ ω ∂P.μ,
        ‖indA (S.factualZ ω) / S.e_val (S.toPOBackdoorSystem.factualX ω)‖ ≤ ε⁻¹ := by
    filter_upwards [he_lower] with ω he
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hpos : 0 < S.e_val (S.toPOBackdoorSystem.factualX ω) :=
        S.e_pos _
      have hle : (S.e_val (S.toPOBackdoorSystem.factualX ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hpos h_overlap.1).2 he
      simpa [BackdoorEstimationSystem.factualZ, indA, projA, hD, one_div,
        Real.norm_eq_abs, abs_of_pos hpos] using hle
    · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
      simpa [BackdoorEstimationSystem.factualZ, indA, projA, hD] using hεinv_nonneg
  have hw_false_bound :
      ∀ᵐ ω ∂P.μ,
        ‖(1 - indA (S.factualZ ω)) /
          (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))‖ ≤ ε⁻¹ := by
    filter_upwards [he_upper] with ω he
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
      simpa [BackdoorEstimationSystem.factualZ, indA, projA, hD] using hεinv_nonneg
    · have hden : ε ≤ 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) := by
        linarith
      have hdenpos : 0 < 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) :=
        lt_of_lt_of_le h_overlap.1 hden
      have hle : (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hdenpos h_overlap.1).2 hden
      simpa [BackdoorEstimationSystem.factualZ, indA, projA, hD, one_div,
        Real.norm_eq_abs, abs_of_pos hdenpos] using hle
  have hw_true_Linf :
      MemLp (fun ω => indA (S.factualZ ω) /
        S.e_val (S.toPOBackdoorSystem.factualX ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ hw_true_bound
    apply Measurable.aestronglyMeasurable
    have hind : Measurable (fun ω => indA (S.factualZ ω)) := by
      simpa [indA, projA, BackdoorEstimationSystem.factualZ] using
        (Measurable.of_discrete
          (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
            S.toPOBackdoorSystem.measurable_factualD
    exact hind.div (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)
  have hw_false_Linf :
      MemLp (fun ω => (1 - indA (S.factualZ ω)) /
        (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ hw_false_bound
    apply Measurable.aestronglyMeasurable
    have hind : Measurable (fun ω => indA (S.factualZ ω)) := by
      simpa [indA, projA, BackdoorEstimationSystem.factualZ] using
        (Measurable.of_discrete
          (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
            S.toPOBackdoorSystem.measurable_factualD
    exact (measurable_const.sub hind).div
      (measurable_const.sub (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))
  have hB_L2 :
      MemLp
        (fun ω =>
          indA (S.factualZ ω) / S.e_val (S.toPOBackdoorSystem.factualX ω) *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val true (S.toPOBackdoorSystem.factualX ω))) 2 P.μ := by
    simpa using (hY_L2.sub (hμ_L2 true)).mul hw_true_Linf
  have hC_L2 :
      MemLp
        (fun ω =>
          (1 - indA (S.factualZ ω)) /
            (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω))) 2 P.μ := by
    simpa using (hY_L2.sub (hμ_L2 false)).mul hw_false_Linf
  have hB_eq :
      (fun ω => (1 / S.e_val (S.toPOBackdoorSystem.factualX ω)) *
        (S.toPOBackdoorSystem.dVar.indicator true ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val true (S.toPOBackdoorSystem.factualX ω))))
        =ᵐ[P.μ]
      (fun ω =>
        indA (S.factualZ ω) / S.e_val (S.toPOBackdoorSystem.factualX ω) *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val true (S.toPOBackdoorSystem.factualX ω))) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    calc
      (1 / S.e_val (S.toPOBackdoorSystem.factualX ω)) *
          (S.toPOBackdoorSystem.dVar.indicator true ω *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ_val true (S.toPOBackdoorSystem.factualX ω)))
          = (S.toPOBackdoorSystem.dVar.indicator true ω /
              S.e_val (S.toPOBackdoorSystem.factualX ω)) *
              (S.toPOBackdoorSystem.factualY ω -
                S.μ_val true (S.toPOBackdoorSystem.factualX ω)) := by
            ring
      _ = indA (S.factualZ ω) / S.e_val (S.toPOBackdoorSystem.factualX ω) *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ_val true (S.toPOBackdoorSystem.factualX ω)) := by
            rw [hindA_true ω]
  have hC_eq :
      (fun ω => (1 / (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) *
        (S.toPOBackdoorSystem.dVar.indicator false ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω))))
        =ᵐ[P.μ]
      (fun ω =>
        (1 - indA (S.factualZ ω)) /
          (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω))) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    calc
      (1 / (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) *
          (S.toPOBackdoorSystem.dVar.indicator false ω *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ_val false (S.toPOBackdoorSystem.factualX ω)))
          = (S.toPOBackdoorSystem.dVar.indicator false ω /
              (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) *
              (S.toPOBackdoorSystem.factualY ω -
                S.μ_val false (S.toPOBackdoorSystem.factualX ω)) := by
            ring
      _ = (1 - indA (S.factualZ ω)) /
          (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ_val false (S.toPOBackdoorSystem.factualX ω)) := by
            rw [hindA_false ω]
  exact aipw_mean_zero S hA
    ((hB_L2.integrable (by norm_num)).congr hB_eq.symm)
    ((hC_L2.integrable (by norm_num)).congr hC_eq.symm)

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean
