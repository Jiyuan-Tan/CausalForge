/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The role of the propensity score (Hahn): AIPW orthogonality to propensity scores

This file proves that the AIPW score `ψ_AIPW` is orthogonal, in
`L²(P_Z)`, to every *propensity-score direction*

    s_e(z) = α(projX z) · (indA z − e_val (projX z)),

where `α : γ → ℝ` is the score of a perturbation of the propensity model `D | X`
(a mean-zero-given-X function of `(D, X)`).  This is the formal statement of
Hahn's observation that propensity-score nuisance directions are killed by the
AIPW score.  The later efficiency statements use an abstract mean-zero tangent
space and an explicitly supplied smaller tangent space; this file does not
construct the known-propensity tangent space.

## Proof

Push the `P_Z`-integral to `Ω` via `P_Z = μ.map factualZ`.  Writing
`ψ_AIPW = A + B − C` with

* `A = μ₁ − μ₀ − θ₀`               (a function of `X` only),
* `B = (a / e(X)) (Y − μ₁)`,
* `C = ((1−a) / (1−e(X))) (Y − μ₀)`,

and `s_e = α(X) (a − e(X))` (`a = 1_{D=true}`), one shows term by term:

* **A·s_e**: `∫ α(X) A(X) (a − e(X)) dμ = 0`, because
  `E[a − e(X) | σ(X)] = 0` a.s. (the σ(X)-conditional expectation of the
  indicator is `e_val(X)`), and `α(X) A(X)` is σ(X)-measurable.  This is
  `propensity_score_residual_integral_zero` below.
* **B·s_e**: `a (a − e) = a (1 − e)` (since `a² = a`), so
  `B·s_e = α(X)·(1−e)/e · a · (Y − μ₁)`, which integrates to zero by
  `weighted_residual_integral_zero` with `d = true`.
* **C·s_e**: `(1−a)(a − e) = −(1−a) e` (since `(1−a) a = 0`), so
  `C·s_e = −α(X)·e/(1−e) · (1−a) · (Y − μ₀)`, which integrates to zero by
  `weighted_residual_integral_zero` with `d = false`.

Sum = 0.
-/

import Causalean.Estimation.ATE.InfluenceFunction
import Causalean.Estimation.Efficiency.TangentProjection
import Causalean.Estimation.Efficiency.ATEVariance
import Causalean.Panel.FWLInstanceL2

/-!
# ATE tangent-space efficiency identities

This module proves that the augmented inverse-probability weighted score is
orthogonal to propensity-score nuisance directions and records its projection
properties in the Hilbert space `Lp ℝ 2 S.P_Z`. The theorem
`BackdoorEstimationSystem.aipw_orthogonal_propensity_score` formalizes Hahn's
propensity-score orthogonality calculation.

The second half builds the full mean-zero tangent space `Tfull`, represents the
AIPW score as `aipwLp`, proves `aipwLp_mem_tangent`, and derives the projection
and variance identities `effBound_eq_variance`, `effBound_eq_hahn`, and
`efficiency_bound_optimal`. The final tangent-shrinking theorem states the
abstract known-propensity corollary for any supplied smaller tangent space that
still contains the AIPW score. The pathwise-gradient/canonical-gradient bridge
is developed in `ATEEfficientIF.lean`.
-/

namespace Causalean
namespace Estimation
namespace Efficiency

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

open Causalean.Estimation.ATE
open Causalean.Estimation.ATE.BackdoorEstimationSystem

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- Any covariate-measurable multiplier has zero integral against the propensity-score residual.

This is the propensity-score analogue of the weighted outcome-residual mean-zero identity. -/
lemma propensity_score_residual_integral_zero
    (S : ATE.BackdoorEstimationSystem P γ)
    (h : γ → ℝ) (hh_meas : Measurable h)
    (h_int : Integrable
      (fun ω => h (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator true ω -
          S.e_val (S.toPOBackdoorSystem.factualX ω))) P.μ) :
    ∫ ω, h (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator true ω -
          S.e_val (S.toPOBackdoorSystem.factualX ω)) ∂P.μ = 0 := by
  -- `h(X)` is σ(X)-measurable.
  have hh_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => h (S.toPOBackdoorSystem.factualX ω)) := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => h (S.toPOBackdoorSystem.factualX ω))
    exact (hh_meas.comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  -- Integrability of the residual `a − e(X)`.
  have hind_int : Integrable (S.toPOBackdoorSystem.dVar.indicator true) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_indicator true
  have he_int : Integrable
      (fun ω => S.e_val (S.toPOBackdoorSystem.factualX ω)) P.μ := by
    -- `e_val(X)` is bounded (it equals `propScore true` a.e., which is in [0,1]),
    -- but here we only need integrability; it is the a.e.-limit of a bounded
    -- conditional expectation.  We get it directly from `e_compat`.
    have hps_int : Integrable (S.toPOBackdoorSystem.propScore true) P.μ := by
      unfold POBackdoorSystem.propScore
      exact integrable_condExp
    exact hps_int.congr S.e_compat
  have hresid_int : Integrable
      (fun ω => S.toPOBackdoorSystem.dVar.indicator true ω -
        S.e_val (S.toPOBackdoorSystem.factualX ω)) P.μ := hind_int.sub he_int
  -- `E[a − e(X) | σ(X)] = 0` a.s.
  have hresid_ce_zero :
      P.μ[fun ω => S.toPOBackdoorSystem.dVar.indicator true ω -
          S.e_val (S.toPOBackdoorSystem.factualX ω) |
          S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    have he_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
        (fun ω => S.e_val (S.toPOBackdoorSystem.factualX ω)) := by
      change StronglyMeasurable[
        MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
        (fun ω => S.e_val (S.toPOBackdoorSystem.factualX ω))
      exact (S.e_meas.comp
        (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
    -- `E[a | σ(X)] = propScore true =ᵐ e_val(X)`.
    have hce_ind :
        P.μ[S.toPOBackdoorSystem.dVar.indicator true | S.toPOBackdoorSystem.sigmaX]
          =ᵐ[P.μ] (fun ω => S.e_val (S.toPOBackdoorSystem.factualX ω)) := by
      have h1 :
          P.μ[S.toPOBackdoorSystem.dVar.indicator true |
              S.toPOBackdoorSystem.sigmaX]
            =ᵐ[P.μ] S.toPOBackdoorSystem.propScore true := by
        unfold POBackdoorSystem.propScore
        exact EventuallyEq.rfl
      exact h1.trans S.e_compat
    -- `E[e(X) | σ(X)] = e(X)` since `e(X)` is σ(X)-measurable.
    have hce_e :
        P.μ[fun ω => S.e_val (S.toPOBackdoorSystem.factualX ω) |
            S.toPOBackdoorSystem.sigmaX]
          =ᵐ[P.μ] (fun ω => S.e_val (S.toPOBackdoorSystem.factualX ω)) :=
      Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable S.toPOBackdoorSystem.sigmaX_le he_sm he_int)
    have hsub :
        P.μ[fun ω => S.toPOBackdoorSystem.dVar.indicator true ω -
            S.e_val (S.toPOBackdoorSystem.factualX ω) |
            S.toPOBackdoorSystem.sigmaX]
          =ᵐ[P.μ]
            P.μ[S.toPOBackdoorSystem.dVar.indicator true |
              S.toPOBackdoorSystem.sigmaX]
            - P.μ[fun ω => S.e_val (S.toPOBackdoorSystem.factualX ω) |
              S.toPOBackdoorSystem.sigmaX] :=
      condExp_sub hind_int he_int S.toPOBackdoorSystem.sigmaX
    filter_upwards [hsub, hce_ind, hce_e] with ω hsubω hindω heω
    rw [hsubω, Pi.sub_apply, hindω, heω, sub_self]
  -- Pull `h(X)` out of the conditional expectation, then use the residual = 0.
  have hcondexp_pull :=
    condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hh_sm h_int hresid_int
  have hhresid_ce_zero :
      P.μ[fun ω => h (S.toPOBackdoorSystem.factualX ω) *
            (S.toPOBackdoorSystem.dVar.indicator true ω -
              S.e_val (S.toPOBackdoorSystem.factualX ω)) |
            S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    refine hcondexp_pull.trans ?_
    filter_upwards [hresid_ce_zero] with ω hω
    have : ((fun ω' => h (S.toPOBackdoorSystem.factualX ω')) *
        P.μ[fun ω' => S.toPOBackdoorSystem.dVar.indicator true ω' -
            S.e_val (S.toPOBackdoorSystem.factualX ω') |
            S.toPOBackdoorSystem.sigmaX]) ω = 0 := by
      rw [Pi.mul_apply, hω, mul_zero]
    exact this
  calc
    ∫ ω, h (S.toPOBackdoorSystem.factualX ω) *
          (S.toPOBackdoorSystem.dVar.indicator true ω -
            S.e_val (S.toPOBackdoorSystem.factualX ω)) ∂P.μ
      = ∫ ω, P.μ[fun ω => h (S.toPOBackdoorSystem.factualX ω) *
            (S.toPOBackdoorSystem.dVar.indicator true ω -
              S.e_val (S.toPOBackdoorSystem.factualX ω)) |
            S.toPOBackdoorSystem.sigmaX] ω ∂P.μ := by
        rw [MeasureTheory.integral_condExp S.toPOBackdoorSystem.sigmaX_le]
    _ = ∫ _, (0 : ℝ) ∂P.μ :=
          MeasureTheory.integral_congr_ae hhresid_ce_zero
    _ = 0 := MeasureTheory.integral_zero _ _

/-! ## Headline theorem: orthogonality to propensity-score directions -/

set_option maxHeartbeats 1000000 in
-- The proof assembles the pointwise `ψ·s_e` decomposition (two `a ∈ {0,1}`
-- field-arithmetic branches), three integrability facts, and three integral
-- vanishings in a single term, exceeding the default heartbeat budget.
/-- **The role of the propensity score (Hahn).**

The AIPW influence function `ψ_AIPW` is orthogonal in `L²(P_Z)` to every
propensity-score direction `s_e(z) = α(projX z) · (indA z − e_val (projX z))`:

    ∫ z, ψ_AIPW(z) · α(projX z) · (indA z − e_val (projX z)) ∂P_Z = 0.

Such directions are the scores of perturbations of the propensity model `D | X`.
The identity says that knowledge of the propensity score lies in the orthogonal
complement of the AIPW influence function, i.e. it does not lower the
semiparametric efficiency bound for the ATE. -/
theorem aipw_orthogonal_propensity_score
    (S : ATE.BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    {ε : ℝ} (h_overlap : S.StrictOverlap ε)
    (α : γ → ℝ) (hα_meas : Measurable α)
    -- `α(X)·(a − e(X))` is integrable (e.g. `α` bounded, or `α(X) ∈ L²`).
    (h_sA_int : Integrable
      (fun ω => ((S.μ_val true (S.toPOBackdoorSystem.factualX ω) -
          S.μ_val false (S.toPOBackdoorSystem.factualX ω) - S.θ₀) *
          α (S.toPOBackdoorSystem.factualX ω)) *
        (S.toPOBackdoorSystem.dVar.indicator true ω -
          S.e_val (S.toPOBackdoorSystem.factualX ω))) P.μ)
    (h_sB_int : Integrable
      (fun ω => (fun x => α x * (1 - S.e_val x) / S.e_val x)
          (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator true ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val true (S.toPOBackdoorSystem.factualX ω)))) P.μ)
    (h_sC_int : Integrable
      (fun ω => (fun x => α x * S.e_val x / (1 - S.e_val x))
          (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator false ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω)))) P.μ) :
    ∫ z, S.ψ_AIPW z *
        (α (projX z) * (indA z - S.e_val (projX z))) ∂S.P_Z = 0 := by
  classical
  -- `h_overlap` records the overlap setting in which the propensity directions
  -- (and the bounded inverse-propensity weights) are well-defined.
  have _hε_pos : 0 < ε := h_overlap.1
  -- Push the integral to `Ω`.
  have hmeas_integrand : Measurable
      (fun z : γ × Bool × ℝ =>
        S.ψ_AIPW z * (α (projX z) * (indA z - S.e_val (projX z)))) := by
    have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
    have hψ : Measurable S.ψ_AIPW := S.measurable_ψ_AIPW
    have hα' : Measurable (fun z : γ × Bool × ℝ => α (projX z)) :=
      hα_meas.comp hx
    have hind : Measurable (fun z : γ × Bool × ℝ => indA z) := by
      unfold indA projA
      exact (Measurable.of_discrete
        (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
          measurable_snd.fst
    have he : Measurable (fun z : γ × Bool × ℝ => S.e_val (projX z)) :=
      S.e_meas.comp hx
    exact hψ.mul (hα'.mul (hind.sub he))
  rw [BackdoorEstimationSystem.P_Z,
    MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
      hmeas_integrand.aestronglyMeasurable]
  -- Ω-level abbreviations.
  set X : P.Ω → γ := S.toPOBackdoorSystem.factualX with hX
  set Y : P.Ω → ℝ := S.toPOBackdoorSystem.factualY with hY
  set a : P.Ω → ℝ := fun ω => indA (S.factualZ ω) with ha
  set e : P.Ω → ℝ := fun ω => S.e_val (S.toPOBackdoorSystem.factualX ω) with he
  set μ1 : P.Ω → ℝ := fun ω => S.μ_val true (S.toPOBackdoorSystem.factualX ω)
    with hμ1
  set μ0 : P.Ω → ℝ := fun ω => S.μ_val false (S.toPOBackdoorSystem.factualX ω)
    with hμ0
  set Afn : P.Ω → ℝ := fun ω => μ1 ω - μ0 ω - S.θ₀ with hAfn
  set Bfn : P.Ω → ℝ := fun ω => (a ω / e ω) * (Y ω - μ1 ω) with hBfn
  set Cfn : P.Ω → ℝ := fun ω => ((1 - a ω) / (1 - e ω)) * (Y ω - μ0 ω) with hCfn
  -- `a ω ∈ {0, 1}` and the indicator identities.
  have ha01 : ∀ ω, a ω = 0 ∨ a ω = 1 := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · right; simp [ha, indA, projA, ATE.BackdoorEstimationSystem.factualZ, hD]
    · left; simp [ha, indA, projA, ATE.BackdoorEstimationSystem.factualZ, hD]
  have ha_ind : ∀ ω, a ω = S.toPOBackdoorSystem.dVar.indicator true ω := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [ha, indA, projA, ATE.BackdoorEstimationSystem.factualZ, hD, hInd]
    · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [ha, indA, projA, ATE.BackdoorEstimationSystem.factualZ, hD, hInd]
  have hna_ind : ∀ ω, 1 - a ω = S.toPOBackdoorSystem.dVar.indicator false ω := by
    intro ω
    have hsum : S.toPOBackdoorSystem.dVar.indicator true ω +
        S.toPOBackdoorSystem.dVar.indicator false ω = 1 :=
      S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
    rw [ha_ind ω]; linarith
  -- Strict positivity of the propensity weights (from overlap).
  have he_pos : ∀ ω, 0 < e ω := fun ω => S.e_pos _
  have he_lt_one : ∀ ω, e ω < 1 := fun ω => S.e_lt_one _
  -- Pointwise: `ψ_AIPW(factualZ ω) · s_e(factualZ ω)`
  --   = Afn·α(X)·(a−e) + sB-residual + sC-residual,
  -- where the sB / sC residuals match `weighted_residual_integral_zero`.
  set sA : P.Ω → ℝ := fun ω =>
    (Afn ω * α (X ω)) *
      (S.toPOBackdoorSystem.dVar.indicator true ω - e ω) with hsA
  set sB : P.Ω → ℝ := fun ω =>
    (fun x => α x * (1 - S.e_val x) / S.e_val x) (X ω) *
      (S.toPOBackdoorSystem.dVar.indicator true ω * (Y ω - μ1 ω)) with hsB
  set sC : P.Ω → ℝ := fun ω =>
    (fun x => α x * S.e_val x / (1 - S.e_val x)) (X ω) *
      (S.toPOBackdoorSystem.dVar.indicator false ω * (Y ω - μ0 ω)) with hsC
  have hpt : ∀ ω,
      S.ψ_AIPW (S.factualZ ω) *
          (α (projX (S.factualZ ω)) *
            (indA (S.factualZ ω) - S.e_val (projX (S.factualZ ω))))
        = sA ω + sB ω + sC ω := by
    intro ω
    -- `ψ_AIPW(factualZ ω) = Afn ω + Bfn ω − Cfn ω`.
    have hexpand :
        S.ψ_AIPW (S.factualZ ω) = Afn ω + Bfn ω - Cfn ω := by
      unfold ATE.BackdoorEstimationSystem.ψ_AIPW ATE.BackdoorEstimationSystem.aipwMoment
      simp only [ATE.BackdoorEstimationSystem.factualZ, projX, projY,
        hBfn, hCfn, ha, he, hμ1, hμ0, hY]
      ring
    -- The propensity-direction factor at `factualZ ω`.
    have hfac : α (projX (S.factualZ ω)) *
          (indA (S.factualZ ω) - S.e_val (projX (S.factualZ ω)))
        = α (X ω) * (a ω - e ω) := by
      simp only [ATE.BackdoorEstimationSystem.factualZ, projX, ha, he, hX]
    rw [hexpand, hfac]
    -- Now expand using `a ∈ {0,1}` to collapse the products.
    have haind := ha_ind ω
    have hnaind := hna_ind ω
    have hepos := (he_pos ω).ne'
    have hediff : (1 - e ω) ≠ 0 := by
      have := he_lt_one ω; linarith
    simp only [hsA, hsB, hsC, hAfn, hBfn, hCfn, hμ1, hμ0, hY, he, hX]
    rcases ha01 ω with h0 | h1
    · -- `a ω = 0`: then `1_{D=true} = 0`, `1_{D=false} = 1`.
      have hi_t : S.toPOBackdoorSystem.dVar.indicator true ω = 0 := by
        rw [← haind, h0]
      have hi_f : S.toPOBackdoorSystem.dVar.indicator false ω = 1 := by
        rw [← hnaind, h0]; ring
      rw [hi_t, hi_f, h0]
      field_simp
      ring
    · -- `a ω = 1`: then `1_{D=true} = 1`, `1_{D=false} = 0`.
      have hi_t : S.toPOBackdoorSystem.dVar.indicator true ω = 1 := by
        rw [← haind, h1]
      have hi_f : S.toPOBackdoorSystem.dVar.indicator false ω = 0 := by
        rw [← hnaind, h1]; ring
      rw [hi_t, hi_f, h1]
      simp only [zero_mul, mul_zero, one_mul]
      field_simp
      ring
  -- Rewrite the integral via the pointwise identity.
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  -- Integrability of the three pieces (from the threaded hypotheses).
  have hsA_int : Integrable sA P.μ := by
    refine h_sA_int.congr (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [hsA, hAfn, hμ1, hμ0, hX]
  have hsB_int : Integrable sB P.μ := h_sB_int
  have hsC_int : Integrable sC P.μ := h_sC_int
  -- Split the integral.
  rw [MeasureTheory.integral_add (f := fun ω => sA ω + sB ω) (g := sC)
      (hsA_int.add hsB_int) hsC_int,
    MeasureTheory.integral_add (f := sA) (g := sB) hsA_int hsB_int]
  -- The three integrals each vanish.
  have hA_zero : ∫ ω, sA ω ∂P.μ = 0 := by
    have hh_meas : Measurable
        (fun x => (S.μ_val true x - S.μ_val false x - S.θ₀) * α x) :=
      (((S.μ_meas true).sub (S.μ_meas false)).sub measurable_const).mul hα_meas
    have hsA_eq : ∀ ω, sA ω =
        (fun x => (S.μ_val true x - S.μ_val false x - S.θ₀) * α x) (X ω) *
          (S.toPOBackdoorSystem.dVar.indicator true ω -
            S.e_val (S.toPOBackdoorSystem.factualX ω)) := by
      intro ω
      simp only [hsA, hAfn, hμ1, hμ0, he, hX]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsA_eq)]
    refine propensity_score_residual_integral_zero S _ hh_meas ?_
    refine (h_sA_int.congr (Filter.Eventually.of_forall (fun ω => ?_)))
    simp only []
    ring
  have hB_zero : ∫ ω, sB ω ∂P.μ = 0 := by
    have hg_meas : Measurable (fun x => α x * (1 - S.e_val x) / S.e_val x) :=
      (hα_meas.mul (measurable_const.sub S.e_meas)).div S.e_meas
    exact S.weighted_residual_integral_zero hA true
      (fun x => α x * (1 - S.e_val x) / S.e_val x) hg_meas hsB_int
      (S.cond_exp_residual_zero hA true)
  have hC_zero : ∫ ω, sC ω ∂P.μ = 0 := by
    have hg_meas : Measurable (fun x => α x * S.e_val x / (1 - S.e_val x)) :=
      (hα_meas.mul S.e_meas).div (measurable_const.sub S.e_meas)
    exact S.weighted_residual_integral_zero hA false
      (fun x => α x * S.e_val x / (1 - S.e_val x)) hg_meas hsC_int
      (S.cond_exp_residual_zero hA false)
  rw [hA_zero, hB_zero, hC_zero]
  ring

end BackdoorEstimationSystem

end Efficiency

namespace ATE.BackdoorEstimationSystem

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO
open Causalean.Estimation.Efficiency

/-! ## AIPW projection and squared-norm bounds in `L²(P_Z)`

We now assemble the abstract Hilbert-projection machine of
`TangentProjection.lean` on the genuine Hilbert space `H := Lp ℝ 2 S.P_Z`,
with `S.ψ_AIPW` as the reference score and the **mean-zero
tangent space** `Tfull S := (ℝ ∙ 1)ᗮ` (the orthogonal complement of the
constants).  The headline results are:

* `aipw_score_meanZero_projection_eq` — the AIPW score is unchanged by projection onto the
  mean-zero tangent space;
* `effBound_eq_hahn` — the efficiency bound equals Hahn's `V_H`;
* `efficiency_bound_optimal` — every abstract gradient has squared
  square-integrable norm at least the projected squared norm;
* `effBound_eq_of_smaller_tangent_containing_aipw` — any supplied smaller tangent space that
  contains the AIPW score has the same abstract bound.
-/

open scoped InnerProductSpace RealInnerProductSpace

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- The observed data law of a backdoor estimation system is a probability measure. -/
instance instIsProbabilityMeasure_P_Z (S : ATE.BackdoorEstimationSystem P γ) :
    IsProbabilityMeasure S.P_Z := by
  rw [ATE.BackdoorEstimationSystem.P_Z]
  haveI : IsProbabilityMeasure P.μ := P.isProb
  exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable

/-- The AIPW influence function is square-integrable under the observed data law. -/
theorem aipw_memLp (S : ATE.BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    MemLp S.ψ_AIPW 2 S.P_Z :=
  (memLp_two_iff_integrable_sq S.measurable_ψ_AIPW.aestronglyMeasurable).2
    (S.aipw_finite_var_of_counterfactual_sq h_overlap hA h_y2 h_yd2)

/-- This is the AIPW influence function represented as a point of the square-integrable Hilbert space. -/
noncomputable def aipwLp (S : ATE.BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    Lp ℝ 2 S.P_Z :=
  (S.aipw_memLp h_overlap hA h_y2 h_yd2).toLp _

/-- This is the constant-one function represented in the square-integrable Hilbert space. -/
noncomputable def oneLp (S : ATE.BackdoorEstimationSystem P γ) :
    Lp ℝ 2 S.P_Z :=
  (memLp_const (1 : ℝ)).toLp _

/-- This is the mean-zero tangent space for the backdoor average treatment effect.

It is the orthogonal complement of the constant functions in the square-integrable Hilbert space. -/
noncomputable def Tfull (S : ATE.BackdoorEstimationSystem P γ) :
    Submodule ℝ (Lp ℝ 2 S.P_Z) :=
  (ℝ ∙ S.oneLp)ᗮ

/-- The span of the constant-one function has an orthogonal projection. -/
instance instHasOrthogonalProjection_span_oneLp
    (S : ATE.BackdoorEstimationSystem P γ) :
    (ℝ ∙ S.oneLp).HasOrthogonalProjection := by
  have : FiniteDimensional ℝ (ℝ ∙ S.oneLp) := inferInstance
  exact inferInstance

/-- The mean-zero tangent space has an orthogonal projection. -/
instance instHasOrthogonalProjection_Tfull
    (S : ATE.BackdoorEstimationSystem P γ) :
    (S.Tfull).HasOrthogonalProjection := by
  rw [Tfull]
  exact Submodule.instHasOrthogonalProjectionOrthogonal (ℝ ∙ S.oneLp)

/-- Inner product against the constant-one function equals integration under the observed data law. -/
theorem inner_oneLp (S : ATE.BackdoorEstimationSystem P γ) (f : Lp ℝ 2 S.P_Z) :
    ⟪f, S.oneLp⟫_ℝ = ∫ z, f z ∂S.P_Z := by
  rw [Causalean.Panel.FWLInstanceL2.inner_eq_integral]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [(memLp_const (1 : ℝ)).coeFn_toLp (p := 2) (μ := S.P_Z)]
    with z hz
  rw [show S.oneLp z = (1 : ℝ) from hz, mul_one]

/-- The AIPW influence function lies in the mean-zero tangent space.

This is the geometric form of the AIPW mean-zero theorem. -/
theorem aipwLp_mem_tangent (S : ATE.BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    S.aipwLp h_overlap hA h_y2 h_yd2 ∈ S.Tfull := by
  rw [Tfull, Submodule.mem_orthogonal_singleton_iff_inner_left,
    S.inner_oneLp]
  have hae : (S.aipwLp h_overlap hA h_y2 h_yd2 : γ × Bool × ℝ → ℝ)
      =ᵐ[S.P_Z] S.ψ_AIPW :=
    (S.aipw_memLp h_overlap hA h_y2 h_yd2).coeFn_toLp
  rw [MeasureTheory.integral_congr_ae hae]
  exact S.aipw_mean_zero_of_square_integrable h_overlap hA h_y2 h_yd2

/-! ### Projection and bound theorems -/

/-- The square-integrable AIPW score is already mean-zero, so projecting it onto
the full mean-zero tangent space leaves it unchanged.

This is the projection identity used by the variance-bound results in this
module. The stronger pathwise-gradient statement is recorded separately in
`ATEEfficientIF.lean`, where the pathwise derivative is supplied as an explicit
Hahn identity. -/
theorem aipw_score_meanZero_projection_eq (S : ATE.BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    efficientIF S.Tfull (S.aipwLp h_overlap hA h_y2 h_yd2)
      = S.aipwLp h_overlap hA h_y2 h_yd2 :=
  efficientIF_eq_self_of_mem S.Tfull
    (S.aipwLp_mem_tangent h_overlap hA h_y2 h_yd2)

/-- The semiparametric efficiency bound equals the variance of the AIPW influence function. -/
theorem effBound_eq_variance (S : ATE.BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    effBound S.Tfull (S.aipwLp h_overlap hA h_y2 h_yd2)
      = ∫ z, (S.ψ_AIPW z) ^ 2 ∂S.P_Z := by
  rw [effBound, S.aipw_score_meanZero_projection_eq h_overlap hA h_y2 h_yd2,
    ← real_inner_self_eq_norm_sq,
    Causalean.Panel.FWLInstanceL2.inner_eq_integral]
  refine MeasureTheory.integral_congr_ae ?_
  have hae : (S.aipwLp h_overlap hA h_y2 h_yd2 : γ × Bool × ℝ → ℝ)
      =ᵐ[S.P_Z] S.ψ_AIPW :=
    (S.aipw_memLp h_overlap hA h_y2 h_yd2).coeFn_toLp
  filter_upwards [hae] with z hz
  rw [hz, sq]

/-- The semiparametric efficiency bound equals Hahn's three-term variance formula.

Chaining the variance identity with the AIPW variance decomposition gives

    V_H = ∫ (μ₁ − μ₀ − θ₀)² dP_X
          + ∫ (a / e²)   (y − μ₁)² dP_Z
          + ∫ ((1−a) / (1−e)²) (y − μ₀)² dP_Z. -/
theorem effBound_eq_hahn (S : ATE.BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    effBound S.Tfull (S.aipwLp h_overlap hA h_y2 h_yd2)
      = (∫ x, (S.μ_val true x - S.μ_val false x - S.θ₀) ^ 2 ∂S.P_X)
        + (∫ z, (indA z / (S.e_val (projX z)) ^ 2) *
            (projY z - S.μ_val true (projX z)) ^ 2 ∂S.P_Z)
        + (∫ z, ((1 - indA z) / (1 - S.e_val (projX z)) ^ 2) *
            (projY z - S.μ_val false (projX z)) ^ 2 ∂S.P_Z) := by
  rw [S.effBound_eq_variance h_overlap hA h_y2 h_yd2,
    S.aipw_variance_hahn_decomposition h_overlap hA h_y2 h_yd2]

/-- Every gradient for the backdoor ATE has squared `L²` norm at least the efficiency bound.

The formal conclusion is the abstract squared-norm inequality for any
`IsGradient` element. It does not by itself identify gradients with mean-zero
influence functions or convert the squared `L²` norm into a variance statement. -/
theorem efficiency_bound_optimal (S : ATE.BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (ψ : Lp ℝ 2 S.P_Z)
    (hψ : IsGradient S.Tfull (S.aipwLp h_overlap hA h_y2 h_yd2) ψ) :
    effBound S.Tfull (S.aipwLp h_overlap hA h_y2 h_yd2) ≤ ‖ψ‖ ^ 2 :=
  effBound_le_normSq hψ

/-! ### Role of the propensity score (propensity-invariance of the bound) -/

/-- For any supplied smaller tangent space that is contained in the mean-zero tangent space and
still contains the AIPW score, the abstract squared-norm efficiency bound is unchanged.

This is only a tangent-shrinking corollary: it assumes the smaller space and AIPW membership rather
than constructing Hahn's known-propensity tangent space. -/
-- TODO(faithfulness): Hahn/standard semiparametric efficiency theory — define the
-- known-propensity tangent space and derive AIPW membership from propensity-score
-- orthogonality, instead of assuming an arbitrary smaller tangent space containing AIPW.
theorem effBound_eq_of_smaller_tangent_containing_aipw (S : ATE.BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (T' : Submodule ℝ (Lp ℝ 2 S.P_Z)) [T'.HasOrthogonalProjection]
    (hle : T' ≤ S.Tfull)
    (hmem : S.aipwLp h_overlap hA h_y2 h_yd2 ∈ T') :
    effBound T' (S.aipwLp h_overlap hA h_y2 h_yd2)
      = effBound S.Tfull (S.aipwLp h_overlap hA h_y2 h_yd2) :=
  (effBound_eq_of_mem_sub S.Tfull T' hle hmem).2.2

end ATE.BackdoorEstimationSystem

end Estimation
end Causalean
