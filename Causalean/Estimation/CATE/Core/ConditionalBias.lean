/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conditional bias of the DR pseudo-outcome — `prop:est-cate-dr-bias-identity`

The σ(X)-conditional bias identity (Kennedy / DR-learner Proposition 2):

    μ[ φ_η(Z) − φ_0(Z) | σ(X) ]
      =ᵐ  ∑_{a ∈ {true, false}}
            ((η.e_fn − η₀.e_fn) (η.μ_fn a − η₀.μ_fn a) /
              (a · η.e_fn + (1 − a) · (1 − η.e_fn)))(X)

equivalently in value space (`P_X`-a.e.) — the closed-form cross-product
remainder driving the double-robustness corollary
`rem:est-cate-double-robust`.

This file provides:
* `condBias η η₀ x`                — the closed-form value-space bias.
* `measurable_condBias`            — measurability of `condBias`.
* `cond_exp_residual_at_h`         — generalized residual-conditional-expectation
                                     helper (parameterised over an arbitrary
                                     measurable `h : γ → ℝ`).
* `phi_eta_minus_phi₀_cond_exp`    — the σ(X)-conditional bias identity (Ω-form).
* `phi_eta_minus_phi₀_at_x`        — lightweight value-space bridge used by
                                     downstream packaging.
* `condBias_zero_of_propensity_match` — DR corollary (correct propensity).
* `condBias_zero_of_outcome_match`     — DR corollary (correct outcomes).
* `cond_exp_phi_eta_dir_deriv_at_truth_zero` — differentiated orthogonality
                                     statement at the truth.
-/

import Causalean.Estimation.CATE.Core.PseudoOutcome
import Causalean.Estimation.CATE.Core.PhiEtaDeriv
import Causalean.Estimation.ATE.Score.MeanZero
import Causalean.Estimation.ATE.Score.ScorePullout

/-!
Derives closed-form conditional-bias and orthogonality formulas for CATE doubly
robust pseudo-outcomes. The value-space function `condBias` records the
cross-product remainder, with `measurable_condBias` providing measurability.

The main theorem `phi_eta_minus_phi₀_cond_exp` identifies the σ(X)-conditional
mean of `phi_eta - phi₀` with `condBias`, and `phi_eta_minus_phi₀_at_x` transports
that identity to the covariate law through the regular conditional
distribution. The double-robustness corollaries
`condBias_zero_of_propensity_match` and `condBias_zero_of_outcome_match` show the
remainder vanishes when either nuisance block is correct. The final theorem
`cond_exp_phi_eta_dir_deriv_at_truth_zero` proves the corresponding conditional
mean-zero statement for the directional derivative at the truth.
-/

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory ProbabilityTheory Filter Topology
  Causalean.PO Causalean.Estimation.ATE

variable {γ : Type*} [MeasurableSpace γ]

/-! ## Closed-form value-space bias -/

/-- The closed-form σ(X)-conditional bias of the DR pseudo-outcome
contrast `φ_η − φ_0`, summed over the two treatment arms:

    condBias η η₀ x
      := ∑_{a ∈ Bool}
           ((η.e_fn x − η₀.e_fn x) (η.μ_fn a x − η₀.μ_fn a x))
             / (if a then η.e_fn x else 1 − η.e_fn x).

The denominator `if a then η.e_fn x else 1 − η.e_fn x` is the LaTeX
`a·π̂(x) + (1−a)·(1−π̂(x))` with `a : Bool`.

Mirrors the right-hand side of `prop:est-cate-dr-bias-identity` in
`doc/basic_concepts/po/estimation/dr_learner_cate.tex`. -/
noncomputable def condBias (η η₀ : NuisanceVec γ) (x : γ) : ℝ :=
  ∑ a : Bool, ((η.e_fn x - η₀.e_fn x) * (η.μ_fn a x - η₀.μ_fn a x)) /
    (if a then η.e_fn x else 1 - η.e_fn x)

/-- `condBias η η₀` is measurable in `x`.

Proof outline: a finite sum over `Bool` of products / quotients of
measurable functions; build it from `η.e_meas`, `η₀.e_meas`,
`η.μ_meas`, `η₀.μ_meas` via `Finset.measurable_sum`,
`Measurable.div`, `Measurable.mul`, `Measurable.sub`. -/
lemma measurable_condBias (η η₀ : NuisanceVec γ) :
    Measurable (fun x : γ => condBias η η₀ x) := by
  unfold condBias
  refine Finset.measurable_sum _ ?_
  intro a _
  cases a
  · have h_num : Measurable (fun x : γ =>
        (η.e_fn x - η₀.e_fn x) * (η.μ_fn false x - η₀.μ_fn false x)) :=
      (η.e_meas.sub η₀.e_meas).mul
        ((η.μ_meas false).sub (η₀.μ_meas false))
    have h_den : Measurable (fun x : γ => 1 - η.e_fn x) :=
      measurable_const.sub η.e_meas
    simpa using h_num.div h_den
  · have h_num : Measurable (fun x : γ =>
        (η.e_fn x - η₀.e_fn x) * (η.μ_fn true x - η₀.μ_fn true x)) :=
      (η.e_meas.sub η₀.e_meas).mul
        ((η.μ_meas true).sub (η₀.μ_meas true))
    simpa using h_num.div η.e_meas

/-! ## Generalized residual-conditional-expectation helper -/

/-- Generalized form of `cond_exp_residual_zero`
(`Estimation/ATE/MeanZero.lean` lines 109–196).  The original lemma fixes
`h := S.μ_val d` and concludes the residual conditional expectation is
zero; this version allows an arbitrary measurable `h : γ → ℝ` and
exposes the residual

    μ[ 1{D=d}·(Y − h(X)) | σ(X) ]
      =ᵐ  propScore d · (μ_val d (factualX ·) − h (factualX ·)).

Proof outline: decompose
`1{D=d}·(Y − h(X)) = 1{D=d}·Y − 1{D=d}·h(X)`.
The first term has conditional expectation
`propScore d · μ_val d (factualX)` (mirror MeanZero.lean lines 159–169
via `S.toPOBackdoorSystem.cate_backdoor`).  The second pulls
`h(factualX)` out of the conditional expectation as it is
σ(X)-measurable (mirror MeanZero.lean lines 179–188 via
`MeasureTheory.condExp_mul_of_stronglyMeasurable_left`), giving
`propScore d · h(factualX)`.  Subtract. -/
private lemma cond_exp_residual_at_h
    {P : POSystem} [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) (d : Bool)
    (h : γ → ℝ) (hh_meas : Measurable h)
    (hh_int : Integrable
      (fun ω => h (S.toPOBackdoorSystem.factualX ω) *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ) :
    P.μ[fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
           (S.toPOBackdoorSystem.factualY ω -
             h (S.toPOBackdoorSystem.factualX ω))
        | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ]
        (fun ω =>
          S.toPOBackdoorSystem.propScore d ω *
            (S.μ_val d (S.toPOBackdoorSystem.factualX ω) -
             h (S.toPOBackdoorSystem.factualX ω))) := by
  have hYind_int : Integrable
      (fun ω => S.toPOBackdoorSystem.factualY ω *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_mul_indicator d hA.integrable_factualY
      S.toPOBackdoorSystem.measurable_factualY
  have hres_eq :
      (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
          (S.toPOBackdoorSystem.factualY ω -
            h (S.toPOBackdoorSystem.factualX ω)))
        = (fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator d ω -
          h (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω) := by
    funext ω
    ring
  have hsub :
      P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator d ω -
          h (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX]
          - P.μ[fun ω => h (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_sub hYind_int hh_int S.toPOBackdoorSystem.sigmaX
  have hYce :
      P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
          S.toPOBackdoorSystem.dVar.indicator d ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          S.toPOBackdoorSystem.propScore d * S.toPOBackdoorSystem.CATE d := by
    have hcate := S.toPOBackdoorSystem.cate_backdoor hA d
    filter_upwards [hcate,
      Causalean.Estimation.ATE.BackdoorEstimationSystem.propScore_ne_zero
        S.toBackdoorEstimationSystem hA d] with ω hcat hneω
    unfold POBackdoorSystem.adjustedCE at hcat
    rw [Pi.mul_apply, hcat]
    field_simp [hneω]
  have hh_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => h (S.toPOBackdoorSystem.factualX ω)) := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => h (S.toPOBackdoorSystem.factualX ω))
    exact (hh_meas.comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  have hind_int : Integrable (S.toPOBackdoorSystem.dVar.indicator d) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_indicator d
  have hhce :
      P.μ[fun ω => h (S.toPOBackdoorSystem.factualX ω) *
          S.toPOBackdoorSystem.dVar.indicator d ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => h (S.toPOBackdoorSystem.factualX ω)) *
            S.toPOBackdoorSystem.propScore d := by
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hh_sm hh_int hind_int
    simpa [POBackdoorSystem.propScore] using hpull
  rw [hres_eq]
  refine hsub.trans ?_
  filter_upwards [hYce, hhce, S.μ_compat hA d] with ω hY hh hcompat
  have hcate_comp : S.toPOBackdoorSystem.CATE d ω =
      S.μ_val d (S.toPOBackdoorSystem.factualX ω) := by
    simpa [POBackdoorSystem.CATE] using hcompat
  rw [Pi.sub_apply, hY, hh, Pi.mul_apply, Pi.mul_apply, hcate_comp]
  ring

/-! ## σ(X)-conditional bias identity -/

/-- The σ(X)-conditional bias identity
(`prop:est-cate-dr-bias-identity`, Ω-form):

    μ[ φ_η(factualZ ω) − φ_0(factualZ ω) | σ(X) ]
      =ᵐ  condBias η η₀ (factualX ·).

Proof outline: expand `phi_eta z η - phi₀ S z` componentwise on `Ω`:

    (η.μ_fn 1 − η.μ_fn 0)(X) − (η₀.μ_fn 1 − η₀.μ_fn 0)(X)
      + (A / η.e_fn(X)) (Y − η.μ_fn 1(X)) − (A / η₀.e_fn(X)) (Y − η₀.μ_fn 1(X))
      − ((1−A) / (1 − η.e_fn(X))) (Y − η.μ_fn 0(X))
      + ((1−A) / (1 − η₀.e_fn(X))) (Y − η₀.μ_fn 0(X)).

Apply `cond_exp_residual_at_h` to each weighted residual term (with
`h := η.μ_fn d` or `η₀.μ_fn d` as appropriate) and use
`MeasureTheory.condExp_mul_of_stronglyMeasurable_left` to pull the
`(1/η.e_fn)(X)` (resp. `(1/η₀.e_fn)(X)`) factors outside the conditional
expectation as σ(X)-measurable.  The truth-side residuals (with `η₀`)
collapse to zero by the special case `h := η₀.μ_fn d` (i.e.
`cond_exp_residual_zero`).  Collect arm by arm using the algebraic
identity

    (e/ê − 1) · (μ − μ̂) = − (ê − e) · (μ̂ − μ) / ê,

which matches the `condBias` definition arm-by-arm. -/
theorem phi_eta_minus_phi₀_cond_exp
    {P : POSystem} [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (η : NuisanceVec γ) {ε : ℝ}
    (h_overlap_η : η ∈ BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
                    BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (hε_pos : 0 < ε)
    -- Per-arm integrability of the candidate outcome regressions on Ω.
    -- Required to build per-summand integrability witnesses for the AIPW
    -- expansion (truth-side η₀-pieces are derivable from `μ_compat` +
    -- `cate_backdoor`, but the candidate η-side needs an explicit hypothesis).
    (h_μ_η_int : ∀ a : Bool,
      Integrable (fun ω => η.μ_fn a (S.toBackdoorEstimationSystem.factualX ω)) P.μ) :
    P.μ[fun ω => phi_eta (S.toBackdoorEstimationSystem.factualZ ω) η -
                 phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)
        | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ]
        (fun ω => condBias η S.toBackdoorEstimationSystem.η₀
                    (S.toBackdoorEstimationSystem.factualX ω)) := by
  let X : P.Ω → γ := S.toPOBackdoorSystem.factualX
  let Y : P.Ω → ℝ := S.toPOBackdoorSystem.factualY
  let indT : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator true
  let indF : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator false
  let base : P.Ω → ℝ := fun ω =>
    η.μ_fn true (X ω) - η.μ_fn false (X ω) -
      (S.μ_val true (X ω) - S.μ_val false (X ω))
  let BηT : P.Ω → ℝ := fun ω =>
    (1 / η.e_fn (X ω)) *
      (indT ω * (Y ω - η.μ_fn true (X ω)))
  let B₀T : P.Ω → ℝ := fun ω =>
    (1 / S.e_val (X ω)) *
      (indT ω * (Y ω - S.μ_val true (X ω)))
  let CηF : P.Ω → ℝ := fun ω =>
    (1 / (1 - η.e_fn (X ω))) *
      (indF ω * (Y ω - η.μ_fn false (X ω)))
  let C₀F : P.Ω → ℝ := fun ω =>
    (1 / (1 - S.e_val (X ω))) *
      (indF ω * (Y ω - S.μ_val false (X ω)))
  have hindA_true : ∀ ω, BackdoorEstimationSystem.indA
      (S.toBackdoorEstimationSystem.factualZ ω) = indT ω := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : indT ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.indA,
        BackdoorEstimationSystem.projA, indT, hD, hInd]
    · have hInd : indT ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.indA,
        BackdoorEstimationSystem.projA, indT, hD, hInd]
  have hφ_eq :
      (fun ω => phi_eta (S.toBackdoorEstimationSystem.factualZ ω) η -
          phi₀ S (S.toBackdoorEstimationSystem.factualZ ω))
        = (fun ω => base ω + BηT ω - B₀T ω - CηF ω + C₀F ω) := by
    funext ω
    have hind_true_z :
        BackdoorEstimationSystem.indA
          (S.toPOBackdoorSystem.factualX ω,
            S.toPOBackdoorSystem.factualD ω,
            S.toPOBackdoorSystem.factualY ω)
          = indT ω := by
      simpa [BackdoorEstimationSystem.factualZ] using hindA_true ω
    have hind_not : 1 - indT ω = indF ω := by
      have hsum : indT ω + indF ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
      linarith
    simp [base, BηT, B₀T, CηF, C₀F, X, Y, indT, indF, phi₀, phi_eta,
      BackdoorEstimationSystem.aipwMoment, BackdoorEstimationSystem.factualZ,
      BackdoorEstimationSystem.projX, BackdoorEstimationSystem.projY,
      BackdoorEstimationSystem.η₀, hind_true_z, hind_not, mul_assoc, mul_comm,
      sub_eq_add_neg, add_assoc, add_comm]
    ring_nf
  have hμ_val_int : ∀ d : Bool, Integrable (fun ω => S.μ_val d (X ω)) P.μ := by
    intro d
    have hcate_int : Integrable (S.toPOBackdoorSystem.CATE d) P.μ := by
      unfold POBackdoorSystem.CATE
      exact MeasureTheory.integrable_condExp
    exact hcate_int.congr (S.μ_compat hA d)
  have hbase_int : Integrable base P.μ := by
    have hη := (h_μ_η_int true).sub (h_μ_η_int false)
    have hμ := (hμ_val_int true).sub (hμ_val_int false)
    refine (hη.sub hμ).congr ?_
    exact Filter.Eventually.of_forall (fun ω => by simp [base, X])
  have hbase_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX] base := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω =>
        η.μ_fn true (S.toPOBackdoorSystem.factualX ω) -
          η.μ_fn false (S.toPOBackdoorSystem.factualX ω) -
            (S.μ_val true (S.toPOBackdoorSystem.factualX ω) -
              S.μ_val false (S.toPOBackdoorSystem.factualX ω)))
    exact ((((η.μ_meas true).comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).sub
        ((η.μ_meas false).comp
          (comap_measurable S.toPOBackdoorSystem.factualX))).sub
        (((S.μ_meas true).comp
          (comap_measurable S.toPOBackdoorSystem.factualX)).sub
          ((S.μ_meas false).comp
            (comap_measurable S.toPOBackdoorSystem.factualX)))).stronglyMeasurable
  have hbase_ce :
      P.μ[base | S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ] base :=
    Filter.EventuallyEq.of_eq
      (MeasureTheory.condExp_of_stronglyMeasurable
        S.toPOBackdoorSystem.sigmaX_le hbase_sm hbase_int)
  have hηe_lower : ∀ ω, ε ≤ η.e_fn (X ω) := fun ω => (h_overlap_η (X ω)).1
  have hηe_upper : ∀ ω, η.e_fn (X ω) ≤ 1 - ε := fun ω => (h_overlap_η (X ω)).2
  have h₀e_lower : ∀ ω, ε ≤ S.e_val (X ω) := by
    intro ω
    exact (h_overlap_η₀ (X ω)).1
  have h₀e_upper : ∀ ω, S.e_val (X ω) ≤ 1 - ε := by
    intro ω
    exact (h_overlap_η₀ (X ω)).2
  have hwηT_Linf : MemLp (fun ω => 1 / η.e_fn (X ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (η.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hpos : 0 < η.e_fn (X ω) := lt_of_lt_of_le hε_pos (hηe_lower ω)
        have hle : (η.e_fn (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 (hηe_lower ω)
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hwηF_Linf : MemLp (fun ω => 1 / (1 - η.e_fn (X ω))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (measurable_const.sub
          (η.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hden : ε ≤ 1 - η.e_fn (X ω) := by linarith [hηe_upper ω]
        have hpos : 0 < 1 - η.e_fn (X ω) := lt_of_lt_of_le hε_pos hden
        have hle : (1 - η.e_fn (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 hden
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hw₀T_Linf : MemLp (fun ω => 1 / S.e_val (X ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hpos : 0 < S.e_val (X ω) := S.e_pos _
        have hle : (S.e_val (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 (h₀e_lower ω)
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hw₀F_Linf : MemLp (fun ω => 1 / (1 - S.e_val (X ω))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (measurable_const.sub
          (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hpos : 0 < 1 - S.e_val (X ω) := by linarith [S.e_lt_one (X ω)]
        have hden : ε ≤ 1 - S.e_val (X ω) := by linarith [h₀e_upper ω]
        have hle : (1 - S.e_val (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 hden
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hYind_int : ∀ d : Bool,
      Integrable (fun ω => Y ω * S.toPOBackdoorSystem.dVar.indicator d ω) P.μ :=
    fun d => S.toPOBackdoorSystem.dVar.integrable_mul_indicator d
      hA.integrable_factualY S.toPOBackdoorSystem.measurable_factualY
  have hημind_int : ∀ d : Bool,
      Integrable (fun ω => η.μ_fn d (X ω) *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ := by
    intro d
    exact S.toPOBackdoorSystem.dVar.integrable_mul_indicator d (h_μ_η_int d)
      ((η.μ_meas d).comp S.toPOBackdoorSystem.measurable_factualX)
  have hμind_int : ∀ d : Bool,
      Integrable (fun ω => S.μ_val d (X ω) *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ := by
    intro d
    exact S.toPOBackdoorSystem.dVar.integrable_mul_indicator d (hμ_val_int d)
      ((S.μ_meas d).comp S.toPOBackdoorSystem.measurable_factualX)
  have hresη_int : ∀ d : Bool,
      Integrable (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
        (Y ω - η.μ_fn d (X ω))) P.μ := by
    intro d
    have hY' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * Y ω) P.μ := by
      simpa [Y, mul_comm] using hYind_int d
    have hμ' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * η.μ_fn d (X ω)) P.μ := by
      simpa [mul_comm] using hημind_int d
    refine (hY'.sub hμ').congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      change S.toPOBackdoorSystem.dVar.indicator d ω * Y ω -
          S.toPOBackdoorSystem.dVar.indicator d ω * η.μ_fn d (X ω) =
        S.toPOBackdoorSystem.dVar.indicator d ω * (Y ω - η.μ_fn d (X ω))
      ring_nf)
  have hresμ_int : ∀ d : Bool,
      Integrable (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
        (Y ω - S.μ_val d (X ω))) P.μ := by
    intro d
    have hY' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * Y ω) P.μ := by
      simpa [Y, mul_comm] using hYind_int d
    have hμ' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * S.μ_val d (X ω)) P.μ := by
      simpa [mul_comm] using hμind_int d
    refine (hY'.sub hμ').congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      change S.toPOBackdoorSystem.dVar.indicator d ω * Y ω -
          S.toPOBackdoorSystem.dVar.indicator d ω * S.μ_val d (X ω) =
        S.toPOBackdoorSystem.dVar.indicator d ω * (Y ω - S.μ_val d (X ω))
      ring_nf)
  have hBηT_int : Integrable BηT P.μ := by
    have hL1 : MemLp BηT 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hwηT_Linf (memLp_one_iff_integrable.2 (hresη_int true))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [BηT, X, Y, indT]
        ring))
    exact hL1.integrable (by norm_num)
  have hCηF_int : Integrable CηF P.μ := by
    have hL1 : MemLp CηF 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hwηF_Linf (memLp_one_iff_integrable.2 (hresη_int false))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [CηF, X, Y, indF]
        ring))
    exact hL1.integrable (by norm_num)
  have hB₀T_int : Integrable B₀T P.μ := by
    have hL1 : MemLp B₀T 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hw₀T_Linf (memLp_one_iff_integrable.2 (hresμ_int true))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [B₀T, X, Y, indT]
        ring))
    exact hL1.integrable (by norm_num)
  have hC₀F_int : Integrable C₀F P.μ := by
    have hL1 : MemLp C₀F 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hw₀F_Linf (memLp_one_iff_integrable.2 (hresμ_int false))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [C₀F, X, Y, indF]
        ring))
    exact hL1.integrable (by norm_num)
  have hweighted :
      ∀ (d : Bool) (g h : γ → ℝ), Measurable g → Measurable h →
        Integrable (fun ω => h (X ω) *
          S.toPOBackdoorSystem.dVar.indicator d ω) P.μ →
        Integrable (fun ω => g (X ω) *
          (S.toPOBackdoorSystem.dVar.indicator d ω * (Y ω - h (X ω)))) P.μ →
        Integrable (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
          (Y ω - h (X ω))) P.μ →
        P.μ[fun ω => g (X ω) *
            (S.toPOBackdoorSystem.dVar.indicator d ω * (Y ω - h (X ω))) |
            S.toPOBackdoorSystem.sigmaX]
          =ᵐ[P.μ]
            (fun ω => g (X ω) *
              (S.toPOBackdoorSystem.propScore d ω *
                (S.μ_val d (X ω) - h (X ω)))) := by
    intro d g h hg_meas hh_meas hh_ind_int hprod_int hres_int
    have hg_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
        (fun ω => g (X ω)) := by
      change StronglyMeasurable[
        MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
        (fun ω => g (S.toPOBackdoorSystem.factualX ω))
      exact (hg_meas.comp
        (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hg_sm hprod_int hres_int
    refine hpull.trans ?_
    filter_upwards [cond_exp_residual_at_h S hA d h hh_meas
      (by simpa [X, mul_comm] using hh_ind_int)] with ω hω
    rw [Pi.mul_apply, hω]
  have hBηT_ce :
      P.μ[BηT | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => (1 / η.e_fn (X ω)) *
            (S.toPOBackdoorSystem.propScore true ω *
              (S.μ_val true (X ω) - η.μ_fn true (X ω)))) := by
    simpa [BηT, X, Y, indT, mul_assoc] using
      hweighted true (fun x => 1 / η.e_fn x) (η.μ_fn true)
        (measurable_const.div η.e_meas) (η.μ_meas true) (hημind_int true) hBηT_int
        (hresη_int true)
  have hB₀T_ce :
      P.μ[B₀T | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => (1 / S.e_val (X ω)) *
            (S.toPOBackdoorSystem.propScore true ω *
              (S.μ_val true (X ω) - S.μ_val true (X ω)))) := by
    simpa [B₀T, X, Y, indT, mul_assoc] using
      hweighted true (fun x => 1 / S.e_val x) (S.μ_val true)
        (measurable_const.div S.e_meas) (S.μ_meas true) (hμind_int true) hB₀T_int
        (hresμ_int true)
  have hCηF_ce :
      P.μ[CηF | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => (1 / (1 - η.e_fn (X ω))) *
            (S.toPOBackdoorSystem.propScore false ω *
              (S.μ_val false (X ω) - η.μ_fn false (X ω)))) := by
    simpa [CηF, X, Y, indF, mul_assoc] using
      hweighted false (fun x => 1 / (1 - η.e_fn x)) (η.μ_fn false)
        (measurable_const.div (measurable_const.sub η.e_meas))
        (η.μ_meas false) (hημind_int false) hCηF_int (hresη_int false)
  have hC₀F_ce :
      P.μ[C₀F | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => (1 / (1 - S.e_val (X ω))) *
            (S.toPOBackdoorSystem.propScore false ω *
              (S.μ_val false (X ω) - S.μ_val false (X ω)))) := by
    simpa [C₀F, X, Y, indF, mul_assoc] using
      hweighted false (fun x => 1 / (1 - S.e_val x)) (S.μ_val false)
        (measurable_const.div (measurable_const.sub S.e_meas))
        (S.μ_meas false) (hμind_int false) hC₀F_int (hresμ_int false)
  have h12_int : Integrable (fun ω => base ω + BηT ω) P.μ :=
    hbase_int.add hBηT_int
  have h123_int : Integrable (fun ω => base ω + BηT ω - B₀T ω) P.μ :=
    h12_int.sub hB₀T_int
  have h1234_int : Integrable (fun ω => base ω + BηT ω - B₀T ω - CηF ω) P.μ :=
    h123_int.sub hCηF_int
  have hadd :
      P.μ[fun ω => base ω + BηT ω | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[base | S.toPOBackdoorSystem.sigmaX] +
            P.μ[BηT | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_add hbase_int hBηT_int S.toPOBackdoorSystem.sigmaX
  have hsubT :
      P.μ[fun ω => base ω + BηT ω - B₀T ω | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => base ω + BηT ω | S.toPOBackdoorSystem.sigmaX] -
            P.μ[B₀T | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_sub h12_int hB₀T_int S.toPOBackdoorSystem.sigmaX
  have hsubF :
      P.μ[fun ω => base ω + BηT ω - B₀T ω - CηF ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => base ω + BηT ω - B₀T ω |
            S.toPOBackdoorSystem.sigmaX] -
            P.μ[CηF | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_sub h123_int hCηF_int S.toPOBackdoorSystem.sigmaX
  have haddF :
      P.μ[fun ω => base ω + BηT ω - B₀T ω - CηF ω + C₀F ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => base ω + BηT ω - B₀T ω - CηF ω |
            S.toPOBackdoorSystem.sigmaX] +
            P.μ[C₀F | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_add h1234_int hC₀F_int S.toPOBackdoorSystem.sigmaX
  rw [hφ_eq]
  refine haddF.trans ?_
  filter_upwards [hsubF, hsubT, hadd, hbase_ce, hBηT_ce, hB₀T_ce, hCηF_ce,
    hC₀F_ce, S.e_compat, BackdoorEstimationSystem.propScore_false_ae
      S.toBackdoorEstimationSystem hA] with
    ω hsubFω hsubTω haddω hbaseω hBTω hB0ω hCFω hC0ω heT heF
  rw [Pi.add_apply, hsubFω, Pi.sub_apply, hsubTω, Pi.sub_apply,
    haddω, Pi.add_apply, hbaseω, hBTω, hB0ω, hCFω, hC0ω]
  rw [heF, heT]
  simp only [X, base, BackdoorEstimationSystem.η₀, one_div, sub_self,
    mul_zero, sub_zero, add_zero] at ⊢
  have hηT_ne : η.e_fn (S.toPOBackdoorSystem.factualX ω) ≠ 0 := by
    simpa [X] using ne_of_gt (lt_of_lt_of_le hε_pos (hηe_lower ω))
  have hηF_ne : 1 - η.e_fn (S.toPOBackdoorSystem.factualX ω) ≠ 0 := by
    have hden : ε ≤ 1 - η.e_fn (X ω) := by linarith [hηe_upper ω]
    simpa [X] using ne_of_gt (lt_of_lt_of_le hε_pos hden)
  let eη : ℝ := η.e_fn (S.toPOBackdoorSystem.factualX ω)
  let e₀ : ℝ := S.e_val (S.toPOBackdoorSystem.factualX ω)
  let mT : ℝ := η.μ_fn true (S.toPOBackdoorSystem.factualX ω)
  let mF : ℝ := η.μ_fn false (S.toPOBackdoorSystem.factualX ω)
  let vT : ℝ := S.μ_val true (S.toPOBackdoorSystem.factualX ω)
  let vF : ℝ := S.μ_val false (S.toPOBackdoorSystem.factualX ω)
  unfold condBias
  rw [Fintype.sum_bool]
  simp only [if_true, if_false, Bool.false_eq_true]
  field_simp [hηT_ne, hηF_ne]
  change ((mT - mF - (vT - vF)) * eη + e₀ * (vT - mT)) *
        (1 - eη) - eη * (1 - e₀) * (vF - mF) =
      (eη - e₀) * ((1 - eη) * (mT - vT) + eη * (mF - vF))
  ring

/-! ## Value-space `P_X`-a.e. form (Kennedy) -/

/-- Value-space `P_X`-a.e. form of the conditional bias identity (Kennedy
form): the σ(X)-conditional Ω-statement transported to `γ` via
`condDistrib`.

For `P_X`-a.e. `x`, the value-space integral of `phi_eta z η - phi₀ S z`
against the regular conditional `condDistrib factualZ factualX P.μ x`
equals `condBias η η₀ x`.

Proof outline:
1. By `phi_eta_minus_phi₀_cond_exp`, the σ(X)-conditional on Ω of
   `phi_eta - phi₀` equals `condBias η η₀ ∘ factualX` a.e.
2. By `MeasureTheory.condExp_ae_eq_integral_condDistrib` applied with
   `X := factualX`, `Y := factualZ`, `f := fun z => phi_eta z η - phi₀ S z`,
   the σ(X)-conditional equals
   `fun ω => ∫ z, (phi_eta z η - phi₀ S z) ∂condDistrib ... (factualX ω)`
   a.e. on Ω.
3. Combine: `(fun ω => ∫ ... condDistrib (factualX ω))
              =ᵐ condBias η η₀ ∘ factualX` on (Ω, P.μ).
4. Transport to (γ, P_X) via `MeasureTheory.ae_map_iff` (set is measurable
   because both sides are measurable in `x`). -/
theorem phi_eta_minus_phi₀_at_x
    {P : POSystem} [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [StandardBorelSpace γ] [Nonempty γ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (η : NuisanceVec γ) {ε : ℝ}
    (h_overlap_η : η ∈ BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
                    BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (hε_pos : 0 < ε)
    (h_μ_η_int : ∀ a : Bool,
      Integrable
        (fun ω => η.μ_fn a (S.toBackdoorEstimationSystem.factualX ω)) P.μ)
    (h_int : Integrable
      (fun ω => phi_eta (S.toBackdoorEstimationSystem.factualZ ω) η -
                phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)) P.μ) :
    ∀ᵐ x ∂(S.toBackdoorEstimationSystem.P_X),
      (∫ z, (phi_eta z η - phi₀ S z)
            ∂condDistrib S.toBackdoorEstimationSystem.factualZ
                         S.toPOBackdoorSystem.factualX P.μ x)
        = condBias η S.toBackdoorEstimationSystem.η₀ x := by
  have hcondΩ :
      P.μ[fun ω => phi_eta (S.toBackdoorEstimationSystem.factualZ ω) η -
                   phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)
          | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => condBias η S.toBackdoorEstimationSystem.η₀
                      (S.toBackdoorEstimationSystem.factualX ω)) :=
    phi_eta_minus_phi₀_cond_exp S hA η h_overlap_η h_overlap_η₀ hε_pos
      h_μ_η_int
  have hf_sm : StronglyMeasurable
      (fun z : γ × Bool × ℝ => phi_eta z η - phi₀ S z) :=
    ((measurable_phi_eta η).sub (measurable_phi₀ S)).stronglyMeasurable
  have hkernel :
      P.μ[fun ω => phi_eta (S.toBackdoorEstimationSystem.factualZ ω) η -
                   phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)
          | MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
        =ᵐ[P.μ]
          (fun ω =>
            ∫ z, (phi_eta z η - phi₀ S z)
              ∂condDistrib S.toBackdoorEstimationSystem.factualZ
                           S.toPOBackdoorSystem.factualX P.μ
                           (S.toPOBackdoorSystem.factualX ω)) :=
    ProbabilityTheory.condExp_ae_eq_integral_condDistrib
      S.toPOBackdoorSystem.measurable_factualX
      S.toBackdoorEstimationSystem.measurable_factualZ.aemeasurable
      hf_sm h_int
  have hΩ :
      (fun ω =>
        ∫ z, (phi_eta z η - phi₀ S z)
          ∂condDistrib S.toBackdoorEstimationSystem.factualZ
                       S.toPOBackdoorSystem.factualX P.μ
                       (S.toPOBackdoorSystem.factualX ω))
        =ᵐ[P.μ]
          (fun ω => condBias η S.toBackdoorEstimationSystem.η₀
                      (S.toBackdoorEstimationSystem.factualX ω)) :=
    hkernel.symm.trans (by
      simpa [POBackdoorSystem.sigmaX] using hcondΩ)
  have hleft_meas : Measurable
      (fun x : γ =>
        ∫ z, (phi_eta z η - phi₀ S z)
          ∂condDistrib S.toBackdoorEstimationSystem.factualZ
                       S.toPOBackdoorSystem.factualX P.μ x) := by
    have hpair_sm : StronglyMeasurable
        (fun p : γ × (γ × Bool × ℝ) => phi_eta p.2 η - phi₀ S p.2) :=
      (hf_sm.comp_measurable measurable_snd)
    exact (MeasureTheory.StronglyMeasurable.integral_condDistrib
      (Y := S.toBackdoorEstimationSystem.factualZ)
      (X := S.toPOBackdoorSystem.factualX) (μ := P.μ) hpair_sm).measurable
  have hset : MeasurableSet
      {x : γ |
        (∫ z, (phi_eta z η - phi₀ S z)
          ∂condDistrib S.toBackdoorEstimationSystem.factualZ
                       S.toPOBackdoorSystem.factualX P.μ x)
          = condBias η S.toBackdoorEstimationSystem.η₀ x} :=
    measurableSet_eq_fun hleft_meas
      (measurable_condBias η S.toBackdoorEstimationSystem.η₀)
  unfold BackdoorEstimationSystem.P_X
  rw [MeasureTheory.ae_map_iff
    S.toPOBackdoorSystem.measurable_factualX.aemeasurable hset]
  simpa using hΩ

/-! ## Double-robustness corollaries (`rem:est-cate-double-robust`) -/

/-- If the propensity matches the truth at `x`, then `condBias η η₀ x = 0`.

Proof outline: substitute `h_e : η.e_fn x = η₀.e_fn x` so each summand
contains the factor `(η.e_fn x − η₀.e_fn x) = 0`; conclude via
`Finset.sum_eq_zero` and `zero_mul`. -/
lemma condBias_zero_of_propensity_match
    (η η₀ : NuisanceVec γ) (x : γ) (h_e : η.e_fn x = η₀.e_fn x) :
    condBias η η₀ x = 0 := by
  unfold condBias
  apply Finset.sum_eq_zero
  intro a _
  rw [show η.e_fn x - η₀.e_fn x = 0 from sub_eq_zero.mpr h_e]
  ring

/-- If both outcome arms match the truth at `x`, then `condBias η η₀ x = 0`.

Proof outline: substitute `h_μ a : η.μ_fn a x = η₀.μ_fn a x` for each
arm `a : Bool` so each summand contains the factor
`(η.μ_fn a x − η₀.μ_fn a x) = 0`; conclude via `Finset.sum_eq_zero`,
`sub_self`, and `zero_div`. -/
lemma condBias_zero_of_outcome_match
    (η η₀ : NuisanceVec γ) (x : γ)
    (h_μ : ∀ a : Bool, η.μ_fn a x = η₀.μ_fn a x) :
    condBias η η₀ x = 0 := by
  unfold condBias
  apply Finset.sum_eq_zero
  intro a _
  rw [show η.μ_fn a x - η₀.μ_fn a x = 0 from sub_eq_zero.mpr (h_μ a)]
  ring

/-! ## σ(X)-conditional of the directional derivative at truth -/

/-- The σ(X)-conditional expectation of the directional derivative
`phi_eta_dir_deriv` at the truth `g₀ = η₀` is zero a.e.

This is the differentiated companion of `phi_eta_minus_phi₀_cond_exp`:
where the latter shows that the σ(X)-conditional of
`phi_eta z η − phi₀ S z` equals the bilinear `condBias η η₀`, this lemma
shows that the derivative of that conditional bias at `η = η₀` (along
any nuisance direction `v`) is zero a.e.

Proof sketch: take σ(X)-conditional of each of the five summands of
`phi_eta_dir_deriv η₀ v (factualZ ω)` separately.

* The σ(X)-measurable lead term `(v.μ_fn true − v.μ_fn false)(factualX)`
  is preserved as-is.
* The two `e_fn`-residual cross-products
    `(v.e_fn / η₀.e_fn² (factualX)) · indA · (Y − η₀.μ_fn true (factualX))`
    `(v.e_fn / (1 − η₀.e_fn)² (factualX)) · (1 − indA) · (Y − η₀.μ_fn false (factualX))`
  vanish via `cond_exp_residual_zero` (with `d := true` and `d := false`).
  Use `condExp_mul_of_stronglyMeasurable_left` to pull the σ(X)-measurable
  envelope `v.e_fn / η₀.e_fn² (factualX)` out of the conditional
  expectation; the resulting inner conditional residual is zero a.s.
* The two `μ_fn`-pullout terms
    `−(1 / η₀.e_fn (factualX)) · v.μ_fn true (factualX) · indA`
    `+(1 / (1 − η₀.e_fn) (factualX)) · v.μ_fn false (factualX) · (1 − indA)`
  collapse via the σ(X)-measurable pull-out plus
  `propScore true =ᵐ η₀.e_fn ∘ factualX` (the `S.e_compat` field) and the
  derived `propScore false =ᵐ 1 − η₀.e_fn ∘ factualX`, leaving
  `−v.μ_fn true (factualX)` and `+v.μ_fn false (factualX)` respectively.

Sum: `(v.μ_fn true − v.μ_fn false)(factualX) + 0 − v.μ_fn true (factualX)
       + 0 + v.μ_fn false (factualX) = 0` a.s.

The boundedness hypotheses on `v.e_fn` and `v.μ_fn` ensure all the
σ(X)-measurable envelopes have finite `L¹(P.μ)` norm under
`IsFiniteMeasure P.μ`, which is what
`condExp_mul_of_stronglyMeasurable_left` requires. -/
theorem cond_exp_phi_eta_dir_deriv_at_truth_zero
    {P : POSystem} [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
                    BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (v : NuisanceVec γ)
    (h_v_μ_bdd : ∃ Cμ : ℝ, ∀ b : Bool, ∀ x : γ, |v.μ_fn b x| ≤ Cμ)
    (h_v_e_bdd : ∃ Ce : ℝ, ∀ x : γ, |v.e_fn x| ≤ Ce) :
    P.μ[fun ω => phi_eta_dir_deriv S.toBackdoorEstimationSystem.η₀ v
                   (S.toBackdoorEstimationSystem.factualZ ω)
        | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
  let X : P.Ω → γ := S.toPOBackdoorSystem.factualX
  let Y : P.Ω → ℝ := S.toPOBackdoorSystem.factualY
  let indT : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator true
  let indF : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator false
  let T1 : P.Ω → ℝ := fun ω => v.μ_fn true (X ω) - v.μ_fn false (X ω)
  let T2 : P.Ω → ℝ := fun ω =>
    (-v.e_fn (X ω) * (1 / S.e_val (X ω)) * (1 / S.e_val (X ω))) *
      (indT ω * (Y ω - S.μ_val true (X ω)))
  let T3 : P.Ω → ℝ := fun ω =>
    (-1 / S.e_val (X ω) * v.μ_fn true (X ω)) * indT ω
  let T4 : P.Ω → ℝ := fun ω =>
    (-v.e_fn (X ω) * (1 / (1 - S.e_val (X ω))) *
        (1 / (1 - S.e_val (X ω)))) *
      (indF ω * (Y ω - S.μ_val false (X ω)))
  let T5 : P.Ω → ℝ := fun ω =>
    (1 / (1 - S.e_val (X ω)) * v.μ_fn false (X ω)) * indF ω
  have hindA_true : ∀ ω, BackdoorEstimationSystem.indA
      (S.toBackdoorEstimationSystem.factualZ ω) = indT ω := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : indT ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.indA,
        BackdoorEstimationSystem.projA, indT, hD, hInd]
    · have hInd : indT ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.indA,
        BackdoorEstimationSystem.projA, indT, hD, hInd]
  have hφ_eq :
      (fun ω => phi_eta_dir_deriv S.toBackdoorEstimationSystem.η₀ v
          (S.toBackdoorEstimationSystem.factualZ ω))
        = (fun ω => T1 ω + T2 ω + T3 ω + T4 ω + T5 ω) := by
    funext ω
    have hind_true_z :
        BackdoorEstimationSystem.indA
          (S.toPOBackdoorSystem.factualX ω,
            S.toPOBackdoorSystem.factualD ω,
            S.toPOBackdoorSystem.factualY ω)
          = indT ω := by
      simpa [BackdoorEstimationSystem.factualZ] using hindA_true ω
    have hind_not : 1 - indT ω = indF ω := by
      have hsum : indT ω + indF ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
      linarith
    simp only [T1, T2, T3, T4, T5, X, Y, indT, indF, phi_eta_dir_deriv,
      BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.projX,
      BackdoorEstimationSystem.projY, BackdoorEstimationSystem.η₀,
      hind_true_z, hind_not]
    have hneT : S.e_val (S.toPOBackdoorSystem.factualX ω) ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le hε_pos
        (h_overlap_η₀ (S.toPOBackdoorSystem.factualX ω)).1)
    have hden : ε ≤ 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) := by
      have hu : S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
        simpa [BackdoorEstimationSystem.η₀] using
          (h_overlap_η₀ (S.toPOBackdoorSystem.factualX ω)).2
      linarith
    have hneF : 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le hε_pos hden)
    field_simp [hneT, hneF]
    ring
  have hμ_val_int : ∀ d : Bool, Integrable (fun ω => S.μ_val d (X ω)) P.μ := by
    intro d
    have hcate_int : Integrable (S.toPOBackdoorSystem.CATE d) P.μ := by
      unfold POBackdoorSystem.CATE
      exact MeasureTheory.integrable_condExp
    exact hcate_int.congr (S.μ_compat hA d)
  rcases h_v_μ_bdd with ⟨Cμ, hCμ⟩
  rcases h_v_e_bdd with ⟨Ce, hCe⟩
  have hvμ_int : ∀ d : Bool, Integrable (fun ω => v.μ_fn d (X ω)) P.μ := by
    intro d
    refine MeasureTheory.Integrable.of_bound
      (((v.μ_meas d).comp S.toPOBackdoorSystem.measurable_factualX).aestronglyMeasurable)
      |Cμ| (Filter.Eventually.of_forall ?_)
    intro ω
    simpa [X, Real.norm_eq_abs] using le_trans (hCμ d (X ω)) (le_abs_self Cμ)
  have hv_e_top : MemLp (fun ω => v.e_fn (X ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ |Ce| (Filter.Eventually.of_forall ?_)
    · exact ((v.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)).aestronglyMeasurable
    · intro ω
      simpa [X, Real.norm_eq_abs] using le_trans (hCe (X ω)) (le_abs_self Ce)
  have hvμ_top : ∀ d : Bool, MemLp (fun ω => v.μ_fn d (X ω)) ⊤ P.μ := by
    intro d
    refine MemLp.of_bound ?_ |Cμ| (Filter.Eventually.of_forall ?_)
    · exact (((v.μ_meas d).comp S.toPOBackdoorSystem.measurable_factualX)).aestronglyMeasurable
    · intro ω
      simpa [X, Real.norm_eq_abs] using le_trans (hCμ d (X ω)) (le_abs_self Cμ)
  have hT1_int : Integrable T1 P.μ := by
    simpa [T1] using (hvμ_int true).sub (hvμ_int false)
  have hT1_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX] T1 := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => v.μ_fn true (S.toPOBackdoorSystem.factualX ω) -
        v.μ_fn false (S.toPOBackdoorSystem.factualX ω))
    exact (((v.μ_meas true).comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).sub
      ((v.μ_meas false).comp
        (comap_measurable S.toPOBackdoorSystem.factualX))).stronglyMeasurable
  have hT1_ce :
      P.μ[T1 | S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ] T1 :=
    Filter.EventuallyEq.of_eq
      (MeasureTheory.condExp_of_stronglyMeasurable
        S.toPOBackdoorSystem.sigmaX_le hT1_sm hT1_int)
  have h₀e_lower : ∀ ω, ε ≤ S.e_val (X ω) := by
    intro ω
    exact (h_overlap_η₀ (X ω)).1
  have h₀e_upper : ∀ ω, S.e_val (X ω) ≤ 1 - ε := by
    intro ω
    exact (h_overlap_η₀ (X ω)).2
  have hw₀T_Linf : MemLp (fun ω => 1 / S.e_val (X ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hpos : 0 < S.e_val (X ω) := lt_of_lt_of_le hε_pos (h₀e_lower ω)
        have hle : (S.e_val (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 (h₀e_lower ω)
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hw₀F_Linf : MemLp (fun ω => 1 / (1 - S.e_val (X ω))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (measurable_const.sub
          (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hden : ε ≤ 1 - S.e_val (X ω) := by linarith [h₀e_upper ω]
        have hpos : 0 < 1 - S.e_val (X ω) := lt_of_lt_of_le hε_pos hden
        have hle : (1 - S.e_val (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 hden
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hYind_int : ∀ d : Bool,
      Integrable (fun ω => Y ω * S.toPOBackdoorSystem.dVar.indicator d ω) P.μ :=
    fun d => S.toPOBackdoorSystem.dVar.integrable_mul_indicator d
      hA.integrable_factualY S.toPOBackdoorSystem.measurable_factualY
  have hμind_int : ∀ d : Bool,
      Integrable (fun ω => S.μ_val d (X ω) *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ := by
    intro d
    exact S.toPOBackdoorSystem.dVar.integrable_mul_indicator d (hμ_val_int d)
      ((S.μ_meas d).comp S.toPOBackdoorSystem.measurable_factualX)
  have hresμ_int : ∀ d : Bool,
      Integrable (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
        (Y ω - S.μ_val d (X ω))) P.μ := by
    intro d
    have hY' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * Y ω) P.μ := by
      simpa [Y, mul_comm] using hYind_int d
    have hμ' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * S.μ_val d (X ω)) P.μ := by
      simpa [mul_comm] using hμind_int d
    refine (hY'.sub hμ').congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      change S.toPOBackdoorSystem.dVar.indicator d ω * Y ω -
          S.toPOBackdoorSystem.dVar.indicator d ω * S.μ_val d (X ω) =
        S.toPOBackdoorSystem.dVar.indicator d ω * (Y ω - S.μ_val d (X ω))
      ring_nf)
  have hgET_top : MemLp
      (fun ω => -v.e_fn (X ω) * (1 / S.e_val (X ω)) * (1 / S.e_val (X ω))) ⊤ P.μ := by
    have htmp : MemLp (fun ω => -v.e_fn (X ω) * (1 / S.e_val (X ω))) ⊤ P.μ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀T_Linf hv_e_top.neg
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀T_Linf htmp
  have hgEF_top : MemLp
      (fun ω => -v.e_fn (X ω) * (1 / (1 - S.e_val (X ω))) *
        (1 / (1 - S.e_val (X ω)))) ⊤ P.μ := by
    have htmp : MemLp (fun ω => -v.e_fn (X ω) * (1 / (1 - S.e_val (X ω)))) ⊤ P.μ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀F_Linf hv_e_top.neg
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀F_Linf htmp
  have hgMT_top : MemLp (fun ω => -1 / S.e_val (X ω) * v.μ_fn true (X ω)) ⊤ P.μ := by
    simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
      MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀T_Linf.neg (hvμ_top true)
  have hgMF_top : MemLp (fun ω => 1 / (1 - S.e_val (X ω)) * v.μ_fn false (X ω)) ⊤ P.μ := by
    simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
      MemLp.mul' (p := ⊤) (q := ⊤) (r := ⊤) hw₀F_Linf (hvμ_top false)
  have hT2_int : Integrable T2 P.μ := by
    have hL1 : MemLp T2 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hgET_top (memLp_one_iff_integrable.2 (hresμ_int true))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [T2, X, Y, indT]
        ring))
    exact hL1.integrable (by norm_num)
  have hT4_int : Integrable T4 P.μ := by
    have hL1 : MemLp T4 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hgEF_top (memLp_one_iff_integrable.2 (hresμ_int false))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [T4, X, Y, indF]
        ring))
    exact hL1.integrable (by norm_num)
  have hT3_int : Integrable T3 P.μ := by
    have hL1 : MemLp T3 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hgMT_top (memLp_one_iff_integrable.2
          (S.toPOBackdoorSystem.dVar.integrable_indicator true))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [T3, X, indT]
        ring))
    exact hL1.integrable (by norm_num)
  have hT5_int : Integrable T5 P.μ := by
    have hL1 : MemLp T5 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hgMF_top (memLp_one_iff_integrable.2
          (S.toPOBackdoorSystem.dVar.integrable_indicator false))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [T5, X, indF]
        ring))
    exact hL1.integrable (by norm_num)
  have hweighted_zero :
      ∀ (d : Bool) (g : γ → ℝ), Measurable g →
        Integrable (fun ω => g (X ω) *
          (S.toPOBackdoorSystem.dVar.indicator d ω *
            (Y ω - S.μ_val d (X ω)))) P.μ →
        P.μ[fun ω => g (X ω) *
            (S.toPOBackdoorSystem.dVar.indicator d ω *
              (Y ω - S.μ_val d (X ω))) |
            S.toPOBackdoorSystem.sigmaX]
          =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    intro d g hg_meas hprod_int
    have hg_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
        (fun ω => g (X ω)) := by
      change StronglyMeasurable[
        MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
        (fun ω => g (S.toPOBackdoorSystem.factualX ω))
      exact (hg_meas.comp
        (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hg_sm hprod_int (hresμ_int d)
    refine hpull.trans ?_
    filter_upwards
      [BackdoorEstimationSystem.cond_exp_residual_zero
        S.toBackdoorEstimationSystem hA d] with ω hω
    rw [Pi.mul_apply, hω, mul_zero]
  have hscore_ce :
      ∀ (d : Bool) (g : γ → ℝ), Measurable g →
        Integrable (fun ω => g (X ω) *
          S.toPOBackdoorSystem.dVar.indicator d ω) P.μ →
        P.μ[fun ω => g (X ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX]
          =ᵐ[P.μ]
            (fun ω => g (X ω) * S.toPOBackdoorSystem.propScore d ω) := by
    intro d g hg_meas hprod_int
    have hg_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
        (fun ω => g (X ω)) := by
      change StronglyMeasurable[
        MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
        (fun ω => g (S.toPOBackdoorSystem.factualX ω))
      exact (hg_meas.comp
        (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hg_sm hprod_int
      (S.toPOBackdoorSystem.dVar.integrable_indicator d)
    simpa [POBackdoorSystem.propScore] using hpull
  have hT2_ce : P.μ[T2 | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    simpa [T2, X, Y, indT] using
      hweighted_zero true (fun x => -v.e_fn x * (1 / S.e_val x) * (1 / S.e_val x))
        (((v.e_meas.neg).mul (measurable_const.div S.e_meas)).mul
          (measurable_const.div S.e_meas)) hT2_int
  have hT4_ce : P.μ[T4 | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    simpa [T4, X, Y, indF] using
      hweighted_zero false
        (fun x => -v.e_fn x * (1 / (1 - S.e_val x)) * (1 / (1 - S.e_val x)))
        (((v.e_meas.neg).mul
          (measurable_const.div (measurable_const.sub S.e_meas))).mul
          (measurable_const.div (measurable_const.sub S.e_meas))) hT4_int
  have hT3_ce : P.μ[T3 | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ] (fun ω => -v.μ_fn true (X ω)) := by
    have hraw := hscore_ce true (fun x => -1 / S.e_val x * v.μ_fn true x)
      ((measurable_const.neg.div S.e_meas).mul (v.μ_meas true)) hT3_int
    filter_upwards [hraw, S.e_compat] with ω hω heω
    rw [hω, heω]
    have hne : S.e_val (X ω) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hε_pos (h₀e_lower ω))
    field_simp [hne]
    ring
  have hT5_ce : P.μ[T5 | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ] (fun ω => v.μ_fn false (X ω)) := by
    have hraw := hscore_ce false (fun x => 1 / (1 - S.e_val x) * v.μ_fn false x)
      ((measurable_const.div (measurable_const.sub S.e_meas)).mul (v.μ_meas false))
      hT5_int
    filter_upwards [hraw, BackdoorEstimationSystem.propScore_false_ae
      S.toBackdoorEstimationSystem hA, S.e_compat] with ω hω hfω heω
    rw [hω, hfω, heω]
    have hden : ε ≤ 1 - S.e_val (X ω) := by linarith [h₀e_upper ω]
    have hne : 1 - S.e_val (X ω) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hε_pos hden)
    field_simp [hne]
    ring
  have h12_int : Integrable (fun ω => T1 ω + T2 ω) P.μ := hT1_int.add hT2_int
  have h123_int : Integrable (fun ω => T1 ω + T2 ω + T3 ω) P.μ :=
    h12_int.add hT3_int
  have h1234_int : Integrable (fun ω => T1 ω + T2 ω + T3 ω + T4 ω) P.μ :=
    h123_int.add hT4_int
  have hadd12 :
      P.μ[fun ω => T1 ω + T2 ω | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[T1 | S.toPOBackdoorSystem.sigmaX] +
            P.μ[T2 | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_add hT1_int hT2_int S.toPOBackdoorSystem.sigmaX
  have hadd123 :
      P.μ[fun ω => T1 ω + T2 ω + T3 ω | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => T1 ω + T2 ω | S.toPOBackdoorSystem.sigmaX] +
            P.μ[T3 | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_add h12_int hT3_int S.toPOBackdoorSystem.sigmaX
  have hadd1234 :
      P.μ[fun ω => T1 ω + T2 ω + T3 ω + T4 ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => T1 ω + T2 ω + T3 ω |
            S.toPOBackdoorSystem.sigmaX] +
            P.μ[T4 | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_add h123_int hT4_int S.toPOBackdoorSystem.sigmaX
  have hadd12345 :
      P.μ[fun ω => T1 ω + T2 ω + T3 ω + T4 ω + T5 ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => T1 ω + T2 ω + T3 ω + T4 ω |
            S.toPOBackdoorSystem.sigmaX] +
            P.μ[T5 | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_add h1234_int hT5_int S.toPOBackdoorSystem.sigmaX
  rw [hφ_eq]
  refine hadd12345.trans ?_
  filter_upwards [hadd1234, hadd123, hadd12, hT1_ce, hT2_ce, hT3_ce, hT4_ce,
    hT5_ce] with ω h1234ω h123ω h12ω h1ω h2ω h3ω h4ω h5ω
  rw [Pi.add_apply, h1234ω, Pi.add_apply, h123ω, Pi.add_apply, h12ω,
    Pi.add_apply, h1ω, h2ω, h3ω, h4ω, h5ω]
  simp [T1]
  ring

end CATE
end Estimation
end Causalean
