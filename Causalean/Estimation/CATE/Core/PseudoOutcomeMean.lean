/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conditional mean of the DR pseudo-outcome (Kennedy, 2023)

This file proves `prop:est-cate-dr-cond-mean` from
`doc/basic_concepts/po/estimation/dr_learner_cate.tex`:

    𝔼[φ₀(Z) | σ(X)] =ᵐ τ₀(X)        (a.s. on Ω),

equivalently `𝔼[φ₀(Z) | X = x] = τ₀(x)` for `P_X`-almost every `x`.

The on-Ω σ(X)-conditional form (`phi₀_factualZ_cond_exp`) is the version we
reduce to existing back-door substrate: it follows from the algebraic
decomposition

    φ₀(factualZ ω) = (μ_val 1 (X) − μ_val 0 (X))
                       + (1 / e_val(X)) · 1{A=1} · (Y − μ_val 1 (X))
                       − (1 / (1 − e_val(X))) · 1{A=0} · (Y − μ_val 0 (X))

after pulling each `1 / e_val(X)` and `1 / (1 − e_val(X))` factor out of the
σ(X)-conditional via `condExp_mul_of_stronglyMeasurable_left` and applying
`cond_exp_residual_zero` to each residual term.  Mirrors the structure of
`weighted_residual_integral_zero` (lines 266–358 of
`Estimation/ATE/MeanZero.lean`) but stops *before* integrating.

The value-space `P_X`-a.e. form (`phi_eta_cond_exp_eq_tau`) records the
corresponding value-space statement consumed by downstream DR-learner code.
-/

import Causalean.Estimation.CATE.Core.PseudoOutcome
import Causalean.Estimation.ATE.Score.MeanZero
import Causalean.Estimation.ATE.Score.ScorePullout

/-! # Mean of the CATE Pseudo-Outcome

This file proves the conditional-mean identity for the doubly robust
pseudo-outcome used to estimate conditional average treatment effects. The
identity shows that, under the back-door assumptions and strict overlap, the
conditional expectation of the true pseudo-outcome given covariates equals the
target conditional treatment effect. The theorem `phi₀_factualZ_cond_exp`
proves the σ(X)-conditional statement on the source probability space, while
`phi_eta_cond_exp_eq_tau` transports it to the value-space law `P_X` using
conditional distributions. -/

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory ProbabilityTheory Filter Topology
  Causalean.PO Causalean.Estimation.ATE

namespace CATEEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

private lemma residual_integrable
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) (d : Bool) :
    Integrable
      (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
        (S.toPOBackdoorSystem.factualY ω -
          S.μ_val d (S.toPOBackdoorSystem.factualX ω))) P.μ := by
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

private lemma weighted_residual_cond_exp_zero
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) (d : Bool)
    (g : γ → ℝ) (hg_meas : Measurable g)
    (h_int : Integrable
      (fun ω => g (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator d ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val d (S.toPOBackdoorSystem.factualX ω)))) P.μ) :
    P.μ[fun ω => g (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator d ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val d (S.toPOBackdoorSystem.factualX ω))) |
        S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
  have hg_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => g (S.toPOBackdoorSystem.factualX ω)) := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => g (S.toPOBackdoorSystem.factualX ω))
    exact (hg_meas.comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  have hresid_int := residual_integrable S hA d
  have hcondexp_pull :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hg_sm h_int hresid_int
  refine hcondexp_pull.trans ?_
  filter_upwards [BackdoorEstimationSystem.cond_exp_residual_zero S hA d] with ω hω
  rw [Pi.mul_apply, hω, mul_zero]

/-- σ(X)-conditional form of `prop:est-cate-dr-cond-mean`:

    𝔼[φ₀(factualZ ·) | σ(X)] =ᵐ τ_val (factualX ·).

Under the back-door causal assumptions and strict overlap, the σ(X)-
conditional expectation of the true DR pseudo-outcome `φ₀` evaluated at the
factual data triple `Z = (X, A, Y)` equals the value-space CATE `τ_val`
pulled back along `factualX`.

-- proof outline:
-- Decompose `phi₀ z = (μ_val 1 (X) - μ_val 0 (X))
--   + (1/e_val(X))·1{A=1}·(Y - μ_val 1 (X))
--   - (1/(1-e_val(X)))·1{A=0}·(Y - μ_val 0 (X))`.
-- The first piece is σ(X)-measurable, so its conditional expectation is itself.
-- The two residual terms have conditional expectation 0 by
-- `cond_exp_residual_zero S hA d` after pulling `1/e_val(X)`
-- (resp. `1/(1-e_val(X))`) out via
-- `condExp_mul_of_stronglyMeasurable_left`.
-- Mirror the structure of `weighted_residual_integral_zero` in
-- `Estimation/ATE/MeanZero.lean` lines 266–358 but stop *before* integrating.
-- The σ(X)-measurable representative of the constant-in-A piece is exactly
-- `S.τ_val ∘ factualX`. -/
theorem phi₀_factualZ_cond_exp
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    {ε : ℝ}
    (h_overlap : S.toBackdoorEstimationSystem.StrictOverlap ε) :
    P.μ[fun ω => phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)
        | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ]
        (fun ω => S.τ_val (S.toPOBackdoorSystem.factualX ω)) := by
  let base : P.Ω → ℝ := fun ω => S.τ_val (S.toPOBackdoorSystem.factualX ω)
  let B : P.Ω → ℝ := fun ω =>
    (1 / S.e_val (S.toPOBackdoorSystem.factualX ω)) *
      (S.toPOBackdoorSystem.dVar.indicator true ω *
        (S.toPOBackdoorSystem.factualY ω -
          S.μ_val true (S.toPOBackdoorSystem.factualX ω)))
  let C : P.Ω → ℝ := fun ω =>
    (1 / (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) *
      (S.toPOBackdoorSystem.dVar.indicator false ω *
        (S.toPOBackdoorSystem.factualY ω -
          S.μ_val false (S.toPOBackdoorSystem.factualX ω)))
  have hindA_true : ∀ ω, BackdoorEstimationSystem.indA
      (S.toBackdoorEstimationSystem.factualZ ω) =
      S.toPOBackdoorSystem.dVar.indicator true ω := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.indA,
        BackdoorEstimationSystem.projA, hD, hInd]
    · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.indA,
        BackdoorEstimationSystem.projA, hD, hInd]
  have hindA_false : ∀ ω, 1 - BackdoorEstimationSystem.indA
      (S.toBackdoorEstimationSystem.factualZ ω) =
      S.toPOBackdoorSystem.dVar.indicator false ω := by
    intro ω
    have hsum : S.toPOBackdoorSystem.dVar.indicator true ω +
        S.toPOBackdoorSystem.dVar.indicator false ω = 1 :=
      S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
    rw [hindA_true ω]
    linarith
  have hφ_eq :
      (fun ω => phi₀ S (S.toBackdoorEstimationSystem.factualZ ω))
        = (fun ω => base ω + B ω - C ω) := by
    funext ω
    have hind_true_z :
        BackdoorEstimationSystem.indA
          (S.toPOBackdoorSystem.factualX ω,
            S.toPOBackdoorSystem.factualD ω,
            S.toPOBackdoorSystem.factualY ω)
          = S.toPOBackdoorSystem.dVar.indicator true ω := by
      simpa [BackdoorEstimationSystem.factualZ] using hindA_true ω
    have hind_not :
        1 - S.toPOBackdoorSystem.dVar.indicator true ω =
          S.toPOBackdoorSystem.dVar.indicator false ω := by
      have hsum : S.toPOBackdoorSystem.dVar.indicator true ω +
          S.toPOBackdoorSystem.dVar.indicator false ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
      linarith
    simp [base, B, C, phi₀, phi_eta, BackdoorEstimationSystem.aipwMoment,
      BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.projX,
      BackdoorEstimationSystem.projY,
      BackdoorEstimationSystem.η₀, CATEEstimationSystem.τ_val, hind_true_z,
      hind_not, mul_assoc, mul_comm, sub_eq_add_neg, add_assoc, add_comm]
    ring_nf
  have hμx_int : ∀ d : Bool,
      Integrable (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) P.μ := by
    intro d
    have hcate_int : Integrable (S.toPOBackdoorSystem.CATE d) P.μ := by
      unfold POBackdoorSystem.CATE
      exact MeasureTheory.integrable_condExp
    exact hcate_int.congr (S.μ_compat hA d)
  have hbase_int : Integrable base P.μ := by
    have hsub := (hμx_int true).sub (hμx_int false)
    refine hsub.congr ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp [base, CATEEstimationSystem.τ_val]
  have hbase_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX] base := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => S.τ_val (S.toPOBackdoorSystem.factualX ω))
    exact ((S.measurable_τ_val).comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  have hbase_ce :
      P.μ[base | S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ] base :=
    Filter.EventuallyEq.of_eq
      (MeasureTheory.condExp_of_stronglyMeasurable
        S.toPOBackdoorSystem.sigmaX_le hbase_sm hbase_int)
  have he_lower :
      ∀ᵐ ω ∂P.μ, ε ≤ S.e_val (S.toPOBackdoorSystem.factualX ω) := by
    filter_upwards [h_overlap.2.2, S.e_compat] with ω hprop hcomp
    simpa [hcomp] using hprop.1
  have he_upper :
      ∀ᵐ ω ∂P.μ, S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
    filter_upwards [h_overlap.2.2, S.e_compat] with ω hprop hcomp
    simpa [hcomp] using hprop.2
  have hw_true_Linf : MemLp
      (fun ω => 1 / S.e_val (S.toPOBackdoorSystem.factualX ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))).aestronglyMeasurable
    · filter_upwards [he_lower] with ω he
      have hpos : 0 < S.e_val (S.toPOBackdoorSystem.factualX ω) :=
        S.e_pos _
      have hle : (S.e_val (S.toPOBackdoorSystem.factualX ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hpos h_overlap.1).2 he
      simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle
  have hw_false_Linf : MemLp
      (fun ω => 1 / (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (measurable_const.sub
          (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)))).aestronglyMeasurable
    · filter_upwards [he_upper] with ω he
      have hden : ε ≤ 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) := by
        linarith
      have hdenpos : 0 < 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) :=
        lt_of_lt_of_le h_overlap.1 hden
      have hle : (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hdenpos h_overlap.1).2 hden
      simpa [one_div, Real.norm_eq_abs, abs_of_pos hdenpos] using hle
  have hresid_true_int :=
    residual_integrable S.toBackdoorEstimationSystem hA true
  have hresid_false_int :=
    residual_integrable S.toBackdoorEstimationSystem hA false
  have hB_int : Integrable B P.μ := by
    have hresid_L1 : MemLp
        (fun ω => S.toPOBackdoorSystem.dVar.indicator true ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val true (S.toPOBackdoorSystem.factualX ω))) 1 P.μ :=
      memLp_one_iff_integrable.2 hresid_true_int
    have hL1 : MemLp B 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hw_true_Linf hresid_L1
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [B]
        ring))
    exact hL1.integrable (by norm_num)
  have hC_int : Integrable C P.μ := by
    have hresid_L1 : MemLp
        (fun ω => S.toPOBackdoorSystem.dVar.indicator false ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω))) 1 P.μ :=
      memLp_one_iff_integrable.2 hresid_false_int
    have hL1 : MemLp C 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hw_false_Linf hresid_L1
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [C]
        ring))
    exact hL1.integrable (by norm_num)
  have hB_zero :
      P.μ[B | S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    have hg_meas : Measurable (fun x => 1 / S.e_val x) :=
      measurable_const.div S.e_meas
    exact weighted_residual_cond_exp_zero S.toBackdoorEstimationSystem hA true
      (fun x => 1 / S.e_val x) hg_meas hB_int
  have hC_zero :
      P.μ[C | S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    have hg_meas : Measurable (fun x => 1 / (1 - S.e_val x)) :=
      measurable_const.div (measurable_const.sub S.e_meas)
    exact weighted_residual_cond_exp_zero S.toBackdoorEstimationSystem hA false
      (fun x => 1 / (1 - S.e_val x)) hg_meas hC_int
  have hsum_int : Integrable (fun ω => base ω + B ω) P.μ :=
    hbase_int.add hB_int
  have hadd :
      P.μ[fun ω => base ω + B ω | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[base | S.toPOBackdoorSystem.sigmaX]
            + P.μ[B | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_add hbase_int hB_int S.toPOBackdoorSystem.sigmaX
  have hsub :
      P.μ[fun ω => base ω + B ω - C ω | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => base ω + B ω | S.toPOBackdoorSystem.sigmaX]
            - P.μ[C | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_sub hsum_int hC_int S.toPOBackdoorSystem.sigmaX
  rw [hφ_eq]
  refine hsub.trans ?_
  filter_upwards [hadd, hbase_ce, hB_zero, hC_zero] with ω haddω hbaseω hBω hCω
  change P.μ[fun ω => base ω + B ω | S.toPOBackdoorSystem.sigmaX] ω -
      P.μ[C | S.toPOBackdoorSystem.sigmaX] ω =
    S.τ_val (S.toPOBackdoorSystem.factualX ω)
  rw [haddω, Pi.add_apply, hbaseω, hBω, hCω]
  simp [base]

/-- Value-space `P_X`-a.e. form of `prop:est-cate-dr-cond-mean`:

    ∫ z, φ₀(z) ∂(condDistrib factualZ factualX P.μ x) = τ_val x
                                                  for P_X-a.e. x.

The integral form of `𝔼[φ₀(Z) | X = x] = τ_val(x)` obtained by transporting
the σ(X)-conditional Ω-form `phi₀_factualZ_cond_exp` along `factualX` via
`condDistrib`.

Proof outline:
1. By `phi₀_factualZ_cond_exp`, the σ(X)-conditional on Ω equals
   `S.τ_val ∘ factualX` a.e.
2. By `MeasureTheory.condExp_ae_eq_integral_condDistrib` applied with
   `X := factualX`, `Y := factualZ`, `f := phi₀ S`, the σ(X)-conditional
   equals `fun ω => ∫ z, phi₀ S z ∂condDistrib factualZ factualX P.μ (factualX ω)`
   a.e. on Ω.
3. Combine: `(fun ω => ∫ ... condDistrib (factualX ω)) =ᵐ S.τ_val ∘ factualX`
   on (Ω, P.μ).
4. Transport to (γ, P_X) via `MeasureTheory.ae_map_iff` (set is measurable
   because both sides are measurable in `x`). -/
theorem phi_eta_cond_exp_eq_tau [StandardBorelSpace γ] [Nonempty γ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    {ε : ℝ}
    (h_overlap : S.toBackdoorEstimationSystem.StrictOverlap ε)
    (h_int : Integrable
      (fun ω => phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)) P.μ) :
    ∀ᵐ x ∂(S.toBackdoorEstimationSystem.P_X),
      (∫ z, phi₀ S z ∂condDistrib S.toBackdoorEstimationSystem.factualZ
                                  S.toPOBackdoorSystem.factualX P.μ x)
        = S.τ_val x := by
  let X := S.toPOBackdoorSystem.factualX
  let Z := S.toBackdoorEstimationSystem.factualZ
  let lhs : γ → ℝ := fun x =>
    ∫ z, phi₀ S z ∂condDistrib Z X P.μ x
  have hcond :
      P.μ[fun ω => phi₀ S (Z ω) | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ] fun ω => lhs (X ω) := by
    simpa [lhs, X, Z, POBackdoorSystem.sigmaX] using
      (ProbabilityTheory.condExp_ae_eq_integral_condDistrib
        (μ := P.μ) (X := X) (Y := Z)
        S.toPOBackdoorSystem.measurable_factualX
        S.toBackdoorEstimationSystem.measurable_factualZ.aemeasurable
        (measurable_phi₀ S).stronglyMeasurable h_int)
  have hΩ : ∀ᵐ ω ∂P.μ, lhs (X ω) = S.τ_val (X ω) :=
    hcond.symm.trans (phi₀_factualZ_cond_exp S hA h_overlap)
  have hlhs_meas : Measurable lhs := by
    have hφ : StronglyMeasurable
        (fun p : γ × (γ × Bool × ℝ) => phi₀ S p.2) :=
      (measurable_phi₀ S).stronglyMeasurable.comp_measurable measurable_snd
    have hsm : StronglyMeasurable
        (fun x => ∫ z, phi₀ S z ∂condDistrib Z X P.μ x) := by
      simpa using
        (MeasureTheory.StronglyMeasurable.integral_condDistrib
          (X := X) (Y := Z) (μ := P.μ) hφ)
    simpa [lhs] using hsm.measurable
  have hset : MeasurableSet {x : γ | lhs x = S.τ_val x} :=
    measurableSet_eq_fun hlhs_meas S.measurable_τ_val
  unfold BackdoorEstimationSystem.P_X
  change ∀ᵐ x ∂P.μ.map X, lhs x = S.τ_val x
  rw [MeasureTheory.ae_map_iff
    S.toPOBackdoorSystem.measurable_factualX.aemeasurable hset]
  simpa [X] using hΩ

end CATEEstimationSystem

end CATE
end Estimation
end Causalean
