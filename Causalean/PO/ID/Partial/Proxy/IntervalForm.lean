/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Proximal partial identification — `Set.Icc` interval form

Closed-interval (`Set.Icc`) restatements of the five proximal sandwich bounds
(`WBased`, `ZBased`, `TwoProxy`). Each source theorem produces a scalar
two-sided bound `L ≤ θ ∧ θ ≤ U`; here we feed that conjunction through the
adapter `Causalean.PartialID.mem_Icc_of_sandwich` to obtain the membership form
`θ ∈ Set.Icc L U`, matching the abstract identified-set vocabulary of
`PartialID/Basic.lean`. No new mathematical content: these are mechanical
corollaries, one per source theorem, sharing the source binders verbatim.

## Main results

* `condMeanYofA_W_mem_Icc`  — `Set.Icc` form of `condMeanYofA_W_bounds`.
* `meanYofA_W_mem_Icc`      — `Set.Icc` form of `meanYofA_W_bounds`.
* `condMeanYofA_Z_mem_Icc`  — `Set.Icc` form of `condMeanYofA_Z_bounds`.
* `meanYofA_Z_mem_Icc`      — `Set.Icc` form of `meanYofA_Z_bounds`.
* `condMeanYofA_WZ_mem_Icc` — `Set.Icc` form of `condMeanYofA_WZ_bounds`.
-/

import Causalean.PO.ID.Partial.Proxy.WBased
import Causalean.PO.ID.Partial.Proxy.ZBased
import Causalean.PO.ID.Partial.Proxy.TwoProxy
import Causalean.PO.ID.Partial.Basic

/-! # Closed-interval forms of proximal proxy bounds

This file converts the scalar two-sided proximal proxy bounds into `Set.Icc`
membership statements. The W-based, Z-based, and two-proxy source theorems keep
their original hypotheses, while this layer adapts them to the common
partial-identification interval vocabulary.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POProximalSystem

variable {P : POSystem}
  {γ_X γ_Z γ_W γ_U : Type*}
  [MeasurableSpace γ_X] [MeasurableSpace γ_Z]
  [MeasurableSpace γ_W] [MeasurableSpace γ_U]
  {S : POProximalSystem P γ_X γ_Z γ_W γ_U}
  {μ : Measure P.Ω} [IsFiniteMeasure μ] [StandardBorelSpace P.Ω]

/-! ### W-based -/

/-- **`Set.Icc` form of Theorem 1** (`condMeanYofA_W_bounds`). Fix a treatment arm `a` and
assume [the W-only proximal bridge assumption bundle](hyp:HA), with [the treatment and
outcome variables distinct](hyp:hAY); let `Lenv`, `Uenv` be [lower and upper envelope
functions bounding the W-proxy density ratio](hyp:hL,hU), with [the off-arm stratum of
positive mass](hyp:hμpos) and [the envelope-weighted bridge moments
integrable](hyp:hU_int_h,hL_int_h). Then [the conditional target `E[Y(a) ∣ A ≠ a]` lies
in the closed interval spanned by the essential `Y`-bounds and the W-proxy envelope
clamps](goal), the `Set.Icc` membership restatement of the scalar sandwich bound
`condMeanYofA_W_bounds`. -/
theorem condMeanYofA_W_mem_Icc
    (HA : POProximalSystem.WBasedAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (Lenv Uenv : Bool × γ_X → ℝ)
    (hL : S.IsLowerEnvW μ a Lenv) (hU : S.IsUpperEnvW μ a Uenv)
    (hμpos : 0 < (μ {ω | S.A ω ≠ a}).toReal)
    (hU_int_h : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) *
          HA.h (a, S.W ω, S.X ω)) μ)
    (hL_int_h : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) *
          HA.h (a, S.W ω, S.X ω)) μ) :
    S.condMeanYofA μ a ∈ Set.Icc
      (max (Classical.choose HA.Y_bdd_below)
        ((μ {ω | S.A ω ≠ a}).toReal⁻¹ *
         ∫ ω in {ω | S.A ω = a},
           S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ))
      (min (Classical.choose HA.Y_bdd_above)
        ((μ {ω | S.A ω ≠ a}).toReal⁻¹ *
         ∫ ω in {ω | S.A ω = a},
           S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ)) := by
  have h := condMeanYofA_W_bounds HA a hAY Lenv Uenv hL hU hμpos hU_int_h hL_int_h
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

/-- **`Set.Icc` form of Corollary 1** (`meanYofA_W_bounds`). Fix a treatment arm `a` and
assume [the W-only proximal bridge assumption bundle](hyp:HA), with [the treatment and
outcome variables distinct](hyp:hAY); let `Lenv`, `Uenv` be [lower and upper envelope
functions bounding the W-proxy density ratio](hyp:hL,hU), and assume [the
envelope-weighted bridge moments](hyp:hU_int_h,hL_int_h) and [the envelope-weighted
observed conditional means](hyp:hU_int_Y,hL_int_Y) are integrable. Then [the marginal
target `E[Y(a)]` lies in the closed interval spanned by the W-proxy marginal lower and
upper clamps](goal), the `Set.Icc` membership restatement of the scalar sandwich bound
`meanYofA_W_bounds`. -/
theorem meanYofA_W_mem_Icc
    (HA : POProximalSystem.WBasedAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (Lenv Uenv : Bool × γ_X → ℝ)
    (hL : S.IsLowerEnvW μ a Lenv) (hU : S.IsUpperEnvW μ a Uenv)
    (hU_int_h : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) *
          HA.h (a, S.W ω, S.X ω)) μ)
    (hL_int_h : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) *
          HA.h (a, S.W ω, S.X ω)) μ)
    (hU_int_Y : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) *
          (μ[S.Y | S.σ_AX]) ω) μ)
    (hL_int_Y : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) *
          (μ[S.Y | S.σ_AX]) ω) μ) :
    S.meanYofA μ a ∈ Set.Icc
      (max (Classical.choose HA.Y_bdd_below * (μ {ω | S.A ω ≠ a}).toReal)
        (∫ ω in {ω | S.A ω = a},
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ)
        + (∫ ω in {ω | S.A ω = a}, S.Y ω ∂μ))
      (min (Classical.choose HA.Y_bdd_above * (μ {ω | S.A ω ≠ a}).toReal)
          (∫ ω in {ω | S.A ω = a},
            S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ)
        + (∫ ω in {ω | S.A ω = a}, S.Y ω ∂μ)) := by
  have h := meanYofA_W_bounds HA a hAY Lenv Uenv hL hU
    hU_int_h hL_int_h hU_int_Y hL_int_Y
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

/-! ### Z-based -/

/-- **`Set.Icc` form of Theorem 2** (`condMeanYofA_Z_bounds`). Fix a treatment arm `a` and
assume [the Z-only proximal bridge assumption bundle](hyp:HA), with [the treatment and
outcome variables distinct](hyp:hAY); let `Lenv`, `Uenv` be [lower and upper envelope
functions bounding the σ(A,Z,X)-conditional mean of the outcome on the on-arm
stratum](hyp:hL,hU), assumed [integrable](hyp:hLInt,hUInt), with [the envelope weighted
by the treatment-proxy bridge](hyp:hL_q,hU_q) and [the envelope weighted by the
likelihood-ratio arm-swap factor](hyp:hL_L,hU_L) both integrable, and [the off-arm
stratum of positive mass](hyp:hμpos). Then [the conditional target `E[Y(a) ∣ A ≠ a]`
lies in the closed interval spanned by the normalised on-arm integrals of `Lenv` and
`Uenv`](goal), the `Set.Icc` membership restatement of the scalar sandwich bound
`condMeanYofA_Z_bounds`. -/
theorem condMeanYofA_Z_mem_Icc
    (HA : POProximalSystem.ZBasedAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (Lenv Uenv : Bool × γ_X → ℝ)
    (hL : S.IsLowerEnvZ μ a Lenv) (hU : S.IsUpperEnvZ μ a Uenv)
    (hLInt : Integrable (fun ω => Lenv (a, S.X ω)) μ)
    (hUInt : Integrable (fun ω => Uenv (a, S.X ω)) μ)
    (hL_q :
      Integrable (fun ω => Lenv (a, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ)
    (hU_q :
      Integrable (fun ω => Uenv (a, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ)
    (hL_L :
      Integrable (fun ω => Lenv (a, S.X ω) * HA.likelihoodRatio_swapA a ω) μ)
    (hU_L :
      Integrable (fun ω => Uenv (a, S.X ω) * HA.likelihoodRatio_swapA a ω) μ)
    (hμpos : 0 < (μ {ω | S.A ω ≠ a}).toReal) :
    S.condMeanYofA μ a ∈ Set.Icc
      ((μ {ω | S.A ω ≠ a}).toReal⁻¹ * ∫ ω in {ω | S.A ω ≠ a}, Lenv (a, S.X ω) ∂μ)
      ((μ {ω | S.A ω ≠ a}).toReal⁻¹ * ∫ ω in {ω | S.A ω ≠ a}, Uenv (a, S.X ω) ∂μ) := by
  have h := condMeanYofA_Z_bounds HA a hAY Lenv Uenv hL hU
    hLInt hUInt hL_q hU_q hL_L hU_L hμpos
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

/-- **`Set.Icc` form of Corollary 2** (`meanYofA_Z_bounds`). Fix a treatment arm `a` and
assume [the Z-only proximal bridge assumption bundle](hyp:HA), with [the treatment and
outcome variables distinct](hyp:hAY); let `Lenv`, `Uenv` be [lower and upper envelope
functions bounding the σ(A,Z,X)-conditional mean of the outcome on the on-arm
stratum](hyp:hL,hU), assumed [integrable](hyp:hLInt,hUInt), with [the envelope weighted
by the treatment-proxy bridge](hyp:hL_q,hU_q) and [the envelope weighted by the
likelihood-ratio arm-swap factor](hyp:hL_L,hU_L) both integrable. Then [the marginal
target `E[Y(a)]` lies in the closed interval spanned by the Z-proxy marginal envelope
integrals](goal), the `Set.Icc` membership restatement of the scalar sandwich bound
`meanYofA_Z_bounds`. -/
theorem meanYofA_Z_mem_Icc
    (HA : POProximalSystem.ZBasedAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (Lenv Uenv : Bool × γ_X → ℝ)
    (hL : S.IsLowerEnvZ μ a Lenv) (hU : S.IsUpperEnvZ μ a Uenv)
    (hLInt : Integrable (fun ω => Lenv (a, S.X ω)) μ)
    (hUInt : Integrable (fun ω => Uenv (a, S.X ω)) μ)
    (hL_q :
      Integrable (fun ω => Lenv (a, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ)
    (hU_q :
      Integrable (fun ω => Uenv (a, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ)
    (hL_L :
      Integrable (fun ω => Lenv (a, S.X ω) * HA.likelihoodRatio_swapA a ω) μ)
    (hU_L :
      Integrable (fun ω => Uenv (a, S.X ω) * HA.likelihoodRatio_swapA a ω) μ) :
    S.meanYofA μ a ∈ Set.Icc
      ((∫ ω in {ω | S.A ω ≠ a}, Lenv (a, S.X ω) ∂μ)
        + (∫ ω in {ω | S.A ω = a}, S.Y ω ∂μ))
      ((∫ ω in {ω | S.A ω ≠ a}, Uenv (a, S.X ω) ∂μ)
        + (∫ ω in {ω | S.A ω = a}, S.Y ω ∂μ)) := by
  have h := meanYofA_Z_bounds HA a hAY Lenv Uenv hL hU
    hLInt hUInt hL_q hU_q hL_L hU_L
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

/-! ### Two-proxy -/

/-- **`Set.Icc` form of Theorem 3** (`condMeanYofA_WZ_bounds`). Fix a treatment arm `a` and
assume [the two-proxy bridge assumption bundle](hyp:HA), with [the treatment and outcome
variables distinct](hyp:hAY); let `Lenv`, `Uenv` be [lower and upper envelope functions
bounding the same-arm joint-versus-product W-Z density ratio](hyp:hL,hU), with [the
off-arm stratum of positive mass](hyp:hμpos) and [the envelope-weighted product of the
two conditional bridge means integrable](hyp:hU_envInt,hL_envInt). Then [the conditional
target `E[Y(a) ∣ A ≠ a]` lies in the closed interval spanned by the essential `Y`-bounds
and the joint-WZ envelope clamps](goal), the `Set.Icc` membership restatement of the
scalar sandwich bound `condMeanYofA_WZ_bounds`. -/
theorem condMeanYofA_WZ_mem_Icc
    (HA : POProximalSystem.TwoProxyAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (Lenv Uenv : Bool × γ_X → ℝ)
    (hL : S.IsLowerEnvWZ μ a Lenv) (hU : S.IsUpperEnvWZ μ a Uenv)
    (hμpos : 0 < (μ {ω | S.A ω ≠ a}).toReal)
    (hU_envInt : Integrable (fun ω =>
          Uenv (a, S.X ω)
          * (μ[fun ω' => HA.h (a, S.W ω', S.X ω') | S.σ_AX]) ω
          * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AX]) ω) μ)
    (hL_envInt : Integrable (fun ω =>
          Lenv (a, S.X ω)
          * (μ[fun ω' => HA.h (a, S.W ω', S.X ω') | S.σ_AX]) ω
          * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AX]) ω) μ) :
    S.condMeanYofA μ a ∈ Set.Icc
      (max (Classical.choose HA.Y_bdd_below)
        ((μ {ω | S.A ω ≠ a}).toReal⁻¹ *
         ∫ ω in {ω | S.A ω = a},
           S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ))
      (min (Classical.choose HA.Y_bdd_above)
        ((μ {ω | S.A ω ≠ a}).toReal⁻¹ *
         ∫ ω in {ω | S.A ω = a},
           S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ)) := by
  have h := condMeanYofA_WZ_bounds HA a hAY Lenv Uenv hL hU hμpos
    hU_envInt hL_envInt
  exact Causalean.PartialID.mem_Icc_of_sandwich h.1 h.2

end POProximalSystem

end PO
end Causalean
