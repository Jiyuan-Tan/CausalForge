/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# CATE estimation system: structure and value-space target

This file defines the CATE-side analogue of `BackdoorEstimationSystem`.
The structure `CATEEstimationSystem` is an empty extension of
`BackdoorEstimationSystem`: we re-use the back-door substrate (consistency,
conditional exchangeability, overlap, integrability, the value-space
representatives `μ_val` / `e_val`, and the Doob–Dynkin compatibility fields
`μ_reg_compat` / `e_compat`).  The counterfactual compatibility statement
`μ_compat` is available only as a derived theorem under the back-door causal
assumptions.  The CATE target

    τ_0(x) := μ_val 1 x − μ_val 0 x

is purely derived; no new fields are needed.

Mirrors `def:est-cate-system` and the conclusion of
`def:est-cate-causal-assumptions` in
`doc/basic_concepts/po/estimation/dr_learner_cate.tex`.
-/

import Causalean.Estimation.ATE.Setup

/-!
Defines the CATE estimation system as a function-valued version of the
back-door ATE setup. It exposes the conditional treatment-effect target and
the nuisance representatives needed by CATE pseudo-outcomes.
-/

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Estimation.ATE

/-! ## CATE estimation system

A `CATEEstimationSystem` is just a `BackdoorEstimationSystem` viewed through
the CATE lens: instead of integrating the outcome contrast against `P_X` to
get a scalar ATE, we expose the function-valued target `τ_val` directly.
The structure adds no new fields; everything is inherited from the back-door
substrate. -/

/-- Wrapper around `BackdoorEstimationSystem` whose semantic role is to
expose the CATE target `τ_val x = μ_val 1 x − μ_val 0 x` as a derived
function-valued estimand.  No new fields are introduced; the underlying
`BackdoorEstimationSystem` carries consistency, conditional exchangeability,
overlap, integrability, the value-space `μ_val` / `e_val`, observable
outcome-regression compatibility `μ_reg_compat`, and propensity compatibility
`e_compat`.  Counterfactual outcome-regression compatibility is derived later
from the back-door causal assumptions, not inherited as a field. -/
structure CATEEstimationSystem (P : POSystem) (γ : Type*)
    [MeasurableSpace γ] [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    extends BackdoorEstimationSystem P γ

namespace CATEEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- Value-space CATE: `τ_val x := μ_val 1 x − μ_val 0 x`.  This is the
"observable CATE regression" `τ_0` of `def:est-cate-system`. -/
def τ_val (S : CATEEstimationSystem P γ) (x : γ) : ℝ :=
  S.μ_val true x - S.μ_val false x

/-- The value-space CATE is measurable, since both arms of `μ_val` are. -/
lemma measurable_τ_val (S : CATEEstimationSystem P γ) :
    Measurable S.τ_val :=
  (S.μ_meas true).sub (S.μ_meas false)

/-- Under the back-door causal assumptions, the value-space CATE pulled
back to `Ω` agrees almost surely with the σ(X)-conditional expectation of
the contrast `Y(1) − Y(0)`.  This is the last sentence of
`def:est-cate-causal-assumptions`:

    τ_0(X) =ᵐ μ[Y(1) − Y(0) | σ(X)].

Proof outline: combine `(S.μ_compat hA true).symm.sub (S.μ_compat hA false).symm`
with `MeasureTheory.condExp_sub` applied to `hA.integrable_Y1` /
`hA.integrable_Y0`. -/
theorem tau_val_eq_CATE (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) :
    (fun ω => S.τ_val (S.toPOBackdoorSystem.factualX ω))
      =ᵐ[P.μ]
    (P.μ[fun ω =>
        S.toPOBackdoorSystem.YofD true ω - S.toPOBackdoorSystem.YofD false ω
        | S.toPOBackdoorSystem.sigmaX]) := by
  have hcompat :
      (fun ω => S.μ_val true (S.toPOBackdoorSystem.factualX ω) -
        S.μ_val false (S.toPOBackdoorSystem.factualX ω))
        =ᵐ[P.μ]
      (fun ω => P.μ[S.toPOBackdoorSystem.YofD true | S.toPOBackdoorSystem.sigmaX] ω -
        P.μ[S.toPOBackdoorSystem.YofD false | S.toPOBackdoorSystem.sigmaX] ω) :=
    (S.μ_compat hA true).symm.sub (S.μ_compat hA false).symm
  have hsub :
      P.μ[fun ω =>
        S.toPOBackdoorSystem.YofD true ω - S.toPOBackdoorSystem.YofD false ω |
        S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
      (fun ω => P.μ[S.toPOBackdoorSystem.YofD true | S.toPOBackdoorSystem.sigmaX] ω -
        P.μ[S.toPOBackdoorSystem.YofD false | S.toPOBackdoorSystem.sigmaX] ω) :=
    MeasureTheory.condExp_sub hA.integrable_Y1 hA.integrable_Y0 S.toPOBackdoorSystem.sigmaX
  calc
    (fun ω => S.τ_val (S.toPOBackdoorSystem.factualX ω))
        =ᵐ[P.μ]
      (fun ω => S.μ_val true (S.toPOBackdoorSystem.factualX ω) -
        S.μ_val false (S.toPOBackdoorSystem.factualX ω)) := by
        filter_upwards with ω
        rfl
    _ =ᵐ[P.μ]
      (fun ω => P.μ[S.toPOBackdoorSystem.YofD true | S.toPOBackdoorSystem.sigmaX] ω -
        P.μ[S.toPOBackdoorSystem.YofD false | S.toPOBackdoorSystem.sigmaX] ω) := hcompat
    _ =ᵐ[P.μ]
      P.μ[fun ω =>
        S.toPOBackdoorSystem.YofD true ω - S.toPOBackdoorSystem.YofD false ω |
        S.toPOBackdoorSystem.sigmaX] := hsub.symm

end CATEEstimationSystem

end CATE
end Estimation
end Causalean
