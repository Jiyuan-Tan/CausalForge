/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Partially linear DML: value-space estimation system and moment instance

This file builds the value-space estimation system `PLRSystem` for the partially
linear model (analogue of `BackdoorEstimationSystem` for the back-door ATE) and
instantiates the abstract double-machine-learning `GeneralMoment` framework with
the Robinson partialling-out score.

* `PLRSystem` — a `POPartialLinearModel` together with value-space representatives
  `ℓ_val, m_val : γ → ℝ` of the outcome and treatment regressions (the ML
  targets), their compatibility with `E[Y|σX]` / `E[D|σX]`, and the
  nondegeneracy `E[(D − m_val(X))²] ≠ 0` (residual treatment variation).
* `P_Z`, `P_X` — the joint observed-data law and the covariate marginal.
* `plrGeneralMoment` — the `GeneralMoment` instance: moment `ψ`, truth nuisance
  `η₀ = (ℓ_val, m_val)`, target `θ₀ = θ`, bilinear seminorms (L²(P_X) of the
  nuisance differences), and Jacobian `J₀ = −E[(D − m_val(X))²]`.
* `integral_P_Z`, `plrMomentFunctional_factualZ` — change-of-variables bridges
  from the `P_Z`-level moment to the `μ`-level potential-outcome facts.

The three analytic facts that feed the DML engine live in sibling files:
`MeanZero.lean` (`plr_meanZero`, `plr_finite_var`) and `RemainderBound.lean`
(`plr_remainder_bound`, the doubly-robust product-rate bound).
-/

import Causalean.PO.ID.Exact.PartialLinear.Identification
import Causalean.Estimation.PLR.Moment
import Causalean.Estimation.OrthogonalMoments.MomentFunctional
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Causalean.Tactic.Attr

/-! # Partially linear DML estimation system

This file provides the value-space estimation system carrying the regression
representatives, the joint observed-data law, and the `GeneralMoment` instance of
the abstract DML framework. The main declarations are `PLRSystem`,
`PLRSystem.factualZ`, `PLRSystem.P_Z`, `PLRSystem.P_X`, `PLRSystem.η₀`,
`PLRSystem.θ₀`, `PLRSystem.residSecondMoment`, `PLRSystem.plrGeneralMoment`, and
the change-of-variables helper `PLRSystem.integral_P_Z`. The resulting partially
linear moment has a DGP-dependent Jacobian equal to minus the residual treatment
variance; sibling files prove the mean-zero, finite-variance, score-L², and
doubly-robust remainder facts used for structural-slope DML normality. -/

namespace Causalean
namespace Estimation
namespace PLR

open MeasureTheory ProbabilityTheory Causalean.PO
open Causalean.Estimation.OrthogonalMoments

/-- A partially linear estimation system extends a partially linear causal model with
value-space regression representatives — [an outcome-regression representative](hyp:lVal)
and [a treatment-regression representative](hyp:mVal) on the covariates — subject to:
each representative is [measurable](hyp:lVal_meas,mVal_meas); [the outcome representative
agrees almost surely with the conditional mean of the outcome given the covariates](hyp:lVal_compat)
and [the treatment representative agrees almost surely with the conditional mean of the
treatment given the covariates](hyp:mVal_compat); and [the treatment retains nonzero
variation after partialling out the covariate](hyp:nondegenerate), which is what makes the
partialling-out Jacobian invertible.

The representatives are the nuisance functions estimated by machine learning;
their compatibility fields tie them to the conditional expectations of outcome
and treatment given covariates. -/
structure PLRSystem (P : POSystem) (γ : Type*) [MeasurableSpace γ]
    [IsFiniteMeasure P.μ]
    extends POPartialLinearModel P γ where
  /-- Value-space outcome regression `ℓ_val(x)` (the conditional mean of `Y` as a
  function of the covariate value). -/
  lVal : γ → ℝ
  /-- The outcome regression representative is measurable. -/
  lVal_meas : Measurable lVal
  /-- Value-space treatment regression `m_val(x)`. -/
  mVal : γ → ℝ
  /-- The treatment regression representative is measurable. -/
  mVal_meas : Measurable mVal
  /-- `ℓ_val` represents the outcome regression: `ℓ_val(X) = E[Y | σ(X)]` a.s. -/
  lVal_compat :
    (fun ω => lVal (toPOPartialLinearSystem.factualX ω))
      =ᵐ[P.μ] toPOPartialLinearModel.lReg
  /-- `m_val` represents the treatment regression: `m_val(X) = E[D | σ(X)]` a.s. -/
  mVal_compat :
    (fun ω => mVal (toPOPartialLinearSystem.factualX ω))
      =ᵐ[P.μ] toPOPartialLinearModel.mReg
  /-- Nondegeneracy: the treatment retains variation after partialling out the
  covariate, `E[(D − m_val(X))²] ≠ 0`.  This is what makes the partialling-out
  Jacobian invertible. -/
  nondegenerate :
    ∫ ω, (toPOPartialLinearSystem.factualD ω
            - mVal (toPOPartialLinearSystem.factualX ω)) ^ 2 ∂P.μ ≠ 0

attribute [fun_prop] PLRSystem.lVal_meas PLRSystem.mVal_meas

namespace PLRSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ] [IsFiniteMeasure P.μ]
variable (S : PLRSystem P γ)

/-- The observed-data map returns the covariate, treatment, and outcome for each
unit in the population space. -/
noncomputable def factualZ : P.Ω → γ × ℝ × ℝ :=
  fun ω => (S.factualX ω, S.factualD ω, S.factualY ω)

/-- The observed-data map is measurable. -/
@[fun_prop]
lemma measurable_factualZ : Measurable S.factualZ :=
  S.measurable_factualX.prodMk (S.measurable_factualD.prodMk S.measurable_factualY)

/-- The joint observed-data law is the distribution of covariate, treatment, and
outcome induced by the population measure. -/
noncomputable def P_Z : Measure (γ × ℝ × ℝ) := P.μ.map S.factualZ

/-- The covariate marginal is the distribution of the observed covariate induced
by the population measure. -/
noncomputable def P_X : Measure γ := P.μ.map S.factualX

/-- The joint observed-data law is the image of the population measure under the map recording
the observed covariate, treatment, and outcome. -/
@[causal_defs_simps]
lemma P_Z_eq : S.P_Z = P.μ.map S.factualZ := rfl

/-- The covariate marginal is the image of the population measure under the observed covariate
map. -/
@[causal_defs_simps]
lemma P_X_eq : S.P_X = P.μ.map S.factualX := rfl

/-- The true nuisance is the pair of value-space outcome and treatment
regressions. -/
noncomputable def η₀ : PLRNuisance γ :=
  ⟨S.lVal, S.mVal, S.lVal_meas, S.mVal_meas⟩

/-- The target parameter is the structural slope in the partially linear model. -/
noncomputable def θ₀ : ℝ := S.θ

/-- The residual second moment measures treatment variation left after
partialling out the covariate.

It is the magnitude of the partialling-out Jacobian. -/
noncomputable def residSecondMoment : ℝ :=
  ∫ ω, (S.factualD ω - S.mVal (S.factualX ω)) ^ 2 ∂P.μ

/-- The partially linear moment instance plugs the Robinson partialling-out
score into the abstract double-machine-learning framework.

It uses the true regression pair as nuisance, the structural slope as target,
covariate-law L² seminorms for nuisance errors, and a Jacobian equal to minus
the residual treatment variance. -/
noncomputable def plrGeneralMoment :
    GeneralMoment P.Ω P.μ (γ × ℝ × ℝ) S.P_Z (PLRNuisance γ) where
  m := plrMomentFunctional
  η₀ := S.η₀
  θ₀ := S.θ₀
  H_ε := Set.univ
  ρ₁ := fun η η' =>
    ⟨max ((eLpNorm (fun x => η.lFn x - η'.lFn x) 2 S.P_X).toReal)
         ((eLpNorm (fun x => η.mFn x - η'.mFn x) 2 S.P_X).toReal),
     le_max_of_le_left ENNReal.toReal_nonneg⟩
  ρ₂ := fun η η' =>
    ⟨max ((eLpNorm (fun x => η.lFn x - η'.lFn x) 2 S.P_X).toReal)
         ((eLpNorm (fun x => η.mFn x - η'.mFn x) 2 S.P_X).toReal),
     le_max_of_le_left ENNReal.toReal_nonneg⟩
  m_meas := fun η θ => measurable_plrMomentFunctional η θ
  η₀_mem := Set.mem_univ _
  J₀ := -S.residSecondMoment
  J₀_ne_zero := neg_ne_zero.mpr S.nondegenerate

/-- Integrating a measurable function under the joint observed-data law equals
integrating its pullback under the population measure.

This is the bridge between abstract observed-data moment statements and
population-level potential-outcome facts. -/
lemma integral_P_Z {f : γ × ℝ × ℝ → ℝ} (hf : Measurable f) :
    ∫ z, f z ∂S.P_Z = ∫ ω, f (S.factualZ ω) ∂P.μ := by
  rw [P_Z, MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
    hf.aestronglyMeasurable]

/-- **Robinson score at the true nuisance, pulled back to the population space.** For
[the observed data generated from a population outcome `ω`](hyp:ω), [the Robinson
partialling-out score evaluated at the true nuisance pair, true data, and true parameter
equals the true residualized outcome times the true treatment residual](goal).

This helper connects observed-data moment expressions to the potential-outcome
quantities used by the partialling-out identities. -/
lemma plrMomentFunctional_factualZ (ω : P.Ω) :
    plrMomentFunctional S.η₀ (S.factualZ ω) S.θ₀
      = (S.factualY ω - S.lVal (S.factualX ω)
          - S.θ * (S.factualD ω - S.mVal (S.factualX ω)))
        * (S.factualD ω - S.mVal (S.factualX ω)) := by
  rfl

end PLRSystem

end PLR
end Estimation
end Causalean
