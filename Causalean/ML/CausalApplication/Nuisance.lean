/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.CausalApplication.RegressionBridge
import Causalean.Estimation.ATE.Score.AIPWMoment

/-! # ML learners as causal nuisance estimators

Using the conditional-expectation bridge (`RegressionBridge`), the population
targets of the `Causalean.ML` learners are exactly the causal nuisance functions
that the AIPW / DML machinery consumes: the squared-loss target on a treatment arm
is the outcome regression `μ(d, x) = E[Y ∣ X, D=d]`, and the squared-loss target
on the treatment indicator is the propensity `e(x) = P(D=1 ∣ X)`.
`mlNuisanceVec` packages two such targets into the `Estimation.ATE.NuisanceVec`
the AIPW moment expects.
-/

namespace Causalean.ML.Causal

open MeasureTheory

variable {γ : Type*} [MeasurableSpace γ]

/-- **Outcome-regression recovery.** On the covariate–outcome law of treatment arm
`d`, the squared-loss ML population target (an `IsL2Projection`) is the outcome
regression `μ(d, x) = E[Y ∣ X = x, D = d]`. -/
theorem mlOutcomeRegression_ae_eq
    (Pd : Measure (γ × ℝ)) [IsFiniteMeasure Pd] {m : γ → ℝ} (hm : Measurable m)
    (hY : Integrable (fun z => z.2) Pd) (hmint : Integrable (fun z => m z.1) Pd)
    (hproj : Causalean.ML.IsL2Projection Pd m) :
    (fun z => m z.1) =ᵐ[Pd] (Pd[fun z => z.2 | covarSigma (X := γ)]) :=
  condExp_of_isL2Projection Pd hm hY hmint hproj

/-- **Propensity recovery.** On the covariate–treatment-indicator law, the
squared-loss population projection of the treatment indicator is the propensity,
the conditional expectation of treatment given covariates. -/
theorem mlPropensity_ae_eq
    (Pe : Measure (γ × ℝ)) [IsFiniteMeasure Pe] {e : γ → ℝ} (he : Measurable e)
    (hD : Integrable (fun z => z.2) Pe) (heint : Integrable (fun z => e z.1) Pe)
    (hproj : Causalean.ML.IsL2Projection Pe e) :
    (fun z => e z.1) =ᵐ[Pe] (Pe[fun z => z.2 | covarSigma (X := γ)]) :=
  condExp_of_isL2Projection Pe he hD heint hproj

/-- Package ML-learned outcome arms `μ_fn` and propensity `e_fn` into the AIPW
nuisance vector consumed by `Estimation.ATE`. -/
noncomputable def mlNuisanceVec
    (μ_fn : Bool → γ → ℝ) (e_fn : γ → ℝ)
    (hμ : ∀ b, Measurable (μ_fn b)) (he : Measurable e_fn) :
    Causalean.Estimation.ATE.NuisanceVec γ where
  μ_fn := μ_fn
  e_fn := e_fn
  μ_meas := hμ
  e_meas := he

end Causalean.ML.Causal
