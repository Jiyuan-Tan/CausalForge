/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.CausalApplication.Nuisance
import Causalean.Estimation.ATE.Score.MeanZero

/-! # End-to-end: ML nuisances → AIPW → the ATE

The payoff of the causal bridge.  When the `Causalean.ML` learners recover the true
nuisances, their packaged `NuisanceVec` makes the AIPW estimating equation
mean-zero at the average treatment effect. The squared-loss recovery statements
live in `ML/CausalApplication/Nuisance`; logistic or other learners can enter this theorem
after their own population-target results show equality with the same true
outcome-regression or propensity functions. This composes the ML side with the
existing `Estimation.ATE` AIPW identification (`aipw_mean_zero`).
-/

namespace Causalean.ML.Causal

open MeasureTheory Causalean.Estimation.ATE Causalean.PO

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **End-to-end identification with ML nuisances.** If ML learners recover the
true outcome regression `μ_val` and propensity `e_val` (correct specification),
their packaged AIPW `NuisanceVec` makes the AIPW moment integrate to zero at the
ATE `θ₀` — the doubly-robust estimating equation identifies the average treatment
effect with machine-learned nuisances. -/
theorem aipw_mlNuisance_meanZero_of_wellSpecified
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε) (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    {mhat : Bool → γ → ℝ} {ehat : γ → ℝ}
    (hmhat : ∀ b, Measurable (mhat b)) (hehat : Measurable ehat)
    (hμ_spec : ∀ b x, mhat b x = S.μ_val b x) (he_spec : ∀ x, ehat x = S.e_val x) :
    (∫ z, BackdoorEstimationSystem.aipwMomentFunctional
        (mlNuisanceVec mhat ehat hmhat hehat) z S.θ₀ ∂ S.P_Z) = 0 := by
  have hηeq :
      mlNuisanceVec mhat ehat hmhat hehat = BackdoorEstimationSystem.η₀ S :=
    NuisanceVec.ext hμ_spec he_spec
  have hfun :
      (fun z => BackdoorEstimationSystem.aipwMomentFunctional
        (mlNuisanceVec mhat ehat hmhat hehat) z S.θ₀) = S.ψ_AIPW := by
    funext z
    rw [hηeq]
    rfl
  rw [hfun]
  exact BackdoorEstimationSystem.aipw_mean_zero_of_square_integrable S h_overlap hA h_y2 h_yd2

end Causalean.ML.Causal
