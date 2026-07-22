/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mean-zero and finite variance of the partially linear score

For the partially linear `GeneralMoment` instance (`plrGeneralMoment`):

* `plr_meanZero` — the score has zero population mean at the truth,
  `E[ψ(η₀, ·, θ₀)] = 0`.  Via change of variables and the regression
  compatibilities this reduces to the orthogonality `E[U·(D − m₀(X))] = 0`.
* `plr_finite_var` — the squared score at the truth is `P_Z`-integrable,
  `E[ψ(η₀, ·, θ₀)²] = E[U²·(D − m₀(X))²] < ∞`.
-/

import Causalean.Estimation.PLR.Setup

/-! # Mean-zero and finite variance for the partially linear score

This file proves the two partially linear score facts consumed by the double
machine-learning engine: `plr_meanZero`, the population mean-zero identity at the
truth, and `plr_finite_var`, finite second moment of the true score under the
observed-data law. -/

namespace Causalean
namespace Estimation
namespace PLR

open MeasureTheory ProbabilityTheory Causalean.PO
open Causalean.Estimation.OrthogonalMoments

namespace PLRSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ] [IsFiniteMeasure P.μ]
variable (S : PLRSystem P γ)

/-- Mean-zero at the truth: `E[ψ(η₀, ·, θ₀)] = 0`. -/
lemma plr_meanZero
    (hU : Integrable S.U P.μ)
    (hUV : Integrable (fun ω => S.U ω * S.toPOPartialLinearModel.resid ω) P.μ)
    (hbX : Integrable (fun ω => S.b (S.factualX ω)) P.μ)
    (hD : Integrable S.factualD P.μ) :
    MeanZero S.plrGeneralMoment := by
  change ∫ z, plrMomentFunctional S.η₀ z S.θ₀ ∂S.P_Z = 0
  rw [S.integral_P_Z (measurable_plrMomentFunctional S.η₀ S.θ₀)]
  have hae :
      (fun ω => plrMomentFunctional S.η₀ (S.factualZ ω) S.θ₀)
        =ᵐ[P.μ] fun ω => S.U ω * S.toPOPartialLinearModel.resid ω := by
    filter_upwards [S.lVal_compat, S.mVal_compat, S.factualY_sub_lReg hD hbX hU]
      with ω hl hm hY
    rw [S.plrMomentFunctional_factualZ ω, hl, hm]
    have hresid : S.toPOPartialLinearModel.resid ω = S.factualD ω - S.mReg ω := rfl
    rw [← hresid, hY]
    ring
  rw [integral_congr_ae hae, S.integral_U_resid hU hUV]

/-- Finite variance of the influence function at the truth. -/
lemma plr_finite_var
    (hsq : Integrable
      (fun ω => (plrMomentFunctional S.η₀ (S.factualZ ω) S.θ₀) ^ 2) P.μ) :
    Integrable (fun z => (plrMomentFunctional S.η₀ z S.θ₀) ^ 2) S.P_Z := by
  have hg : AEStronglyMeasurable
      (fun z => (plrMomentFunctional S.η₀ z S.θ₀) ^ 2) S.P_Z :=
    ((measurable_plrMomentFunctional S.η₀ S.θ₀).pow_const 2).aestronglyMeasurable
  change Integrable (fun z => (plrMomentFunctional S.η₀ z S.θ₀) ^ 2) (P.μ.map S.factualZ)
  rw [MeasureTheory.integrable_map_measure hg S.measurable_factualZ.aemeasurable]
  exact hsq

end PLRSystem

end PLR
end Estimation
end Causalean
