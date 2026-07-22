/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# DR-Learner CATE estimator and its oracle

This file defines the one-shot DR-Learner CATE estimator and its oracle
counterpart, as defined in
`doc/basic_concepts/po/estimation/dr_learner_cate.tex`
(`def:est-cate-dr-learner`):

    τ̂^{DR}_n(x) := Ê_{n,B}{ φ̂_n(Z) | X = x },
    τ̃_n(x)     := Ê_{n,B}{ φ_0(Z) | X = x },
    R^*_n(x)^2 := E[ (τ̃_n(x) - τ_0(x))^2 ].

The second-stage regression operator `Ê_{n,B}` is supplied as an abstract
`SecondStageOperator P.Ω P.μ γ`, and the pseudo-outcomes `phi_eta` / `phi₀`
come from `Causalean.Estimation.CATE.Core.PseudoOutcome`.

The declarations are thin definitional wrappers around the abstract
second-stage regression operator.
-/

import Causalean.Estimation.CATE.Core.PseudoOutcome
import Causalean.Estimation.OrthogonalMoments.SecondStageOperator

/-! # DR-Learner CATE Estimator

This file defines the doubly robust learner for conditional average treatment
effects using an abstract second-stage regression operator. It also defines the
oracle version `drOracleEstimator` that uses the true pseudo-outcome, the
associated pointwise risk scale `drOracleRiskScale`, and the unfolding lemma
`drOracleEstimator_eq_oracleEstimator` for connecting the CATE-specific API to
the generic second-stage-operator API. -/

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory ProbabilityTheory Filter Topology
  Causalean.PO Causalean.Estimation.ATE Causalean.Estimation.OrthogonalMoments

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **DR-Learner CATE estimator** at `x` (Def `def:est-cate-dr-learner`,
`τ̂^{DR}_n(x)`).

Given a CATE estimation system `S`, an abstract second-stage regression
operator `op` over the data law context `(P.Ω, P.μ)`, and a sequence of
estimated nuisance vectors `η_hat n ω` (trained on the nuisance fold encoded
in `ω`), the DR-Learner at sample size `n`, randomness `ω`, and query point
`x` is the operator applied to the uncentered AIPW pseudo-outcome
`φ_{η_hat n ω}`.

The system parameter `_S` is kept in the signature for API symmetry with
`drOracleEstimator` / `drOracleRiskScale`, even though the estimator itself
only depends on `η_hat`. -/
noncomputable def drLearnerEstimator
    (_S : CATEEstimationSystem P γ)
    (op : SecondStageOperator P.Ω P.μ γ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (n : ℕ) (ω : P.Ω) (x : γ) : ℝ :=
  op.evalAt n ω (fun z => phi_eta z (η_hat n ω)) x

/-- **Oracle DR-Learner** at `x` (Def `def:est-cate-dr-learner`, `τ̃_n(x)`).

The oracle counterpart of `drLearnerEstimator` substitutes the true pseudo-
outcome `φ_0` (built from the truth nuisance `η₀` carried by the back-door
substrate of `S`) in place of the estimated pseudo-outcome. -/
noncomputable def drOracleEstimator
    (S : CATEEstimationSystem P γ)
    (op : SecondStageOperator P.Ω P.μ γ)
    (n : ℕ) (ω : P.Ω) (x : γ) : ℝ :=
  op.evalAt n ω (fun z => phi₀ S z) x

/-- **Oracle pointwise risk scale** `R^*_n(x)` (Def `def:est-cate-dr-learner`).

This specializes `SecondStageOperator.oracleRiskScale` to the AIPW pseudo-
outcome `φ_0` and the value-space CATE target `τ_val`:

    R^*_n(x) := sqrt( ∫ (op.evalAt n ω φ_0 x - τ_val x)^2 ∂P.μ ).

It is the L²(P.μ) deviation of the oracle DR-Learner from the CATE target at
the fixed query point `x`, treated as a deterministic function of `n`. -/
noncomputable def drOracleRiskScale
    (S : CATEEstimationSystem P γ)
    (op : SecondStageOperator P.Ω P.μ γ)
    (x : γ) (n : ℕ) : ℝ :=
  op.oracleRiskScale (fun z => phi₀ S z) S.τ_val x n

/-- Sanity unfolding: `drOracleEstimator` is the abstract `oracleEstimator`
of `op` applied to the true DR pseudo-outcome `φ_0`. -/
lemma drOracleEstimator_eq_oracleEstimator
    (S : CATEEstimationSystem P γ)
    (op : SecondStageOperator P.Ω P.μ γ) :
    drOracleEstimator S op = op.oracleEstimator (fun z => phi₀ S z) := rfl

end CATE
end Estimation
end Causalean
