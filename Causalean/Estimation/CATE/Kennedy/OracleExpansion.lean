/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Oracle expansion for the DR-Learner CATE estimator

This file proves the oracle expansion of the DR-Learner CATE estimator from
`doc/basic_concepts/po/estimation/dr_learner_cate.tex`, specialised to the AIPW
pseudo-outcomes `phi_eta` / `phi₀`.

Two declarations are provided:

* `dr_oracle_expansion` — direct specialisation of
  `Causalean.Estimation.OrthogonalMoments.oracle_expansion` to the AIPW pseudo-outcomes.
* `dr_oracle_efficient` — corollary: if the smoothed-bias term is
  `o_p(R*_n(x))`, the DR-Learner is oracle-efficient at `x`.

The proofs specialize the abstract second-stage expansion and combine
stochastic-order remainders.
-/

import Causalean.Estimation.CATE.Kennedy.DRLearner
import Causalean.Estimation.CATE.Core.ConditionalBias
import Causalean.Estimation.ATE.Remainder.Identity
import Causalean.Estimation.OrthogonalMoments.SecondStageOperator
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.SampleSplit.OneShot

/-! # DR-Learner Oracle Expansion

This file specializes the abstract second-stage oracle expansion to the
doubly robust pseudo-outcomes used for conditional average treatment effects.
It decomposes the DR-Learner around its oracle estimator and the smoothed
conditional-bias term in `dr_oracle_expansion`, then records the
oracle-efficiency consequence `dr_oracle_efficient` when that bias is
negligible relative to the oracle risk scale. -/

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory ProbabilityTheory Filter Topology
  Causalean.PO Causalean.Stat Causalean.Estimation.ATE Causalean.Estimation.OrthogonalMoments

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **Oracle expansion for the DR-Learner CATE estimator.** Fix a CATE estimation system under
[the back-door causal assumptions](hyp:_hA), a query point `x`, and a sequence of estimated
nuisance vectors `η_hat`. Suppose [the abstract second-stage regression operator `op` is stable
at `x` with respect to a distance `d_n`, meaning the caller-supplied bias-identification
predicate `BiasIdent` correctly separates the operator-level discrepancy between the
estimated-nuisance and true pseudo-outcomes into a bias term plus a negligible
remainder](hyp:hStab); [`d_n` converges to zero in probability](hyp:hCons); and [the contrast
between the AIPW pseudo-outcome built from `η_hat` and the true pseudo-outcome is identified,
through `BiasIdent`, with the closed-form conditional bias `condBias(η_hat, η₀)`](hyp:hBias).
Then [the DR-Learner CATE estimator, minus its oracle counterpart, minus the operator applied to
that closed-form bias, equals `o_p(R*_n(x))`, where `R*_n(x)` is the oracle risk scale at
`x`](goal).

This is the AIPW-specialised form of the abstract second-stage oracle
expansion. The rearrangement to "DR estimate minus oracle estimate equals the
smoothed conditional bias plus a negligible remainder" is bookkeeping. -/
theorem dr_oracle_expansion
    (S : CATEEstimationSystem P γ)
    (_hA : S.toPOBackdoorSystem.Assumptions)
    (op : SecondStageOperator P.Ω P.μ γ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (x : γ)
    (d_n : ℕ → P.Ω → ℝ)
    (BiasIdent :
      (ℕ → P.Ω → γ × Bool × ℝ → ℝ) →
      (γ × Bool × ℝ → ℝ) →
      (ℕ → P.Ω → γ → ℝ) → Prop)
    (hStab : Stable op S.τ_val d_n x BiasIdent)
    (hCons : Tendsto_inProb d_n (fun _ => 0) P.μ)
    (hBias : BiasIdent
              (fun n ω z => phi_eta z (η_hat n ω))
              (fun z => phi₀ S z)
              (fun n ω u => condBias (η_hat n ω)
                            S.toBackdoorEstimationSystem.η₀ u)) :
    IsLittleOp
      (fun n ω =>
        drLearnerEstimator S op η_hat n ω x
          - drOracleEstimator S op n ω x
          - op.evalAt n ω
              (fun z => condBias (η_hat n ω)
                          S.toBackdoorEstimationSystem.η₀ z.1) x)
      (fun n => drOracleRiskScale S op x n) P.μ := by
  unfold drLearnerEstimator drOracleEstimator drOracleRiskScale
  exact Causalean.Estimation.OrthogonalMoments.oracle_expansion op S.τ_val x d_n
    (fun n ω z => phi_eta z (η_hat n ω))
    (fun z => phi₀ S z)
    (fun n ω u => condBias (η_hat n ω) S.toBackdoorEstimationSystem.η₀ u)
    BiasIdent hStab hCons hBias

/-- **Oracle efficiency for the DR-Learner CATE estimator, at a query point `x`** — corollary of
`dr_oracle_expansion`. Under [the back-door causal assumptions](hyp:hA) and the same
operator-stability, consistency, and bias-identification hypotheses as `dr_oracle_expansion` —
[`op` is stable at `x` w.r.t. a distance `d_n`, via the bias-identification predicate
`BiasIdent`](hyp:hStab), [`d_n` converges to zero in probability](hyp:hCons), and [the AIPW
pseudo-outcome contrast is identified with the closed-form conditional bias `condBias(η_hat,
η₀)`](hyp:hBias) — if in addition [that smoothed conditional-bias term, the operator applied to
`condBias(η_hat, η₀)` at `x`, is itself `o_p(R*_n(x))`](hyp:hSmoothedBias), then [the DR-Learner
CATE estimator is oracle-efficient at `x`: it differs from its oracle counterpart by
`o_p(R*_n(x))`](goal). -/
theorem dr_oracle_efficient
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (op : SecondStageOperator P.Ω P.μ γ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (x : γ)
    (d_n : ℕ → P.Ω → ℝ)
    (BiasIdent :
      (ℕ → P.Ω → γ × Bool × ℝ → ℝ) →
      (γ × Bool × ℝ → ℝ) →
      (ℕ → P.Ω → γ → ℝ) → Prop)
    (hStab : Stable op S.τ_val d_n x BiasIdent)
    (hCons : Tendsto_inProb d_n (fun _ => 0) P.μ)
    (hBias : BiasIdent
              (fun n ω z => phi_eta z (η_hat n ω))
              (fun z => phi₀ S z)
              (fun n ω u => condBias (η_hat n ω)
                            S.toBackdoorEstimationSystem.η₀ u))
    (hSmoothedBias : IsLittleOp
      (fun n ω => op.evalAt n ω
        (fun z => condBias (η_hat n ω)
                    S.toBackdoorEstimationSystem.η₀ z.1) x)
      (fun n => drOracleRiskScale S op x n) P.μ) :
    IsLittleOp
      (fun n ω => drLearnerEstimator S op η_hat n ω x
                    - drOracleEstimator S op n ω x)
      (fun n => drOracleRiskScale S op x n) P.μ := by
  have hExp := dr_oracle_expansion S hA op η_hat x d_n BiasIdent hStab hCons hBias
  have hrn_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ drOracleRiskScale S op x n :=
    Filter.Eventually.of_forall (fun n => by
      unfold drOracleRiskScale SecondStageOperator.oracleRiskScale
      exact Real.sqrt_nonneg _)
  have hSum :=
    IsLittleOp.add_eventually_nonneg_rate (μ := P.μ) hrn_nonneg hExp hSmoothedBias
  convert hSum using 1
  funext n ω
  ring

end CATE
end Estimation
end Causalean
