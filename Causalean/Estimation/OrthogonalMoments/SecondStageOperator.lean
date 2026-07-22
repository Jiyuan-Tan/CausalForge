/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Abstract second-stage regression operator for the DR-Learner CATE estimator

This file provides the abstract `SecondStageOperator` bundle described in
`doc/basic_concepts/po/estimation/dr_learner_cate.tex`
(`def:est-cate-second-stage`, `def:est-cate-stability`, `thm:est-cate-dr-oracle`).

The operator takes:
* a sample-size index `n`,
* a randomness scope `Ω` (carrying the data fold and any auxiliary randomness),
* a real-valued pseudo-outcome `f : γ × Bool × ℝ → ℝ` defined on data tuples
  `z = (x, a, y)`, and
* an evaluation point `x : γ`,

and returns a real number `̂E_{n,B}{f(Z) | X = x}`.

The structure here is deliberately abstract: the linear-smoother specialisation
lives in `Causalean/Estimation/OrthogonalMoments/LinearSmoother.lean`, and callers supply a
`BiasIdent` predicate to `Stable` / `oracle_expansion` to encode the
conditional-bias identification (e.g. AIPW DR cross-product = condExp at fold A).

`oracle_expansion` is fully proved (one-line application of `Stable`).
-/

import Causalean.Stat.Limit.Convergence
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Abstract Second-Stage Regression Operators

This file defines the target-agnostic second-stage operator used in DR-Learner
CATE estimation. The public API consists of `SecondStageOperator`, the
input-linearity predicate `SecondStageOperator.IsLinearInInput`, the oracle
estimator and oracle risk scale, the stability predicate `Stable`, and the
abstract oracle-expansion theorem `oracle_expansion`. It separates the operator
itself from linearity and conditional-bias identification assumptions. -/

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory Filter Topology Causalean.Stat

/-- Abstract bundle for a second-stage regression operator (Def
`def:est-cate-second-stage`).

* `evalAt n ω f x` is the operator at sample size `n`, randomness scope `ω : Ω`,
  applied to the pseudo-outcome `f : γ × Bool × ℝ → ℝ` and evaluated at the
  query point `x : γ`.
* `meas_evalAt_const` is a minimal joint-measurability assumption: for every
  fixed constant pseudo-outcome `(fun _ => c)` the resulting
  `(ω, x) ↦ evalAt n ω _ x` is jointly measurable. Stronger measurability
  assumptions (e.g. measurability in the function argument) are deferred to
  concrete instances.

The linearity of the operator in its function input is **not** required by the
structure; instead it is supplied as the separate predicate `IsLinearInInput`
below. This keeps the structure usable for nonlinear smoothers (e.g. local
constant regression). -/
structure SecondStageOperator
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (γ : Type*) [MeasurableSpace γ] where
  evalAt : ℕ → Ω → (γ × Bool × ℝ → ℝ) → γ → ℝ
  meas_evalAt_const :
    ∀ (n : ℕ) (c : ℝ),
      Measurable (fun (p : Ω × γ) => evalAt n p.1 (fun _ => c) p.2)

namespace SecondStageOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {γ : Type*} [MeasurableSpace γ]

/-- Linearity of the operator in its pseudo-outcome input. A second-stage
operator is *linear in input* iff
`evalAt n ω (f + g) x = evalAt n ω f x + evalAt n ω g x` for all sample sizes,
randomness, pseudo-outcomes, and query points. Linear smoothers satisfy this
predicate; kernel-or-tree mean estimators with random splits need not satisfy
it. -/
def IsLinearInInput (op : SecondStageOperator Ω μ γ) : Prop :=
  ∀ (n : ℕ) (ω : Ω) (f g : γ × Bool × ℝ → ℝ) (x : γ),
    op.evalAt n ω (fun z => f z + g z) x =
      op.evalAt n ω f x + op.evalAt n ω g x

/-- Oracle estimator: the operator applied to a fixed "true" pseudo-outcome
`f` (Def `def:est-cate-dr-learner`, `\tilde\tau_n`). -/
def oracleEstimator (op : SecondStageOperator Ω μ γ)
    (f : γ × Bool × ℝ → ℝ) : ℕ → Ω → γ → ℝ :=
  fun n ω x => op.evalAt n ω f x

/-- Oracle pointwise risk scale `R^*_n(x)` from `def:est-cate-dr-learner`:

  `R^*_n(x) := sqrt( ∫ (op.evalAt n ω f x - target x)^2 ∂μ )`.

This is the L²(μ) deviation of the oracle estimator from `target` at the
fixed query point `x`, treated as a deterministic function of `n`. -/
noncomputable def oracleRiskScale
    (op : SecondStageOperator Ω μ γ) (f : γ × Bool × ℝ → ℝ)
    (target : γ → ℝ) (x : γ) (n : ℕ) : ℝ :=
  Real.sqrt (∫ ω, (op.evalAt n ω f x - target x) ^ 2 ∂μ)

end SecondStageOperator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {γ : Type*} [MeasurableSpace γ]

/-- Stability of a second-stage regression operator at a query point `x` with
respect to a distance `d_n` between pseudo-outcomes
(Def `def:est-cate-stability`).

For every sequence of estimated pseudo-outcomes `fHat_n` and every true
pseudo-outcome `f`, with claimed conditional bias `bHat_n`, if `d_n →_p 0` and
the user-supplied conditional-bias identification predicate `BiasIdent`
holds, then the operator-level discrepancy between `evalAt _ fHat_n` and
`evalAt _ f`, *minus* the smoothed bias term `evalAt _ (bHat_n)`, is
`o_p(R^*_n(x))`.

`BiasIdent` encodes the concrete conditional-bias identification (e.g.
`bHat_n n ω u =ᵐ μ[fHat_n n ω Z − f Z | A_σ(n), σ(X) = u]` for a DR-Learner
with the AIPW pseudo-outcome). Concrete instances pass their explicit
identification predicate. -/
def Stable
    (op : SecondStageOperator Ω μ γ) (target : γ → ℝ)
    (d_n : ℕ → Ω → ℝ) (x : γ)
    (BiasIdent :
      (ℕ → Ω → γ × Bool × ℝ → ℝ) →
      (γ × Bool × ℝ → ℝ) →
      (ℕ → Ω → γ → ℝ) → Prop) : Prop :=
  ∀ (fHat_n : ℕ → Ω → γ × Bool × ℝ → ℝ) (f : γ × Bool × ℝ → ℝ)
    (bHat_n : ℕ → Ω → γ → ℝ),
    Tendsto_inProb d_n (fun _ => 0) μ →
    BiasIdent fHat_n f bHat_n →
    IsLittleOp
      (fun n ω =>
        op.evalAt n ω (fHat_n n ω) x - op.evalAt n ω f x
          - op.evalAt n ω (fun z => bHat_n n ω z.1) x)
      (fun n => SecondStageOperator.oracleRiskScale op f target x n) μ

/-- **Oracle expansion for the DR-Learner** (Thm `thm:est-cate-dr-oracle`,
abstract operator-level form).

Given a stable operator at `x`, a consistent first-stage in the stability
distance `d_n`, and a conditional-bias identification witness for the
caller-supplied `BiasIdent`, the operator-level oracle expansion holds modulo
`o_p(R^*_n(x))`.

The model-specific input — Prop `prop:est-cate-dr-bias-identity` — enters
through `hBias : BiasIdent …`, which the caller supplies.

NOTE: statement is the operator-level conclusion `̂E{fHat} − ̂E{f} − ̂E{bHat} =
o_p(R^*_n(x))`; the rearrangement to `\hat\tau^{DR}_n(x) - \tilde\tau_n(x)
= ̂E{bHat_n} + o_p(R^*_n(x))` is bookkeeping handled at the application site. -/
theorem oracle_expansion
    (op : SecondStageOperator Ω μ γ) (target : γ → ℝ) (x : γ)
    (d_n : ℕ → Ω → ℝ)
    (fHat_n : ℕ → Ω → γ × Bool × ℝ → ℝ) (f : γ × Bool × ℝ → ℝ)
    (bHat_n : ℕ → Ω → γ → ℝ)
    (BiasIdent :
      (ℕ → Ω → γ × Bool × ℝ → ℝ) →
      (γ × Bool × ℝ → ℝ) →
      (ℕ → Ω → γ → ℝ) → Prop)
    (hStab : Stable op target d_n x BiasIdent)
    (hCons : Tendsto_inProb d_n (fun _ => 0) μ)
    (hBias : BiasIdent fHat_n f bHat_n) :
    IsLittleOp
      (fun n ω =>
        op.evalAt n ω (fHat_n n ω) x - op.evalAt n ω f x
          - op.evalAt n ω (fun z => bHat_n n ω z.1) x)
      (fun n => SecondStageOperator.oracleRiskScale op f target x n) μ := by
  exact hStab fHat_n f bHat_n hCons hBias

end OrthogonalMoments
end Estimation
end Causalean
