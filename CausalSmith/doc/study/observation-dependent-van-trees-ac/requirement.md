# Substrate requirement: observation-dependent-van-trees-ac

## Goal

Prove a reusable, paper-agnostic van Trees (Bayesian Cramér--Rao) inequality for a sigma-finite dominated observation model whose target may depend on both the parameter and the observation.

## Provides (API contract)

- An observation-dependent van Trees theorem on a real interval with a compactly supported continuously differentiable prior density.
- Reusable lemmas for absolute-continuity product integration by parts, guarded-score algebra on density-zero sets, decomposition of prior plus Fisher information, and the product-measure weighted L2 Cauchy--Schwarz step.

## Statement / milestones

Let `mu` be a sigma-finite measure on an observation space, let `[ell,u]` be a real interval, let `w` be a compactly supported `C1` prior density, let `p(theta,x)` be a dominated likelihood density, let `g(theta,x)` be an observation-dependent target, and let `T(x)` be an estimator. Assume:

- for almost every `x`, the sections `p(.,x)` and `g(.,x)` are `AbsolutelyContinuousOnInterval`;
- `dp` and `dg` are almost-everywhere derivative representatives;
- the guarded joint score is defined on `{w*p > 0}` and handled correctly on density-zero sets;
- the boundary product `w*p*(T-g)` vanishes at both endpoints;
- likelihood normalization and differentiation-under-the-integral give score centering;
- the total prior-plus-Fisher information is positive and finite;
- all signed error-times-score, derivative-product, and weighted-square fields used below are explicitly product-measure `AEStronglyMeasurable` and integrable, with enough cross-integrability for Fubini and weighted L2 Cauchy--Schwarz.

Conclude

`E[(T(X)-g(theta,X))^2] >= E[partial_theta g(theta,X)]^2 / (J(w)+E[I(theta)])`,

with all expectations taken under the joint prior-likelihood law.

## Required derivations

- AC product integration by parts using `AbsolutelyContinuousOnInterval` and a.e. derivatives;
- guarded-score numerator identity, including density-zero cases;
- score centering and exact prior/Fisher denominator decomposition;
- product-measure Fubini/Tonelli exchanges under the explicit joint hypotheses;
- weighted L2 Cauchy--Schwarz and the final ratio inequality.

## Intended reuse

The immediate consumer has a finite discrete observation carrier and will instantiate the theorem with counting measure or finite sums, a smooth compact prior, Bernoulli/binomial likelihood sections, and an observation-dependent conditional target. The theorem must remain independent of that experiment and of all CausalSmith research namespaces.

## Standard reference

This is the observation-dependent-target extension of the van Trees Bayesian Cramér--Rao inequality, proved by integration by parts under the joint prior-likelihood law followed by weighted Cauchy--Schwarz. The parameter-only reference implementation is `Causalean.Stat.Limit.VanTrees`; the absolute-continuity and product-measure steps use the Mathlib modules listed below.

## May assume / must derive

May assume exactly the explicit sigma-finiteness, interval, prior smoothness/support, a.e.-absolute-continuity, derivative-representative, boundary, normalization, positivity/finiteness, joint measurability, and integrability hypotheses stated above. Must derive the guarded-score identity, score centering, prior/Fisher decomposition, all Fubini exchanges, weighted L2 inequality, and final van Trees bound. No target-invariance or parameter-only restriction may be assumed.

## Known building blocks

- `Mathlib.MeasureTheory.Function.AbsolutelyContinuous`
- `Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun`
- `Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable`
- `Mathlib.MeasureTheory.Integral.Prod`
- `Causalean.Stat.Limit.VanTrees`

## Non-goals

- Do not formalize the multi-arm experiment, its binomial prior, or its minimax lower bound.
- Do not import any `CausalSmith/*_Research` module.
- Do not hide joint measurability, Fubini, or integrability obligations behind informal prose or an axiom.
- Do not weaken the result to a parameter-only target.
- No `sorry`, `admit`, `native_decide`, or custom axioms may remain in delivered declarations.
