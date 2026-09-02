# Substrate requirement: finite-schedule-continuous-prior-bayes-minimax

## Goal

Prove a reusable real-valued Bayes-to-minimax bridge for finite decision games when a possibly continuous prior is pushed through a measurable probability kernel into the finite state space.

## Provides (API contract)

- A theorem showing that the continuous-prior mixture of kernel-averaged nonnegative real loss for any action is bounded by that action's finite worst-case risk.
- A theorem passing this inequality through the infimum over actions, so the corresponding real-valued Bayes risk is at most `Causalean.Stat.minimaxValue`.
- Convenient specializations for a deterministic measurable map into the finite state and for `Causalean.Experimentation.DesignBased.FiniteDesign`, including finite-sum/integral interchange and boundedness/integrability facts derived from finiteness.

## Statement / milestones

Let `Theta` be a possibly continuous measurable parameter space with probability measure `pi`, let `S` be a finite nonempty state space, let `K` be a measurable probability kernel from `Theta` to `S`, let `A` be a nonempty action space, and let `loss : A -> S -> Real` be nonnegative and finite-state bounded. For every action `a`, prove

`integral theta, integral s, loss a s d(K theta) d pi <= worstCaseRisk loss a`.

Define the corresponding real Bayes risk by taking the infimum over actions, and prove that it is at most `Causalean.Stat.minimaxValue loss`. Derive deterministic-pushforward and `FiniteDesign` corollaries without converting loss or the consumer API to `ENNReal`.

## Standard reference

This is the elementary Bayes-risk lower-bound step in statistical decision theory: an average of statewise risks is bounded by their supremum, and infimizing over decisions preserves the order. `ProbabilityTheory.bayesRisk_le_minimaxRisk` is the existing ENNReal/kernel analogue; this study provides the native real-valued finite-state specialization required by Causalean's minimax API.

## Intended reuse

The immediate consumer uses a smooth continuous prior whose induced distribution or kernel lands in a finite two-arm schedule/effect-triple space with real squared loss. The result must also be reusable by other finite-state statistical decision problems with continuous mixing.

## May assume / must derive

May assume the parameter prior is a probability measure, the kernel is Markov/probability-valued and measurable, the state space is finite and nonempty, the action space is nonempty, and loss is nonnegative. Must derive all finite-state boundedness and integrability facts, the finite-sum/integral interchange, the actionwise average-to-worst-case bound, the infimum/minimax bridge, and deterministic-map and `FiniteDesign` specializations.

## Non-goals (optional)

- Do not formalize the multi-arm schedule kernel, binomial likelihood identity, smooth prior, or coarse minimax lower bound.
- Do not import any `CausalSmith/*_Research` module.
- Do not replace the real-valued API with an `ENNReal` consumer.
- No `sorry`, `admit`, `native_decide`, or custom axioms may remain.

## Known building blocks (optional)

- `Causalean.Stat.Minimax.Basic`
- `Causalean.Experimentation.DesignBased.FiniteDesign`
- `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- `Mathlib.MeasureTheory.Integral.Prod`
- `ProbabilityTheory.bayesRisk_le_minimaxRisk`
