# Substrate requirement: real_valued_vc_subgraph_covering

## Goal

Formalize an arbitrary-probability-measure covering theorem for bounded real-valued VC-subgraph classes, suitable for empirical-metric Dudley chaining.

## Provides (API contract)

- A paper-agnostic theorem in `Causalean.Stat.Concentration.Covering` turning a finite VC-subgraph or pseudo-dimension certificate for a uniformly bounded real-valued class into a polynomial `L²(Q)` covering bound, uniformly over every probability measure `Q`.
- Closure interfaces sufficient for fixed finite sums/products, bounded finite-dimensional linear parameters, and composition with a VC family of indicators.
- A bridge from the arbitrary-`Q` result to empirical measures of finite samples, so the existing fixed-sample Dudley and symmetrization APIs can consume it.

Exact names and the internal combinatorial representation may follow the existing `VCCovering`, `HausslerPacking`, and `DudleyEntropy` APIs. A theorem only for one fixed population measure, or only for binary indicator classes, does not satisfy the contract.

## Statement / milestones

1. Define or reuse the real-valued subgraph/pseudo-dimension notion and connect it to the existing finite VC combinatorics.
2. Prove a polynomial covering-number estimate in `L²(Q)` for every probability measure `Q`, with envelope-relative radius `ε U`, `0 < ε ≤ 1`.
3. Establish the finite algebraic closure lemmas needed for bounded polynomial score classes with moving-center ball indicators and bounded coefficient vectors.
4. Provide the empirical-measure specialization and a small example consumed by fixed-sample Dudley chaining.
5. Verify zero `sorry`, zero new axioms, full target build, source grep, and `#print axioms`.

## Standard reference

This is the classical polynomial entropy bound for uniformly bounded VC-subgraph classes (equivalently finite pseudo-dimension), uniform over probability measures, together with its standard finite-algebra closures.

## Intended reuse

The immediate consumer is `stat_bdd_uniform_log_penalty`: its winsorized moving-center local-polynomial score class needs a uniform empirical-metric cover before the existing symmetrization and Dudley layers apply. The result is paper-agnostic and reusable across nonparametric regression, empirical-process bounds, policy learning, and uniform causal estimators.

## May assume / must derive

May use the proved Causalean finite-VC, Haussler packing, fixed-sample Dudley, separability, and symmetrization layers, plus Mathlib finite-dimensional norm and measure APIs. Must derive the real-valued arbitrary-measure covering bridge and its empirical specialization. Do not assume the target expected maximal inequality or any paper-specific score bound.

## Non-goals

Do not formalize the CTY law class, signed-distance geometry, winsorized estimator, hard-square family, or minimax theorem. Do not bake `h`, `B`, local-polynomial bases, or a particular score space into the public theorem.

## Known building blocks

Start from `Causalean.Stat.Concentration.Covering.VCCovering`, `HausslerPacking`, `DudleyEntropy`, `Separable`, and `Causalean.Stat.Concentration.Rademacher.Symmetrization`. The current APIs cover binary/factored finite VC localization and fixed-sample Dudley, but not the required real-valued moving-parameter class uniformly over arbitrary `Q`.
