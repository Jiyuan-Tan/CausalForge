# Variance-adaptive expected maximal inequality for VC-type real classes

## Goal

Build a reusable Causalean theorem for a countable real-valued function class
on a probability space whose expected empirical supremum adapts to the class's
L² radius rather than only its envelope.

## Provides

- A countable-class variance-adaptive expected maximal inequality.
- A statement directly usable without a continuum-supremum measurability assumption.
- Optionally, a set/range wrapper compatible with the existing covering API.

## Statement / milestones

Assume:

- every indexed function is measurable;
- the class has a constant envelope `U`;
- every function has `L²(P)` norm at most `σ`, with `0 < σ < U`;
- the class has polynomial `L²(Q)` covering numbers, uniformly over the
  finitely supported probability measures `Q` used by the empirical metric,
  with the standard normalization `A ≥ exp(1)` and exponent `v ≥ 1`.

Prove a universal-constant bound of the standard variance-adaptive form

    E sup_f |n⁻¹ ∑ᵢ (f(Xᵢ) - P f)|
      ≤ C [σ * sqrt(v * log(A * U / σ) / n)
             + v * U * log(A * U / σ) / n]

for `n ≥ 1`, allowing harmless equivalent normalizations of the logarithm
such as `log(max e (A * U / σ))`.  The theorem should be stated so a
countable enumeration can be used directly, avoiding any continuum-supremum
measurability assumption.  A set/range wrapper is welcome if it makes the
existing covering API easier to consume.

The proof should combine symmetrization, localization/truncation or peeling,
the empirical `L²` covering bound, and Dudley chaining.  It must retain the
variance-sensitive `σ` leading term; an envelope-only `U / sqrt(n)` estimate
does not discharge the consumer.

## Standard reference

The standard empirical-process variance-adaptive VC-type maximal inequality,
proved by symmetrization, empirical L² entropy, localization or peeling, and
Dudley chaining. Harmless equivalent logarithmic normalizations are allowed.
The lower bounds `A ≥ exp(1)` and `v ≥ 1` are the canonical VC-type
normalization and prevent the false vanishing-rate singleton edge case.

## Intended reuse

The immediate paper-local adapter is
`CausalSmith.Stat.BddUniformLogPenalty.vcEntropy_chaining_bound` in
`CausalSmith/Stat/STAT_BddUniformLogPenalty_Research/Causal/EmpiricalProcess/EntropyChaining.lean`.
It then feeds `vcExpectedMaximalInequality` and the frozen theorem
`cty_winsorized_score_maximal_bound`. The theorem is otherwise a reusable
concentration primitive for bounded real-valued VC-type classes.

## May assume / must derive

May assume and reuse:

- `Causalean.Stat.Concentration.Covering.RealValuedVCSubgraph.Basic`
- `Causalean.Stat.Concentration.Covering.RealValuedVCSubgraph.Algebra`
- `Causalean.Stat.Concentration.Covering.RealValuedVCSubgraph.Parametric`
- `Causalean.Stat.Concentration.Covering.RealValuedVCSubgraph.Empirical`
- `Causalean.Stat.Concentration.Covering.DudleyEntropy`
- `Causalean.Stat.Concentration.Rademacher.Symmetrization`
- `Causalean.Stat.Concentration.UniformDeviation.LocalizedEnvelopeExpectation`

In particular, inspect and reuse `HasPolynomialL2Cover`,
`real_vcSubgraph_empirical_l2_covering`,
`real_vcSubgraph_empirical_coveringNumber_le`, and
`real_vcSubgraph_dudley_example`.  The last theorem is currently only a
fixed-sample, envelope-scale signed-Rademacher bound, so an additional
variance-localization argument is required.

Must derive the variance-sensitive `σ` leading term and the second-order
`U/n` term; an envelope-only bound is insufficient.

The promoted module must import only Mathlib/Causalean modules, never a
`CausalSmith/*_Research` module.  Deliver a zero-`sorry`, zero-new-axiom build,
reachable from `Causalean.lean`, with docstrings/index/embeddings/docs updated
under the normal study-promotion workflow.
