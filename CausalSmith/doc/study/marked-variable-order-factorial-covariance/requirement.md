# Substrate requirement: marked-variable-order-factorial-covariance

## Goal

Build reusable covariance infrastructure for normalized ordered injective
product statistics of different orders, including one square-integrable marked
coordinate and mutually exclusive finite labels. The substrate must stop before
any paper-specific Chebyshev-coefficient summation and must not state
`linear_mark_factorial_covariance` or its `6^(2*K)` conclusion.

## Provides (API contract)

1. A finite type `PartialMatching r s`, or an equivalent bijection between
   subsets of `Fin r` and `Fin s`, together with matching size and the fixed-size
   family `partialMatchingsOfSize r s h`. Prove
   `card = Nat.choose r h * Nat.choose s h * h.factorial`.
2. A normalized ordered-product statistic compatible with
   `Causalean.Stat.uStatisticOrder`: for coordinate functions
   `f : Fin r -> X -> Real`, average `prod i, f i (sample (t i))` over
   injective `t : Fin r -> Fin n`, normalized by `n.descFactorial r`.
3. A mixed-order partial-matching product or covariance identity. For orders
   `r,s`, expand the product/covariance of the normalized statistics as a finite
   sum over partial matchings. A size-`h` matching has normalization
   ```
   (n.descFactorial (r + s - h) : Real) /
     ((n.descFactorial r : Real) * (n.descFactorial s : Real))
   ```
   and its product-law moment is obtained by merging the matched coordinate
   factors. Hypotheses should be limited to probability, measurability, and
   integrability of the finitely many merged products; an L2 sufficient wrapper
   is acceptable. Expose the `h = 0` centered correction explicitly.
4. Mixed-order normalization bounds: if `r <= R`, `s <= R`, and
   `4 * R^2 <= n`, then the size-`h` ratio is at most `exp 1 / n^h`, and the
   disjoint correction is at most `2 * R^2 / n`.
5. Optionally, a thin specialization `oneMarkSelectorKernel` for a finite label
   map `cell : X -> iota`, an arm map, and a mark `v : X -> Real`, exposing the
   merged-factor cases: no coincident marks uses first moments, coincident marks
   uses one truncated second moment, and incompatible labels give zero. Its
   conclusion must remain a pairwise/matching bound, never the paper's summed
   Chebyshev rate.

Equivalent canonical formulations are acceptable if they compose to all four
required bullets without hiding the desired covariance conclusion in a bespoke
structure.

## Statement / milestones

Construct the partial-matching type and prove its fixed-size cardinality; define
the normalized ordered-product statistic; prove the unequal-order product or
covariance expansion with the h = 0 centered correction exposed; and prove the
stated factorial-ratio and disjoint-correction bounds under `4 * R^2 <= n`.

## Standard reference

The standard framework is Hoeffding's overlap enumeration for U-statistic
products and covariance, together with the falling-factorial count of pairs of
injective tuples classified by their shared sample indices. The requested
extension allows unequal orders and a square-integrable marked coordinate.

## Proposed imports

- `Causalean.Stat.UStatistic.OrderM.Variance` for ordered tuples, product-law
  transport, and L2 infrastructure.
- Selected generic overlap facts from
  `Causalean.Stat.UStatistic.OrderM.RemainderSecondMoment` only if generalized
  to unequal orders; do not inherit its first-degeneracy premise.
- `Mathlib.Data.Fintype.CardEmbedding`.
- `Mathlib.Probability.ProductMeasure`.
- Targeted covariance and integral modules as required.

The study substrate must not import any `CausalSmith.Stat.*_Research` module.

## Staging prerequisite

Extract or generalize the factorial normalization inequalities currently in
`CausalSmith/Stat/STAT_DiscreteAteMinimaxLoggap_Research/Helpers/FactorialMoments.lean`
(the `factorial_ratio_bound` and `factorial_cross_ratio_bound` cluster) into
`CausalSmith/CausalSmith/Substrate/MarkedVariableOrderFactorialCovariance/`, or
prove equivalent generic lemmas there. Keep compatibility wrappers in the
accepted sibling research module if later promotion moves them.

## Exact paper-local residual after substrate

- Prove the bridge from `allBlockOrderedMarkedFactorial` to the generic
  ordered-product statistic at order `j + 2`, including denominator positivity.
- From `RealLaw.arm_outcome_factorization`, `outcomeMean_eq`, mean
  normalization, and `SecondCentralMoment`, derive `abs z_ak <= s_ak / 2` and
  `E[(Y/M)^2 * 1{X=k,A=a}] <= (5/4) * s_ak`, plus the required measurability and
  integrability facts.
- Instantiate the matching identity for the mark, cell, and arm indicator
  pattern; eliminate incompatible cross-cell/arm matches and separate
  mark-mark, other within-cell, and disjoint cross-cell terms.
- Prove or reuse `shiftedCoefficient K j = gCoefficient K j`, apply the
  coefficient envelope, use `p_k <= B/4` and
  `4 * (K + 2) / m <= 3 * B/4`, and perform the paper-specific summations to
  obtain `linear_mark_factorial_covariance`.

This residual remains part of the paper contribution and may not be moved into
the substrate gate.

## Intended reuse

The infrastructure supports covariance calculations for mixed-order factorial
estimators with unbounded but square-integrable marks, including marked
species-count, causal, and missing-data estimators. It fills the gap between
fixed-order Hoeffding projection theory and binary multinomial factorial-count
covariance calculations.

## May assume / must derive

May assume existing Mathlib probability, finite-combinatorics, product-measure,
integral, and exponential-inequality APIs, plus the paper-independent ordered
tuple and U-statistic infrastructure already in Causalean. Must derive the
partial-matching count, unequal-order product/covariance decomposition, merged
product-law moment representation, and normalization bounds. Any factorial-ratio
fact currently available only in a paper research module must be generalized or
reproved in the neutral study tree; the reusable substrate may not import that
paper module.

## Non-goals

- No ATE model class, overlap assumption, cell-mass cutoff, estimator selector,
  Chebyshev coefficient sum, minimax risk, or headline rate.
- No assumption that directly implies the paper's covariance lemma.
- No bounded-outcome replacement for the L2 marked-coordinate interface.
- No `sorry`, custom axiom, or paper-specific substrate gate.

## Known building blocks

- `Causalean.Stat.UStatistic.OrderM.Basic` supplies ordered injective tuples,
  fixed-order U-statistics, first projections, and degenerate remainders.
- `Causalean.Stat.UStatistic.OrderM.Variance` and
  `RemainderSecondMoment` supply same-order variance machinery, but currently do
  not provide unequal-order nondegenerate cross moments.
- The accepted discrete-ATE sibling proves scalar falling-factorial
  normalization ratios and binary multinomial monomial covariance. These must
  be generalized or extracted; they do not cover a real L2 mark collision.
