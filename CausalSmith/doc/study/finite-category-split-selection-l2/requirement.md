# Substrate requirement: finite-category-split-selection-l2

## Goal

Formalize reusable L2 transfer for a finite branch selected by an independent
pilot sample, together with a finite-category pilot-count mass sandwich.  The
substrate must be neutral product-law/sample-splitting infrastructure: it must
not mention ATEs, heavy/light Chebyshev estimators, minimax rates, or any paper
calibration.

## Provides (API contract)

1. For a probability space carrying independent measurable pilot and tail
   coordinates, a finite selector `select : alpha -> iota`, and branch errors
   `err : iota -> beta -> Real`, prove an API equivalent to

   ```text
   IndepFun.integral_finiteSelector_sq_le:
     IndepFun pilot tail mu ->
     Measurable pilot -> Measurable tail ->
     Measurable select ->
     MeasurableSet good ->
     (forall a in good, Eligible (select a)) ->
     (forall i, Eligible i ->
       integral b, (err i b)^2 d(mu.map tail) <= V) ->
     integral omega in pilot ⁻¹' good,
       (err (select (pilot omega)) (tail omega))^2 dmu <= V.
   ```

   Equivalent formulations using a finite sum over `iota` are acceptable.
   Supply the measurability and integrability variants needed to compose this
   with iid finite-product sample splits.  Also expose a bad-event corollary:
   if the squared error is pointwise at most `H` and
   `mu (pilot ⁻¹' goodᶜ) <= delta`, the full integral is at most
   `V + H * delta`.

2. For iid observations with measurable label into a finite category type,
   define a pilot category count on an arbitrary finite coordinate block.
   At an arbitrary positive threshold `t`, prove lower- and upper-mass
   misclassification Chernoff bounds and a union-bound sandwich.  An intended
   headline is

   ```text
   finiteCategoryPilot_bad_probability
   ```

   whose good event guarantees simultaneously that every selected category has
   mass at least a supplied lower band and every rejected category has mass at
   most a supplied upper band.  Retain the cardinality factor and explicit
   exponential tail; do not specialize constants or impose asymptotic alphabet
   restrictions.

3. A thin iid half-split corollary may package the independent pilot/tail maps
   for `Fin n` samples, but the main selector theorem should remain useful for
   any pair of independent measurable functions.

## Statement / milestones

Prove finite-selector expansion by measurable disjoint indicators, factor the
pilot and tail integrals using independence, sum the uniform fixed-branch L2
bound, and derive the bad-event corollary.  Separately prove the binomial count
tails and finite-category union bound, then expose a composition-friendly good
pilot event.

## Standard reference

This is finite conditioning by enumeration: partition the pilot space by the
selected branch, use independence to factor each pilot indicator from the tail
squared error, and sum.  The pilot sandwich is the standard multiplicative
Chernoff bound for binomial counts plus a union bound over categories.

## Proposed imports

- `Causalean.Stat.SampleSplit.OneShot`
- `Causalean.Mathlib.IndepIntegral`
- `Causalean.Stat.Sample.PiTransport`
- `Mathlib.Probability.ProductMeasure`
- targeted Bernoulli-count and Chernoff modules

The study must not import any `CausalSmith.Stat.*_Research` module.

## Exact paper-local residual after substrate

1. Instantiate the deterministic half split, observation category `Obs.x`, and
   selector given by the thresholded `pilotCount`.
2. Supply the fixed-selected-set light covariance bound from
   `linear_mark_factorial_covariance` and the paper-local deterministic-set
   marked-factorial bias bound.
3. Supply the fixed-heavy-set real-mark ratio bound from the separate
   `finite-stratum-marked-ratio-mse` study.
4. Choose the paper constants `256`, `4096`, the logarithmic degree, cutoff,
   and alphabet range; absorb the cardinality-weighted pilot tail against the
   coefficient growth.
5. Handle clipping, zero fallback, final polynomial rate, and executable
   program certification locally.

## Intended reuse

The API applies to cross-fitted model selection, sample-split thresholding,
post-stratification, marked-species estimators, and other finite pilot-selected
estimators analyzed through uniform fixed-branch L2 bounds.

## May assume / must derive

May assume standard Mathlib independence, map-measure, finite-sum, binomial,
and Chernoff facts.  Must derive the finite-selector L2 factorization, bad-event
extension, iid split bridge, and finite-category mass sandwich with zero-count
and empty-category cases totalized.

## Non-goals

- No ATE model, overlap, outcome-moment, Chebyshev, minimax, or rate theorem.
- No constants `256` or `4096`, and no `d <= c n log n` premise.
- No premise that directly assumes the selected random-branch risk bound.
- No `sorry`, custom axiom, `admit`, or `native_decide`.

## Known building blocks

- `Causalean.Stat.SampleSplit.OneShot` supplies reusable split maps.
- `Causalean.Mathlib.IndepIntegral` supplies independence/integral
  factorization primitives.
- The accepted binary discrete-ATE `PilotSandwich` and pilot-conditioning files
  are paper-scoped prototypes only; they may be consulted but not imported.
