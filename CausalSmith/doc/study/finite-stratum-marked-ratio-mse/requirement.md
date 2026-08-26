# Substrate requirement: finite-stratum-marked-ratio-mse

## Goal

Formalize the fixed-selected-set MSE bound for finite-stratum, occupancy-weighted
arm means with a real square-integrable mark.  The estimator must totalize empty
arm counts and the proof must retain the missing-arm remainder.  It must not
mention pilot selection, ATEs, polynomial estimators, or minimax rates.

## Provides (API contract)

Let `Omega` be measurable, `kappa` finite measurable, `mu : Measure Omega` a
probability law, `group : Omega -> kappa`, `arm : Omega -> Bool`, and
`Y : Omega -> Real`.  For `z : Fin m -> Omega` and a deterministic
`H : Finset kappa`, define category/arm counts, mark sums, totalized arm means,
and the fixed-set score

```text
sum k in H,
  groupCount z k / m *
    (totalizedArmMean z true k - totalizedArmMean z false k).
```

Define the corresponding population target using category masses and
arm-category conditional mark means.  Under assumptions equivalent to

- `q(a,k) >= epsilon * p(k)` for positive-mass categories;
- `B <= p(k)` for every `k in H`;
- `|center a k| <= M`;
- supported arm-category residuals are centered and in L2;
- their square integrals are at most `q(a,k) * M^2`;

provide measurability/MemLp facts, an explicit noise plus missing-arm
decomposition, and a theorem such as

```text
integral_fixedStratumMarkedRatio_error_sq_le
```

with a conclusion of the same scale as

```text
M^2 * (
  8 * (sum k in H, p k) / (m * epsilon)
  + 6 / m
  + 4 * (H.card /
      (((((m - 2 : Nat) : Real) / 2 * epsilon)^2) * B))^2).
```

Constant relaxation or an exponentially damped missing-arm envelope is
acceptable, provided it preserves the parametric `M^2/m` noise scale, composes
under a deterministic mass lower bound, and is uniform at `m = 0`, `B = 0`,
zero-mass strata, and all empirical zero denominators.

If cleaner, expose separate single-arm and signed two-arm theorems.  The public
API should make the fixed-set target and missing-arm term explicit rather than
hiding the desired conclusion in a bespoke premise.

## Statement / milestones

Define the totalized statistics and prove measurability.  Decompose each arm
score into centered noise and a missing-arm bias.  Use iid coordinate
orthogonality and inverse-binomial counts for the noise term; compute or bound
the first and second moments of the aggregate missing-arm count; sum over the
fixed set; combine the two arms into the signed score.

## Standard reference

This is the standard post-stratified ratio calculation for a fixed collection
of strata.  Conditional on stratum occupancy, arm counts are binomial under
overlap.  Centered real marks remove cross-coordinate terms, while the event of
an empty arm produces an exponentially damped remainder controlled by the
stratum mass lower bound.

## Proposed imports

- `Causalean.Stat.Sample.PiTransport`
- `Causalean.Mathlib.Probability.IidMeanVariance`
- `Causalean.Mathlib.Probability.BernoulliMeasure`
- `Mathlib.Probability.ProductMeasure`
- targeted variance, binomial, finite-sum, integral, and `MemLp` modules

The study must not import any `CausalSmith.Stat.*_Research` module.

## Exact paper-local residual after substrate

1. Instantiate `Omega := Obs d`, `kappa := Fin d`, `mu` by the observed law,
   `group := Obs.x`, `arm := Obs.a`, `Y := Obs.y`, and centers by the paper's
   arm-cell outcome means.
2. Bridge the generic count/sum/mean/score to `estimationArmCount`,
   `estimationArmSum`, `estimationArmMean`, and `heavyEmpiricalTerm`.
3. Discharge overlap, centering, mean envelope, and conditional second-moment
   hypotheses from `ModelClass`.
4. Obtain the deterministic pilot-selected set's mass lower bound from the
   separate finite-selector/pilot-sandwich substrate and combine through its
   L2 transfer theorem.
5. Keep light marked-factorial bias/covariance, false-light error, calibrated
   rate algebra, clipping/fallback, and executable complexity paper-local.

## Intended reuse

The result supports fixed-stratum post-stratified means, missing-data scores,
causal contrasts, and marked-species estimators under conditional second
moments without bounded outcomes.

## May assume / must derive

May assume standard Mathlib iid product, binomial, integral, finite-sum, and
`MemLp` facts.  Must derive the centered-noise orthogonality, inverse-count
control, missing-arm first/second moments, finite-set aggregation, signed-arm
combination, and all totalized boundary cases.

## Non-goals

- No pilot selector, Chernoff union bound, ATE model, polynomial approximation,
  clipping, minimax risk, or final rate.
- No bounded-outcome substitute for the L2 mark assumptions.
- No premise directly asserting the fixed-set MSE conclusion.
- No `sorry`, custom axiom, `admit`, or `native_decide`.

## Known building blocks

- `Causalean.Stat.Sample.OccupancyWeightedMean` proves related real-mark
  coordinate orthogonality and inverse-count control for a normalized usable-
  occupancy statistic, but not this fixed-set category-mass-weighted score.
- The accepted binary `HeavyCellMoments`/`HeavyCell` files contain paper-scoped
  prototypes for inverse counts and missing-arm aggregation; they may be
  consulted but cannot be imported or treated as real-mark substrate.
