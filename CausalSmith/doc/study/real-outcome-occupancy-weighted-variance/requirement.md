# Substrate requirement: real-outcome-occupancy-weighted-variance

## Goal

Formalize the reusable weak-moment noise bound for an occupancy-weighted
collection of within-group treated/control sample means under an i.i.d. product
law. Outcomes may be unbounded. The result must use only arm-group centering,
arm-group L2 bounds, and fixed overlap. It must not mention ATEs, homogeneity,
clipping, Zeng et al., `frontierRate`, or any paper theorem.

## Provides (API contract)

Let `Omega` be a measurable observation space, `kappa` a finite measurable
group type, `mu : Measure Omega` a probability law, `group : Omega -> kappa`,
`arm : Omega -> Bool`, `Y : Omega -> Real`, and
`center : Bool -> kappa -> Real`. For a finite sample `z : Fin n -> Omega`,
provide reusable design statistics:

- `groupArmCount z a k := #{i | group (z i) = k and arm (z i) = a}`;
- `groupCount z k := groupArmCount z false k + groupArmCount z true k`;
- `usableGroup z k` when both arm counts are positive;
- `usableGroupTotal z`, the sum of group counts over usable groups;
- the totalized arm residual mean, zero when its count is zero;
- `occupancyWeightedResidual`, the totalized statistic
  `1 / R * sum k usable N_k * (residualMean true k - residualMean false k)`,
  with value zero at `R = 0`.

All public definitions need measurability lemmas sufficient for integration
under `Measure.pi`.

Under the assumptions below, provide `occupancyWeightedResidual_memLp_two` and
an explicit-constant theorem, or an existential corollary, equivalent to

```text
integral_occupancyWeightedResidual_sq_le_reciprocal:
  integral z, (occupancyWeightedResidual mu group arm Y center z)^2
    d Measure.pi (fun _ : Fin n => mu)
  <= C(epsilon) * V^2 *
    integral z, (if 0 < usableGroupTotal group arm z
      then (usableGroupTotal group arm z : Real)^(-1) else 0)
      d Measure.pi (fun _ : Fin n => mu).
```

Here `0 < C(epsilon)` depends only on `epsilon`; an explicit fixed multiple of
`1 / (epsilon^2 * (1 - epsilon))` is preferred. The theorem must remain valid
for `n = 0`, empty group types, zero-mass groups, and all empirical zero-count
boundaries.

## Statement / milestones

For each arm/group event `E(a,k) = {omega | group omega = k and arm omega = a}`
and residual `r(a,k,omega) = Y omega - center a k`, assume:

1. `group`, `arm`, and `Y` are measurable;
2. the supported residual `E(a,k).indicator (r a k)` belongs to `L2(mu)`;
3. `integral omega in E(a,k), r a k omega d mu = 0`;
4. `integral omega in E(a,k), (r a k omega)^2 d mu
   <= (mu E(a,k)).toReal * V^2`;
5. `0 < epsilon`, `epsilon <= 1/2`, and for every positive-mass group and
   either arm, `epsilon * (mu {omega | group omega = k}).toReal
   <= (mu E(a,k)).toReal`.

Derive finite-product orthogonality of different-coordinate residuals,
same-coordinate cross-label vanishing by disjoint support, diagonal
residual-square comparison from the L2 envelope, and the design-only
reciprocal-count step. Conditional on group count `m` and usability, the two
arm counts are binomial with parameter in `[epsilon, 1-epsilon]`, hence their
inverse counts are `O_epsilon(1/m)`; summing over usable groups yields the
advertised `O_epsilon(1/R)` bound.

Conditioning may be implemented by finite design pushforward and count
enumeration; do not require a new regular-conditional-probability framework.
If useful, expose a generic totalized inverse-binomial interior-event bound.

## Standard reference

This is the standard conditional-variance calculation for stratified or
post-stratified differences of sample means, combined with elementary inverse
binomial-count bounds. The proof conditions on the finite group/arm design,
uses centered independent residuals to remove cross-coordinate terms, and
then averages the reciprocal arm counts.

## Proposed imports

- `Causalean.Stat.Sample.PiTransport`
- `Causalean.Mathlib.Probability.VarianceProd` if genuinely needed
- `Mathlib.Probability.ProductMeasure`
- `Mathlib.Data.Nat.Choose.Sum`
- targeted Bochner integral and `MemLp` modules

The study must not import any `CausalSmith.Stat.*_Research` module. The binary
finite-space implementation in
`STAT_DiscreteAteMinimaxLoggap_Research/Helpers/HeavyCellMoments.lean` is only
a prototype and may not be a promoted dependency.

## Exact paper-local residual after substrate

1. Import the promoted module, intended as
   `Causalean.Stat.Sample.OccupancyWeightedMean`.
2. Instantiate `Omega := Obs d`, `kappa := Fin d`,
   `mu := P.law.observedLaw`, `group := Obs.x`, `arm := Obs.a`,
   `Y := Obs.y`, `center := P.law.outcomeMean`, and `V := M`.
3. Reuse `observed_arm_cell_centered_integral_eq_zero` and
   `observed_arm_cell_centered_sq_integral_le`; prove only the supported
   residual `MemLp 2` bridge if the generic API requires it.
4. Prove the extensional bridge from the unclipped collision expression minus
   `collisionDesignCenter P` to `occupancyWeightedResidual`, including equality
   of generic counts and `armCount`, `cellCount`, `usableCell`, `usableTotal`.
5. Combine the promoted square-integral bound with
   `integral_collisionDesignCenter_bias_sq_le`, clipping contraction, and a
   standard squared-sum inequality.
6. Apply `ZengUsableOccupancyReciprocal`, then `occupancy_max_rate_le` and
   `exp_neg_div_absorbed_by_linear_rate`, and choose one positive
   `C_epsilon` dominating the paper-local noise, bias, tail, and rate terms.

These steps remain part of the paper contribution and may not be moved into
the reusable substrate.

## Intended reuse

The API supports weak-moment post-stratified, causal, missing-data, and survey
estimators whose weights depend only on finite group/arm occupancy, while the
outcomes themselves are real-valued and merely square-integrable.

## May assume / must derive

May assume standard Mathlib product-measure, finite-sum, binomial, integral,
and `MemLp` facts, plus existing generic Causalean sample transport. Must derive
the product-coordinate orthogonality, diagonal L2 comparison, totalized
inverse-count control, and final reciprocal-usable-total integral inequality.
Zero-mass groups and zero empirical denominators must be proved safe rather
than excluded by assumptions.

## Non-goals

- No ATE model class, approximate homogeneity, clipping, occupancy-tail
  citation, minimax risk, or final frontier rate.
- No bounded-outcome or finite-outcome replacement for the L2 interface.
- No premise that directly states the desired paper theorem or its risk bound.
- No `sorry`, custom axiom, `admit`, `native_decide`, or hidden strengthening.

## Known building blocks

- `Causalean.Stat.Sample.PiTransport` supplies reusable product-law transport.
- `Causalean.Mathlib.Probability.VarianceProd` supplies finite-product variance
  infrastructure where applicable.
- The accepted binary helper
  `integral_coordinate_designWeight_residual_sq_le_indicator` demonstrates the
  replacement-coordinate factorization in a finite binary-outcome model, but
  it does not cover a general real L2 mark or the full reciprocal-count
  assembly required here.
