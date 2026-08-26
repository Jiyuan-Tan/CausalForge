# Substrate requirement: deterministic-experiment-squared-risk-transport

## Goal

Formalize reusable squared-risk transfer through a measurable deterministic
observation map, including its coordinatewise finite-product pushforward.  The
result should turn a source hardness statement quantified over all measurable
estimators into the corresponding hardness statement for an embedded target
experiment when the statistical target changes affinely.  It must not mention
ATEs, binary outcomes, `RealLaw`, clipping constants, or a paper-specific rate.

## Provides (API contract)

Let `mu : Measure X` be a probability measure, `phi : X -> Y` measurable, and
`n : Nat`.  First expose the product transport

```text
(Measure.pi (fun _ : Fin n => mu)).map (fun z i => phi (z i)) =
  Measure.pi (fun _ : Fin n => mu.map phi)
```

with the coordinatewise map's measurability, plus an integral corollary for a
measurable real function on `Fin n -> Y`.

Next define, or work directly with, squared risk

```text
sqRisk law est theta := integral z, (est z - theta)^2 dlaw.
```

For source parameters `j : Iota`, source laws `P j` on `X`, embedded target
laws `Q j` on `Y`, source targets `theta j`, and target targets
`a * theta j + b`, provide a theorem equivalent to

```text
forall_estimator_exists_sqRisk_ge_of_deterministic_affine_transport:
  a != 0 ->
  (forall j, Q j = (P j).map phi) ->
  (forall measurable sourceEst,
     exists j, L <= sqRisk (P j) sourceEst (theta j)) ->
  forall measurable targetEst,
     exists j,
       a^2 * L <= sqRisk (Q j) targetEst (a * theta j + b).
```

The proof must construct the pullback estimator
`sourceEst z = (targetEst (phi z) - b) / a`, prove it measurable, and prove the
exact pointwise/integral loss identity.  Also provide the `Fin n`
coordinatewise-product version so consumers do not have to manually rewrite
`Measure.pi_map_pi`.

An optional generic minimax corollary formulated with `iInf`/`iSup` is welcome,
but the quantified-estimator hardness theorem is mandatory because it composes
with bespoke estimator subtypes and model-class suprema.

## Statement / milestones

Prove coordinatewise measurability, the product pushforward identity, integral
transport, pullback-estimator measurability, the affine squared-loss identity,
and finally transport the source existential hardness witness to the target
experiment.  Cover `n = 0`, empty parameter types (where the hardness premise
is necessarily impossible), arbitrary signs of nonzero `a`, and nonintegrable
risks using Lean's existing integral semantics without laundering through an
undefined-integral branch.

## Standard reference

This is the standard deterministic experiment reduction: every target
estimator pulls back along the observation map, and affine target scaling
multiplies squared loss by `a^2`.  Applying the same map coordinatewise
commutes with iid finite products.

## Proposed imports

- `Causalean.Stat.Sample.PiTransport`
- `Mathlib.MeasureTheory.Constructions.Pi`
- `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- targeted measurable-map and finite-product modules

The study must not import any `CausalSmith.Stat.*_Research` module.

## Exact paper-local residual after substrate

1. Construct the concrete affine binary-to-`RealLaw` law, including observed
   pushforward, arm/cell conditional laws, full-data coupling, outcome means,
   overlap, consistency, exchangeability, moment bounds, and exact homogeneity.
2. Show its observed iid product law is the coordinatewise affine image of the
   binary source product law and its ATE target is multiplied by `M` (with zero
   affine offset for the contrast).
3. Pull each clipped real estimator back to a measurable binary estimator and
   invoke the promoted quantified hardness transfer.
4. Keep source-alphabet capping, subclass inclusion, `iInf`/`iSup` comparison,
   strictness of the image, the radial Bernoulli channel, and final rate algebra
   paper-local.

## Intended reuse

The API supports deterministic sufficient-statistic reductions, recodings of
experiments, outcome rescaling, coarsening lower bounds, and minimax subclass
transport under squared loss.

## May assume / must derive

May assume Mathlib's `Measure.pi_map_pi`, `integral_map`, and standard
measurability/algebra facts.  Must derive the exact coordinatewise transport,
pullback estimator, affine risk identity, and quantified hardness conclusion.

## Non-goals

- No causal model, binary experiment, `RealLaw`, overlap, homogeneity, minimax
  rate, alphabet cap, or paper constants.
- No premise directly asserting the target risk lower bound.
- No use of `bayesRisk` as a substitute for the quantified squared-risk claim.
- No `sorry`, custom axiom, `admit`, `native_decide`, or hidden integrability
  assumption that excludes legitimate nonintegrable estimators.

## Known building blocks

- `Causalean.Stat.Sample.PiTransport` contains finite-product sample transport
  and related integral identities, but not the affine squared-risk/hardness API.
- Mathlib's generic Bayes-risk data-processing theorem is a near miss: this
  consumer uses squared loss and a bespoke measurable-estimator minimax
  interface rather than the Bayes-risk abstraction.
