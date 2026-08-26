# Substrate requirement: markov-kernel-squared-risk-transport

## Goal

Formalize reusable squared-risk hardness transport through a randomized Markov
kernel (a Blackwell garbling), including a finite iid/product-channel form.  A
target estimator is pulled back to the source experiment by its kernel
conditional mean; Jensen then shows target squared risk dominates the source
pullback risk.  The result must not mention Bernoulli variables, ATEs,
`RealLaw`, homogeneity, or a paper-specific rate.

## Provides (API contract)

Let `P j : Measure X` be source probability laws, `K : Kernel X Y` a Markov
kernel, and `Q j := K.map (P j)` / `P j ∘ K` in the library's standard
notation.  For a measurable bounded target estimator `T : Y -> Real`, define
its kernel pullback

```text
kernelMean K T x := integral y, T y d(K x).
```

Prove measurability, the tower/integration identity, conditional Jensen for
squared loss, and an API equivalent to

```text
forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport:
  a != 0 ->
  (forall j, Q j = bind/map (P j) K) ->
  (forall measurable bounded sourceEst,
     exists j, L <= sqRisk (P j) sourceEst (theta j)) ->
  forall measurable targetEst bounded,
    exists j,
      a^2 * L <= sqRisk (Q j) targetEst (a * theta j + b).
```

The source estimator should be
`(kernelMean K targetEst x - b) / a`.  Bounds on `targetEst` must imply a
usable bound on the pullback; do not assume its risk inequality directly.
Equivalent formulations with an explicit source-estimator admissibility
predicate are acceptable if they expose the constructed pullback and Jensen
inequality.

Also provide a finite-product form.  Given a Markov probability kernel `K`
applied independently to each coordinate, construct or reuse its `Fin n`
product kernel and prove that applying it to
`Measure.pi (fun _ : Fin n => P)` yields
`Measure.pi (fun _ : Fin n => K.map P)` (or the equivalent bind law).  Export
the quantified squared-risk hardness theorem for this product experiment,
including `n = 0`.

## Statement / milestones

Establish bounded kernel-integral measurability, integral interchange/tower,
pointwise conditional Jensen for `x ↦ (T y - c)^2`, integrate it against the
source law, incorporate the affine target scale, and transport the existential
hardness witness.  Then package independent finite-product kernels and repeat
the argument for sample estimators.

## Standard reference

This is the standard Blackwell comparison for squared loss.  Randomization
cannot improve estimation risk: Rao--Blackwellizing a target-experiment
estimator back to the source experiment weakly decreases squared loss.  An
affine change of estimand multiplies squared loss by the square of its slope.

## Proposed imports

- `Mathlib.Probability.Kernel.Basic`
- `Mathlib.Probability.Kernel.Composition.Comp`
- `Mathlib.Probability.Kernel.Disintegration.StandardBorel`
  only if genuinely necessary
- `Mathlib.MeasureTheory.Integral.Jensen`
- `Causalean.Stat.Minimax.MinimaxRisk`
- `Causalean.Stat.Sample.PiTransport`

The study must not import any `CausalSmith.Stat.*_Research` module.

## Exact paper-local residual after substrate

1. Instantiate the source laws with the capped binary one-arm hard family and
   the kernel with the hypothesis-independent Bernoulli contraction followed
   by affine outcome scaling.
2. Prove the concrete target observed law/product law equals the kernel image,
   and that the source treated-functional separation scales by `M * sigma/2`.
3. Discharge target estimator boundedness from the paper's clipped `Estimator`
   subtype and construct `RiskTransferCertificate` from the promoted theorem.
4. Keep `LeastFavorableHandle`, source caps, class membership, coupling,
   realization-wise radius, TV data processing, constants, and final
   `converseRate` algebra paper-local.

## Intended reuse

The result supports minimax lower-bound transfer under noisy channels,
coarsening, missingness, randomized response, privacy mechanisms, and general
Blackwell comparison of experiments under squared loss.

## May assume / must derive

May assume Mathlib's kernel composition, kernel integrals, Jensen inequality,
and finite-product kernel primitives where available.  Must derive the bounded
pullback estimator, its measurability, the squared-risk comparison, the
quantified hardness conclusion, and the finite-product form.

## Non-goals

- No Bernoulli-specific channel, causal model, ATE, `RealLaw`, radius,
  minimax rate, source cap, or paper constants.
- No premise asserting the target risk lower bound or Jensen comparison.
- No deterministic-only substitute; randomness in the channel is essential.
- No `sorry`, custom axiom, `admit`, `native_decide`, or hidden assumption that
  simply excludes all target estimators.

## Known building blocks

- `Causalean.Stat.forall_estimator_exists_sqRisk_ge_of_deterministic_affine_transport`
  and its `_pi` variant handle deterministic recodings only.
- Mathlib kernels provide map/bind and Jensen ingredients, but repository
  search found no packaged quantified squared-risk hardness transport through
  a randomized channel.
