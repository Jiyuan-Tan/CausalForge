# Substrate requirement: complex-certified-contour-semantics

## Goal
Build a reusable, executable and proof-carrying semantics for certified complex
transcendental evaluation and finite contour quadrature over nested rational
rectangle names. The API must support a canonical finite rational contour
program without wrapping exact transcendental or contour-integral values.

## Provides (API contract)
- Certified complex rectangle names whose fuel-indexed enclosures contain one
  complex value, are nested by recursive finite intersection, and converge in
  width.
- Certified rational enclosures of `π`, `sin`, `cos`, and complex `exp`, with
  soundness and effective convergence when their input names refine.
- Sound rectangle addition, subtraction, multiplication, guarded division,
  and modulus/square-root bounds, with explicit width propagation.
- Circle-node semantics for `ρ * exp(2π i q/N)`, including the endpoint used
  by deterministic quadrature.
- A shared schedule record connecting the operation counts, input precision,
  mesh, fuel, and split error budgets used by both implementation and proofs.
- A finite contour-evaluation theorem: under a certified denominator-away-from-
  zero condition, the returned rectangle contains the normalized exact contour
  integral, and its real projection has width at most a requested tolerance.
- A specialization yielding width at most `1 / max n 1`, suitable for bounding
  the midpoint error of a canonical finite-rational statistic.

## Statement / milestones
1. Extend the existing real `CertifiedContourIntervalArithmetic` API with
   rational complex rectangles and executable primitive operations. Prove all
   containment and width lemmas without axioms or exact-value wrappers.
2. Define fuel-indexed transcendental outputs by recursively tightening raw
   Taylor/range-reduction enclosures through finite intersections. Prove
   containment, adjacent-fuel subinterval nesting, and convergence. Do not
   infer nesting from rational tolerance order or denominators.
3. Prove `π`, complex exponential, sine, cosine, modulus, and guarded division
   semantics compositionally on refining input names. A fixed nondegenerate
   input interval may not have arbitrarily small image width; convergence must
   include the shrinking input-name diameter.
4. Define one schedule object used definitionally by executable calls, trace
   events, and semantic specifications. Include magnitude-dependent error
   amplification and split node/mesh/quadrature budgets.
5. Prove circle-node containment and deterministic quadrature containment for
   every endpoint actually evaluated.
6. Prove the generic contour evaluation enclosure and width theorem, then its
   `1 / max n 1` specialization.

## Standard reference
Validated numerics and outward-rounded interval arithmetic as in
Moore--Kearfott--Cloud, *Introduction to Interval Analysis*, combined with the
standard Type-2/nested-rational representation of computable real and complex
numbers. Taylor models with explicit remainders, range reduction for elementary
transcendentals, interval extensions, and deterministic trapezoidal/quadrature
error bounds are standard constructions in validated numerics.

## Intended reuse
The immediate consumer is the canonical finite-rational contour estimator in
`stat_sa_plm_cumulant_converse / nongaussian_spectral_annihilation`, especially
its midpoint-accuracy lemma. Keep the API paper-independent: it should also
serve certified argument-principle computations, Fourier/Laplace contour
integrals, and other validated complex numerical procedures.

## May assume / must derive
- MAY reuse the promoted real interval API under
  `Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic`, standard
  Mathlib power-series/Taylor bounds, complex norm algebra, and deterministic
  finite-sum/integral estimates.
- MAY take explicit Lipschitz/derivative and denominator-separation bounds as
  inputs to generic contour enclosure theorems.
- MUST derive all complex/transcendental containment, nesting, width,
  convergence, schedule correspondence, and quadrature semantics.
- MUST provide concrete constructors/implementations. Do not leave contracts
  as uninhabited structures, axioms, `opaque` constants, `sorry`, proof-selected
  search, or wrappers around exact `Complex.exp`, `Real.pi`, `circleIntegral`,
  `sInf`, or zero counts.

## Non-goals (optional)
The PLM model, statistical selector, Rouché argument, empirical-process bounds,
minimax risk proof, and paper-specific contour bank are out of scope. The study
proves reusable certified complex-contour semantics only.

## Known building blocks (optional)
Reuse the existing certified real/interval operations, mesh, quadrature,
finite-search, and API modules in
`Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic`. The earlier
study's promoted argument-principle modules may inform semantics, but the
executable enclosure layer must not assume the paper's result or import any
`CausalSmith.*_Research` module.
