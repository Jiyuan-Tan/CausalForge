## Done

- `ProductTransport.lean`: proved `measurable_finCoordinatewise`, `map_pi_finCoordinatewise`, and `integral_comp_finCoordinatewise` using Mathlib's `Measure.pi_map_pi` and `integral_map`.
- `AffineRisk.lean`: defined `sqRisk` and `affinePullbackEstimator`; proved pullback measurability, exact pointwise affine squared-loss identity, exact mapped-risk identity, and `forall_estimator_exists_sqRisk_ge_of_deterministic_affine_transport`.
- `FiniteProduct.lean`: proved `forall_estimator_exists_sqRisk_ge_of_deterministic_affine_transport_pi`; the umbrella module exports the full API.
- Ground-truth verification this round: all four source modules pass direct `lake env lean`; targeted umbrella `lake build` succeeds; Lean-LSP reports zero errors in every implementation file; source audit finds no `sorry`, `admit`, `axiom`, or `native_decide`; all eight public theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining

- None.

## Blocked

- None.

## Decisions

- `sqRisk` uses the real Bochner integral directly, so nonintegrable risks follow Lean's existing integral semantics without an integrability branch.
- Scalar transport permits arbitrary source measures; product transport assumes probability factors, exactly supplying `Measure.pi_map_pi`'s sigma-finiteness and covering `n = 0`.
- No inhabitance assumption on `Iota` and only `a ≠ 0` are imposed, preserving empty parameter types and either sign of `a`.
- Target laws remain explicit through `Q j = (P j).map phi`; the product theorem performs the coordinatewise rewrite for consumers.
- Project and Mathlib searches confirmed the intended reusable primitives; no named primary paper/source was supplied, so no source fetch was applicable. No research module is imported.
