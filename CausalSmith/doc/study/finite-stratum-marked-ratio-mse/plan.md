## Done
- Ground-truth scan found zero `sorry`, `admit`, `native_decide`, or custom `axiom` occurrences in the six substrate modules.
- `Basic.lean`: totalized counts, sums, arm means, scores, targets, measurability, exact centered-noise/mass-fluctuation/missing-arm decomposition, and center-target identification are closed.
- `MissingMoments.lean` and `MissingBound.lean`: exact missing-count first/second/cross moments, exponential and lower-mass envelopes, and the missing-remainder bound are closed.
- `NestedCountBound.lean` and `CenteredNoiseBound.lean`: inverse nested-count control and `integral_fixedStratumArmCenteredNoise_sq_le` are closed.
- `Main.lean`: MemLp results, mass-fluctuation bound, exponential and deterministic-lower-mass single-arm bounds, and `integral_fixedStratumMarkedRatio_error_sq_le` are closed.
- Fresh source-level `lake env lean` checks passed for all six files; targeted `lake build CausalSmith.Substrate.FiniteStratumMarkedRatioMse.Main` completed successfully with warnings only.
- Axiom audit of eleven central declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Imports are confined to Mathlib, Causalean, and this substrate tree; no paper/research module or prohibited paper-local concept occurs.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Ready for review: the API is genuine and non-vacuous, retains an explicit missing-arm remainder/envelope, and handles `m = 0`, `B = 0`, zero-mass strata, and empirical zero denominators through totalized definitions.
- The signed theorem uses a universal constant relaxation and the boundary-safe `lowerMassMissingEnvelope`; `lowerMassMissingEnvelope_eq_of_pos` exposes the advertised inverse-polynomial formula when `m ≥ 3`, `epsilon > 0`, and `B > 0`.
- Library search confirmed reuse of Causalean occupancy-weighted residual orthogonality, inverse-binomial, IID mean, and product-measure infrastructure. No primary paper/source was named in the requirement, so no source fetch applied.
- No filler subagents are needed because no open proof obligations remain.