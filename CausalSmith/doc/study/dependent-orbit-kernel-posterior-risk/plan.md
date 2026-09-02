## Done
- Ground-truth audit completed for `Model.lean`, `Lower.lean`, `Upper.lean`, and `Main.lean`; all required declarations are fully proved.
- Library searches confirmed reuse of `FinitePosteriorBayesRisk`, `FiniteKernelBayes`, and `FiniteSquaredLoss` minimax APIs; no named primary source required fetching.
- Verified every source file directly with `lake env lean` and built `CausalSmith.Substrate.DependentOrbitKernelPosteriorRisk.Main` successfully.
- Source audit found zero `sorry`, `admit`, `native_decide`, or custom `axiom` occurrences.
- Axiom audit of the square-completion, infimum, lower-minimax, Jensen, range-preservation, and upper-minimax results found only `propext`, `Classical.choice`, and `Quot.sound`.
- Confirmed imports remain within Mathlib, Causalean, and this substrate tree; no research module is imported.
- Reviewed the API against the requirement: predictive normalization and null fibers, exact square completion and posterior optimality, averaged minimax lower transport, guarded barycenter range preservation, dependent Jensen, and statewise-to-minimax upper transport are all present without support assumptions or weakened conclusions.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Keep the three-layer split: `Model.lean` for experiments, `Lower.lean` for posterior-risk lower bounds, and `Upper.lean` for barycenter upper bounds, with `Main.lean` as the public entry point.
- Use unrestricted real decisions for posterior optimality and transport the resulting lower bound to the existing bounded-procedure minimax API.
- Use zero on null predictive fibers and a caller-supplied interval-bounded default on null design fibers.
- Advance to review; no filler subagents are needed because the verified tree has no open proofs.