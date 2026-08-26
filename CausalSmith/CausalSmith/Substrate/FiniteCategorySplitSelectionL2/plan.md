## Done

- `Selector.lean`: proved selector-cell and selected-square measurability, all-branch and eligible-on-good-event integrability, the exact finite selector-cell expansion, the uniform eligible-branch L2 transfer, and its bounded bad-event extension.
- `PilotCount.lean`: proved category-indicator/count identities, arbitrary-finite-block tilted Chernoff tails, the measurable simultaneous mass-sandwich event, and cardinality-weighted bad-event bounds (including an explicit `±log 2` corollary).
- `OneShot.lean`: proved the IID one-shot fold bridge using `OneShotSplit.folds_indep` and measurable finite-product coordinate maps.
- Ground-truth verification this round: every source file and the umbrella module typecheck directly; `lake build CausalSmith.Substrate.FiniteCategorySplitSelectionL2` succeeds; integrity grep is clean; principal theorem axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Require `Integrable` for every eligible fixed-branch square; AEStrong measurability alone is unsound under Lean's non-integrable Bochner-integral convention.
- Derive integrability only on the good-event pullback by partitioning into selector cells; ineligible branches have empty cells.
- Keep the main selector theorem generic over arbitrary independent measurable pilot/tail maps; `OneShot.lean` is only the IID split adapter.
- Retain `0 ≤ V`, arbitrary finite pilot blocks and tilts, explicit category-cardinality factors, and empty-block/category totalization.
- Reuse `integrableOn_finite_iUnion`, `IndepFun.integral_restrict_preimage_eq_mul`, `OneShotSplit.folds_indep`, and `BinomialCount` MGF infrastructure. No primary paper/source was named, so none was fetched; no paper-local module is imported.
