## Done

- `Selector.lean`: proved selector-cell and square measurability, eligible-on-good-event integrability, exact finite selector-cell expansion, uniform eligible-branch L2 transfer, and the bounded bad-event extension.
- `PilotCount.lean`: proved category count identities, arbitrary-block tilted Chernoff tails, measurable mass-sandwich event, and cardinality-weighted bad-event bounds, including the explicit `±log 2` corollary.
- `OneShot.lean`: proved the IID one-shot fold bridge using `OneShotSplit.folds_indep` and measurable finite-product maps.
- Verified every source and umbrella module by direct Lean typechecking; targeted build succeeds; integrity grep is clean; principal theorem axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Require fixed-branch square integrability for eligible branches; measurability alone is unsound under Lean's non-integrable Bochner-integral convention.
- Derive integrability only on the good-event pullback; ineligible selector cells are empty.
- Keep the selector theorem generic over arbitrary independent pilot/tail maps and isolate IID splitting in a thin adapter.
- Retain `0 ≤ V`, arbitrary finite blocks and tilts, explicit cardinality factors, and empty-case totalization.
- Reuse existing independence, split, and binomial-MGF infrastructure. No primary paper was named, and no paper-local module is imported.