## Done
- `Main.lean`: all fiber-mass, guarded conditional-weight/mean, zero-fiber safety, disintegration, interval-preservation, and squared-loss contraction declarations are proved.
- Re-ran project search; existing `FiniteDesign.map`/`E_map` and `FiniteRaoBlackwell` patterns remain the appropriate dependencies.
- Verified the live source with `lake env lean`; zero errors and zero `sorry`/`admit`/`native_decide`/custom axioms.
- Target build succeeds. `#print axioms` for all 15 theorems reports only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), never `sorryAx`.
- Audited the statements against the requirement: arbitrary nonnegative finite-design weights, guarded null fibers, exact disintegration, pointwise interval preservation, and covariate-parametric squared-loss contraction are retained without uniformity, independence, surjectivity, or full-support assumptions.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Ready for review; no filler subagents are needed.
- Keep the focused 281-line `Main.lean` module and its clean dependency layer.
- The standard reference is the generic finite conditional-expectation/Jensen construction rather than a named primary source, so no source fetch was applicable.
- Existing unused-`Fintype` linter warnings are harmless and match the requirement's finite-type context.