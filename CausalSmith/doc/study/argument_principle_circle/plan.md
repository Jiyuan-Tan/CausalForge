## Done
- `Basic.lean`: definitions, local logarithmic-derivative factorization, and centered-monomial circle integral are proved.
- `ArgumentPrinciple.lean`: finite interior-zero support, `argumentPrinciple_circle`, natural-valuedness, and positivity consequences are proved.
- `Homotopy.lean`: straight-line homotopy invariance, multiplicity-count invariance, `rouche_circle`, and normalized Rouché equality are proved.
- Dependency search found no packaged Causalean/Mathlib argument-principle or Rouché theorem; the implementation uses Mathlib analytic order, meromorphic divisor factorization, Cauchy–Goursat, and circle integrals.
- Ahlfors §5.2 was fetched and checked: it identifies the residue of `f'/f` with zero order and derives Rouché from the strict boundary inequality.
- Fresh direct Lean typechecking of all four source files exited 0; umbrella LSP diagnostics are empty. Source grep found no `sorry`, `admit`, `native_decide`, or custom `axiom`. `#print axioms` for every public theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Keep `AnalyticOnNhd ℂ f (closedBall c R)` and positive radius as the genuine circle hypotheses.
- Represent the count by a natural-valued `finsum` of `analyticOrderNatAt`, accompanied by explicit finite-support and finite-zero-set theorems.
- Factor through Mathlib's meromorphic divisor to prove the global equality; use continuity plus discreteness of natural-valued counts for homotopy invariance.
- The API is non-vacuous and directly supplies the equality, integrality/nonnegativity witness, enclosed-zero positivity, homotopy invariance, and standard Rouché corollaries needed by `ArgumentPrincipleInterface`.
- No filler subagents are needed because zero proof holes remain.