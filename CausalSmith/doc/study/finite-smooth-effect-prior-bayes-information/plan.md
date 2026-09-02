## Done
- Ground-truth audit: `Prior.lean`, `FiniteExperiment.lean`, `VanTreesAssembly.lean`, and the umbrella module contain no `sorry`, `admit`, `native_decide`, or custom `axiom`.
- `Prior.lean`: concrete quartic prior and derivative; nonnegativity/interior positivity; exact ordinary/topological support; strict ambient support and endpoint vanishing; C¹/absolute continuity; normalization; guarded-score measurability/integrability; exact information `10 / a^2` and bound `≤ 40 / a^2`.
- `FiniteExperiment.lean`: counting-integral identities, likelihood normalization, finite differentiation and derivative centering, guarded-score identities, finite Fisher sum, and prior-averaged pointwise information bound.
- `VanTreesAssembly.lean`: non-vacuous finite-model regularity interface, abstract native-real bound `s^2 / (I + P)`, and canonical quartic-prior specialization `s^2 / (I + 40 / a^2)`; downstream `FiniteKernelBayes` import is present.
- Verified by direct Lean checking of the umbrella source and targeted umbrella build; both succeed with no errors or sorry warnings. `#print axioms` on representative prior, information, averaging, and assembly results reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Searched the Causalean index first and reused its observation-dependent van Trees and guarded-information APIs. Fetched and inspected the TeX source of arXiv:2402.01895 as a primary van-Trees/Fisher-information reference.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Retain the scaled quartic beta density: its exact Fisher information constant `10` directly implies the requested `40` bound.
- Keep model-specific absolute-continuity and joint-integrability obligations explicit in `FiniteVanTreesModelRegularity`, while deriving all canonical-prior obligations internally.
- Keep the Bayes-risk and information API entirely in `ℝ`; no desired Bayes/minimax conclusion is assumed.