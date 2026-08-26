## Done

- `Design.lean`: all public design statistics and measurability lemmas are proved; no `sorry` remains.
- `Binomial.lean`: all inverse-binomial lemmas are proved; no `sorry` remains.
- `FiniteDesign.lean`: finite arm/group enumeration and `sum_jointWeight_variance_le_inverse` are proved; no `sorry` remains.
- `Variance.lean`: orthogonality, diagonal L2 comparison, `integral_occupancyDesignVarianceFactor_le_reciprocal`, `occupancyWeightedResidual_memLp_two`, and `integral_occupancyWeightedResidual_sq_le_reciprocal` are proved.
- Round-6 verification: direct `lake env lean` checks of all four source files and targeted build of `Variance` succeed with warnings only; source scan is clean.
- Axiom audit for both public endpoint theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Preserve the general measurable observation space, supported real L2 assumptions, explicit measure argument, constant `16 / (epsilon^2 * (1-epsilon))`, and all zero-denominator totalizations.
- Dependencies stay limited to Mathlib, Causalean, and this run tree; do not import paper/research modules or other substrate runs.
- Library search was completed before review; no replacement substrate result was found. No specific primary source is named, so source fetching was skipped.
- The final theorem is genuine and non-vacuous: its assumptions are the required centering, supported L2 envelope, and fixed overlap hypotheses, including totalized zero-count cases.