## Done

- `Basic.lean`: all definitions closed.
- `IntegrationByParts.lean`: all AC/product integration-by-parts lemmas closed.
- `GuardedInformation.lean`: guarded-score zero-set algebra, score centering, and information decomposition closed.
- `WeightedL2.lean`: product Fubini and weighted L2 Cauchy–Schwarz closed.
- `Main.lean`: `observation_dependent_van_trees` closed with an observation-dependent target and explicit product-measure hypotheses.
- Re-ran library/Mathlib searches and inspected the canonical `Causalean.Stat.Limit.van_trees_inequality` source.
- Source scan finds no `sorry`, `admit`, `native_decide`, custom `axiom`, or research-module import.
- Diagnostics report no errors; `lake build +CausalSmith.Substrate.ObservationDependentVanTreesAc.Main` succeeds.
- Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Oriented interval helpers retain `a ≤ b`; reversed-endpoint versions are false.
- Density-zero algebra is explicit through `jointScore_mul_jointDensity` and `errorScoreField_eq_numerator`.
- Derivative representatives are joint-a.e. under `parameterMeasure.prod μ`, enabling both section orders via product swap and Fubini.
- Expectations remain product-measure weighted integrals, and the target remains observation-dependent.
- The API is genuine and non-vacuous; the module is ready for review.