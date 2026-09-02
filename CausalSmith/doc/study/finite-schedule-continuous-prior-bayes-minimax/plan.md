## Done
- `Core.lean`: all finite-range, integrability, kernel measurability, finite-sum interchange, actionwise mixture bound, and real Bayes-to-minimax declarations are proved.
- `Deterministic.lean`: all pullback-integrability, deterministic-kernel rewrite, Bayes equality, and minimax specialization declarations are proved.
- `FiniteDesign.lean`: all arbitrary-design facts, `inducedFiniteDesign` fields, expectation equality, Bayes equality, and minimax specialization declarations are proved.
- Ground-truth verification: direct `lake env lean` checks and targeted builds of all three modules succeed; source/import scans are clean; all theorem axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
- Searched Causalean first and reused `Causalean.Stat` minimax lemmas plus `FiniteDesign.toMeasure`/`integral_toMeasure`; fetched Mathlib's canonical `ProbabilityTheory.bayesRisk_le_minimaxRisk` source at the pinned dependency revision.

## Remaining
- None: zero `sorry`, `admit`, `native_decide`, custom axioms, or hard build errors.

## Blocked
- None.

## Decisions
- Keep the public loss/risk API in `ℝ`; singleton measure masses use `.real` only internally.
- Derive boundedness and integrability from finite `S`, without exposing extra boundedness assumptions.
- Represent the continuous-prior/kernel mixture as an induced `FiniteDesign` while retaining arbitrary-design and deterministic-map APIs.
- Existing unused-variable/Fintype linter messages are non-failing generality warnings and do not affect correctness or applicability.