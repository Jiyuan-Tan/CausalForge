## Done

- `FinitePosterior.lean`: all declarations proved, including guarded posterior normalization/safety, disintegration, numerator identity, exact square completion, posterior-mean optimality, risk infimum, and finite-design Bayes-risk identification.
- `ContinuousMixture.lean`: all declarations proved, including induced-design compatibility, mixed Bayes-risk identification, and explicit integrated-risk lower-bound transfers.
- Reuses indexed Causalean results `inducedFiniteDesign_expectedLoss_eq_mixedKernelLoss` and `realBayesRisk_eq_inducedFiniteDesignBayesRisk`.
- Both source files pass direct `lake env lean`; the targeted module build succeeds.
- Source audit finds no `sorry`, `admit`, `native_decide`, or custom `axiom`. Headline `#print axioms` audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Null-fiber posterior weights are zero; normalization is stated on positive fibers with separate zero-fiber safety.
- Kernel probabilities, risks, and infima remain in native `ℝ` without an `ENNReal` bridge.
- Targets may depend on observations via `t : S → X → ℝ`; `statewiseSquaredLoss` connects estimators to existing finite-design and mixture APIs.
- Continuous transfer retains explicit estimatorwise compatibility and lower-bound premises. No concrete external primary source was named; canonical in-repository results were used.