## Done
- `IIDPoisson.lean`: stream/count product law and finite-prefix product law proved; zero `sorry`.
- `Basic.lean`: finite-sample measurability, count law, and exact fixed-count fibre law proved; zero `sorry`.
- `Partition.lean`: measurable restrictions, normalized cell laws, exact independent joint splitting, and Poisson cell-count marginals proved; zero `sorry`.
- `Superposition.lean`: measurable superposition/mark ordering, canonical restriction and inverse-in-law superposition, a.s.-distinct marks, and exact retained-prefix product laws proved; zero `sorry`.
- `KL.lean`: finite-measure normalization, marked experiment count law, exact equal-mass KL identity, and its upper-bound consequence proved; zero `sorry`.
- 2026-08-10 verification: umbrella build and direct Lean elaboration exit 0; LSP reports no errors in every implementation file; source audit finds no `sorry`, `admit`, `native_decide`, or custom `axiom`; key API theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Keep `FiniteSample X := Σ n, Fin n → X`; fixed-count restrictions encode conditional i.i.d. laws without kernels.
- Keep measurable classifiers and the zero-mass ambient-law fallback; no positivity assumptions were added.
- Use raw arrival order for splitting and canonical mark order for superposition; atomlessness removes sorting ties almost surely.
- Causalean and LeanSearch found scalar-Poisson, multinomial, and generic KL/product ingredients but no ready-made finite marked-Poisson splitting theorem.
- No named paper/source was supplied; local Mathlib sources are the primary reference.
- The completed statements genuinely expose exact independence, inverse-in-law superposition, exact retained `P^n`, and the finite-measure Poisson KL identity without paper-specific assumptions.