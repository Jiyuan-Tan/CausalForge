## Done
- `IIDPoisson.lean`: stream/count product law and finite-prefix product law proved; zero `sorry`.
- `Basic.lean`: finite-sample measurability, count law, and exact fixed-count fibre law proved; zero `sorry`.
- `Partition.lean`: partition bridge, normalized cell laws, measurable restrictions, exact independent joint splitting (`map_restrictPartition_finiteMarkedPoissonSampleLaw`), and Poisson cell-count marginal proved; zero `sorry`.
- `Superposition.lean`: measurable superposition/mark ordering, exact canonical restriction and superposition laws, a.s.-distinct marks, and exact retained-prefix product laws proved; zero `sorry`.
- `KL.lean`: finite-measure normalization, marked experiment count law, exact equal-mass KL identity, and upper bound proved; zero `sorry`.
- 2026-08-10 ground truth: umbrella `lake build` and direct `lake env lean` both exit 0; LSP reports no errors in all implementation files; source audit finds no `sorry`, `admit`, `native_decide`, or custom `axiom`; key API theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Keep `FiniteSample X := Σ n, Fin n → X`; fixed-count restrictions encode conditional i.i.d. laws without kernels.
- Keep measurable classifiers and the zero-mass ambient-law fallback; do not strengthen positivity assumptions.
- Raw arrival order is used for splitting; canonical configurations sort by atomless marks. Stable restriction commutes with sorting only after handling ties (a.s. distinct marks).
- Reuse `Measure.map_congr`, `Measure.pi_map_pi`, and the proved raw splitting theorem; current Causalean and LeanSearch checks found scalar Poisson, multinomial, and generic KL/product ingredients but no ready-made finite marked-Poisson splitting/sorting theorem.
- No named paper/source was supplied to fetch; the local Mathlib sources for product maps, finite sorting, and scalar Poisson laws are the primary implementation reference.
- Keep the completed canonical laws `map_restrictPartition_canonicalMarkedPoissonSampleLaw`, `map_superposeByMarks_map_restrictPartition`, and `map_superposeByMarks_canonicalCellLaws`; atomless marks discharge sorting ties almost surely.
