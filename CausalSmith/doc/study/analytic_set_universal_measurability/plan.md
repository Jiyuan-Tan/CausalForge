## Done
- `Capacity.lean`: defines `ChoquetCapacity`; proves Baire-cylinder compactness machinery, `MeasureTheory.AnalyticSet.isCapacitable`, and that finite Polish Borel measures induce capacities.
- `UniversalMeasurability.lean`: proves `ChoquetCapacity.IsCapacitable.nullMeasurableSet` and the required `MeasureTheory.AnalyticSet.nullMeasurableSet` at full stated generality.
- `UpperSemianalytic.lean`: proves completed measurability and `lintegral_completion_eq_outerLIntegral` for upper-semi-analytic extended-nonnegative functions.
- Ground-truth verification completed: all three source files elaborate directly; targeted import-closure build exits 0; source scan finds no `sorry`, `admit`, `native_decide`, or new `axiom`.
- `#print axioms` for capacitability, universal measurability, completed measurability, and the integral identity reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Keep the genuine Polish/Borel/finite-measure API without strengthened assumptions or special cases.
- Use compact-neighborhood right-continuity in the capacity interface; decreasing-compact continuity alone is insufficient on general non-σ-compact Polish spaces.
- Keep the narrowly scoped pointwise-majorant `outerLIntegral` compatibility API.
- Project and Mathlib searches found no existing universal-measurability theorem to reuse; the completed proof is self-contained over the cited Mathlib primitives.