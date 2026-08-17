## Done

- All declarations in `Basic`, `Transcendental`, `ComplexExp`, `CircleSchedule`, `Program`, and `Contour` are proved; source grep finds no `sorry`, `admit`, `axiom`, `opaque`, or `native_decide`.
- Executable rational rectangles/names, Taylor/intersection transcendental semantics, guarded arithmetic, shared schedules/traces, circle endpoints, compositional node-width propagation, contour containment/width, and reciprocal-`max` specialization are present.
- Fresh source checks (`lake env lean` on every file in dependency order) and `lake build CausalSmith.Substrate.ComplexCertifiedContourSemantics.API` succeed with warnings only.
- Axiom audit of the main transcendental, circle, propagation, generic contour, and specialization theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Exact `Real.pi`, `Complex.exp`, and the circle integral occur only as semantic targets/proof specifications; returned enclosures are computed from rational primitives and recursive finite intersections.
- Fixed-input sine/cosine/exp bounds retain input diameter; effective convergence is proved only after refining the certified input name.
- One `Schedule` is used definitionally by execution, trace events, mesh/fuel selection, and split node/mesh/quadrature budgets; node width is derived compositionally rather than supplied as a premise.
- The SIAM reference confirms set-image interval operations and division guarded by `0 ∉ Y`; project search identified and the implementation reuses the promoted deterministic quadrature enclosure/width lemmas.
