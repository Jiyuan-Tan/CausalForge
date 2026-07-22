# Presentation equivalence adjudication — 2026-07-12

P1 flagged two paper statements that overstated their mapped Lean declarations.

- `def:real-atlas-handle` maps correctly to `realAtlasHandleOutput` in `Handles.lean`. The Lean declaration is the cited, general CAD and Tarski--Seidenberg interface; it deliberately does not establish a nonempty paper-specific `RealAtlasCADData m`. The frozen paper body now presents that interface and labels the atlas realization as open.
- `oeq:generic-separation` maps correctly to `genericSeparationQuestion` in `TGenericSeparation.lean`. It is a residual `Prop` recorded as open, not the generic-separation theorem. The frozen paper body now asks the same question and makes its recovery consequence conditional.

The accepted research note was not edited. `def:forward-lvlingam-class` was manually cache-seeded as faithful after a malformed auditor receipt: its frozen body was checked against the accepted graph review and `ForwardLvLiNGAM`, and states every load-bearing witness and constraint. `def:forward-cumulant-map` passed on the fresh audit.
