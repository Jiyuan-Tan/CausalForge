## Status
Round 2. Module COMPLETE and verified from ground truth. `CausalSmith/Substrate/L2ResidualQuadraticProjection/Basic.lean` (namespace `CausalSmith.Substrate.L2ResidualQuadratic`): 0 sorries, 0 diagnostics.

## Done (all proven, no sorry)
- Defs: `moment`, `FiniteMoment4` (int of y,y²,y³,y⁴), `residualQuad`, `l2ResidualQuadratic`, `optIntercept`, `optSlope` (closed form delegated to `Causalean.Stat.MomentEnvelope`).
- `residualQuad_eq` — ∫-to-moment bridge (ring-expand + term-by-term integral split; const term via `IsProbabilityMeasure`).
- `residualQuad_opt_eq` (attainment), `l2ResidualQuadratic_le` (infimum lower bound), `l2ResidualQuadratic_nonneg`, `iInf_residualQuad` (headline `⨅ b₀ b₁, ∫(y²−b₀−b₁y)² = l2ResidualQuadratic`, via `le_antisymm` + `ciInf_le`/`le_ciInf`).

## Verification this turn
- LSP full-file diagnostics: empty (clean).
- `lean_verify` on `iInf_residualQuad` and `residualQuad_eq`: axioms = {propext, Classical.choice, Quot.sound} only — no sorryAx.
- rg: no `sorry` in file.
- Hand-checked `MomentEnvelope.momentResidual` numerator = required Hankel form `(m₄−m₂²)−(m₃−m₁m₂)²/(m₂−m₁²)` after common sign flip → l2ResidualQuadratic genuine, not laundered.

## Remaining
None.

## Blocked
None.

## Decisions
- Reuse Causalean MomentEnvelope for all polynomial/SOS algebra; only ∫-expansion + ciInf bridge are new (matches requirement's "known building blocks").
- Hypotheses `IsProbabilityMeasure`+`FiniteMoment4`+`m₁²<m₂` are the honest, satisfiable domain the requirement permits (positive variance) — not vacuous, not laundering.
- `import Mathlib` retained (avoids import-hunting; sibling study files do same).