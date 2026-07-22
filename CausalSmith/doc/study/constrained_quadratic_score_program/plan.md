## Status: round 2 — COMPLETE. Both files compile with zero sorries, zero errors; headline verified with only standard axioms. Ready for review.

Two files under `CausalSmith/Substrate/ConstrainedQuadraticScoreProgram/`, namespace `CausalSmith.Substrate.ConstrainedQuadraticScoreProgram`. Reuses `Causalean.Stat.Nonparametric.L2ResidualQuadratic` (ns `CausalSmith.Substrate.L2ResidualQuadratic`: `moment, optIntercept, optSlope, l2ResidualQuadratic, residualQuad, FiniteMoment4, residualQuad_opt_eq`).

## Done (verified this round from disk + LSP)
- `ProjectionResidual.lean`: `memL2_id, memL2_sq, projResidual_memL2, integrable_projResidual, integral_projResidual, integral_id_mul_projResidual, integral_sq_projResidual, integral_sq_mul_projResidual` — all proven, no sorry. LSP `success:true`, empty diagnostics.
- `ScoreProgram.lean`: `FeasibleScore` (structure), `optScore`, `scoreCost` (defs); `optScore_feasible, optScore_cost, feasibleScore_cost_lower_bound, scoreCost_eq` — all proven, no sorry. LSP `success:true`, empty diagnostics.
- Ground-truth checks this turn: `grep` finds no sorry/admit; `lean_diagnostic_messages` empty for both; `lean_verify` on `scoreCost_eq` and `integral_sq_mul_projResidual` → axioms = {propext, Classical.choice, Quot.sound} only (no sorryAx).

## Remaining
- None.

## Blocked
- None. (Note: `lake build` was not runnable in sandbox in prior rounds due to read-only lock write outside workspace + blocked network; LSP diagnostics + verify used as ground truth instead — both are clean.)

## Decisions
- Hypotheses: `[IsProbabilityMeasure μ] + FiniteMoment4 μ + hnd: moment μ 1^2 < moment μ 2 + hr: 0 < l2ResidualQuadratic μ`. `r>0` is the genuine non-degeneracy (m₁²<m₂ alone doesn't force r>0: 2-pt measure has r=0). Jointly satisfiable (Unif[0,1]) → non-vacuous.
- Feasibility via `MemLp s 2 μ` (honest L², supplies measurability + Integrable s² and s on finite μ).
- Lower bound by COMPLETING THE SQUARE (`∫(s−(x/r)q)² = ∫s² − x²/r ≥ 0`), not a named Cauchy–Schwarz lemma — only integral linearity + `integral_nonneg`.
- Moment lemmas reduce to raw-moment algebra via `optIntercept/optSlope` closed forms + `field_simp[hd]; ring` with `hd: m₁²−m₂≠0`; `∫q²=r` via `residualQuad_opt_eq`.