## superpop_network_mean_clt — status ledger

### Module layout (all under `CausalSmith.Substrate.SuperpopNetworkMeanClt`)
- `Field.lean` — `centeredNormalizedField` (the `NetworkDependence` whose summand is `(Yᵢ−E[Yᵢ])/s`) + `@[simp]` unfolders `centeredNormalizedField_X`, `centeredNormalizedField_adj`.
- `Hypotheses.lean` — the three engine hypotheses, derived: `centeredNormalizedField_integral_eq_zero` (mean-zero), `centeredNormalizedField_sq_integral` (unit total variance), `centeredNormalizedField_abs_le` (uniform bound `≤ 2c/s`).
- `MeanCLT.lean` — `networkMean_clt` (corollary of `Causalean…networkSum_clt`).

Engine (sibling package): `Causalean.Experimentation.SuperPopulation.networkSum_clt`, built on `stein_cdf_clt_of_depGraph`. Reduction pattern mirrored: `Causalean.Experimentation.DesignBased.prodDesign_clt`.

## Done (VERIFIED this round from ground truth)
- `lake build CausalSmith.Substrate.SuperpopNetworkMeanClt.MeanCLT` → exit 0, only linter warnings (unused `DecidableEq`/`IsProbabilityMeasure` section vars; signatures intentionally unchanged).
- `grep sorry` over the three `.lean` files → NONE (only prose hits in `plan.md`).
- `lean_verify networkMean_clt` → axioms `{propext, Classical.choice, Quot.sound}` only; no `sorryAx`. Genuine proof.
- `Field.lean`: structure assembled; `meas` proven; `adj/refl/symm/decAdj` inherited; `indep` closed via `IndepFun.comp` through affine measurable standardization map; simp unfolders proven.
- `Hypotheses.lean`: all three lemmas proven (mean-zero via `integral_div`+`integral_sub`; unit variance via `variance_add_const`/`variance_mul_const` + `s²=Var`; uniform bound `≤2c/s` via `abs_div`).
- `MeanCLT.lean`: `networkMean_clt` fully assembled — builds `F`, discharges `B≥0`, `B→0` (via `card≥1` squeeze + cube-root `Real.pow_rpow_inv_natCast`), feeds `networkSum_clt`, rewrites pushforward CDF to studentized set.

## Remaining
- None. Module compiles with zero sorries / zero errors.

## Blocked
- None.

## Decisions
- Statements faithful, NO laundering: smallness kept exactly `card·(c/s)³→0` (= engine `card·B³→0` with const 8); bound is genuine `2c/s` (tight `c/s` weakened by `c≥0`); m-dependence TRANSFERRED via `IndepFun.comp`, not assumed on the field; all 3 field hypotheses DERIVED.
- Non-vacuous: hypotheses jointly satisfiable (bounded m-dependent fields, positive growing sum-variance, negligibility).
- `cₙ/sₙ→0` NOT assumed; `B→0` derived from `card(Vₙ)≥1` (nonempty from `s²=Var>0`) + squeeze + cube-root.
- `centeredNormalizedField` keeps `have h := hindepY …` in the `indep` proof so autobound retains `hindepY` — do NOT delete.
- Square-integrability carried as `MemLp (Y n i) 2 (μ n)`.
- Linter warnings (unused `DecidableEq`/`IsProbabilityMeasure`) left as-is to keep public signatures matching the contract.