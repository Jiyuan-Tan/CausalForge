## Module: KlDensityTiltExpansion — COMPLETE (0 sorries, build exit 0)
Files: CausalSmith/Substrate/KlDensityTiltExpansion/{Basic,CubicRemainder,KLExpansion}.lean
Generality: `{Z} [MeasurableSpace Z] (μ : Measure Z)`, `s : Z → ℝ`, `import Mathlib`.

## Done (all proven, verified this turn)
- Basic.lean: `tiltMeasure`, `tiltMeasure_absolutelyContinuous`, `tiltDensity_nonneg`, `integrable_of_bounded`, `integral_tiltDensity`, `isProbabilityMeasure_tiltMeasure`.
- CubicRemainder.lean: `abs_tiltRemainder_le` (|(1+x)log(1+x)-x-x²/2|≤|x|³ on |x|≤1/2) — proved via monotonicity of the two remainder-plus/minus-cube auxiliaries (HasDerivAt + `monotoneOn_of_hasDerivWithinAt_nonneg`, using `log_le_sub_one` / `one_sub_inv_le_log`), NOT `taylor_mean_remainder_lagrange` (that route abandoned; the monotonicity route worked cleanly).
- KLExpansion.lean: `klDiv_tiltMeasure_toReal_eq`, `abs_klRemainder_le`, `klDiv_tilt_expansion` (MAIN, `=o[𝓝 0] (fun h => h^2)`).

## Verification (this turn, ground truth)
- `lake build ...KLExpansion` → exit 0, only 1 linter warning (unused `[MeasurableSpace Z]` section var on `tiltDensity_nonneg`; non-fatal).
- `rg sorry` across the 3 files → 0 matches.
- `lean_verify` on `klDiv_tilt_expansion` and `abs_tiltRemainder_le` → axioms `[propext, Classical.choice, Quot.sound]` only (no sorryAx).

## Remaining
- none.

## Blocked
- none.

## Decisions
- Bound hyps phrased `|h|*C ≤ 1` (nonneg) / `≤ 1/2` (Taylor band); `0≤C` derived in MAIN from `nonempty_of_isProbabilityMeasure`. Non-vacuous (C≥0, s bounded/mean-zero all satisfiable, e.g. s=0).
- KL route: `toReal_klDiv_of_measure_eq` + `rnDeriv_withDensity` + `integral_withDensity_eq_integral_toReal_smul` → `∫(1+hs)log(1+hs)dμ`. Remainder dominated by `∫|hs|³ ≤ C³|h|³`, then `isLittleO_iff` with coefficient `C³|h|→0`.
- Cubic bound: monotonicity route (see Done) replaced the planned Lagrange route.

## Note for reviewer
API contract fully met: `tiltMeasure`, `isProbabilityMeasure_tiltMeasure` (= `tiltMeasure_isProbability`), `klDiv_tilt_expansion` (MAIN IsLittleO). Ready for consumption by `stat_neyman_regret_minimax` (linear_tilt_path_valid arm-marginal KL clause).