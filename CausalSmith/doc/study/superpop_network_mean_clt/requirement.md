# Substrate requirement: superpop_network_mean_clt

## Goal
Make the abstract m-dependent network CLT (`networkSum_clt`) usable for a concrete estimand by
delivering the standardized asymptotic normality of the network sample mean: from raw
network-dependent outcomes `Y i` with a common mean, build the centered/scaled unit-variance field
and conclude `(∑ᵢ Yᵢ − ∑ᵢ E[Yᵢ]) / √Var(∑ᵢ Yᵢ) ⇝ N(0,1)`.

## Provides (API contract)
- `centeredNormalizedField` — from a sequence of outcome families `Y n : V n → Ω n → ℝ` with a
  network (reflexive/symmetric/bounded-degree) and the m-dependence (non-adjacent outcome tuples
  independent), measurable, square-integrable, with `sₙ² := Var(∑ᵢ Yₙ ᵢ) > 0`, construct a
  `NetworkDependence (V n) (Ω n) (μ n)` whose summand is `Xᵢ = (Yₙ ᵢ − E[Yₙ ᵢ]) / sₙ`. Show its
  hypotheses hold: mean-zero, unit total variance, and `|Xᵢ| ≤ Bₙ` with `Bₙ = 2·cₙ / sₙ` when
  `|Yₙ ᵢ − E[Yₙ ᵢ]| ≤ cₙ`.
- `networkMean_clt` — under bounded degree `m`, bounded centered outcomes `|Yₙ ᵢ − E[Yₙ ᵢ]| ≤ cₙ`,
  and the standard smallness condition `card(V n)·(cₙ / sₙ)³ → 0` (a Lyapunov/Lindeberg-type
  negligibility of the per-unit contribution), the standardized network sum converges in
  distribution to the standard normal:
  `Tendsto (fun n => (μ n).real {ω | (∑ᵢ Yₙ ᵢ ω − ∑ᵢ E[Yₙ ᵢ]) / sₙ ≤ t}) atTop (𝓝 Φ(t))`.

## Statement / milestones
1. **Field construction** (`centeredNormalizedField`): assemble the `NetworkDependence` record with
   `X i = (Y i − μ[Y i]) / sₙ`; the `indep` field transfers from the outcome m-dependence because
   `Xᵢ` is an affine measurable function of `Yᵢ` (compose the outcome-tuple independence with the
   affine maps — `IndepFun.comp`).
2. **Hypothesis discharge**: mean-zero (`E[Xᵢ] = (E[Yᵢ] − E[Yᵢ])/sₙ = 0`); unit total variance
   (`Var(∑Xᵢ) = Var(∑Yᵢ)/sₙ² = 1`, using `sₙ² = Var(∑Yᵢ)`); uniform bound
   (`|Xᵢ| ≤ 2cₙ/sₙ =: Bₙ`).
3. **CLT** (`networkMean_clt`): feed (1)–(2) into `networkSum_clt`; the smallness hypothesis
   `card·(cₙ/sₙ)³ → 0` is exactly the engine's `card·Bₙ³ → 0` up to the constant `8`. Rewrite the
   probability set `{(∑Y − ∑E[Y])/sₙ ≤ t}` to `{depSum X ≤ t}` to match `networkSum_clt`'s
   conclusion, and identify `Φ` with `(gaussianReal 0 1).real (Set.Iic t)`.

## Standard reference
The classical m-dependent / locally-dependent CLT for the sample mean (Hoeffding–Robbins 1948 for
m-dependence; Chen–Shao 2004 for the dependency-graph version). The design-based counterpart in
this repo is the studentized-statistic interface `LocalDependenceCLT` in
`Causalean/Experimentation/ExposureMappingInterference/Asymptotics/SteinCLT.lean`.

## Intended reuse
The bridge that lets any super-population network-dependent MEAN-type estimand (a treatment-arm
mean outcome, an exposure-level average, a difference of two such means via a paired field) inherit
asymptotic normality from `networkSum_clt` without re-deriving the CLT. Consumed by future
Experimentation-cluster super-population / network papers and pairs with the HAC variance estimator
(`superpop_network_hac_consistency`) to give a full Wald interval.

## May assume / must derive
- **May assume**: bounded degree `m`, bounded centered outcomes `|Yₙ ᵢ − E[Yₙ ᵢ]| ≤ cₙ`, square
  integrability, `sₙ² = Var(∑ᵢ Yₙ ᵢ) > 0`, the outcome m-dependence (non-adjacent outcome tuples
  independent), and the negligibility `card(V n)·(cₙ/sₙ)³ → 0`.
- **Must derive**: the field construction and ALL three field hypotheses (mean-zero, unit total
  variance, uniform bound) from the outcome-level assumptions, and the final CLT as a corollary of
  `networkSum_clt`. Do NOT re-assume any field hypothesis; derive each. Do NOT re-prove a Stein CLT
  — reduce to `networkSum_clt`.

## Non-goals
- The variance-estimator / HAC side (separate run `superpop_network_hac_consistency`).
- Relaxing the uniform outcome bound to a moment (Lyapunov) condition — that needs generalizing the
  bounded-summand Stein engine and is a separate substrate.
- Any random-graph / graphon construction; the network is fixed.

## Known building blocks
- `Causalean.Experimentation.SuperPopulation.NetworkDependence`, `.networkSum_clt`, `depSum`.
- Mathlib: `IndepFun.comp` (affine transfer of independence), `variance` scaling
  (`variance_smul` / `variance_div`), `integral` linearity, `gaussianReal`, `squeeze_zero`,
  `MeasureTheory.map_measureReal_apply`.
- The reduction pattern is `Causalean/Experimentation/DesignBased/IndepSummandsCLT.lean`
  (`prodDesign_clt`), which does the analogous "check field hypotheses → feed the engine →
  rewrite the probability set" assembly.

## Target module
`Causalean.Experimentation.SuperPopulation.MeanCLT`
