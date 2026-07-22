# Substrate requirement: product_loss_monotone_coupling

## Goal
Over all couplings of two real probability measures with finite second moments,
the product expectation E_π[XY] is maximized by the comonotone (quantile)
coupling and minimized by the countermonotone coupling, with optimal values
given by the quantile-transform formulas.

## Provides (API contract)
- `IsCoupling (π : Measure (ℝ × ℝ)) (μ ν : Measure ℝ) : Prop` — π is a
  probability measure with `π.map Prod.fst = μ` and `π.map Prod.snd = ν`
  (search the library first; reuse a Mathlib coupling notion if one exists).
- `comonotoneCoupling (μ ν : Measure ℝ) : Measure (ℝ × ℝ)` — pushforward of
  `Unif(0,1)` under `u ↦ (quantile μ u, quantile ν u)`.
- `countermonotoneCoupling (μ ν : Measure ℝ) : Measure (ℝ × ℝ)` — pushforward
  under `u ↦ (quantile μ u, quantile ν (1 - u))`.
- `quantile_map_uniform : (volume.restrict (Ioo 0 1)).map (quantile μ) = μ`
  (probability-integral-transform) for a Borel probability measure μ.
- `isCoupling_comonotoneCoupling` / `isCoupling_countermonotoneCoupling` — each
  IS a coupling of (μ, ν).
- `frechet_hoeffding_upper` / `frechet_hoeffding_lower` — pointwise bounds on the
  joint cdf H_π of ANY coupling: `max (F x + G y - 1) 0 ≤ H_π x y ≤ min (F x) (G y)`,
  with equality attained by the comonotone (upper) / countermonotone (lower) coupling.
- `hoeffding_cov_identity` — `Cov_π(X,Y) = ∫∫ (H_π x y - F x * G y) dx dy` for L² marginals.
- `product_expectation_le_comonotone` — for every coupling π of (μ,ν),
  `∫ p, p.1 * p.2 ∂π ≤ ∫ p, p.1 * p.2 ∂(comonotoneCoupling μ ν)`.
- `countermonotone_le_product_expectation` — the matching lower bound.
- (optional) closed form `∫ p, p.1*p.2 ∂(comonotoneCoupling μ ν) = ∫ u in Ioo 0 1, quantile μ u * quantile ν u`.

## Statement / milestones
Bottom-up dependency chain — build in this order:
1. **PIT**: `quantile μ` pushes `Unif(0,1)` to μ (from `quantile_le_iff`:
   `P(quantile μ U ≤ x) = P(U ≤ cdf μ x) = cdf μ x`).
2. **Marginals**: comonotone / countermonotone couplings are couplings of (μ,ν)
   (marginals via PIT; monotonicity of `quantile` and of `u ↦ 1-u`).
3. **Fréchet–Hoeffding**: pointwise cdf bounds for any coupling, with equality
   `H = min(F,G)` for comonotone and `H = max(F+G-1,0)` for countermonotone.
4. **Hoeffding covariance identity** (the hard lemma — Fubini/Tonelli on the tail
   representation `xy = ∫∫ (1{s<x} - 1{s<0})(1{t<y} - 1{t<0}) ds dt`).
5. **Capstone optimality**: `E_π[XY] = Cov_π + E[X]E[Y]` and `E[X]E[Y]` is
   CONSTANT across Π(μ,ν); so maximizing `E_π[XY]` ⇔ maximizing `∫∫ H_π`, done
   pointwise by `min(F,G)` — hence comonotone is the argmax, countermonotone the argmin.

## Standard reference
- Hoeffding's covariance identity: Hoeffding (1940); Lehmann, "Some Concepts of
  Dependence" (Ann. Math. Statist. 1966); Nelsen, *An Introduction to Copulas* §2.
- Fréchet–Hoeffding bounds: Fréchet (1951); Nelsen §2.5.
- 1-D optimal transport / monotone rearrangement: Villani, *Topics in Optimal
  Transportation* §2.2; Santambrogio, *Optimal Transport for Applied
  Mathematicians* §2.1 (the Fréchet class, monotone coupling).

## Intended reuse
The primitives are the reusable core (this is why it is substrate, not a one-off):
- 1-D Wasserstein-2 (quadratic cost reduces to this via the ‖x-y‖² expansion).
- Rank / Spearman-correlation extremes; comonotone dependence.
- Fréchet bounds on joint distributions in partial identification; rank-preserving
  (comonotone) assumptions in the potential-outcomes calculus and QTE.

## May assume / must derive
- **May assume**: μ, ν Borel probability measures on ℝ with finite second moments
  (`MemLp id 2 μ`); the existing `Causalean.Stat.Quantile` API (`quantile`,
  `quantile_le_iff`, `quantile_mono`); Mathlib Fubini/Tonelli (`integral_prod` /
  `lintegral_prod`), `ProbabilityTheory.cdf`, `Measure.map` / `.fst` / `.snd`.
- **Must derive**: PIT from `quantile_le_iff`; the marginals of the explicit
  couplings; Fréchet–Hoeffding; the Hoeffding identity; the optimality theorem.

## Non-goals
- NOT general Kantorovich duality, n-dimensional OT, or general cost functions.
- NOT existence of optimal couplings in abstract Polish spaces (we exhibit the
  explicit optimizer).
- Uniqueness of the optimizer only if it falls out cheaply.

## Known building blocks
- `Causalean/Stat/Quantile/Quantile.lean`: `quantile`, `quantile_le_iff`, `quantile_mono`.
- Mathlib: `ProbabilityTheory.cdf`; `MeasureTheory.Measure.map` / `.fst` / `.snd`;
  `MeasureTheory.integral_prod` & `lintegral_prod` (Fubini/Tonelli); the layer-cake /
  tail formula (`lintegral_eq_lintegral_meas_lt`) for the Hoeffding identity;
  `Mathlib/Algebra/Order/Rearrangement.lean` and `Monovary.lean` as the finite
  rearrangement backstop.

## Target module
Multi-file module → promotes to `Causalean/Substrate/ProductLossMonotoneCoupling/`.
(Custom single-module `## Target module` placement is single-file-only, so it does
not apply here.) On later human promotion, the coupling infrastructure is a natural
candidate for `Causalean/Stat/Coupling/`.
