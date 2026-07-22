# Substrate requirement: hoeffding_covariance_identity

## Goal
Hoeffding's covariance identity: for real random variables with finite second
moments, the covariance equals the double integral of the gap between the joint
cdf and the product of the marginal cdfs.

## Provides (API contract)
- `hoeffding_cov_identity` — for a probability measure `π : Measure (ℝ × ℝ)` whose
  marginals `μ = π.map Prod.fst`, `ν = π.map Prod.snd` satisfy `MemLp id 2`,
  writing `H x y = π (Iic x ×ˢ Iic y)`, `F = cdf μ`, `G = cdf ν`:
  `∫ p, p.1 * p.2 ∂π - (∫ x, x ∂μ) * (∫ y, y ∂ν) = ∫ x, ∫ y, (H x y - F x * G y)`.
- (helper, likely needed) `sub_eq_integral_indicator_diff` — the scalar tail
  representation `a - b = ∫ s, (Set.indicator {s | s < a} 1 - Set.indicator {s | s < b} 1) s`,
  and its product form used inside the Fubini computation.

## Statement / milestones
1. Scalar representation `a - b = ∫_ℝ (1{s < a} - 1{s < b}) ds` (compactly supported integrand).
2. Product/iid-copy form: with `(X₁,Y₁),(X₂,Y₂)` iid `∼ π`,
   `(X₁-X₂)(Y₁-Y₂) = ∫∫ (1{s<X₁}-1{s<X₂})(1{t<Y₁}-1{t<Y₂}) ds dt`.
3. Take expectations, apply Fubini/Tonelli (justified by L² ⟹ the integrand is
   integrable on the product), and simplify `E[·]` of the indicator products into
   `H - F·G`, using `2·Cov = E[(X₁-X₂)(Y₁-Y₂)]`.

## Standard reference
Hoeffding (1940), "Masstabinvariante Korrelationstheorie"; Lehmann, "Some Concepts
of Dependence" (Ann. Math. Statist. 1966), Lemma 2; Nelsen, *An Introduction to
Copulas*, §2 (the "Hoeffding's lemma" covariance formula).

## Intended reuse
Consumed by the product-loss optimal-coupling optimality theorem
(`product_loss_monotone_coupling`), which reduces maximizing `E_π[XY]` over a
Fréchet class to maximizing `∫∫ H_π` via this identity. Also the standard bridge
to copula-based dependence measures (Spearman's ρ, Kendall's τ).

## May assume / must derive
- **May assume**: `π` a probability measure on `ℝ × ℝ`; both marginals `MemLp id 2`;
  Mathlib Fubini/Tonelli (`integral_prod`, `lintegral_prod`, `integrable_prod_iff`),
  `ProbabilityTheory.cdf`, `Measure.map` / `.fst` / `.snd`, product-measure API.
- **Must derive**: the scalar tail representation, the integrability of the product
  integrand from L², and the Fubini reduction to `H - F·G`.

## Non-goals
- NOT the optimal-coupling optimality theorem itself (that consumes this).
- NOT weakening to first moments only (L² is the working hypothesis; do not
  strengthen or weaken the moment assumption to force the proof through).

## Known building blocks
- Mathlib: `MeasureTheory.integral_prod`, `lintegral_prod`, `integrable_prod_iff`,
  `MeasureTheory.integral_indicator`, `Real.volume_Ioo`; `ProbabilityTheory.cdf`
  and its `measure (Iic x)` characterization; `MeasureTheory.Measure.map_apply`.
- The iid-copy trick uses the product measure `π.prod π` on `(ℝ×ℝ)×(ℝ×ℝ)`.

## Target module
Single file → eligible for a custom target. Suggested:
`Causalean.Stat.Coupling.HoeffdingCovariance` (set as `## Target module` if you
want it promoted straight there rather than to `Causalean/Substrate/…`).
