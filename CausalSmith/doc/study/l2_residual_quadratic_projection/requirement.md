# Substrate requirement: l2_residual_quadratic_projection

## Goal
Closed-form L² projection residual of `y ↦ y²` onto `span{1, y}` in `L²(μ)` for a probability measure `μ` on `ℝ` with finite fourth moment (the residual variance of regressing `y²` on `(1, y)`).

## Provides (API contract)
- `residualQuad (μ) (b₀ b₁ : ℝ) : ℝ := ∫ y, (y^2 - b₀ - b₁ * y)^2 ∂μ` — the quadratic objective.
- `l2ResidualQuadratic (μ) : ℝ` — the closed-form minimum residual `r(μ) = (m₄ − m₂²) − (m₃ − m₁ m₂)² / (m₂ − m₁²)` in the moments `mₖ = ∫ yᵏ ∂μ` (equivalently the Hankel-determinant ratio `det H₃ / det H₂`).
- `optIntercept (μ) : ℝ`, `optSlope (μ) : ℝ` — the least-squares optimal coefficients `b₁* = (m₃ − m₁ m₂)/(m₂ − m₁²)`, `b₀* = m₂ − b₁* m₁`.
- `residualQuad_opt_eq : m₁² < m₂ → residualQuad μ (optIntercept μ) (optSlope μ) = l2ResidualQuadratic μ` (attainment).
- `l2ResidualQuadratic_le : m₁² < m₂ → l2ResidualQuadratic μ ≤ residualQuad μ b₀ b₁` (it is the infimum — normal-equation / SOS certificate).
- `l2ResidualQuadratic_nonneg : 0 ≤ l2ResidualQuadratic μ`.

## Statement / milestones
For a probability measure `μ` on `ℝ` with finite 4th moment and non-degenerate `Var(y) = m₂ − m₁² > 0`:
`⨅ (b₀ b₁ : ℝ), residualQuad μ b₀ b₁ = l2ResidualQuadratic μ`, attained at `(optIntercept μ, optSlope μ)`.
Prove via the normal equations for least squares of `y²` on `{1, y}`: expand `residualQuad μ b₀ b₁` as a positive-semidefinite quadratic in `(b₀, b₁)`, whose minimizer is the normal-equation solution and whose minimum value is the stated Hankel ratio. The `≤` (infimum) direction is a completed-square / SOS identity; attainment is a direct `field_simp; ring` at the optimum.

## Standard reference
Standard least-squares / Hankel-moment-matrix algebra; e.g. any regression or moment-problem text (Shohat–Tamarkin, *The Problem of Moments*; or the finite-dimensional orthogonal-projection / Gram-matrix residual formula).

## Intended reuse
Consumed by the CausalSmith research run `stat_neyman_regret_minimax`: `armTangentStrength ν a = ⨅ b₀ b₁, ∫ (y² − b₀ − b₁ y)² d(armMarginal ν a)` and `arm_score_program_solution` (the moment-preserving score program value `J_{a,ν}(x) = x² / r_{a,ν}`). Required at general-measure generality (arm marginals on `[0,1]`), not gerrymandered to that setting.

## May assume / must derive
May assume: `μ` is a probability (or finite) measure with `∫ y⁴ ∂μ < ∞` (all lower moments finite), and non-degeneracy `m₁² < m₂`. Must derive: the closed-form residual, optimality, attainment, and non-negativity — from the integral definition (no assuming the Hankel formula).

## Known building blocks
`MeasureTheory.integral_*` (linearity, `integral_add`, `integral_smul`, `integral_const`), `inner_mul_le_norm_mul_norm` / completed square, and `Causalean.Stat.Nonparametric.MomentEnvelope` (`momentResidual`, its SOS min-certificate) for the moment-level algebra — the new content is the MEASURE-level `∫`-form and the `⨅`/optimality bridge.

## Target module
Causalean.Stat.Nonparametric.L2ResidualQuadratic
