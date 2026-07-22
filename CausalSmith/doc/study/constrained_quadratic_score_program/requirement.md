# Substrate requirement: constrained_quadratic_score_program

## Goal
The constrained quadratic "score program" dual to the L² projection residual: for a probability measure μ on ℝ (finite 4th moment, non-degenerate), the minimum L²(μ) norm of a score s constrained to be moment-orthogonal to (1, y) with a prescribed y²-moment x equals x² / r, where r is the unconstrained L² residual of y² onto span{1,y}.

## Provides (API contract)
- `scoreCost (μ) (x : ℝ) : ℝ := ⨅ s ∈ {s : ℝ → ℝ | ∫ s dμ = 0 ∧ ∫ y*s dμ = 0 ∧ ∫ y²*s dμ = x ∧ Integrable (s² ) μ}, ∫ s² dμ` — the constrained score program value (state it however is cleanest — an `sInf` over feasible scores, or the closed form directly with an attainment+lower-bound pair).
- `scoreCost_eq : (h : m₁² < m₂) → scoreCost μ x = x^2 / l2ResidualQuadratic μ` — the DUALITY (score program value = x² / residual), the main result.
- `optScore (μ) (x : ℝ) : ℝ → ℝ` — the optimal score `s*(y) = (x / r) · q(y)` where `q = y² − (optIntercept μ + optSlope μ · y)` is the projection residual function; and a lemma that it is feasible and attains `x²/r`.

## Statement / milestones
For μ a probability measure on ℝ with finite 4th moment and `r := l2ResidualQuadratic μ > 0` (non-degeneracy `m₁² < m₂`):
1. FEASIBILITY + ATTAINMENT: `s* = (x/r)·q` (q the L² residual of y² on span{1,y}) satisfies `∫ s* dμ = 0`, `∫ y·s* dμ = 0`, `∫ y²·s* dμ = x`, and `∫ (s*)² dμ = x²/r`.
2. LOWER BOUND: any feasible score s (moment-orthogonal to 1,y with `∫y²s dμ = x`) has `∫ s² dμ ≥ x²/r`. Proof: `x = ∫ y² s dμ = ∫ q s dμ` (since s ⟂ span{1,y}), then Cauchy–Schwarz `x² = (∫ q s)² ≤ (∫ q²)(∫ s²) = r·∫ s²`.
So `scoreCost μ x = x²/r`.

## Standard reference
Standard Lagrangian / Cauchy–Schwarz duality for a constrained least-norm (minimum-norm interpolation) problem; e.g. any functional-analysis or estimation text (the "efficient score" / minimum-variance-unbiased minimum-norm construction), or Rockafellar convex duality.

## Intended reuse
Consumed by the CausalSmith research run `stat_neyman_regret_minimax`: `armScoreCost ν a` / `arm_score_program_solution` (`J_{a,ν}(x) = x² / r_{a,ν}` where `r_{a,ν} = armTangentStrength ν a`). Required at general-measure generality on [0,1].

## May assume / must derive
May assume: μ a probability measure with `∫ y⁴ dμ < ∞`, non-degeneracy `m₁² < m₂`. Must derive: feasibility, attainment, the Cauchy–Schwarz lower bound, and the closed form `x²/r` — reusing `Causalean.Stat.Nonparametric.L2ResidualQuadratic` (`l2ResidualQuadratic`, `optIntercept`, `optSlope`, `residualQuad_opt_eq`) for the residual `r` and the projection `q`. Do NOT re-derive the residual closed form.

## Known building blocks
`Causalean.Stat.Nonparametric.L2ResidualQuadratic`; `MeasureTheory.integral_*`; Cauchy–Schwarz `MeasureTheory.integral_mul_le_L2norm_mul_L2norm` / `inner_mul_le_norm_mul_norm`.

## Target module
Causalean.Stat.Nonparametric.ConstrainedScoreProgram
