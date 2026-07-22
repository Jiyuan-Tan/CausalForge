# Substrate requirement: holder_pointwise_l1_interpolation

## Goal
Build the canonical Tsybakov nonparametric-minimax lower-bound primitive: for a function in a
multivariate Hölder ball, a pointwise value forces a local L¹ mass lower bound via a
moment-cancelling kernel.

## Provides (API contract)
- `holder_point_l1_interpolation` (main lemma) — informal signature: for `d : ℕ`, `γ > 0`, `M > 0`,
  `r > 0`, `x0` interior to the domain, and any `g : (Fin d → ℝ) → ℝ` in the standard
  `⌈γ⌉-1`-convention Hölder ball `HolderBallStd g γ M S` on a neighborhood `S ⊇ supBall x0 r`:
  `∃ cH > 0` (depending only on `γ, d, M, r`) such that
  `∫ x in supBall x0 r, |g x| ≥ cH · |g x0| ^ (1 + d / γ)`.
- Supporting (scaffolder may name/add): a moment-cancelling product kernel `K` on `[-1,1]^d`
  (`∫ K = 1`, `∫ uᵛ K = 0` for `1 ≤ |ν| ≤ m := ⌈γ⌉−1`) obtained by a 1-D Vandermonde moment solve +
  tensorization; a multivariate Taylor-with-Hölder-remainder bias bound; the `h`-optimization step.

## Statement / milestones
Main statement: the `holder_point_l1_interpolation` bound above, stated on a GENERIC Hölder ball
(not tied to any CATE/estimand type) so it reuses across runs. Proof milestones (standard Tsybakov,
writeup L190–194):
1. **Moment-cancelling product kernel.** Bounded `K` on `[-1,1]^d`, `∫ K = 1`, vanishing moments
   `∫ uᵛ K(u) du = 0` for `1 ≤ |ν| ≤ m := ⌈γ⌉−1`. Solve the 1-D nonsingular polynomial (Vandermonde)
   moment system for a compactly supported 1-D kernel `k`, then TENSORIZE `K(u) = ∏ᵢ k(uᵢ)`.
2. **Taylor + moment cancellation.** For `0 < h ≤ r`, multivariate Taylor of `g` at `x0` to order `m`
   with the integer-order Hölder/Lipschitz remainder + the moment cancellations gives
   `|g(x0) − ∫ h^{-d} K((x−x0)/h) g(x) dx| ≤ C_{γ,d} · M · h^γ`. (Integer `γ`: degree `γ−1` Taylor
   polynomial + Lipschitz remainder in the integer-order Hölder definition.)
3. **Optimize `h`.** With `Δ = |g(x0)|`, choose `h = c_* Δ^{1/γ}`,
   `c_* = min{ r / Δ_max^{1/γ}, (4 C_{γ,d} M)^{-1/γ} }`, so `h ≤ r` and the remainder is `≤ Δ/4`; then
   `3Δ/4 ≤ |∫ h^{-d} K((x−x0)/h) g| ≤ ‖K‖_∞ h^{-d} ∫_{supBall x0 r} |g|`. Rearranging + substituting
   `h` gives `∫_{supBall x0 r} |g| ≥ cH Δ h^d = cH Δ^{1 + d/γ}`. The `Δ = 0` case is immediate.

## Standard reference
Tsybakov, *Introduction to Nonparametric Estimation* (2009), Ch. 1–2 (kernel bias / moment-cancelling
kernels) and the standard two-point / Assouad nonparametric-minimax lower-bound machinery.

## Intended reuse
Consumed by `stat_dp_cate_minimax_v1 / holder_central_dp`, node `lem:holder-point-l1-interpolation`
(gated substrate on the headline `thm:causal-dp-two-point-barrier`): specialize to `g = τ_P − τ_Q`
with `τ = μ1 − μ0`, `M = 2L`, `r = rStar r0 x0`, evaluation point `x0`. More broadly, EVERY
Hölder-class two-point / TV-contraction / Assouad-style lower bound needs "pointwise value ⟹ local L¹
mass lower bound via a moment-cancelling kernel", so state it on a generic Hölder ball for full reuse.

## May assume / must derive
- **May assume:** membership of `g` in `HolderBallStd(γ, M, S)`; standard Mathlib measure theory /
  integration on `ℝ^d`; `iteratedFDeriv` / multivariate Taylor infrastructure; basic linear algebra
  (nonsingular Vandermonde) for the 1-D moment solve.
- **Must derive:** the moment-cancelling product-kernel CONSTRUCTION (Vandermonde solve +
  tensorization, with the vanishing-moment property), the multivariate Taylor bias bound with the
  Hölder remainder, and the `h`-optimization rearrangement yielding the `Δ^{1 + d/γ}` exponent.

## Non-goals (optional)
Not tied to any CATE/estimand/`CateLaw` type — it is a generic Hölder-ball lemma. Not the full
minimax theorem, DP contraction, or the barrier assembly (those stay in the paper's run). No claim of
sharpness of the constant `cH`.

## Known building blocks (optional)
Mathlib: `iteratedFDeriv` + Taylor's theorem, `MeasureTheory` integrals / `setIntegral`, `Finset`
products for tensorization, Vandermonde nonsingularity. Causalean/CausalSmith: only a 1-D
`KernelOrder` / `kernelSmoothingBias_bound` exists (insufficient — 1-D, specific); the sibling
`DoseResponseMinimax` has only a 1-D `ContDiffBump` + specific-bump KL route, NOT this general
arbitrary-`g` interpolation.

## Target module (optional)
`Causalean.Stat.Minimax.HolderInterpolation` (advisory; a `Causalean.Stat.Concentration` sibling is
also acceptable — final placement chosen by the coordinate phase). State on a generic Hölder ball.
