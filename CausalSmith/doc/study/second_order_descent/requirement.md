# Substrate requirement: second_order_descent

## Goal
A general, reusable second-order **descent lemma** for a real function of one real
variable: if `f : ℝ → ℝ` is twice differentiable on an interval with its second
derivative bounded above by `M`, then `f` obeys the quadratic Taylor upper bound,
and — when the initial slope is strictly negative — a strictly-positive descent gap
over a feasible step, optimized in closed form. This is the classical "descent
lemma" of smooth optimization, stated abstractly (no dependence on any specific
objective). It discharges the missing bridge in the bipartite-minimax paper's
`envelope_segment_descent_gap` (a segment restriction of `V_env` with second
derivative bounded by the directional modulus `dirModulus`).

## Target module
`Causalean.Mathlib.Analysis.SecondOrderDescent`

## Provides (API contract)
State everything for `f : ℝ → ℝ` on `Set.Icc 0 T` (or a general `Icc a b`); prefer
Mathlib's `taylor_mean_remainder_lagrange` and `Icc`-segment derivative lemmas.
Search Mathlib first — reuse any existing descent/`ConvexOn`/Taylor lemma; only add
what is genuinely missing.

- `second_order_upper_bound` — for `T ≥ 0`, if `f` is `C²`/twice-differentiable on
  `Icc 0 T` with `∀ t ∈ Icc 0 T, deriv (deriv f) t ≤ M`, then for `t ∈ Icc 0 T`:
  `f t ≤ f 0 + deriv f 0 * t + (M / 2) * t ^ 2`.
  (Lagrange remainder: `f t = f 0 + f' 0 * t + f''(ξ)/2 * t²` for some `ξ ∈ (0,t)`,
  then bound `f''(ξ) ≤ M`. Handle `M = 0` — pure first-order — as a corollary.)

- `second_order_descent_gap` — the optimized descent. With the hypotheses of
  `second_order_upper_bound` plus `deriv f 0 ≤ -c` (`c > 0`) and `M ≥ 0`, letting
  `tstar := if M = 0 then T else min T (c / M)`, then `tstar ∈ Icc 0 T` and
  `f 0 - f tstar ≥ c * tstar - (M / 2) * tstar ^ 2`, and the RHS simplifies to a
  clean lower bound `≥ (c / 2) * min T (c / M)` (M>0) resp. `≥ c * T` (M=0). State
  it so a caller can read off `f 0 - f tstar ≥ c * min T (c/M)` up to the standard
  constant; expose both the raw `c*tstar - (M/2)tstar²` form and the simplified min
  form so the caller can match its own constant.

- (helper, if useful) `deriv2_le_on_Icc` glue: a member-of-a-`sSup` corollary is
  NOT part of this general module — the caller supplies the pointwise `deriv(deriv f) t ≤ M`
  bound (in the paper it comes from `M = dirModulus` via `le_ciSup`). Keep this module
  objective-agnostic.

## Statement / milestones
1. **Quadratic upper bound** from a second-derivative upper bound, via
   `taylor_mean_remainder_lagrange` (order 2) + bounding the remainder. This is the core.
2. **Optimized gap**: minimize `c*t - (M/2)t²` over `t ∈ [0,T]`; unconstrained optimum
   `t = c/M`, clipped to `[0,T]`; evaluate to get the `min T (c/M)` closed form; handle `M=0`.
3. Keep statements fully general (`f : ℝ → ℝ`, abstract `M, c, T`); no
   CausalSmith/bipartite-specific objects. Standard, promotable to Causalean.

## Standard reference
- Descent lemma / quadratic upper bound for L-smooth functions: Nesterov,
  *Introductory Lectures on Convex Optimization* §1.2.2 (Lemma 1.2.3); Bubeck,
  *Convex Optimization: Algorithms and Complexity* §3.2.
- Taylor with Lagrange remainder: standard (Mathlib `taylor_mean_remainder_lagrange`).

## Intended reuse
The immediate consumer is the bipartite-minimax paper's `envelope_segment_descent_gap`
(`heterogeneity_separation`): the segment restriction `t ↦ V_env(phom + t·d)` has second
derivative bounded by `L = dirModulus`, and needs this lemma to turn a negative initial
slope `−Δg` into the explicit gap `≥ 2Δg·min{η_box, Δg/L}`. Reusable for ANY first-order /
interior-point-suboptimality argument that quantifies a descent gap from a curvature bound
(KKT-style proofs). Fully general (a real function of one real variable), so it belongs in
`Causalean.Mathlib.Analysis`.

## May assume / must derive
- **May assume**: `f : ℝ → ℝ` is twice differentiable (`C²`) on `Icc 0 T` — the CALLER
  establishes this and PASSES it as a hypothesis; `M ≥ 0`, `c > 0`, `T ≥ 0` are given; the
  pointwise bound `∀ t ∈ Icc 0 T, deriv (deriv f) t ≤ M` is a HYPOTHESIS (the caller supplies
  it — in the paper via `le_ciSup` from `dirModulus`); and `deriv f 0 ≤ -c`.
- **Must derive**: the quadratic upper bound (via `taylor_mean_remainder_lagrange`, order 2)
  and the optimized descent gap. Do NOT assume the descent lemma itself — that IS the goal.
  Reuse Mathlib's Taylor-remainder theorem rather than re-deriving it. Keep every statement
  objective-agnostic (NO `varEnvelope`/`dirModulus`/bipartite objects).

## Non-goals
- The `sSup`-membership extraction (`line-2nd-deriv ≤ dirModulus`) — caller-side, paper-specific.
- The `C²` regularity of the specific reciprocal-product envelope line — caller-side.
- Multivariate / full gradient-descent generality; real-valued one-dimensional is enough.

## Known building blocks
- Mathlib: `taylor_mean_remainder_lagrange`, `taylorWithinEval`, `iteratedDeriv`,
  `deriv`/`HasDerivAt`/`ContDiffOn` calculus, `Convex.inner_le`/`ConvexOn.deriv_le_slope`,
  and `min`/`Icc`/`le_div_iff` algebra for the step optimization.
