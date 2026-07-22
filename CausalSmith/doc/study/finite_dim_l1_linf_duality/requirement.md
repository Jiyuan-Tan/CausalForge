# Substrate requirement: finite_dim_l1_linf_duality

## Goal
Finite-dimensional ℓ¹/ℓ∞ duality for minimum-norm representation: the smallest ℓ¹ norm of a weight vector representing the endpoint contrast on degree-≤β polynomials sampled at k+1 distinct nodes equals the sup of that contrast over polynomials bounded by 1 at the nodes.

## Provides (API contract)
- `l1_repr_eq_sup_dual` (the reusable identity): for `k+1` distinct nodes `p : Fin (k+1) → ℝ`, `β ≤ k`, with
  `W = { w : Fin (k+1) → ℝ | ∀ ℓ ≤ β, ∑ j, w j * (p j)^ℓ = (if ℓ = 0 then 0 else 1) }`,
  `sInf { s | ∃ w ∈ W, s = ∑ j, |w j| } = sSup { t | ∃ r : Polynomial ℝ, r.natDegree ≤ β ∧ (∀ j, |r.eval (p j)| ≤ 1) ∧ t = |r.eval 1 - r.eval 0| }`.
- Optionally the squared form and nonemptiness of `W`.

## Statement / milestones
This is finite-dim LP / ℓ¹-ℓ∞ Hahn–Banach duality specialized to the node-sampling map. Identify a degree-β polynomial `r` with its coefficient vector `b`; node-evaluation `Ev : b ↦ (r.eval (p j))_j` is linear, and `L b = r.eval 1 - r.eval 0 = ∑_{ℓ=1}^β b ℓ`. A weight `w` represents `L` iff `Evᵀ w = L*` (= the `W`-moment condition). Then `min{‖w‖₁ : Evᵀ w = L*} = max{L b : ‖Ev b‖_∞ ≤ 1}`. Milestones:
1. `W` nonempty (Vandermonde: `β ≤ k` distinct nodes ⇒ moment system solvable).
2. Weak duality: for `w ∈ W` and `r` with `∀j |r(p_j)| ≤ 1`, `|r(1)−r(0)| = |∑ j w j r(p_j)| ≤ ∑ j |w j|`. Hence `sup ≤ inf`.
3. Strong duality (`inf ≤ sup`, the hard direction): finite-dim LP duality — a separating-hyperplane / Hahn–Banach argument on `ℝ^{k+1}` (or an explicit optimal `w*`/`r*`). Use Mathlib's `geometric_hahn_banach*` / finite-dim convex duality if a direct min-norm-representation = dual-sup lemma is absent.

## Standard reference
Finite-dim LP duality / ℓ¹-ℓ∞ Hahn–Banach duality; the min-norm-representation = dual-sup identity is standard optimal-recovery/convex-analysis duality (the ℓ¹/ℓ∞ pairing on ℝⁿ).

## Intended reuse
Discharges `lem:amplification-dual-norm` (`amplification_dual_norm`) of run `exp_rollout_chebyshev_minimax / tv_envelope_rollout_design`: it needs this identity plus `amplification β k p = (that sSup)^2`. State it generally (arbitrary distinct nodes, arbitrary `β ≤ k`), NOT gerrymandered to the Chebyshev schedule.

## May assume / must derive
- MAY assume: Mathlib finite-dim linear algebra, `Polynomial.eval`, Vandermonde non-singularity for distinct nodes, `Finset` sums, `sInf`/`sSup` API, convex analysis / Hahn–Banach in finite dim.
- MUST derive: both duality directions (weak easy; strong = the real argument). Do NOT assume the duality as an axiom/sorry. If the strong direction genuinely needs a substantial Mathlib LP-duality development not present, PROVE weak duality + nonemptiness and report the exact remaining strong-duality goal + missing Mathlib lemma — do NOT fake it.

## Non-goals (optional)
Infinite-dimensional duality, general `L^p`, numeric optimal weights out of scope. Only the finite-dim ℓ¹/ℓ∞ identity + attainment.

## Known building blocks (optional)
- `Matrix.vandermonde` / `Polynomial.eval` for nonemptiness.
- Mathlib convex analysis: `Convex`, separating hyperplane (`geometric_hahn_banach*`), `Finset.sum`, dual norms.

## Target module (optional)
`Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality`
