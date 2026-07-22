# Substrate requirement: bernstein_szego_trig

## Goal
The sharp Bernstein/Szegő differential inequality for the trigonometric polynomial `Q(t) = R(cos t)` arising from a real algebraic polynomial `R` of degree ≤ β: the derivative is controlled by `β·√(‖Q‖∞² − Q²)`.

## Provides (API contract)
- `szego_deriv_sq_bound (R : Polynomial ℝ) (β : ℕ) (hβ : R.natDegree ≤ β) (M : ℝ) (hM : ∀ t, |R.eval (Real.cos t)| ≤ M)` :
  `∀ t, (deriv (fun s => R.eval (Real.cos s)) t)^2 + β^2 * (R.eval (Real.cos t))^2 ≤ β^2 * M^2`.
  (Equivalently `|Q'(t)| ≤ β·√(M² − Q(t)²)` where `Q t = R.eval (cos t)`.)

## Statement / milestones
Let `Q(t) = R.eval (cos t)` for `R : ℝ[X]`, `R.natDegree ≤ β`. Then `Q` is a real even trigonometric polynomial of degree ≤ β and `Q'(t)² + β²Q(t)² ≤ β²‖Q‖∞²`. Decomposition (zero-counting / Szegő route — build these sub-lemmas):
1. `Q'(t) = -sin t · R'(cos t)`; `Q` is C^∞. (chain rule, `Polynomial.deriv`, `Real.deriv_cos`.)
2. **≤2β zeros lemma** (the load-bearing step, absent from Mathlib): via `z = exp(i t)`, `cos t = (z + z⁻¹)/2`, so `Q(t) = R((z+z⁻¹)/2)`. Clearing denominators, `z^β · Q = P(z)` for an algebraic polynomial `P : ℂ[X]` of degree ≤ 2β; hence `Q` (as a function of `t ∈ [0,2π)`) has at most `2β` zeros counted with multiplicity — from `Polynomial.card_roots` / `Polynomial.roots` on `P`. State and prove this zero-count.
3. **Szegő comparison**: fix `t₀`; the degree-β trig interpolant `S(t) = Q(t₀)·cos(β(t−t₀)) + (Q'(t₀)/β)·sin(β(t−t₀))` matches `Q` and `Q'` at `t₀`; if the inequality failed at `t₀`, `Q − S` (a degree ≤ β trig poly) would have `> 2β` zeros/sign changes on a period, contradicting step 2. Conclude the pointwise bound.

If a cleaner Mathlib-native route exists (e.g. a direct `Polynomial.Chebyshev`/`Complex` argument, or an existing Bernstein/Markov lemma), take it — the deliverable is `szego_deriv_sq_bound`, however proved.

## Standard reference
Szegő's inequality / Bernstein's inequality for trigonometric polynomials; see Rivlin, "The Chebyshev Polynomials" (1974), or DeVore–Lorentz "Constructive Approximation" Ch. 4 (Bernstein–Szegő). Standard, classical.

## Intended reuse
Discharges the last 2 sorries of `CausalSmith/Substrate/EhlichZellerMesh/Bernstein.lean` (`czTrig_szego_deriv` and, via it, `czTrig_arccos_lipschitz`), completing the Ehlich–Zeller mesh inequality and thereby the headline of run `exp_rollout_chebyshev_minimax / tv_envelope_rollout_design`. Needs the general R-of-arbitrary-degree-β statement.

## May assume / must derive
- MAY assume Mathlib real/complex analysis: `Real.cos`, `Real.sin`, `deriv`, chain rule, `Polynomial.eval`, `Polynomial.natDegree`, `Complex.exp`, `Polynomial.roots`, `Polynomial.card_roots_le_degree`.
- MUST derive: the ≤2β-zeros lemma (step 2) and the Szegő comparison (step 3). Do NOT assume Bernstein/Szegő as an unproven axiom or `sorry`. If, after a genuine attempt, step 2 (the z=e^{it} zero-count) or step 3 needs a substantial upstream Mathlib development, STOP and report the precise remaining sub-lemma as the blocker — honest partial progress with a precise blocker is valuable.

## Non-goals (optional)
The `L^p` Bernstein inequality, sharp constants beyond `β`, complex-coefficient trig polynomials, and the general (non-`R(cos t)`) trig-polynomial formulation are out of scope. Only the even `R(cos t)` form is needed.

## Known building blocks (optional)
- `Real.deriv_cos`, `Real.sin_sq_add_cos_sq`, `Polynomial.deriv`, chain rule (`deriv_comp` / `HasDerivAt.comp`).
- `Complex.exp`, `Complex.cos`, the substitution `cos t = (e^{it}+e^{-it})/2`.
- `Polynomial.roots`, `Polynomial.card_roots_le_degree`, `Multiset.card`.

## Target module (optional)
`Causalean.Mathlib.Analysis.BernsteinSzego`
