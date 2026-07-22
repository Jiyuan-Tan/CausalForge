# Substrate requirement: converging_together_clt

## Goal
Prove the general "converging-together" (Billingsley Thm 3.2 / Slutsky-for-⇒) theorem: a sequence
of real random variables that is approximated in L² by a triangular family, each row of which
converges in distribution to a common limit law, itself converges in distribution to that limit.
This is the load-bearing diagonal step of every approximation-based CLT (m-dependent approximation
of a mixing / ψ-dependent field, blocking arguments, etc.).

## Provides (API contract)
- `tendsto_charFun_sub_le` — the characteristic-function approximation bound: for real,
  integrable `S T : Ω → ℝ` on a probability measure `μ` and `t : ℝ`,
  `‖charFun (μ.map S) t − charFun (μ.map T) t‖ ≤ |t| * ∫ ω, |S ω − T ω| ∂μ`
  (hence `≤ |t| * (∫ |S − T|²)^(1/2)` by Cauchy–Schwarz). The elementary input is
  `‖Complex.exp (i a) − Complex.exp (i b)‖ ≤ |a − b|`.
- `tendsto_inDistribution_of_l2_approx` — the converging-together theorem. Let `G` be a limit
  probability measure on `ℝ`, `S : ℕ → Ω n → ℝ`, and for each `m` a row `T m : ℕ → Ω n → ℝ`
  (square-integrable, on probability measures `μ n`). If
  (H1) for every `m`, the laws `(μ n).map (T m n)` converge weakly to `G` as `n → ∞`, and
  (H2) `∀ ε > 0, ∃ M, ∀ m ≥ M, limsup_n ∫ ω, |S n ω − T m n ω|² ∂(μ n) ≤ ε`,
  then `(μ n).map (S n)` converges weakly to `G` as `n → ∞`.
- `clt_of_l2_approx` — the specialization with `G = gaussianReal 0 1`, packaged as the standard-
  normal converging-together corollary (the shape an m-dependent-approximation CLT consumes).

## Statement / milestones
1. **charFun Lipschitz-in-L¹ bound** (`tendsto_charFun_sub_le`): from
   `‖cexp (i·a) − cexp (i·b)‖ ≤ |a − b|` and `charFun ν t = ∫ cexp (i·t·x) dν`, bound the
   difference of the two pushforward char-functions by `|t| · ∫|S − T| dμ`; then Cauchy–Schwarz to
   the L² form.
2. **Diagonal ε/3 argument** (`tendsto_inDistribution_of_l2_approx`): work through characteristic
   functions. For each `t`, `|charFun(law S n)(t) − charFun(G)(t)| ≤
   |charFun(law S n) − charFun(law T m n)| + |charFun(law T m n) − charFun(G)|`. Bound the first by
   (1) + (H2); the second → 0 by (H1) (weak convergence ⇒ pointwise charFun convergence, the easy
   direction of Lévy continuity). Pick `m` large then `n` large (the iterated-limit (H2)).
   Conclude pointwise `charFun(law S n)(t) → charFun(G)(t)` for all `t`.
3. **Lévy continuity** to upgrade pointwise charFun convergence to weak convergence of `law S n`
   to `G` — use the `clt` package's continuity theorem
   `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun` (and `tendsto_of_tendsto_charFun`).
4. **Corollary** `clt_of_l2_approx` with `G = gaussianReal 0 1`.

## Standard reference
Billingsley, *Convergence of Probability Measures* (2nd ed.), Theorem 3.2 (the "converging
together"/approximation theorem); the characteristic-function proof is standard (e.g. via Lévy's
continuity theorem). Used as the diagonal step in Bolthausen (1982, Ann. Probab. 10:1047) and
Chen–Shao (2004) for mixing/locally-dependent CLTs.

## Intended reuse
The diagonal step of ANY approximation-based CLT. The immediate consumer is a future
ψ-dependence / mixing network CLT (`Causalean.Experimentation.SuperPopulation`), which approximates
a decaying-dependence field by its radius-m conditional-expectation truncation and needs exactly
this lemma to pass from the per-m m-dependent CLT (already proved: `networkSum_clt`) to the limit.
Also reusable for design-based blocking-CLT arguments. Fully general (not network-specific), so it
belongs in `Causalean.Mathlib.Probability`.

## May assume / must derive
- **May assume**: `S n`, `T m n` are measurable and square-integrable under the probability
  measures `μ n`; the per-row weak convergence (H1) and the iterated-L² control (H2) are the
  hypotheses. The limit `G` is an arbitrary probability measure on `ℝ` (then specialized to
  Gaussian).
- **Must derive**: the charFun bound (1) and the diagonal argument (2)–(3) from these hypotheses.
  Do NOT assume a Slutsky/converging-together result (that IS the goal). Reuse the `clt` package's
  Lévy continuity theorem rather than re-proving it. Do NOT specialize the statement to a network /
  m-dependent setting — keep it a general real-RV approximation theorem.

## Non-goals
- The m-dependent approximation-error bound itself (the `∑_{s>m} D_n(s)·θ_{n,s}` mixing-tail
  estimate) — that is ψ-dependence-specific and belongs to the future mixing-CLT run.
- Any Stein bound under covariance-decay, and any coupling (Berbee/Bradley) construction.
- Multivariate / metric-space generality; real-valued is enough for the CLT consumers.

## Known building blocks
- `clt` package (`.lake/packages/clt/Clt/Inversion.lean`):
  `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`,
  `MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun` (Lévy continuity);
  `Clt/Tight.lean`, `Clt/Prokhorov.lean` for weak-convergence/tightness plumbing.
- Mathlib: `charFun` and its integral form; `Complex.norm_exp_… ` / the bound
  `‖cexp (I*a) − cexp (I*b)‖ ≤ |a−b|`; `MeasureTheory.integral_mono`,
  Cauchy–Schwarz (`MeasureTheory.integral_mul_le_L2…` / `inner_mul_le_norm_mul_norm`),
  `Filter.limsup`, `gaussianReal`, `Filter.Tendsto` ε/3 lemmas.

## Target module
`Causalean.Mathlib.Probability.ConvergingTogether`
