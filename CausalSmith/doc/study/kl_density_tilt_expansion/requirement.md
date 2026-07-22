# Substrate requirement: kl_density_tilt_expansion

## Goal
Second-order Taylor expansion of the Kullback–Leibler divergence of a bounded linear density tilt: for a probability measure μ and a bounded score s with mean zero, `KL((1 + h·s)·μ ‖ μ) = (h²/2)·∫ s² dμ + o(h²)` as `h → 0`.

## Provides (API contract)
- `tiltMeasure (μ) (s : ℝ → ℝ) (h : ℝ) : Measure _ := μ.withDensity (fun y => ENNReal.ofReal (1 + h * s y))` — the linear tilt (or reuse an existing `withDensity` form).
- `tiltMeasure_isProbability : (bounded s) → (∫ s dμ = 0) → |h| small → IsProbabilityMeasure (tiltMeasure μ s h)` — the tilt is a probability measure for small `|h|`.
- `klDiv_tilt_expansion : (bounded s, ∫ s dμ = 0) → (fun h => (InformationTheory.klDiv (tiltMeasure μ s h) μ).toReal − (h^2/2) * ∫ y, s y ^ 2 ∂μ) =o[𝓝 0] (fun h => h^2)` — the MAIN result (the `o(h²)` KL expansion, in `Asymptotics.IsLittleO` form).

## Statement / milestones
For μ a probability measure and s : ℝ → ℝ bounded (`∃ C, ∀ y, |s y| ≤ C`) with `∫ s dμ = 0`:
- For `|h| ≤ 1/(2C)`, `1 + h·s ≥ 1/2 > 0` a.e., so `tiltMeasure μ s h` is a probability measure (density integrates to `1 + h·∫s = 1`).
- `KL((1+h s)μ ‖ μ) = ∫ (1 + h s)·log(1 + h s) dμ`. Using `(1+x)·log(1+x) = x + x²/2 + O(x³)` uniformly for `|x| ≤ 1/2` and `∫ s dμ = 0`: `= (h²/2)·∫ s² dμ + o(h²)`.
Deliver the `o(h²)` remainder rigorously (dominated remainder via the uniform cubic bound on the bounded support).

## Standard reference
Standard local-asymptotic-normality / Fisher-information expansion; e.g. van der Vaart, *Asymptotic Statistics*, Ch. 5 (differentiability in quadratic mean), or any information-geometry text (KL ≈ ½·Fisher).

## Intended reuse
Consumed by the CausalSmith research run `stat_neyman_regret_minimax`: `linear_tilt_path_valid` / `IsLocalPath` — the arm-marginal KL clause `KL(nu_a^h, nu_a) = (h²/2)·armScoreCost nu a u_a + o(h²)` (the tilt is `dnu_a^h = (1 + h s_a) dnu_a`). General-measure generality.

## May assume / must derive
May assume: μ a probability measure, s bounded and mean-zero. Must derive: the probability-measure property of the tilt for small h, and the `o(h²)` KL expansion — from the definitions of `withDensity`, `klDiv`, and the elementary `(1+x)log(1+x)` expansion. Do not assume the expansion.

## Known building blocks
`InformationTheory.klDiv`, `MeasureTheory.Measure.withDensity`, `Real.add_one_mul_log` / `Real.log` expansions, `Asymptotics.IsLittleO`, `MeasureTheory.integral_*`, dominated convergence for the remainder.

## Target module
Causalean.Mathlib.InformationTheory.KLDensityTiltExpansion
