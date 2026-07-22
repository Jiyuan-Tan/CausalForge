# Substrate requirement: gaussian_kl

## Goal
Compute the closed-form Kullback–Leibler divergence between two real Gaussian
measures (`ProbabilityTheory.gaussianReal`), which Mathlib does not provide.

## Provides (API contract)
Using Mathlib's `gaussianReal m v` (mean `m : ℝ`, variance `v : ℝ≥0`) and
`MeasureTheory.klDiv` (value in `ℝ≥0∞`):
- `gaussianKL_eq` (REQUIRED — the reusable workhorse): for equal variance `v` with
  `0 < v`,
      `klDiv (gaussianReal m₀ v) (gaussianReal m₁ v)
         = ENNReal.ofReal ((m₀ - m₁)^2 / (2 * (v : ℝ)))`.
  This is the canonical KL input for Gaussian-location minimax lower bounds.
- `gaussianKL_general` (OPTIONAL stretch — only if it falls out cleanly): for
  `0 < v₀`, `0 < v₁`,
      `klDiv (gaussianReal m₀ v₀) (gaussianReal m₁ v₁)
         = ENNReal.ofReal ((1/2) * (Real.log (v₁/v₀) + v₀/v₁
             + (m₀ - m₁)^2 / v₁ - 1))`.
  Skip / escalate this one if it needs substantially more than the equal-variance
  proof; `gaussianKL_eq` alone fulfills the goal.

## Statement / milestones (equal-variance route — a sketch, not a mandate)
1. Absolute continuity: `gaussianReal m₀ v ≪ gaussianReal m₁ v` (both are
   `volume.withDensity (gaussianPDF · v)` with a strictly positive pdf, hence
   mutually absolutely continuous with `volume`).
2. Log-likelihood ratio: `llr (gaussianReal m₀ v) (gaussianReal m₁ v)` is a.e. equal
   to `x ↦ (m₀ - m₁) * (2*x - m₀ - m₁) / (2*v)` — the difference of the two Gaussian
   log-densities (the normalizing constants cancel at equal variance; `rnDeriv` ratio
   = `gaussianPDF m₀ v / gaussianPDF m₁ v`).
3. Integrability of that llr under `gaussianReal m₀ v` (it is affine in `x`, and the
   Gaussian has finite first moment).
4. `klDiv = ∫ llr ∂(gaussianReal m₀ v)`; evaluate using `∫ x ∂gaussianReal m₀ v = m₀`
   (`integral_id_gaussianReal`):  `(m₀-m₁)·(2 m₀ - m₀ - m₁)/(2 v) = (m₀-m₁)^2/(2 v)`.
5. Package as `ENNReal.ofReal` of the (nonnegative) closed form.

(The proof route is the scaffolder's call — any sound, sorry-free derivation of the
stated equality is acceptable. The general formula additionally needs the second
moment / variance of the Gaussian and the `log (v₁/v₀)` term.)

## Standard reference
Standard closed form (any information-theory / statistics text), e.g. Cover & Thomas
or the Gaussian-KL identity `KL(N(m₀,σ²) ∥ N(m₁,σ²)) = (m₀−m₁)²/(2σ²)`; general two-
variance form `KL = ½(log(σ₁²/σ₀²) + σ₀²/σ₁² + (m₀−m₁)²/σ₁² − 1)`. FETCH a reference to
confirm the exact general-form constants if attempting the stretch goal.

## Intended reuse
The canonical KL input for Gaussian-location minimax lower bounds: feed `gaussianKL_eq`
into the existing `Causalean.Stat.klForm_two_point_lower_bound` (and the iid product-KL
tensorization) to obtain Le Cam / two-point converses for any Gaussian-noise estimation
problem (Gaussian sequence model, normal-means, Gaussian-noise dose-response). Must be
generic in `m₀, m₁, v`.

## May assume / must derive
- MAY assume: `0 < v` (nondegenerate Gaussian; for the general case `0 < v₀, 0 < v₁`).
- MUST derive (no `sorry`, no assumed gaussian-KL gate): the absolute continuity, the
  llr formula, the integrability, and the integral evaluation — from Mathlib's
  `gaussianReal` / `klDiv` API. Do NOT assume the closed form (or `klDiv`'s value) as a
  black-box hypothesis.

## Non-goals
- No multivariate / `EuclideanSpace` Gaussian KL (real `gaussianReal` only).
- No degenerate `v = 0` (Dirac) case.
- Do NOT re-prove Mathlib's Gaussian API (`rnDeriv_gaussianReal`, `integral_id_gaussianReal`,
  `gaussianPDF` facts) — import and use them.

## Known building blocks
- `ProbabilityTheory.gaussianReal`, `gaussianReal_of_var_ne_zero`
  (`= volume.withDensity (gaussianPDF μ v)`), `gaussianPDF`, `gaussianPDFReal`,
  `rnDeriv_gaussianReal` (`∂(gaussianReal μ v)/∂volume =ᵃˢ gaussianPDF μ v`),
  `integral_id_gaussianReal` (`∫ x ∂gaussianReal μ v = μ`), `noAtoms_gaussianReal`.
- `MeasureTheory.klDiv`, `klDiv_eq_integral_klFun` / `klDiv_of_ac_of_integrable`,
  `ProbabilityTheory.llr`, `llr_def`, and `Measure.rnDeriv` / `withDensity` lemmas for
  absolute continuity.
- `Real.log_div`, `Real.log_mul`, `Real.log_exp`, basic `integral` linearity.

## Target module (optional)
Causalean.Mathlib.InformationTheory.GaussianKL
