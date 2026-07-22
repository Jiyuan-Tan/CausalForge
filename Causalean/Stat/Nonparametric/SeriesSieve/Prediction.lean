/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.LeastSquares.NormalEquations
import Causalean.Stat.Nonparametric.LeastSquares.SmootherVariance

/-!
# Series / sieve least-squares prediction error

Prediction-error decompositions for series least squares, combining deterministic approximation
error with the spherical-noise variance of the projected fit.

This file assembles the **series least-squares prediction rate** `O(J^{−s/d} + √(J/N))` from the
two reusable substrate pieces:

* **approximation** (deterministic, bias side): the empirical best-approximation error of the
  least-squares fit is controlled by the sup-norm error of any comparator, so an externally supplied
  approximation bound can transfer to the weighted empirical objective;
* **stochastic** (variance side): the exact orthogonal (Pythagorean) decomposition of the
  prediction error splits off the projected noise, whose expected weighted quadratic form is
  `σ² · (effective degrees of freedom)`.

Conditioning on the design, the data fit `Φ ĉ` and the noise-free projection `Φ ĉ⁰` differ by a
*deterministic linear image* of the noise (the hat matrix), so the stochastic term's expectation
reduces, via the Gauss–Markov spherical-variance identity (`linearSmoother_variance_spherical`),
to `σ²·∑ᵢ wᵢ ∑ₖ aᵢₖ²`. If a separate design argument bounds that effective-degree-of-freedom
sum by `V`, and if a separate approximation argument bounds the noise-free projection error by
`A`, the main theorem gives the oracle inequality `A + σ² V`.

All results are generic in the design matrix `Φ` (Newey 1997; Chen 2007; Belloni–Chernozhukov–
Chetverikov–Kato 2015).
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- **Empirical approximation error is controlled by the best uniform approximant.** If the
least-squares fit `c` to target values `f` has residual orthogonal to every design column
(`lstsq_normal_equations`) and some comparator `cstar` approximates `f` uniformly within `δ` at
the design points (`|fᵢ − ∑ⱼ cstarⱼ Φᵢⱼ| ≤ δ`), then the empirical fit error is at most
`(∑ᵢ wᵢ)·δ²`. With the Jackson rate `δ = C·J^{−s/d}` this is the empirical best-approximation
half of the series prediction rate. -/
theorem seriesApprox_le_of_sup {N : ℕ} {ι : Type*} [Fintype ι]
    {Φ : Fin N → ι → ℝ} {w f : Fin N → ℝ} {c cstar : ι → ℝ} {δ : ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hortho : ∀ k : ι, ∑ i, w i * lstsqResidual Φ f c i * Φ i k = 0)
    (hsup : ∀ i, |f i - ∑ j, cstar j * Φ i j| ≤ δ) :
    lstsqObjective Φ w f c ≤ (∑ i, w i) * δ ^ 2 := by
  have hopt := lstsq_objective_le_of_orthogonal hw hortho cstar
  refine hopt.trans ?_
  unfold lstsqObjective
  calc
    ∑ i, w i * lstsqResidual Φ f cstar i ^ 2
        ≤ ∑ i, w i * δ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (hw i)
          have hres : |lstsqResidual Φ f cstar i| ≤ δ := by
            simpa [lstsqResidual] using hsup i
          calc
            lstsqResidual Φ f cstar i ^ 2 = |lstsqResidual Φ f cstar i| ^ 2 := (sq_abs _).symm
            _ ≤ δ ^ 2 := by
                  apply pow_le_pow_left₀ (abs_nonneg _) hres
    _ = (∑ i, w i) * δ ^ 2 := by rw [← Finset.sum_mul]

/-- **Pythagorean decomposition of the series prediction error.** If the noise-free projection
coefficient `c0` (least-squares fit to the true values `f`) has residual orthogonal to every
design column, then for *any* coefficient vector `chat` the prediction error of `Φ·chat` against
the truth `f` splits exactly into the approximation error of the projection plus the squared
fitted-value gap:

`‖f − Φ·chat‖²_w = ‖f − Φ·c0‖²_w + ∑ᵢ wᵢ (∑ⱼ (c0ⱼ − chatⱼ) Φᵢⱼ)²`.

For `chat` the data least-squares fit, the second term is the projected noise. (Immediate from
`lstsq_pythagoras` with target `f`, base `c0`, comparator `chat`.) -/
theorem seriesLS_prediction_decomp {N : ℕ} {ι : Type*} [Fintype ι]
    {Φ : Fin N → ι → ℝ} {w f : Fin N → ℝ} {c0 chat : ι → ℝ}
    (hortho : ∀ k : ι, ∑ i, w i * lstsqResidual Φ f c0 i * Φ i k = 0) :
    lstsqObjective Φ w f chat
      = lstsqObjective Φ w f c0 + ∑ i, w i * (∑ j, (c0 j - chat j) * Φ i j) ^ 2 :=
  lstsq_pythagoras hortho chat

/-- **Expected weighted quadratic form of a deterministic linear image of spherical mean-zero
noise.** If `ε` is a spherical mean-zero square-integrable family with scale `σ`, and `a` is a
deterministic matrix of coefficients, then the linear image `Dᵢ(ω) = ∑ₖ aᵢₖ εₖ(ω)` has expected
weighted sum of squares

`𝔼[∑ᵢ wᵢ Dᵢ²] = σ² · ∑ᵢ wᵢ ∑ₖ aᵢₖ²`.

The weights are arbitrary real weights in this identity; nonnegative or normalized weights are not
assumed here. -/
theorem expected_weighted_sq_image_spherical {Ω : Type*} {N : ℕ} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : Fin N → Ω → ℝ} {a : Fin N → Fin N → ℝ}
    {w : Fin N → ℝ} {σ : ℝ}
    (hε : ∀ k, MemLp (ε k) 2 μ)
    (hmean : ∀ k, ∫ ω, ε k ω ∂μ = 0)
    (hsph : Causalean.GaussMarkov.SphericalFamily ε μ σ) :
    ∫ ω, ∑ i, w i * (∑ k, a i k * ε k ω) ^ 2 ∂μ
      = σ ^ 2 * ∑ i, w i * ∑ k, a i k ^ 2 := by
  -- RECIPE (codex):
  -- Let `D i ω = ∑ k, a i k * ε k ω`.
  -- (1) Pull the finite sum out of the integral: `integral_finset_sum`, with each summand
  --     `fun ω => w i * (D i ω)^2` integrable. Integrability: `(D i)` is `MemLp _ 2` as a finite
  --     sum of `L²` functions (`MemLp.const_mul`, `memLp_finset_sum'`), so `(D i)^2` is `L¹`
  --     (`MemLp.integrable_sq` / `MemLp.integrable (le_refl)` after `.pow`); the `w i *` is a
  --     constant multiple (`Integrable.const_mul`).
  -- (2) Constant `w i` out of each integral (`integral_const_mul`).
  -- (3) `∫ (D i)^2 = Var[D i; μ]`: because `∫ D i = ∑ k a i k * ∫ ε k = 0` (linearity of the
  --     integral over the finite sum + `hmean`). Use `ProbabilityTheory.variance_eq`
  --     (`Var[X] = ∫ X^2 - (∫ X)^2`, valid for `MemLp X 2`) and simplify the `(∫ D i)^2 = 0` term.
  --     The variance form: `Var[fun ω => ∑ k, a i k * ε k ω; μ]`.
  -- (4) `Var[fun ω => ∑ k, a i k * ε k ω; μ] = σ^2 * ∑ k, (a i k)^2` by
  --     `linearSmoother_variance_spherical (S := a i) hε hsph`.
  -- (5) Assemble: `∑ i, w i * (σ^2 * ∑ k, (a i k)^2) = σ^2 * ∑ i, w i * ∑ k, (a i k)^2`
  --     via `Finset.mul_sum`/`ring`-style sum manipulation (reduce with
  --     `Finset.sum_congr rfl (fun _ _ => ?_)` then `ring` at the scalar leaf).
  let D : Fin N → Ω → ℝ := fun i ω => ∑ k, a i k * ε k ω
  have hDmemlp : ∀ i, MemLp (D i) 2 μ := by
    intro i
    dsimp [D]
    convert memLp_finset_sum' Finset.univ
        (fun k _ => (hε k).const_mul (a i k)) using 1
    ext ω
    simp
  have hDint : ∀ i, ∫ ω, D i ω ∂μ = 0 := by
    intro i
    calc
      ∫ ω, D i ω ∂μ = ∫ ω, ∑ k, a i k * ε k ω ∂μ := rfl
      _ = ∑ k, ∫ ω, a i k * ε k ω ∂μ := by
            simpa using
              (integral_finset_sum Finset.univ
                (fun k _ => ((hε k).const_mul (a i k)).integrable (by norm_num)))
      _ = 0 := by
            simp [integral_const_mul, hmean]
  have hDsq : ∀ i, ∫ ω, (D i ω) ^ 2 ∂μ = σ ^ 2 * ∑ k, a i k ^ 2 := by
    intro i
    have hvarint : Var[D i; μ] = ∫ ω, (D i ω) ^ 2 ∂μ := by
      rw [variance_eq_integral (hDmemlp i).aemeasurable]
      rw [hDint i]
      simp
    calc
      ∫ ω, (D i ω) ^ 2 ∂μ = Var[D i; μ] := hvarint.symm
      _ = σ ^ 2 * ∑ k, a i k ^ 2 := by
            simpa [D] using
              (linearSmoother_variance_spherical (Y := ε) (S := a i) (σ := σ) hε hsph)
  have hterm_int : ∀ i, Integrable (fun ω => w i * (D i ω) ^ 2) μ := by
    intro i
    exact (hDmemlp i).integrable_sq.const_mul (w i)
  calc
    ∫ ω, ∑ i, w i * (∑ k, a i k * ε k ω) ^ 2 ∂μ
        = ∫ ω, ∑ i, w i * (D i ω) ^ 2 ∂μ := by
          simp [D]
    _ = ∑ i, ∫ ω, w i * (D i ω) ^ 2 ∂μ := by
          simpa using
            (integral_finset_sum Finset.univ (fun i _ => hterm_int i))
    _ = ∑ i, w i * ∫ ω, (D i ω) ^ 2 ∂μ := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [integral_const_mul]
    _ = ∑ i, w i * (σ ^ 2 * ∑ k, a i k ^ 2) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hDsq i]
    _ = σ ^ 2 * ∑ i, w i * ∑ k, a i k ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring

/-- **Conditional oracle inequality for series least-squares prediction.** Combining a supplied
approximation bound for the noise-free projection with the exact Pythagorean decomposition and the
spherical stochastic-term identity, the expected weighted quadratic prediction error of the fitted
series coefficients against the target values is

`𝔼[‖f − Φ·ĉ‖²_w] ≤ A + σ² V`,

where `A` is the assumed bound on the noise-free least-squares objective and `V` is the assumed
bound on the weighted coefficient sum `∑ᵢ wᵢ ∑ₖ aᵢₖ²`. The theorem does not itself supply
smoothness rates, nonnegative or normalized weights, or an effective-degree-of-freedom calculation;
those are supplied — and the full `O(J^{−2s/d} + J/N)` series/sieve rate assembled — in
`Causalean.Stat.Nonparametric.SeriesSieve.seriesLS_prediction_rate` (module `PredictionRate`).

Hypotheses: `c0` is the noise-free projection (orthogonal residual against `f`); the data fit
`chat ω` differs from `c0` by the deterministic linear image `a` of the noise `ε`
(`hlin` — the hat-matrix linearity of least squares); `ε` is spherical mean-zero `L²`. -/
theorem seriesLS_expected_prediction_le {Ω : Type*} {N : ℕ} {ι : Type*} [Fintype ι]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Φ : Fin N → ι → ℝ} {w f : Fin N → ℝ} {c0 : ι → ℝ}
    {chat : Ω → ι → ℝ} {ε : Fin N → Ω → ℝ} {a : Fin N → Fin N → ℝ}
    {σ A V : ℝ}
    (hortho : ∀ k : ι, ∑ i, w i * lstsqResidual Φ f c0 i * Φ i k = 0)
    (hApprox : lstsqObjective Φ w f c0 ≤ A)
    (hlin : ∀ ω, ∀ i, (∑ j, (c0 j - chat ω j) * Φ i j) = ∑ k, a i k * ε k ω)
    (hε : ∀ k, MemLp (ε k) 2 μ) (hmean : ∀ k, ∫ ω, ε k ω ∂μ = 0)
    (hsph : Causalean.GaussMarkov.SphericalFamily ε μ σ)
    (hlev : (∑ i, w i * ∑ k, a i k ^ 2) ≤ V) :
    ∫ ω, lstsqObjective Φ w f (chat ω) ∂μ ≤ A + σ ^ 2 * V := by
  -- Pointwise decomposition + linearity substitution.
  have hpt : ∀ ω, lstsqObjective Φ w f (chat ω)
      = lstsqObjective Φ w f c0 + ∑ i, w i * (∑ k, a i k * ε k ω) ^ 2 := by
    intro ω
    rw [seriesLS_prediction_decomp hortho]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hlin ω i]
  -- Integrate.
  have hstoch_int : Integrable
      (fun ω => ∑ i, w i * (∑ k, a i k * ε k ω) ^ 2) μ := by
    apply integrable_finset_sum
    intro i _
    have hD : MemLp (fun ω => ∑ k, a i k * ε k ω) 2 μ := by
      convert memLp_finset_sum' Finset.univ
          (fun k _ => (hε k).const_mul (a i k)) using 1
      ext ω
      simp
    exact (hD.integrable_sq.const_mul (w i))
  calc
    ∫ ω, lstsqObjective Φ w f (chat ω) ∂μ
        = ∫ ω, (lstsqObjective Φ w f c0
            + ∑ i, w i * (∑ k, a i k * ε k ω) ^ 2) ∂μ := by
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = lstsqObjective Φ w f c0
            + ∫ ω, ∑ i, w i * (∑ k, a i k * ε k ω) ^ 2 ∂μ := by
          rw [integral_add (integrable_const _) hstoch_int, integral_const]
          simp
    _ = lstsqObjective Φ w f c0 + σ ^ 2 * ∑ i, w i * ∑ k, a i k ^ 2 := by
          rw [expected_weighted_sq_image_spherical hε hmean hsph]
    _ ≤ A + σ ^ 2 * V := by
          have hvar : σ ^ 2 * ∑ i, w i * ∑ k, a i k ^ 2 ≤ σ ^ 2 * V :=
            mul_le_mul_of_nonneg_left hlev (sq_nonneg σ)
          linarith

end Causalean.Stat.Nonparametric
