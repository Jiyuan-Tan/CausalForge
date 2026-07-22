/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.SeriesSieve.Prediction

/-!
# Series / sieve least-squares prediction rate `O(J^{−2s/d} + J/N)`

The Causalean file `Causalean.Stat.Nonparametric.SeriesSieve.Prediction` proves a *conditional*
oracle inequality `seriesLS_expected_prediction_le`:

    𝔼[‖f − Φ·ĉ‖²_w] ≤ A + σ² · V,

where `A` is any bound on the noise-free least-squares objective (bias side) and `V` is any bound
on the effective-degrees-of-freedom sum `∑ᵢ wᵢ ∑ₖ aᵢₖ²` (variance side). This module supplies the
two missing rate ingredients and combines them into the standard series/sieve prediction rate.

## Main results

* `jacksonSeriesBias_le` — squares the Jackson best-approximation bound
  `A ≤ (∑ᵢ wᵢ)·(C_J·J^{−s/d})²` into the explicit bias rate `A ≤ ((∑ᵢ wᵢ)·C_J²)·J^{−2s/d}`.
  The Jackson approximation power of the sieve is taken as an explicit hypothesis (no attempt to
  prove Jackson's theorem for a concrete basis).
* `seriesEffectiveDoF_le` — for normalized weights `wᵢ = 1/N` and a Frobenius / trace hypothesis on
  the hat map `∑ᵢ ∑ₖ aᵢₖ² ≤ Cvar·J`, the effective-degrees-of-freedom sum obeys
  `∑ᵢ wᵢ ∑ₖ aᵢₖ² ≤ Cvar·J/N`, i.e. it is controlled by (basis dimension)/(sample size). The trace
  bound is an explicit hypothesis (not derived from an explicit Gram matrix).
* `seriesLS_prediction_rate` — feeds the two suppliers into `seriesLS_expected_prediction_le` to
  obtain the full rate `𝔼[‖f − Φ·ĉ‖²_w] ≤ ((∑ᵢ wᵢ)·C_J²)·J^{−2s/d} + σ²·(Cvar·J/N)`.

Here `J^{−s/d}` is the real power `(J : ℝ) ^ (-(s/d))` (`Real.rpow`), keeping `s, d, J, N, σ` as
free parameters; no concrete basis is assumed. See Newey (1997), Chen (2007),
Belloni–Chernozhukov–Chetverikov–Kato (2015) for the econometric series-estimator theory and
DeVore–Lorentz, *Constructive Approximation*, for the Jackson/Bernstein bias term.
-/

namespace Causalean.Stat.Nonparametric.SeriesSieve

open Causalean.Stat.Nonparametric
open scoped BigOperators

/-- **Jackson bias rate for the series least-squares objective.** Given the squared Jackson
best-approximation bound `A ≤ (∑ᵢ wᵢ)·(C_J·J^{−s/d})²` on the noise-free least-squares objective
`A := lstsqObjective Φ w f c0` (the shape produced by `seriesApprox_le_of_sup` with sup-error
`δ = C_J·J^{−s/d}`), the objective satisfies the explicit bias rate

    A ≤ ((∑ᵢ wᵢ)·C_J²) · J^{−2s/d}.

The power `J^{−s/d}` is the real power `(J : ℝ) ^ (-(s/d))`; squaring it doubles the exponent to
`−2s/d`. The Jackson approximation power is an assumed hypothesis (no concrete basis). -/
theorem jacksonSeriesBias_le {N : ℕ} {ι : Type*} [Fintype ι]
    {Φ : Fin N → ι → ℝ} {w f : Fin N → ℝ} {c0 : ι → ℝ}
    {s d C_J : ℝ} {J : ℕ}
    (hJack : lstsqObjective Φ w f c0
      ≤ (∑ i, w i) * (C_J * (J : ℝ) ^ (-(s / d))) ^ 2) :
    lstsqObjective Φ w f c0 ≤ ((∑ i, w i) * C_J ^ 2) * (J : ℝ) ^ (-(2 * s / d)) := by
  -- Rewrite the squared Jackson bound into the doubled-exponent rate, then transfer `hJack`.
  have hpow : ((J : ℝ) ^ (-(s / d))) ^ 2 = (J : ℝ) ^ (-(2 * s / d)) := by
    rw [← Real.rpow_natCast ((J : ℝ) ^ (-(s / d))) 2,
        ← Real.rpow_mul (Nat.cast_nonneg J)]
    congr 1
    push_cast
    ring
  have hrw : (∑ i, w i) * (C_J * (J : ℝ) ^ (-(s / d))) ^ 2
      = ((∑ i, w i) * C_J ^ 2) * (J : ℝ) ^ (-(2 * s / d)) := by
    rw [mul_pow, hpow]; ring
  exact hJack.trans_eq hrw

/-- **Effective degrees of freedom is controlled by `J/N`.** For normalized least-squares weights
`wᵢ = 1/N` and a Frobenius/trace hypothesis on the hat map `a`, namely `∑ᵢ ∑ₖ aᵢₖ² ≤ Cvar·J`, the
weighted coefficient sum (the effective degrees of freedom `V` of the oracle inequality) obeys

    ∑ᵢ wᵢ ∑ₖ aᵢₖ² ≤ Cvar · J / N.

For a rank-`J` projection hat matrix the Frobenius sum equals the trace `= J`, so this expresses the
standard "effective DoF ≈ J" fact after normalization by `N`; the trace bound is taken as an
explicit hypothesis rather than derived from an explicit Gram matrix. -/
theorem seriesEffectiveDoF_le {N : ℕ} {a : Fin N → Fin N → ℝ} {w : Fin N → ℝ}
    {Cvar : ℝ} {J : ℕ} (hN : 0 < N)
    (hw : ∀ i, w i = (1 : ℝ) / N)
    (htr : (∑ i, ∑ k, a i k ^ 2) ≤ Cvar * J) :
    (∑ i, w i * ∑ k, a i k ^ 2) ≤ Cvar * (J : ℝ) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (∑ i, w i * ∑ k, a i k ^ 2)
        = (1 / (N : ℝ)) * ∑ i, ∑ k, a i k ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by rw [hw i])
    _ ≤ (1 / (N : ℝ)) * (Cvar * J) := by
          exact mul_le_mul_of_nonneg_left htr (by positivity)
    _ = Cvar * (J : ℝ) / N := by ring

/-- **Series / sieve least-squares prediction rate `O(J^{−2s/d} + J/N)`.** Combining the Jackson
bias supplier `jacksonSeriesBias_le` and the effective-degrees-of-freedom supplier
`seriesEffectiveDoF_le` with the conditional oracle inequality `seriesLS_expected_prediction_le`,
the expected weighted quadratic prediction error of the fitted series coefficients obeys the
standard series/sieve rate

    𝔼[‖f − Φ·ĉ‖²_w] ≤ ((∑ᵢ wᵢ)·C_J²) · J^{−2s/d} + σ² · (Cvar · J / N).

Bias hypothesis `hJack`: the squared Jackson best-approximation bound. Variance hypotheses
`hw`/`htr`: normalized weights and the hat-matrix Frobenius/trace bound. Design/noise hypotheses
`hortho`, `hlin`, `hε`, `hmean`, `hsph` are exactly those of the underlying oracle inequality
(`c0` the noise-free projection, `a` the hat-matrix linear image of the spherical mean-zero `L²`
noise `ε`). -/
theorem seriesLS_prediction_rate {Ω : Type*} {N : ℕ} {ι : Type*} [Fintype ι]
    [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {Φ : Fin N → ι → ℝ} {w f : Fin N → ℝ} {c0 : ι → ℝ}
    {chat : Ω → ι → ℝ} {ε : Fin N → Ω → ℝ} {a : Fin N → Fin N → ℝ}
    {s d C_J Cvar σ : ℝ} {J : ℕ}
    (hN : 0 < N)
    (hortho : ∀ k : ι, ∑ i, w i * lstsqResidual Φ f c0 i * Φ i k = 0)
    (hlin : ∀ ω, ∀ i, (∑ j, (c0 j - chat ω j) * Φ i j) = ∑ k, a i k * ε k ω)
    (hε : ∀ k, MeasureTheory.MemLp (ε k) 2 μ)
    (hmean : ∀ k, ∫ ω, ε k ω ∂μ = 0)
    (hsph : Causalean.GaussMarkov.SphericalFamily ε μ σ)
    (hJack : lstsqObjective Φ w f c0
      ≤ (∑ i, w i) * (C_J * (J : ℝ) ^ (-(s / d))) ^ 2)
    (hw : ∀ i, w i = (1 : ℝ) / N)
    (htr : (∑ i, ∑ k, a i k ^ 2) ≤ Cvar * J) :
    ∫ ω, lstsqObjective Φ w f (chat ω) ∂μ
      ≤ ((∑ i, w i) * C_J ^ 2) * (J : ℝ) ^ (-(2 * s / d)) + σ ^ 2 * (Cvar * (J : ℝ) / N) := by
  have hA := jacksonSeriesBias_le (Φ := Φ) (w := w) (f := f) (c0 := c0)
    (s := s) (d := d) (C_J := C_J) (J := J) hJack
  have hV := seriesEffectiveDoF_le (a := a) (w := w) (Cvar := Cvar) (J := J) hN hw htr
  exact seriesLS_expected_prediction_le hortho hA hlin hε hmean hsph hV

end Causalean.Stat.Nonparametric.SeriesSieve
