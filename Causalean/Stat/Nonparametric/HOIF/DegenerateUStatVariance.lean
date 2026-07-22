/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.UStatistic.Variance

/-!
# Variance of the degenerate (rank-2) U-statistic: the `J/(nh)²` term

Variance bounds for degenerate rank-2 U-statistic terms in higher-order influence-function
estimators.

The order-`m` HOIF estimator's stochastic term is dominated by a *degenerate* order-2
U-statistic whose kernel is a `J`-dimensional, bandwidth-`h` localized projection.  For such a
kernel `g` (`∫ g(x,·) dP = 0`, symmetric, square-integrable) the off-diagonal second-moment
computation of `Causalean.Stat.UStatistic.Variance` (`integral_offDiag_sum_sq`) gives the exact
variance

  `Var[Uₙ] = 2ζ / (n(n−1))`,   `ζ = ∬ g² dP dP`.

When the localized projection kernel has L²-energy `ζ ≤ C·J/h²`, this yields the HOIF
*degenerate U-statistic variance bound*

  `Var[Uₙ] ≤ 4C·J / (nh)²`,

the `O(J/(nh)²)` term of the projection-risk decomposition. The sibling
`HOIF.ProjectedKernelTrace` file supplies the algebraic inverse-Gram trace identity `ζ = J`
for the unlocalized projected kernel; the bandwidth-localized inequality is the hypothesis
passed to `degenerate_uStatistic_variance_le`.
-/

namespace Causalean.Stat.Nonparametric.HOIF

open MeasureTheory ProbabilityTheory
open Causalean.Stat

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {g : X → X → ℝ}

/-- The degenerate order-2 U-statistic is in `L²` (rescaling the `√n`-version). -/
theorem memLp_uStatistic (S : IIDSample Ω X μ P) (hg : DegenKernel P g) {n : ℕ}
    (hn : 2 ≤ n) : MemLp (uStatistic S g n) 2 μ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by
    simp only [ne_eq, Real.sqrt_eq_zero']; push_neg; exact hn0
  have hres : MemLp (fun ω => Real.sqrt (n : ℝ) * uStatistic S g n ω) 2 μ :=
    S.memLp_rescaled hg n
  have hrw : uStatistic S g n
      = fun ω => (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ) * uStatistic S g n ω) := by
    funext ω; rw [← mul_assoc, inv_mul_cancel₀ hsqrt, one_mul]
  rw [hrw]
  exact hres.const_mul _

/-- **Mean of the degenerate U-statistic is zero.** -/
theorem integral_uStatistic_eq_zero (S : IIDSample Ω X μ P) (hg : DegenKernel P g)
    {n : ℕ} (hn : 2 ≤ n) : ∫ ω, uStatistic S g n ω ∂μ = 0 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by
    simp only [ne_eq, Real.sqrt_eq_zero']; push_neg; exact hn0
  have h := S.integral_rescaled_eq_zero hg n
  rw [integral_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hsqrt

/-- **Exact variance of the degenerate order-2 U-statistic.**
For a symmetric, square-integrable, doubly-degenerate kernel `g` and `n ≥ 2`, the order-2
U-statistic has variance `Var[Uₙ] = 2ζ / (n(n−1))`, where `ζ = ∬ g² dP dP`.  This is the
Hoeffding rank-2 variance: the off-diagonal sum contributes `2·|offDiag|·ζ`, rescaled by
`(n(n−1))⁻²`. -/
theorem degenerate_uStatistic_variance (S : IIDSample Ω X μ P) (hg : DegenKernel P g)
    {n : ℕ} (hn : 2 ≤ n) :
    variance (uStatistic S g n) μ
      = 2 * IIDSample.zeta P g / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmem : MemLp (uStatistic S g n) 2 μ := memLp_uStatistic S hg hn
  have hmean : ∫ ω, uStatistic S g n ω ∂μ = 0 := integral_uStatistic_eq_zero S hg hn
  -- Second moment from the √n-rescaled identity:  ∫ (√n Uₙ)² = n · ∫ Uₙ² = 2ζ/(n−1).
  have hsq : ∫ ω, (uStatistic S g n ω) ^ 2 ∂μ
      = 2 * IIDSample.zeta P g / ((n : ℝ) * ((n : ℝ) - 1)) := by
    have hres := S.integral_rescaled_sq hg hn
    have hpoint : (fun ω => (Real.sqrt (n : ℝ) * uStatistic S g n ω) ^ 2)
        = (fun ω => (n : ℝ) * (uStatistic S g n ω) ^ 2) := by
      funext ω; rw [mul_pow, Real.sq_sqrt (le_of_lt hn0)]
    rw [hpoint, integral_const_mul] at hres
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    have hn1 : (n : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      intro h; linarith
    field_simp at hres ⊢
    linarith [hres]
  rw [ProbabilityTheory.variance_eq_sub hmem, hmean]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  exact hsq

/-- **HOIF degenerate U-statistic variance bound `O(J/(nh)²)`.**
If the localized, `J`-dimensional projection kernel `g` has L²-energy bounded by `ζ ≤ C·J/h²`
(the trace bound), then the degenerate order-2 U-statistic's variance satisfies

  `Var[Uₙ] ≤ 4C·J / (nh)²`.

This is the `O(J/(nh)²)` stochastic term of the HOIF projection-risk decomposition. -/
theorem degenerate_uStatistic_variance_le (S : IIDSample Ω X μ P) (hg : DegenKernel P g)
    {C J h : ℝ} {n : ℕ} (hn : 2 ≤ n) (hh : 0 < h) (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (hzeta : IIDSample.zeta P g ≤ C * J / h ^ 2) :
    variance (uStatistic S g n) μ ≤ 4 * C * J / ((n : ℝ) * h) ^ 2 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hζnn : 0 ≤ IIDSample.zeta P g := IIDSample.zeta_nonneg
  rw [degenerate_uStatistic_variance S hg hn]
  have hprodpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hn0 hnm1
  have hnhpos : 0 < ((n : ℝ) * h) ^ 2 := by positivity
  have hh2 : 0 < h ^ 2 := by positivity
  have hCJ : 0 ≤ C * J := mul_nonneg hC hJ
  -- ζ·h² ≤ C·J  (clear the denominator in the trace bound).
  have hζh2 : IIDSample.zeta P g * h ^ 2 ≤ C * J :=
    (le_div_iff₀ hh2).mp hzeta
  rw [div_le_div_iff₀ hprodpos hnhpos]
  -- goal: 2ζ · (nh)² ≤ 4CJ · (n(n−1))
  nlinarith [hζh2, hCJ, hn2, hh2, mul_nonneg hCJ (le_of_lt hn0),
    mul_le_mul_of_nonneg_left hζh2 (by positivity : (0:ℝ) ≤ (n:ℝ) ^ 2),
    mul_nonneg hCJ (sub_nonneg.mpr hn2)]

end Causalean.Stat.Nonparametric.HOIF
