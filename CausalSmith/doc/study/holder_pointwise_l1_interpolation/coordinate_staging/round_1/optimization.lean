/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation.Kernel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Bandwidth optimization for Hölder interpolation

Internal implementation layer for the multivariate Hölder pointwise-to-local-mass interpolation theorem.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators Pointwise Manifold ContDiff

/-- Choosing a bandwidth proportional to a positive pointwise signal raised to
the reciprocal smoothness exponent converts a kernel lower bound into the
pointwise-to-local-mass power law. -/
theorem l1_lower_of_bias_bound {d : ℕ} {γ Ksup Δ Ival cstar h : ℝ}
    (hγ : 0 < γ) (hKsup : 0 < Ksup) (hΔ : 0 < Δ) (hcstar : 0 < cstar)
    (hheq : h = cstar * Δ ^ ((1 : ℝ) / γ))
    (hbound : 3 * Δ / 4 ≤ Ksup * h⁻¹ ^ d * Ival) :
    (3 / (4 * Ksup)) * cstar ^ d * Δ ^ (1 + (d : ℝ) / γ) ≤ Ival := by
  have hqpos : (0 : ℝ) < Δ ^ ((d : ℝ) / γ) := Real.rpow_pos_of_pos hΔ _
  have hcpos : 0 < cstar ^ d := pow_pos hcstar _
  have hABpos : 0 < cstar ^ d * Δ ^ ((d : ℝ) / γ) := mul_pos hcpos hqpos
  -- `h ^ d = cstar ^ d * Δ ^ (d/γ)`.
  have hpow : h ^ d = cstar ^ d * Δ ^ ((d : ℝ) / γ) := by
    have h1 : (Δ ^ ((1 : ℝ) / γ)) ^ d = Δ ^ ((d : ℝ) / γ) := by
      rw [← Real.rpow_natCast (Δ ^ ((1 : ℝ) / γ)) d, ← Real.rpow_mul hΔ.le]
      congr 1
      ring
    rw [hheq, mul_pow, h1]
  -- Rewrite the hypothesis with the explicit `h ^ d`.
  rw [inv_pow, hpow] at hbound
  -- Clear the inverse: `(3Δ/4)·(cstar^d·Δ^{d/γ}) ≤ Ksup·Ival`.
  have hmul : 3 * Δ / 4 * (cstar ^ d * Δ ^ ((d : ℝ) / γ)) ≤ Ksup * Ival := by
    have h2 := mul_le_mul_of_nonneg_right hbound hABpos.le
    have e : Ksup * (cstar ^ d * Δ ^ ((d : ℝ) / γ))⁻¹ * Ival
        * (cstar ^ d * Δ ^ ((d : ℝ) / γ)) = Ksup * Ival := by
      field_simp
    rwa [e] at h2
  -- `Δ ^ (1 + d/γ) = Δ · Δ ^ (d/γ)`.
  have hΔadd : Δ ^ (1 + (d : ℝ) / γ) = Δ * Δ ^ ((d : ℝ) / γ) := by
    rw [Real.rpow_add hΔ, Real.rpow_one]
  have goaleq : (3 / (4 * Ksup)) * cstar ^ d * (Δ * Δ ^ ((d : ℝ) / γ))
      = (3 * Δ / 4 * (cstar ^ d * Δ ^ ((d : ℝ) / γ))) / Ksup := by
    field_simp
  rw [hΔadd, goaleq, div_le_iff₀ hKsup, mul_comm Ival Ksup]
  exact hmul


end Causalean.Stat.Nonparametric
