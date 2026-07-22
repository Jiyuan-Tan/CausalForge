/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Estimation.GaussMarkov.Variance

/-!
# Variance of a fixed-weight linear smoother under spherical errors

Variance identities and leverage bounds for fixed-weight linear smoothers under spherical errors.

A linear smoother `∑ᵢ Sᵢ Yᵢ` with deterministic weights `Sᵢ` (the local-polynomial /
series equivalent-kernel weights, conditional on the design) applied to a **spherical**
random family `Y` — distinct cells uncorrelated, each of variance `σ²` — has variance

`Var[∑ᵢ Sᵢ Yᵢ] = σ² · ∑ᵢ Sᵢ²`.

This is the generic (design-agnostic) variance half of the interior nonparametric estimator
analysis: it reduces the target stochastic-error bound `O((Nh)^{−1/2})` to a leverage bound
`∑ᵢ Sᵢ² = O(1/(Nh))`. It is a direct corollary of the Gauss–Markov covariance–quadratic-form
identity (`Causalean.GaussMarkov`). Both the local-polynomial and the series/sieve estimators
consume it; the local-polynomial-specific corollary lives in
`Causalean.Stat.Nonparametric.LocalPoly.SmootherVariance`.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- **Variance of a fixed-weight linear smoother under spherical errors.** If `Y` is a
spherical random family with scale `σ` (each cell has variance `σ²`, distinct cells are
uncorrelated) and each `Yᵢ` is `L²`, then the linear smoother with deterministic weights `S`
has variance `Var[∑ᵢ Sᵢ Yᵢ] = σ² · ∑ᵢ Sᵢ²`. -/
theorem linearSmoother_variance_spherical {Ω : Type*} {N : ℕ} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Fin N → Ω → ℝ} {S : Fin N → ℝ} {σ : ℝ}
    (hY : ∀ i, MemLp (Y i) 2 μ)
    (hsph : Causalean.GaussMarkov.SphericalFamily Y μ σ) :
    Var[fun ω => ∑ i, S i * Y i ω; μ] = σ ^ 2 * ∑ i, S i ^ 2 := by
  rw [Causalean.GaussMarkov.variance_linearCombination Y hY S,
    Causalean.GaussMarkov.quadVar_spherical
      (Causalean.GaussMarkov.sphericalFamily_covMatrix
        (fun i => (hY i).aestronglyMeasurable.aemeasurable) hsph) S]
  congr 1
  simp only [dotProduct]
  exact Finset.sum_congr rfl (fun i _ => (pow_two (S i)).symm)

/-- **Stochastic-error bound for a fixed-weight linear smoother.** Under spherical errors with
scale `σ`, if the leverage is controlled by `∑ᵢ Sᵢ² ≤ V` then the smoother variance is at most
`σ² V`. Taking `V = O(1/(Nh))` gives the interior `O((Nh)^{−1/2})` stochastic-error rate. -/
theorem linearSmoother_variance_le {Ω : Type*} {N : ℕ} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Fin N → Ω → ℝ} {S : Fin N → ℝ} {σ V : ℝ}
    (hY : ∀ i, MemLp (Y i) 2 μ)
    (hsph : Causalean.GaussMarkov.SphericalFamily Y μ σ)
    (hlev : (∑ i, S i ^ 2) ≤ V) :
    Var[fun ω => ∑ i, S i * Y i ω; μ] ≤ σ ^ 2 * V := by
  rw [linearSmoother_variance_spherical hY hsph]
  exact mul_le_mul_of_nonneg_left hlev (sq_nonneg σ)

end Causalean.Stat.Nonparametric
