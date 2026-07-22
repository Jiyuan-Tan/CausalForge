/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Probability bridge for the finite Gauss-Markov variance quadratic form

This file justifies the deterministic `quadVar` object of
`Causalean/Estimation/GaussMarkov/QuadForm.lean` by proving that the variance of a
random linear combination `∑ i, w i * Y i` equals the covariance quadratic form
`wᵀ Σ w`, where `Σ i j = cov(Yᵢ, Yⱼ)`.
-/

import Causalean.Estimation.GaussMarkov.QuadForm
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance

/-! # Variance Bridge

This file connects the deterministic Gauss-Markov quadratic form to the
probability theory of finite random families.  It defines `covMatrix Y μ`, the
covariance matrix of the observations `Y i`, and proves
`variance_linearCombination`: the variance of `∑ i, w i * Y i` is exactly
`quadVar (covMatrix Y μ) w`.

It also defines `SphericalFamily`, the probabilistic condition that all cells
have variance `σ²` and distinct cells are uncorrelated, and proves
`sphericalFamily_covMatrix`, which turns that condition into the deterministic
`SphericalErrors` hypothesis used by the Gauss-Markov ordering theorems. -/

namespace Causalean.GaussMarkov

open MeasureTheory ProbabilityTheory Matrix

variable {Ω Obs : Type*} [Fintype Obs] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Covariance matrix of a finite family of random variables `Y i`. -/
noncomputable def covMatrix (Y : Obs → Ω → ℝ) (μ : Measure Ω) : Matrix Obs Obs ℝ :=
  fun i j => cov[Y i, Y j; μ]

/-- **Variance of a linear combination = covariance quadratic form.**
The variance of the random linear estimator `∑ i, w i * Y i` equals `wᵀ Σ w`
where `Σ = covMatrix Y μ`. -/
theorem variance_linearCombination [IsProbabilityMeasure μ]
    (Y : Obs → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ) (w : Obs → ℝ) :
    Var[fun ω => ∑ i, w i * Y i ω; μ] = quadVar (covMatrix Y μ) w := by
  set X : Obs → Ω → ℝ := fun i ω => w i * Y i ω with hX_def
  have hX : ∀ i, MemLp (X i) 2 μ := fun i => (hY i).const_mul (w i)
  have hfun : (∑ i, X i) = fun ω => ∑ i, X i ω := by
    funext ω; exact Finset.sum_apply ω Finset.univ X
  have hSumMemLp : MemLp (fun ω => ∑ i, X i ω) 2 μ := by
    rw [← hfun]
    exact memLp_finset_sum' (μ := μ) (p := 2) Finset.univ (fun i (_ : i ∈ Finset.univ) => hX i)
  have hSum : AEMeasurable (fun ω => ∑ i, X i ω) μ :=
    hSumMemLp.aestronglyMeasurable.aemeasurable
  calc Var[fun ω => ∑ i, w i * Y i ω; μ]
      = cov[fun ω => ∑ i, X i ω, fun ω => ∑ i, X i ω; μ] := (covariance_self hSum).symm
    _ = ∑ i, ∑ j, cov[X i, X j; μ] := covariance_fun_sum_fun_sum hX hX
    _ = ∑ i, ∑ j, w i * (w j * covMatrix Y μ i j) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hX_def]
        rw [covariance_const_mul_left, covariance_const_mul_right]
        rfl
    _ = quadVar (covMatrix Y μ) w := by
        simp only [quadVar, dotProduct, mulVec, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring

/-- A random family has *spherical errors* with scale `σ`: distinct cells are
uncorrelated and each has variance `σ²`. -/
def SphericalFamily (Y : Obs → Ω → ℝ) (μ : Measure Ω) (σ : ℝ) : Prop :=
  (∀ i, Var[Y i; μ] = σ ^ 2) ∧ (∀ i j, i ≠ j → cov[Y i, Y j; μ] = 0)

omit [Fintype Obs] in
/-- A spherical random family has a spherical (scalar-identity) covariance matrix. -/
lemma sphericalFamily_covMatrix [DecidableEq Obs] {Y : Obs → Ω → ℝ} {σ : ℝ}
    (hY : ∀ i, AEMeasurable (Y i) μ) (h : SphericalFamily Y μ σ) :
    SphericalErrors (covMatrix Y μ) σ := by
  ext i j
  simp only [covMatrix, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    rw [covariance_self (hY i), h.1 i]
    simp
  · rw [h.2 i j hij]
    simp [hij]

end Causalean.GaussMarkov
