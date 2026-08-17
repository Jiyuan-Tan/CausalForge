/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Best linear unbiased estimation (finite Gauss-Markov, probabilistic form)

Combines the probability bridge (`variance_linearCombination`) with the algebraic
least-norm ordering theorems (`gauss_markov_spherical`, `gauss_markov_gls`) to state
the Gauss-Markov / BLUE conclusion directly in terms of `ProbabilityTheory.variance`
of the random linear estimators.

* `covMatrix_posSemidef`: a covariance matrix is positive semidefinite.
* `variance_blue_spherical`: under a spherical random family, an OLS weight (in the
  column span of the design) has minimum variance in the linear-unbiased class.
* `variance_blue_gls`: for any known covariance, a GLS weight has minimum variance.
-/

import Causalean.Estimation.GaussMarkov.LeastNorm
import Causalean.Estimation.GaussMarkov.Variance

/-! # Best Linear Unbiased Estimation

This file states the finite Gauss-Markov conclusions in probabilistic variance
language. It combines the covariance-matrix bridge with the least-norm ordering
theorems to prove the best-linear-unbiased-estimator results for spherical
errors and for a known covariance matrix. -/

namespace Causalean.GaussMarkov

open MeasureTheory ProbabilityTheory Matrix

variable {Ω Obs : Type*} [Fintype Obs]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

set_option linter.unusedFintypeInType false in
/-- A covariance matrix of an `L²` random family is positive semidefinite: it is
symmetric (`cov` is symmetric) and its quadratic form is a genuine variance, hence
nonnegative.  (`Fintype Obs` appears only under the `PosSemidef` definition, which
the `unusedFintypeInType` linter cannot see; it is genuinely required.) -/
lemma covMatrix_posSemidef [IsProbabilityMeasure μ]
    (Y : Obs → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ) :
    (covMatrix Y μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    change star (covMatrix Y μ j i) = covMatrix Y μ i j
    rw [star_trivial]
    exact covariance_comm (Y j) (Y i)
  · intro w
    have hsw : star w ⬝ᵥ (covMatrix Y μ) *ᵥ w = quadVar (covMatrix Y μ) w := by
      simp [quadVar, star_trivial]
    rw [hsw, ← variance_linearCombination Y hY]
    exact variance_nonneg _ _

variable {Param : Type*} [Fintype Param]

/-- **BLUE under spherical errors (variance form).** For a finite family of random
variables `Y i`, each [square-integrable](hyp:hY), suppose [the family is
spherical: distinct cells are uncorrelated and every cell has the same variance
`σ²`](hyp:hsph). Among all linear combinations `∑ i, w i * Y i` whose weights
satisfy [the same unbiasedness constraint `w ᵥ* X = c`](hyp:hUStar,hU) relative
to a design `X` and target combination `c`, if [`wStar` lies in the column span
of `X`, `wStar = X *ᵥ g`](hyp:hStar), then [the linear combination built from
`wStar` (the OLS weight) has variance no larger than that of any other unbiased
linear combination](goal). -/
theorem variance_blue_spherical [IsProbabilityMeasure μ]
    {X : Matrix Obs Param ℝ} {c : Param → ℝ}
    (Y : Obs → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ) {σ : ℝ}
    (hsph : SphericalFamily Y μ σ)
    {w wStar : Obs → ℝ} {g : Param → ℝ}
    (hStar : wStar = X *ᵥ g) (hUStar : wStar ᵥ* X = c) (hU : w ᵥ* X = c) :
    Var[fun ω => ∑ i, wStar i * Y i ω; μ] ≤ Var[fun ω => ∑ i, w i * Y i ω; μ] := by
  classical
  rw [variance_linearCombination Y hY, variance_linearCombination Y hY]
  have hsph' : SphericalErrors (covMatrix Y μ) σ :=
    sphericalFamily_covMatrix (fun i => (hY i).aestronglyMeasurable.aemeasurable) hsph
  exact gauss_markov_spherical hsph' hStar hUStar hU

/-- **BLUE for known covariance (GLS, variance form).** For a finite family of
random variables `Y i`, each [square-integrable](hyp:hY), consider linear
combinations `∑ i, w i * Y i` whose weights satisfy [the same unbiasedness
constraint `w ᵥ* X = c`](hyp:hUStar,hU) relative to a design `X` and target
combination `c`. If [the weight `wStar` is a generalized-least-squares (GLS)
weight — i.e. the family's covariance matrix applied to `wStar` lies in the
column span of `X`](hyp:hGLS), then [the linear combination built from `wStar`
has variance no larger than that of any other unbiased linear
combination](goal). -/
theorem variance_blue_gls [IsProbabilityMeasure μ]
    {X : Matrix Obs Param ℝ} {c : Param → ℝ}
    (Y : Obs → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ)
    {w wStar : Obs → ℝ} {g : Param → ℝ}
    (hGLS : (covMatrix Y μ) *ᵥ wStar = X *ᵥ g)
    (hUStar : wStar ᵥ* X = c) (hU : w ᵥ* X = c) :
    Var[fun ω => ∑ i, wStar i * Y i ω; μ] ≤ Var[fun ω => ∑ i, w i * Y i ω; μ] := by
  rw [variance_linearCombination Y hY, variance_linearCombination Y hY]
  exact gauss_markov_gls (covMatrix_posSemidef Y hY) hGLS hUStar hU

end Causalean.GaussMarkov
