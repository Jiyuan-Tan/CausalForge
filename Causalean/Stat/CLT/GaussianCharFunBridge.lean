/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Gaussian characteristic-function bridge for the multivariate CLT

`Causalean/Stat/CLT/MultivariateCLT.lean`, `Stat/Inference/WaldVec.lean`, and
`Stat/Inference/RatioDeltaMethod.lean`
state their limit laws against an *abstract* target measure `Q` together with the
hypothesis
`charFun Q t = exp(−½ ∫⟪t,ψ⟫² dP)`  (`hQ`).
At the current Mathlib pin the multivariate-Gaussian characteristic-function
formula is available as
`ProbabilityTheory.IsGaussian.charFun_eq'`
(`Mathlib/Probability/Distributions/Gaussian/CharFun.lean`):
`charFun μ t = exp(⟪t, μ[id]⟫·I − covarianceBilin μ t t / 2)`.

This file provides the verified glue that converts a *concrete* centered Gaussian
`Q` whose covariance is identified with the influence-function second moment into
exactly the `hQ` shape those theorems consume. The concrete `Q` is now
constructed in `Causalean/Stat/CLT/GaussianLimit.lean` (`gaussianLimit`), as
`stdGaussian.map √Σ` with `Σ` the second-moment operator
(`Causalean/Stat/CLT/SecondMomentOperator.lean`) and `√Σ` its positive operator square
root (`Causalean/Mathlib/OperatorSqrt.lean`); de-abstraction is complete.
-/
import Mathlib.Probability.Distributions.Gaussian.CharFun

/-! # Gaussian Characteristic-Function Bridge

This file connects concrete centered Gaussian measures with the characteristic
function form used by the library's multivariate central-limit theorems. It
identifies the Gaussian covariance with the second moment of an influence
function so that abstract limit-law hypotheses can be discharged.

`charFun_isGaussian_centered` specializes the Mathlib Gaussian characteristic
function formula to centered Gaussian measures. `charFun_isGaussian_of_cov_eq`
then rewrites the covariance form into the influence-function integral
`∫ ⟪t, ψ x⟫² ∂P`, matching the abstract target used by the multivariate CLT
theorems. -/

open MeasureTheory ProbabilityTheory Complex
open scoped RealInnerProductSpace

namespace Causalean.Stat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- **Centered-Gaussian characteristic function.** For a Gaussian measure `Q` with
mean zero, `charFun Q t = exp(−½ · covarianceBilin Q t t)`. Specialisation of
`IsGaussian.charFun_eq'` with `Q[id] = 0`. -/
theorem charFun_isGaussian_centered (Q : Measure E) [IsGaussian Q]
    (hmean : ∫ x, x ∂Q = 0) (t : E) :
    charFun Q t = Complex.exp (-(covarianceBilin Q t t : ℂ) / 2) := by
  rw [IsGaussian.charFun_eq']
  have h0 : (∫ x, id x ∂Q) = 0 := by simpa using hmean
  rw [h0, inner_zero_right, Complex.ofReal_zero]
  congr 1
  ring

/-- **Bridge to the abstract CLT target `hQ`.** If `Q` is a centered Gaussian
whose covariance bilinear form is identified with the influence-function second
moment `t ↦ ∫⟪t,ψ⟫² dP`, then its characteristic function is exactly the target
`exp(−½ ∫⟪t,ψ⟫² dP)` taken as the hypothesis `hQ` by
`IIDSample.clt_normalizedSum_vec_of_charFun` and friends. -/
theorem charFun_isGaussian_of_cov_eq {X : Type*} [MeasurableSpace X]
    {P : Measure X} {ψ : X → E} (Q : Measure E) [IsGaussian Q]
    (hmean : ∫ x, x ∂Q = 0)
    (hcov : ∀ t : E, covarianceBilin Q t t = ∫ x, (⟪t, ψ x⟫) ^ 2 ∂P)
    (t : E) :
    charFun Q t
      = Complex.exp (-(((∫ x, (⟪t, ψ x⟫) ^ 2 ∂P : ℝ)) : ℂ) / 2) := by
  rw [charFun_isGaussian_centered Q hmean t, hcov t]

end Causalean.Stat
