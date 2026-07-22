/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Ratio / quotient delta method

The corollary of the multivariate Δ-method (`Causalean.Stat.deltaMethod`) for the
ratio map `g(x, y) = x / y`.  This is the form needed by Wald-ratio / LATE /
instrumental-variable estimands: if `√n • ((N̂ₙ, D̂ₙ) − (a, b)) ⇒ Q` and
`b ≠ 0`, then `√n • (N̂ₙ / D̂ₙ − a / b)` converges in distribution to the
pushforward of `Q` along the Fréchet derivative of the ratio at `(a, b)`.

The carrier is `EuclideanSpace ℝ (Fin 2)`, a finite-dimensional real
inner-product space, so that the multivariate CLT contact
`IIDSample.clt_normalizedSum_vec_of_charFun` can later be chained without
changing the carrier.  The derivative is defined explicitly as the continuous
linear map `(1/b) • proj₀ − (a/b²) • proj₁`, then verified from the
product/inverse derivative rules.

The limit law is kept abstract (the pushforward `Q.toMeasure.map (ratioDeriv t₀)`)
exactly as in `deltaMethod`.  Concrete Gaussian inputs can be supplied via
`gaussianLimit` (`Causalean/Stat/CLT/GaussianLimit.lean`) using the available
multivariate-Gaussian characteristic-function formula `IsGaussian.charFun_eq'`.

Reference: van der Vaart (1998), Theorem 3.1 (and the `g(x,y) = x/y` example).
-/

import Causalean.Stat.Inference.DeltaMethod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
This file specializes the multivariate delta method to ratio statistics such as
Wald-ratio and LATE estimands.  It defines the closed-form derivative
`ratioDeriv t₀ = (1 / b) • proj₀ - (a / b ^ 2) • proj₁` on
`EuclideanSpace ℝ (Fin 2)`, proves `hasFDerivAt_ratio` for the map
`v ↦ v 0 / v 1` when the denominator coordinate is nonzero, and instantiates
`deltaMethod` in `deltaMethod_ratio`.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## Fréchet derivative of the ratio map -/

/-- The Fréchet derivative of `v ↦ v 0 / v 1` at `t₀`, in closed form via
`smulRight` on the coordinate projections `EuclideanSpace.proj 0`,
`EuclideanSpace.proj 1`:
`ratioDeriv t₀ = (1/b) • proj₀ − (a / b²) • proj₁` with `(a, b) = (t₀ 0, t₀ 1)`.
This is the gradient of `x/y` at `(a, b)` paired against the coordinate
functionals.  (This Mathlib has no bundled `HasFDerivAt.div`, so we give the
closed form explicitly and verify it via the product/inverse rules.) -/
noncomputable def ratioDeriv (t₀ : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) 0).smulRight (t₀ 1)⁻¹ -
    (EuclideanSpace.proj (𝕜 := ℝ) 1).smulRight (t₀ 0 * ((t₀ 1) ^ 2)⁻¹)

/-- **Fréchet derivative of the ratio map.**  On `EuclideanSpace ℝ (Fin 2)`, the
map `v ↦ v 0 / v 1` is Fréchet-differentiable at any `t₀` whose second
coordinate is nonzero, with derivative `ratioDeriv t₀`.

Built from the coordinate projections (continuous linear, hence `HasFDerivAt`
via `ContinuousLinearMap.hasFDerivAt`).  Since this Mathlib has no bundled
`HasFDerivAt.div`, we use `x / y = x * y⁻¹`: `hasFDerivAt_inv` composed with the
second projection gives the derivative of `v ↦ (v 1)⁻¹`, then `HasFDerivAt.mul`
gives the product; the resulting CLM is matched to the closed-form
`ratioDeriv`. -/
theorem hasFDerivAt_ratio {t₀ : EuclideanSpace ℝ (Fin 2)} (hb : t₀ 1 ≠ 0) :
    HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 2) => v 0 / v 1) (ratioDeriv t₀) t₀ := by
  have h0 : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 2) => v 0)
      (EuclideanSpace.proj (𝕜 := ℝ) 0) t₀ :=
    (EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt
  have h1 : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin 2) => v 1)
      (EuclideanSpace.proj (𝕜 := ℝ) 1) t₀ :=
    (EuclideanSpace.proj (𝕜 := ℝ) 1).hasFDerivAt
  -- derivative of `v ↦ (v 1)⁻¹` by composing scalar `hasFDerivAt_inv` with `h1`
  have hinv := (hasFDerivAt_inv hb).comp t₀ h1
  -- `x / y = x * y⁻¹`
  have heq : (fun v : EuclideanSpace ℝ (Fin 2) => v 0 / v 1)
      = (fun v : EuclideanSpace ℝ (Fin 2) => v 0 * (v 1)⁻¹) := by
    funext v; rw [div_eq_mul_inv]
  rw [heq]
  have hmul := h0.mul hinv
  convert hmul using 1
  ext v
  simp only [ratioDeriv, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, Function.comp_apply,
    smul_eq_mul]
  ring

/-! ## Ratio delta method -/

/-- **Ratio / quotient delta method.**  Let `t₀ = (a, b)` with `b ≠ 0` and let
`Tn n ω = (N̂ₙ, D̂ₙ)` be the bivariate estimator.  If the rescaled deviation
`√n • (Tn − t₀)` converges in distribution to a probability measure `Q` on
`EuclideanSpace ℝ (Fin 2)`, then the rescaled ratio
`√n • (Tn 0 / Tn 1 − a / b)` converges in distribution to the pushforward of `Q`
along the ratio derivative `ratioDeriv t₀`.

This is `deltaMethod` instantiated at `g v = v 0 / v 1`, `Dg = ratioDeriv t₀`,
with the differentiability contact supplied by `hasFDerivAt_ratio`.  The limit
law is kept abstract (the pushforward), mirroring `deltaMethod`; for Gaussian `Q`
it is the usual Wald-ratio asymptotic variance
`(1/b , −a/b²) Σ (1/b , −a/b²)ᵀ`. -/
theorem deltaMethod_ratio
    (Tn : ℕ → Ω → EuclideanSpace ℝ (Fin 2)) (t₀ : EuclideanSpace ℝ (Fin 2))
    (hb : t₀ 1 ≠ 0) (Q : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (hTn : ∀ n, AEMeasurable (fun ω => (Real.sqrt ((n : ℕ) : ℝ)) • (Tn n ω - t₀)) μ)
    (hgTn : ∀ n, AEMeasurable
      (fun ω => (Real.sqrt ((n : ℕ) : ℝ)) • ((Tn n ω 0 / Tn n ω 1) - t₀ 0 / t₀ 1)) μ)
    (_hCLT :
      Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
        (fun n =>
          ⟨μ.map (fun ω => (Real.sqrt ((n : ℕ) : ℝ)) • (Tn n ω - t₀)),
            Measure.isProbabilityMeasure_map (hTn n)⟩)
        atTop (𝓝 Q)) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n =>
        ⟨μ.map (fun ω => (Real.sqrt ((n : ℕ) : ℝ)) • ((Tn n ω 0 / Tn n ω 1) - t₀ 0 / t₀ 1)),
          Measure.isProbabilityMeasure_map (hgTn n)⟩)
      atTop
      (𝓝 ⟨Q.toMeasure.map (ratioDeriv t₀),
            Measure.isProbabilityMeasure_map
              (ratioDeriv t₀).continuous.measurable.aemeasurable⟩) :=
  deltaMethod Tn t₀ (fun v => v 0 / v 1) (ratioDeriv t₀) Q hTn hgTn
    (hasFDerivAt_ratio hb) _hCLT

end Causalean.Stat
