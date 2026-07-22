/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Directional-derivative bundles for a `LearningSystem`

Mirrors `Estimation.OrthogonalMoments.HasDirDeriv`, but for the loss `ℓ : Z → Θ → G → ℝ`
of an orthogonal statistical-learning system rather than a moment functional.  We carry three bundles:

* `HasDirDerivTheta S g`   — pointwise dir derivative of `θ ↦ ℓ z θ g` along
                              the segment `θ₀ → θ`.
* `HasDirDerivG S`         — pointwise dir derivative of `g ↦ ℓ z θ₀ g` along
                              the segment `g₀ → g`.
* `HasMixedDirDeriv S Dθ`  — pointwise dir derivative of the *target*
                              directional-derivative datum `Dθ.dℓ_θ θ z` in
                              the nuisance variable along `g₀ → g`.

We additionally state the population first-order inequality
`FirstOrderInequality S Dθ` parameterised by a target-direction DD bundle.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-system` (the first-order inequality is the closing remark of
this definition) and the preamble of `def:est-osl-neyman-loss`.
-/

import Causalean.Estimation.OrthogonalLearning.Setup

/-! # Directional Derivatives for Losses

This file packages directional derivatives of an orthogonal
statistical-learning loss in the target coordinate, the nuisance coordinate,
and the mixed target-nuisance coordinate. These derivative bundles provide the
analytic inputs used to state first-order optimality and Neyman orthogonality
for population risks.

The public bundles are `HasDirDerivTheta`, `HasDirDerivG`, and
`HasMixedDirDeriv`. The predicate `FirstOrderInequality` records the integrated
target-direction first-order condition at the true nuisance. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- Pointwise directional derivative of `θ ↦ ℓ z θ g` along the segment from
`θ₀` to `θ`, packaged with the pointwise tendsto witness and measurability.

`dℓ_θ θ z` is the directional derivative *value* at `(θ₀, g)` in the
direction `θ - θ₀`.  In the integrated form
`∫ z, dℓ_θ θ z ∂P_Z = D_θ L(θ₀, g)[θ - θ₀]`. -/
structure HasDirDerivTheta
    (S : LearningSystem Ω μ Z P_Z Θ G) (g : G) where
  dℓ_θ : Θ → Z → ℝ
  pointwise_tendsto : ∀ θ ∈ S.Θ_set, ∀ z,
    Tendsto (fun t : ℝ =>
      (S.ℓ z (S.θ₀ + t • (θ - S.θ₀)) g - S.ℓ z S.θ₀ g) / t)
      (𝓝[≠] 0) (𝓝 (dℓ_θ θ z))
  dℓ_θ_meas         : ∀ θ, Measurable (dℓ_θ θ)

/-- Pointwise directional derivative of `g ↦ ℓ z θ₀ g` along the segment from
`g₀` to `g`, packaged with the pointwise tendsto witness and measurability.

`dℓ_g g z` is the directional derivative *value* at `(θ₀, g₀)` in the
nuisance direction `g - g₀`.  In the integrated form
`∫ z, dℓ_g g z ∂P_Z = D_g L(θ₀, g₀)[g - g₀]`. -/
structure HasDirDerivG
    (S : LearningSystem Ω μ Z P_Z Θ G) where
  dℓ_g : G → Z → ℝ
  pointwise_tendsto : ∀ g ∈ S.G_set, ∀ z,
    Tendsto (fun t : ℝ =>
      (S.ℓ z S.θ₀ (S.g₀ + t • (g - S.g₀)) - S.ℓ z S.θ₀ S.g₀) / t)
      (𝓝[≠] 0) (𝓝 (dℓ_g g z))
  dℓ_g_meas         : ∀ g, Measurable (dℓ_g g)

/-- Mixed directional derivative `D_g D_θ ℓ` at `(θ₀, g₀)`.

We package this as a *family* of target-direction directional-derivative
data — one bundle `Dθ_at g` for each accessible nuisance `g ∈ G_set ∪ {g₀}`
— together with a tendsto witness saying that the value
`(Dθ_at g').dℓ_θ θ z` at `g' := g₀ + t • (g - g₀)` differentiates in `t`
to `dℓ_θg θ g z` at `t = 0`.

Carrying the family is what the natural-language note's
`D_g D_θ L(θ₀, g₀)[ν_θ, ν_g]` requires: the inner derivative is taken
*at the truth* `θ₀`, but the function being differentiated outside is
itself a directional derivative anchored at the perturbed nuisance.

`dℓ_θg θ g z` is the mixed directional derivative value at `(θ₀, g₀)` in
directions `(θ - θ₀, g - g₀)`. -/
structure HasMixedDirDeriv
    (S : LearningSystem Ω μ Z P_Z Θ G) where
  /-- A target-direction DD bundle anchored at *each* accessible nuisance. -/
  Dθ_at : ∀ g : G, HasDirDerivTheta S g
  /-- The mixed directional-derivative value field. -/
  dℓ_θg              : Θ → G → Z → ℝ
  pointwise_tendsto  : ∀ θ ∈ S.Θ_set, ∀ g ∈ S.G_set, ∀ z,
    Tendsto (fun t : ℝ =>
      ((Dθ_at (S.g₀ + t • (g - S.g₀))).dℓ_θ θ z
        - (Dθ_at S.g₀).dℓ_θ θ z) / t)
      (𝓝[≠] 0) (𝓝 (dℓ_θg θ g z))
  dℓ_θg_meas         : ∀ θ g, Measurable (dℓ_θg θ g)

/-- Population first-order inequality at the truth: for every admissible
target `θ ∈ Θ_set`, the integrated target directional derivative at the
true nuisance is non-negative.  This is the population KKT condition
characterising `θ₀` as a minimizer of `L(·, g₀)` over the convex set
`Θ_set`.

Parameterised over `Dθ : HasDirDerivTheta S S.g₀` so that the integral can
be expressed using the DD datum already attached to the truth. -/
def FirstOrderInequality
    (S : LearningSystem Ω μ Z P_Z Θ G) (Dθ : HasDirDerivTheta S S.g₀) : Prop :=
  ∀ θ ∈ S.Θ_set, 0 ≤ ∫ z, Dθ.dℓ_θ θ z ∂P_Z

end OrthogonalLearning
end Estimation
end Causalean
