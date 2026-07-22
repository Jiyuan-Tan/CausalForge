/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Neyman orthogonality of an orthogonal statistical-learning loss

`NeymanOrthogLoss S Dθ Dg M` says the *integrated* mixed directional
derivative `∫ M.dℓ_θg θ g z dP_Z` vanishes for every admissible target
direction `θ ∈ Θ_set` and nuisance direction `g ∈ G_set`.  This is the
loss-side analogue of `Estimation.OrthogonalMoments.NeymanOrthogonal`.

We also state DCT envelope predicates `DiffQuotientEnvelopeTheta` and
`DiffQuotientEnvelopeG` for the two coordinate directions, mirroring
`Estimation.OrthogonalMoments.DiffQuotientEnvelope`.  These envelopes are the
hypotheses required to swap derivative and integral when bridging from
the pointwise dir derivatives to the integrated population risk.

Finally, we record the score-reformulation theorem
`neymanOrthog_iff_score_deriv_zero`: the note states that Neyman
orthogonality is equivalent to the score map `g ↦ D_θ L(θ₀, g)[ν_θ]`
having zero first derivative at `g₀` for every admissible `ν_θ`.  The
equivalence requires a DCT swap, packaged here as
`MixedScoreDCTBridge`; under that hypothesis the proof is a routine
limit-uniqueness argument.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-neyman-loss`.
-/

import Causalean.Estimation.OrthogonalLearning.Population.DirectionalDeriv

/-! # Neyman Orthogonality for Losses

This file formulates Neyman orthogonality for an orthogonal
statistical-learning loss as the vanishing of the integrated mixed directional
derivative in every admissible target and nuisance direction. It also records
the domination assumptions needed to pass between pointwise directional
derivatives and derivatives of the population risk.

The main predicate is `NeymanOrthogLoss`. The auxiliary predicates
`DiffQuotientEnvelopeTheta`, `DiffQuotientEnvelopeG`, and `MixedScoreDCTBridge`
package dominated-convergence hypotheses, and
`neymanOrthog_iff_score_deriv_zero` proves the score-derivative reformulation
under the bridge hypothesis. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- Neyman orthogonality of the loss: for every admissible target and
nuisance direction, the integrated mixed directional derivative at
`(θ₀, g₀)` vanishes. -/
def NeymanOrthogLoss
    (S : LearningSystem Ω μ Z P_Z Θ G) (M : HasMixedDirDeriv S) : Prop :=
  ∀ θ ∈ S.Θ_set, ∀ g ∈ S.G_set, ∫ z, M.dℓ_θg θ g z ∂P_Z = 0

/-- L¹(P_Z) envelope dominating the *target-direction* difference quotient
of the loss locally near `t = 0`, uniformly in `θ ∈ Θ_set`.  Mirrors
`Estimation.OrthogonalMoments.DiffQuotientEnvelope`. -/
def DiffQuotientEnvelopeTheta
    (S : LearningSystem Ω μ Z P_Z Θ G) (g : G) : Prop :=
  ∀ θ ∈ S.Θ_set, ∃ δ : ℝ, 0 < δ ∧ ∃ env : Z → ℝ,
    Integrable env P_Z ∧
    ∀ᵐ z ∂P_Z, ∀ t : ℝ, t ∈ Set.Ioo (-δ) δ → t ≠ 0 →
      ‖(S.ℓ z (S.θ₀ + t • (θ - S.θ₀)) g - S.ℓ z S.θ₀ g) / t‖ ≤ env z

/-- L¹(P_Z) envelope dominating the *nuisance-direction* difference quotient
of the loss locally near `t = 0`, uniformly in `g ∈ G_set`.  Mirrors
`Estimation.OrthogonalMoments.DiffQuotientEnvelope`. -/
def DiffQuotientEnvelopeG
    (S : LearningSystem Ω μ Z P_Z Θ G) : Prop :=
  ∀ g ∈ S.G_set, ∃ δ : ℝ, 0 < δ ∧ ∃ env : Z → ℝ,
    Integrable env P_Z ∧
    ∀ᵐ z ∂P_Z, ∀ t : ℝ, t ∈ Set.Ioo (-δ) δ → t ≠ 0 →
      ‖(S.ℓ z S.θ₀ (S.g₀ + t • (g - S.g₀)) - S.ℓ z S.θ₀ S.g₀) / t‖ ≤ env z

/-- DCT-bridge hypothesis for the score reformulation: for every admissible
target direction `ν_θ = θ - θ₀` and nuisance direction `ν_g = g - g₀`,
the integrated centred difference quotient of the target dir derivatives
along the nuisance perturbation tends to the integrated mixed dir
derivative `∫ z, M.dℓ_θg θ g z ∂P_Z` as `t → 0` along `𝓝[≠] 0`.

This is exactly what the dominated-convergence theorem yields under the
nuisance-direction envelope `DiffQuotientEnvelopeG` together with
integrability of the inner integrands.  We package the conclusion as a
hypothesis so that the score reformulation can be stated abstractly. -/
def MixedScoreDCTBridge
    (S : LearningSystem Ω μ Z P_Z Θ G) (M : HasMixedDirDeriv S) : Prop :=
  ∀ θ ∈ S.Θ_set, ∀ g ∈ S.G_set,
    Tendsto (fun t : ℝ =>
      ((∫ z, (M.Dθ_at (S.g₀ + t • (g - S.g₀))).dℓ_θ θ z ∂P_Z)
        - (∫ z, (M.Dθ_at S.g₀).dℓ_θ θ z ∂P_Z)) / t)
      (𝓝[≠] 0) (𝓝 (∫ z, M.dℓ_θg θ g z ∂P_Z))

/-- **Score reformulation of Neyman orthogonality.** The note states (closing
sentence of `def:est-osl-neyman-loss`) that Neyman orthogonality is
equivalent to the score map `g' ↦ D_θ L(θ₀, g')[ν_θ]` having zero first
derivative at `g₀` for every admissible target direction `ν_θ`.

Operationally, this is the statement that the difference quotient
`((Dθ_at(g₀ + t • (g - g₀))).dℓ_θ θ z - (Dθ_at g₀).dℓ_θ θ z) / t`
integrates to zero in the limit `t → 0` for every admissible `(θ, g)`,
which is exactly `NeymanOrthogLoss S M` after bridging through the mixed
DD bundle `M`.

The bridge between the integrated centred difference quotient and
`∫ z, M.dℓ_θg θ g z ∂P_Z` (DCT swap) is captured by
`MixedScoreDCTBridge S M`; under that hypothesis the iff is a routine
limit-uniqueness argument. -/
theorem neymanOrthog_iff_score_deriv_zero
    (S : LearningSystem Ω μ Z P_Z Θ G) (M : HasMixedDirDeriv S)
    (hBridge : MixedScoreDCTBridge S M) :
    NeymanOrthogLoss S M ↔
      ∀ θ ∈ S.Θ_set, ∀ g ∈ S.G_set,
        Tendsto (fun t : ℝ =>
          ((∫ z, (M.Dθ_at (S.g₀ + t • (g - S.g₀))).dℓ_θ θ z ∂P_Z)
           - (∫ z, (M.Dθ_at S.g₀).dℓ_θ θ z ∂P_Z)) / t)
          (𝓝[≠] 0) (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · intro hNO θ hθ g hg
    have hbr := hBridge θ hθ g hg
    have hzero : (∫ z, M.dℓ_θg θ g z ∂P_Z) = 0 := hNO θ hθ g hg
    simpa [hzero] using hbr
  · intro hScore θ hθ g hg
    have hbr := hBridge θ hθ g hg
    have hScr := hScore θ hθ g hg
    haveI : (𝓝[≠] (0 : ℝ)).NeBot := NormedField.nhdsNE_neBot 0
    exact tendsto_nhds_unique hbr hScr

end OrthogonalLearning
end Estimation
end Causalean
