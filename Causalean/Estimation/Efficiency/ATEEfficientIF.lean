/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Estimation.Efficiency.PathwiseGradient
import Causalean.Estimation.Efficiency.ATETangent

/-!
# AIPW as the efficient influence function for the backdoor ATE

This module connects the abstract pathwise-gradient layer to the backdoor ATE
system. It first rewrites the Hilbert-space inner product against `aipwLp` as
the covariance pairing with `ψ_AIPW`, then proves that regular submodel scores
belong to the full mean-zero tangent space `Tfull`.

Under an explicit Hahn pathwise-derivative identity and an explicit
nonparametric tangent-space hypothesis, `aipw_isPathwiseGradient_ATE` proves
that the AIPW score is a pathwise gradient of the ATE functional, and
`aipw_is_efficientInfluenceFunction` proves that this AIPW score is the
canonical efficient influence function in the mean-zero tangent space.
-/

namespace Causalean
namespace Estimation
namespace ATE.BackdoorEstimationSystem

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO
open Causalean.Estimation.Efficiency
open scoped InnerProductSpace RealInnerProductSpace

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- The covariance pairing between the AIPW influence function and any
square-integrable score equals the Hilbert-space inner product against the AIPW
element in the observed-data square-integrable space.

This bridge rewrites the inner product of `S.aipwLp` against `f` as the integral
of `S.ψ_AIPW` times `f`, using the existing `Lp` inner-product formula and the
almost-everywhere representative equality for `S.aipwLp`. -/
theorem inner_aipwLp_eq_integral (S : ATE.BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (f : Lp ℝ 2 S.P_Z) :
    ⟪S.aipwLp h_overlap hA h_y2 h_yd2, f⟫_ℝ
      = ∫ z, S.ψ_AIPW z * f z ∂S.P_Z := by
  rw [Causalean.Panel.FWLInstanceL2.inner_eq_integral]
  refine MeasureTheory.integral_congr_ae ?_
  have hae : (S.aipwLp h_overlap hA h_y2 h_yd2 : γ × Bool × ℝ → ℝ)
      =ᵐ[S.P_Z] S.ψ_AIPW :=
    (S.aipw_memLp h_overlap hA h_y2 h_yd2).coeFn_toLp
  filter_upwards [hae] with z hz
  rw [hz]

/-- Every regular submodel score is mean-zero, so every such score belongs to
the full nonparametric tangent space for the observed-data law.

The proof unfolds the full tangent space as the orthogonal complement of the
constant-one direction and applies the score mean-zero field of a regular
submodel. -/
theorem score_mem_Tfull (S : ATE.BackdoorEstimationSystem P γ)
    (m : RegularSubmodel S.oneLp S.P_Z) : m.score ∈ S.Tfull := by
  rw [Tfull, Submodule.mem_orthogonal_singleton_iff_inner_left]
  exact m.score_meanZero

/-- The full mean-zero space is a genuine tangent space once the supplied
nonparametric-model hypothesis says it is contained in the closed span of
regular-submodel scores.

The reverse containment needed for the tangent-space interface is automatic
because regular-submodel scores are mean-zero. -/
theorem isTangentSpace_Tfull (S : ATE.BackdoorEstimationSystem P γ)
    (hdense : S.Tfull ≤ tangentSpace S.oneLp S.P_Z) :
    IsTangentSpace S.oneLp S.P_Z S.Tfull where
  scores_mem m := S.score_mem_Tfull m
  le_closure := hdense

/-- Hahn's pathwise-derivative identity makes the AIPW score a pathwise gradient
of the backdoor ATE functional along every regular submodel.

The only model-specific analytic input is the supplied Hahn derivative identity.
The proof converts Hahn's covariance derivative into the abstract inner-product
form using `inner_aipwLp_eq_integral`. -/
theorem aipw_isPathwiseGradient_ATE (S : ATE.BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (ψ : Measure (γ × Bool × ℝ) → ℝ)
    (hHahn : ∀ m : RegularSubmodel S.oneLp S.P_Z,
      HasDerivAt (fun t => ψ (m.path t))
        (∫ z, S.ψ_AIPW z * (m.score z) ∂S.P_Z) 0) :
    IsPathwiseGradient S.oneLp S.P_Z ψ (S.aipwLp h_overlap hA h_y2 h_yd2) := by
  intro m
  rw [S.inner_aipwLp_eq_integral h_overlap hA h_y2 h_yd2 m.score]
  exact hHahn m

/-- The AIPW influence function is the efficient influence function for the
backdoor average treatment effect in the nonparametric observed-data model.

Under the supplied Hahn derivative identity and nonparametric tangent-space
hypothesis, the AIPW score is a pathwise gradient, belongs to the full mean-zero
tangent space, and equals the canonical projected gradient obtained from any
other pathwise gradient. -/
theorem aipw_is_efficientInfluenceFunction (S : ATE.BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (ψ : Measure (γ × Bool × ℝ) → ℝ)
    (hHahn : ∀ m : RegularSubmodel S.oneLp S.P_Z,
      HasDerivAt (fun t => ψ (m.path t))
        (∫ z, S.ψ_AIPW z * (m.score z) ∂S.P_Z) 0)
    (hdense : S.Tfull ≤ tangentSpace S.oneLp S.P_Z) :
    IsPathwiseGradient S.oneLp S.P_Z ψ (S.aipwLp h_overlap hA h_y2 h_yd2)
      ∧ S.aipwLp h_overlap hA h_y2 h_yd2 ∈ S.Tfull
      ∧ ∀ g, IsPathwiseGradient S.oneLp S.P_Z ψ g →
          efficientIF S.Tfull g = S.aipwLp h_overlap hA h_y2 h_yd2 := by
  have hgrad := S.aipw_isPathwiseGradient_ATE h_overlap hA h_y2 h_yd2 ψ hHahn
  have hmem := S.aipwLp_mem_tangent h_overlap hA h_y2 h_yd2
  have hT := S.isTangentSpace_Tfull hdense
  refine ⟨hgrad, hmem, fun g hg => ?_⟩
  exact (isPathwiseGradient_eq_efficientIF_of_mem hT hg hgrad hmem).symm

end ATE.BackdoorEstimationSystem
end Estimation
end Causalean
