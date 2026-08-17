/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Neyman orthogonality and DCT bridge for `GeneralMoment`

* `NeymanOrthogonal M D` — `∫ D.dM η dP_Z = 0` for every `η ∈ M.H_ε`.
* `DiffQuotientEnvelope M` — existence of an L¹(P_Z) envelope dominating the
  difference quotient `(m_t - m_0)/t` near `t = 0`.
* `integratedMoment_diffQuotient_tendsto_zero` — DCT bridge: combining the
  pointwise convergence in `HasDirDeriv` with the integrability envelope and
  Neyman orthogonality yields that the integrated difference quotient tends
  to zero at the truth.

See `docs/superpowers/specs/2026-05-06-general-dml-framework-design.md` §4.3.
-/

import Causalean.Estimation.OrthogonalMoments.DirectionalDeriv

/-! # Neyman Orthogonality for Abstract Moments

This file defines Neyman orthogonality for a moment functional through the
vanishing population integral of its nuisance directional derivative. It also
records the dominated-convergence envelope needed to pass pointwise directional
derivatives through integration. -/

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- Neyman orthogonality for the `(M, D)` pair: the population integral of the
directional derivative vanishes at every nuisance perturbation. -/
def NeymanOrthogonal
    (M : GeneralMoment Ω μ Z P_Z H) (D : HasDirDeriv M) : Prop :=
  ∀ η ∈ M.H_ε, ∫ z, D.dM η z ∂P_Z = 0

/-- `DiffQuotientEnvelope M` asserts that, locally near `t = 0`, the
difference quotient of `m` along the segment `η₀ → η` is dominated by a
fixed L¹(P_Z) function. -/
def DiffQuotientEnvelope (M : GeneralMoment Ω μ Z P_Z H) : Prop :=
  ∀ η ∈ M.H_ε, ∃ δ : ℝ, 0 < δ ∧ ∃ g : Z → ℝ,
    Integrable g P_Z ∧
    ∀ᵐ z ∂P_Z, ∀ t : ℝ, t ∈ Set.Ioo (-δ) δ → t ≠ 0 →
      ‖(M.m (M.η₀ + t • (η - M.η₀)) z M.θ₀ - M.m M.η₀ z M.θ₀) / t‖ ≤ g z

/-- **Abstract DCT bridge.** Given a general moment M with directional-derivative
structure D, assume [Neyman orthogonality — the population directional derivative
vanishes at every admissible nuisance perturbation](hyp:hNO), and [an L¹(P_Z) envelope
dominating the difference quotient of the moment near `t = 0`](hyp:hEnv). Suppose
[η lies in the admissible nuisance neighborhood `M.H_ε`](hyp:hη), that [the moment along
the segment from η₀ to η is integrable at every nonzero t](hyp:hMt_int), and that [the
moment at η₀ is integrable](hyp:hM0_int). Then [the integrated difference quotient
`(∫ m(η₀ + t · (η − η₀)) dP_Z − ∫ m(η₀) dP_Z) / t` tends to zero as t → 0 along the
punctured neighborhood](goal). -/
theorem integratedMoment_diffQuotient_tendsto_zero
    (M : GeneralMoment Ω μ Z P_Z H) (D : HasDirDeriv M)
    (hNO : NeymanOrthogonal M D)
    (hEnv : DiffQuotientEnvelope M)
    {η : H} (hη : η ∈ M.H_ε)
    (hMt_int : ∀ t ≠ (0 : ℝ), Integrable
      (fun z => M.m (M.η₀ + t • (η - M.η₀)) z M.θ₀) P_Z)
    (hM0_int : Integrable (fun z => M.m M.η₀ z M.θ₀) P_Z) :
    Tendsto (fun t : ℝ =>
      (∫ z, M.m (M.η₀ + t • (η - M.η₀)) z M.θ₀ ∂P_Z
         - ∫ z, M.m M.η₀ z M.θ₀ ∂P_Z) / t)
      (𝓝[≠] 0) (𝓝 0) := by
  rcases hEnv η hη with ⟨δ, hδ_pos, g, hg_int, hg_bound⟩
  let F : ℝ → Z → ℝ := fun t z =>
    (M.m (M.η₀ + t • (η - M.η₀)) z M.θ₀ - M.m M.η₀ z M.θ₀) / t
  have hIoo : Set.Ioo (-δ) δ ∈ 𝓝[≠] (0 : ℝ) := by
    have hIoo_nhds : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := by
      exact Ioo_mem_nhds (by linarith) hδ_pos
    exact nhdsWithin_le_nhds hIoo_nhds
  have h_ne : {t : ℝ | t ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := self_mem_nhdsWithin
  have hlim_integral :
      Tendsto (fun t : ℝ => ∫ z, F t z ∂P_Z) (𝓝[≠] 0)
        (𝓝 (∫ z, D.dM η z ∂P_Z)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence g
    · exact Filter.Eventually.of_forall (fun t =>
        (((M.m_meas (M.η₀ + t • (η - M.η₀)) M.θ₀).sub
          (M.m_meas M.η₀ M.θ₀)).div_const t).aestronglyMeasurable)
    · filter_upwards [hIoo, h_ne] with t htIoo ht_ne
      exact hg_bound.mono (fun z hz => by
        simpa [F] using hz t htIoo ht_ne)
    · exact hg_int
    · exact Filter.Eventually.of_forall (fun z => by
        simpa [F] using D.pointwise_tendsto η hη z)
  have h_eq :
      (fun t : ℝ => ∫ z, F t z ∂P_Z) =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun t : ℝ =>
          (∫ z, M.m (M.η₀ + t • (η - M.η₀)) z M.θ₀ ∂P_Z
             - ∫ z, M.m M.η₀ z M.θ₀ ∂P_Z) / t) := by
    filter_upwards [h_ne] with t ht_ne
    calc
      ∫ z, F t z ∂P_Z
          = (∫ z, M.m (M.η₀ + t • (η - M.η₀)) z M.θ₀
              - M.m M.η₀ z M.θ₀ ∂P_Z) / t := by
            simp [F, MeasureTheory.integral_div]
      _ = (∫ z, M.m (M.η₀ + t • (η - M.η₀)) z M.θ₀ ∂P_Z
             - ∫ z, M.m M.η₀ z M.θ₀ ∂P_Z) / t := by
            rw [MeasureTheory.integral_sub (hMt_int t ht_ne) hM0_int]
  have hlim_to_deriv :
      Tendsto (fun t : ℝ =>
        (∫ z, M.m (M.η₀ + t • (η - M.η₀)) z M.θ₀ ∂P_Z
           - ∫ z, M.m M.η₀ z M.θ₀ ∂P_Z) / t)
        (𝓝[≠] 0) (𝓝 (∫ z, D.dM η z ∂P_Z)) :=
    hlim_integral.congr' h_eq
  simpa [NeymanOrthogonal, hNO η hη] using hlim_to_deriv

end OrthogonalMoments
end Estimation
end Causalean
