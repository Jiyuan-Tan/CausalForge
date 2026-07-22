/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Abstract semiparametric-efficiency Hilbert-projection machine

This file is **Layer A** of the Hahn (1998) semiparametric-efficiency
formalization: pure Hilbert-space geometry, no measure theory and no causal
content. It is the reusable abstraction that every estimator-efficiency
theorem will cite.

Fix a real Hilbert space `H` and a *tangent subspace* `T : Submodule ℝ H`
(in applications, the closure of the set of scores of regular parametric
submodels). A reference influence function `g : H` is a *gradient* if its
inner product against every tangent direction is matched. The **efficient
influence function** `efficientIF T g` is the orthogonal projection of `g`
onto `T`, and the **efficiency bound** `effBound T g` is its squared norm.
Pythagoras gives the efficiency lower bound: every gradient `ψ` satisfies
`effBound T g ≤ ‖ψ‖²`, with equality iff `ψ = efficientIF T g`.

The closing section records the *tangent-shrinking corollary* (the abstract
"role of the propensity score"): if the reference influence function already
lies in the smaller tangent space, shrinking the tangent space leaves the
efficiency bound unchanged.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Tangent-Space Projection for Efficiency

This file develops the Hilbert-space geometry behind semiparametric efficiency:
gradients are compared along a tangent subspace, the efficient influence
function is the orthogonal projection onto that subspace, and the efficiency
bound is its squared norm. It also proves the abstract tangent-shrinking
principle used in the Hahn efficiency formalization. -/

namespace Causalean.Estimation.Efficiency

open scoped InnerProductSpace RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- `ψ` is a *gradient* of `g` relative to the tangent space `T` when its inner
product against every tangent direction matches that of `g`. In semiparametric
models `g` is a reference influence function and the gradients are exactly the
influence functions of regular asymptotically linear estimators. -/
def IsGradient (T : Submodule ℝ H) (g ψ : H) : Prop :=
  ∀ s ∈ T, ⟪ψ, s⟫_ℝ = ⟪g, s⟫_ℝ

/-- The **efficient influence function**: the orthogonal projection of the
reference gradient `g` onto the tangent space `T`, coerced back into `H`. -/
noncomputable def efficientIF (T : Submodule ℝ H) [T.HasOrthogonalProjection]
    (g : H) : H :=
  (T.orthogonalProjection g : H)

/-- The **semiparametric efficiency bound**: the squared norm of the efficient
influence function. -/
noncomputable def effBound (T : Submodule ℝ H) [T.HasOrthogonalProjection]
    (g : H) : ℝ :=
  ‖efficientIF T g‖ ^ 2

variable {T : Submodule ℝ H} [T.HasOrthogonalProjection]

/-- `efficientIF` is the coerced star-projection (the projection seen as an
endomorphism of `H`). -/
theorem efficientIF_eq_starProjection (g : H) :
    efficientIF T g = T.starProjection g := rfl

/-- The efficient influence function lies in the tangent space. -/
theorem efficientIF_mem (g : H) : efficientIF T g ∈ T :=
  (T.orthogonalProjection g).2

omit [T.HasOrthogonalProjection] in
/-- A vector is a gradient of `g` iff it differs from `g` by an element of the
orthogonal complement of the tangent space. -/
theorem isGradient_iff_sub_mem_orthogonal (g ψ : H) :
    IsGradient T g ψ ↔ ψ - g ∈ Tᗮ := by
  constructor
  · intro h
    rw [Submodule.mem_orthogonal]
    intro s hs
    rw [inner_sub_right, real_inner_comm ψ s, real_inner_comm g s, h s hs, sub_self]
  · intro h s hs
    rw [Submodule.mem_orthogonal] at h
    have hzero := h s hs
    rw [inner_sub_right, sub_eq_zero] at hzero
    rw [real_inner_comm s ψ, real_inner_comm s g, hzero]

/-- The efficient influence function is itself a gradient of `g`. -/
theorem efficientIF_isGradient (g : H) : IsGradient T g (efficientIF T g) := by
  intro s hs
  exact T.inner_orthogonalProjection_eq_of_mem_right ⟨s, hs⟩ g

/-- A gradient `ψ` projects onto the same efficient influence function as `g`. -/
theorem orthogonalProjection_eq_of_isGradient {g ψ : H} (h : IsGradient T g ψ) :
    (T.orthogonalProjection ψ : H) = efficientIF T g := by
  have hsub : ψ - g ∈ Tᗮ := (isGradient_iff_sub_mem_orthogonal g ψ).1 h
  have hz : T.orthogonalProjection (ψ - g) = 0 :=
    T.orthogonalProjection_eq_zero_iff.mpr hsub
  have hlin : T.orthogonalProjection ψ - T.orthogonalProjection g
      = T.orthogonalProjection (ψ - g) := by
    rw [map_sub]
  rw [hz, sub_eq_zero] at hlin
  rw [efficientIF, hlin]

/-- **Pythagoras for gradients.** For any gradient `ψ`, the squared norm splits
into the efficiency bound plus the squared norm of the orthogonal remainder. -/
theorem normSq_gradient_decomp {g ψ : H} (h : IsGradient T g ψ) :
    ‖ψ‖ ^ 2 = ‖efficientIF T g‖ ^ 2 + ‖ψ - efficientIF T g‖ ^ 2 := by
  have hproj : (T.orthogonalProjection ψ : H) = efficientIF T g :=
    orthogonalProjection_eq_of_isGradient h
  have hmem : efficientIF T g ∈ T := efficientIF_mem g
  have horth : ψ - efficientIF T g ∈ Tᗮ := by
    rw [← hproj]
    exact T.sub_starProjection_mem_orthogonal ψ
  have hzero : ⟪efficientIF T g, ψ - efficientIF T g⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).1 horth _ hmem
  have hsplit : ψ = efficientIF T g + (ψ - efficientIF T g) := by abel
  calc ‖ψ‖ ^ 2 = ‖efficientIF T g + (ψ - efficientIF T g)‖ ^ 2 := by rw [← hsplit]
    _ = ‖efficientIF T g‖ ^ 2 + ‖ψ - efficientIF T g‖ ^ 2 := by
        rw [norm_add_sq_real, hzero]; ring

/-- **Efficiency lower bound.** The efficiency bound is at most the squared norm
of any gradient. -/
theorem effBound_le_normSq {g ψ : H} (h : IsGradient T g ψ) :
    effBound T g ≤ ‖ψ‖ ^ 2 := by
  rw [effBound, normSq_gradient_decomp h]
  have : (0 : ℝ) ≤ ‖ψ - efficientIF T g‖ ^ 2 := sq_nonneg _
  linarith

/-- **Sharpness.** A gradient attains the efficiency bound iff it equals the
efficient influence function. -/
theorem norm_eq_iff_eq_efficientIF {g ψ : H} (h : IsGradient T g ψ) :
    ‖ψ‖ ^ 2 = effBound T g ↔ ψ = efficientIF T g := by
  rw [effBound, normSq_gradient_decomp h]
  constructor
  · intro heq
    have hsq : ‖ψ - efficientIF T g‖ ^ 2 = 0 := by linarith
    have hnorm : ‖ψ - efficientIF T g‖ = 0 := by
      exact pow_eq_zero_iff (by norm_num) |>.1 hsq
    rw [norm_eq_zero, sub_eq_zero] at hnorm
    exact hnorm
  · intro heq
    rw [heq, sub_self, norm_zero]; ring

/-- A gradient that lies in the tangent space is the efficient influence
function. -/
theorem efficientIF_unique {g ψ : H} (h : IsGradient T g ψ) (hψ : ψ ∈ T) :
    ψ = efficientIF T g := by
  have hproj : (T.orthogonalProjection ψ : H) = efficientIF T g :=
    orthogonalProjection_eq_of_isGradient h
  rw [← hproj]
  exact (T.starProjection_eq_self_iff.mpr hψ).symm

/-! ### Tangent-shrinking corollary (abstract "role of the propensity score") -/

/-- If the reference gradient already lies in the tangent space, the efficient
influence function equals it. -/
theorem efficientIF_eq_self_of_mem (T : Submodule ℝ H) [T.HasOrthogonalProjection]
    {g : H} (hg : g ∈ T) : efficientIF T g = g := by
  rw [efficientIF_eq_starProjection]
  exact T.starProjection_eq_self_iff.mpr hg

/-- **Tangent-shrinking corollary.** If the reference influence function lies in
the smaller tangent space `T' ≤ T`, then both the smaller and larger tangent
spaces leave it fixed, so the efficiency bound is unchanged. Interpretation:
knowing the propensity score shrinks the tangent space, but if `ψ_AIPW` already
lives in the smaller space the efficiency bound does not move. -/
theorem effBound_eq_of_mem_sub
    (T T' : Submodule ℝ H) [T.HasOrthogonalProjection] [T'.HasOrthogonalProjection]
    (hle : T' ≤ T) {g : H} (hg : g ∈ T') :
    efficientIF T' g = g ∧ efficientIF T g = g ∧ effBound T' g = effBound T g := by
  have h1 : efficientIF T' g = g := efficientIF_eq_self_of_mem T' hg
  have h2 : efficientIF T g = g := efficientIF_eq_self_of_mem T (hle hg)
  exact ⟨h1, h2, by rw [effBound, effBound, h1, h2]⟩

end Causalean.Estimation.Efficiency
