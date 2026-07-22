/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Nuisance subspace, weighted orthogonal projection, and residual maker

For `c : WeightedSupport R` and a linear subspace `H : Submodule ℝ (R → ℝ)`,
this file defines the `c.ip`-orthogonal projection `c.proj H : (R → ℝ) →ₗ[ℝ]
(R → ℝ)` onto `H` and the residual maker `c.residualize H = id - c.proj H`,
together with their basic algebraic properties.

This is the **WLS-projection** layer of the FWL substrate.  Its WLS-optimality
characterization (`proj_eq_argmin`, `residualize_orth_iff_argmin`) lives in
`Causalean/Panel/Weighted/WLS.lean`; the FWL coefficient layer
(`Q_XX`, `rhsVec`, `thetaHat`, `fwl_identity`) lives in
`Causalean/Panel/Weighted/FWL.lean`.

Mirrors Definition 2.2 of
`CausalSmith/doc/general_projection_carryover_note.tex`.

## Implementation note

The ambient space `R → ℝ` carries the weighted inner product `c.ip`, but
`c.ip` is only positive-semidefinite (definiteness fails off the observed
indices).  Mathlib's `Submodule.orthogonalProjection` is stated on a Hilbert
space, so we cannot reuse it off-the-shelf without quotienting / reweighting.

The projection lemma is proved by packaging `c.ip` as a positive-semidefinite
bilinear form and applying the generic helper
`Causalean.Mathlib.exists_orthogonalProjection_of_posSemidef`.
-/

import Causalean.Panel.Weighted.InnerProduct
import Causalean.Mathlib.SemiInnerProjection
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Module.LinearMap.Defs

/-! # Weighted projections and residual makers

This file defines the weighted orthogonal projection onto a nuisance subspace
and the corresponding residual maker.

The projection exists for the semidefinite weighted inner product because only
observed records matter. The resulting projection and residual maker are used by
the WLS optimality and finite-cell Frisch-Waugh-Lovell layers. -/

open scoped BigOperators

namespace Causalean
namespace Panel.Weighted
namespace WeightedSupport

variable {R : Type*}
variable [Fintype R] [DecidableEq R]

/-! ### Existence of the weighted orthogonal projection -/

/-- Existence of a `c.ip`-orthogonal projection onto a subspace `H`.

There exists a linear map `P : (R → ℝ) →ₗ[ℝ] (R → ℝ)` such that

* `P X ∈ H` for every `X`;
* `c.ip (X - P X) h = 0` for every `X : R → ℝ` and every `h ∈ H`.

This is sufficient to derive idempotence and all algebraic properties of
the residual maker `M_H = id - P` used in the FWL/WLS algebra. -/
lemma weighted_orthogonal_projection_exists
    (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ)) :
    ∃ P : (R → ℝ) →ₗ[ℝ] (R → ℝ),
      (∀ X, P X ∈ H) ∧ (∀ X, ∀ h ∈ H, c.ip (X - P X) h = 0) := by
  classical
  let B : LinearMap.BilinForm ℝ (R → ℝ) :=
    LinearMap.mk₂ ℝ (fun X Y => c.ip X Y)
      (by
        intro X Y Z
        exact c.ip_add_left X Y Z)
      (by
        intro a X Z
        exact c.ip_smul_left a X Z)
      (by
        intro X Y Z
        exact c.ip_add_right X Y Z)
      (by
        intro a X Z
        exact c.ip_smul_right a X Z)
  have hsymm : ∀ X Y : R → ℝ, B X Y = B Y X := by
    intro X Y
    exact c.ip_symm X Y
  have hpos : ∀ X : R → ℝ, 0 ≤ B X X := by
    intro X
    exact c.ip_self_nonneg X
  rcases Causalean.Mathlib.exists_orthogonalProjection_of_posSemidef
      (B := B) hsymm hpos H with ⟨P, hmem, horth⟩
  refine ⟨P, hmem, ?_⟩
  intro X h hH
  change B (X - P X) h = 0
  exact horth X h hH

/-- The `c.ip`-orthogonal projection onto `H`, chosen via classical choice
from `weighted_orthogonal_projection_exists`. -/
noncomputable def proj (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ)) :
    (R → ℝ) →ₗ[ℝ] (R → ℝ) :=
  (c.weighted_orthogonal_projection_exists H).choose

/-- The chosen weighted projection always lands in the nuisance subspace. -/
lemma proj_mem (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ)) (X : R → ℝ) :
    c.proj H X ∈ H :=
  (c.weighted_orthogonal_projection_exists H).choose_spec.1 X

/-- The residual from the chosen weighted projection is orthogonal to every
element of the nuisance subspace. -/
lemma proj_orthogonal (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    (X : R → ℝ) {h : R → ℝ} (hH : h ∈ H) :
    c.ip (X - c.proj H X) h = 0 :=
  (c.weighted_orthogonal_projection_exists H).choose_spec.2 X h hH

/-! ### Idempotence of `c.proj H` -/

/-- If `Y ∈ H` then `c.proj H Y` agrees with `Y` on every observed index. -/
lemma proj_apply_of_mem (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    {Y : R → ℝ} (hY : Y ∈ H) (r : R) (hr : r ∈ c.observed) :
    c.proj H Y r = Y r := by
  have hdiff : Y - c.proj H Y ∈ H := H.sub_mem hY (c.proj_mem H Y)
  have hself : c.ip (Y - c.proj H Y) (Y - c.proj H Y) = 0 :=
    c.proj_orthogonal H Y hdiff
  have hzero : ∀ s ∈ c.observed, (Y - c.proj H Y) s = 0 :=
    (c.ip_self_eq_zero_iff (Y - c.proj H Y)).mp hself
  have h := hzero r hr
  have hh : Y r - c.proj H Y r = 0 := h
  exact (sub_eq_zero.mp hh).symm

/-- Projection uniqueness on observed indices.

If `Y ∈ H` and `X - Y` is orthogonal to every element of `H`, then the
chosen semidefinite projection `c.proj H X` agrees with `Y` on the observed
support.  Off the support the projection is not unique and no equality is
claimed. -/
lemma proj_apply_eq_of_mem_orthogonal (c : WeightedSupport R)
    (H : Submodule ℝ (R → ℝ))
    (X : R → ℝ) {Y : R → ℝ} (hY : Y ∈ H)
    (horth : ∀ h ∈ H, c.ip (X - Y) h = 0)
    (r : R) (hr : r ∈ c.observed) :
    c.proj H X r = Y r := by
  let W : R → ℝ := Y - c.proj H X
  have hWmem : W ∈ H := H.sub_mem hY (c.proj_mem H X)
  have hproj : c.ip (X - c.proj H X) W = 0 :=
    c.proj_orthogonal H X hWmem
  have hYorth : c.ip (X - Y) W = 0 := horth W hWmem
  have hdecomp : X - c.proj H X = (X - Y) + W := by
    ext s
    simp [W]
  have hsplit :
      c.ip (X - c.proj H X) W = c.ip (X - Y) W + c.ip W W := by
    rw [hdecomp, c.ip_add_left]
  have hself : c.ip W W = 0 := by
    rw [hproj, hYorth, zero_add] at hsplit
    exact hsplit.symm
  have hzero : ∀ s ∈ c.observed, W s = 0 :=
    (c.ip_self_eq_zero_iff W).mp hself
  have hrzero : Y r - c.proj H X r = 0 := hzero r hr
  exact (sub_eq_zero.mp hrzero).symm

/-- Idempotence of the projection on the observed indices. -/
lemma proj_idem_apply (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    (X : R → ℝ) (r : R) (hr : r ∈ c.observed) :
    c.proj H (c.proj H X) r = c.proj H X r :=
  c.proj_apply_of_mem H (c.proj_mem H X) r hr

/-! ### Residual maker -/

/-- The residual maker `M_H = id - P_H`. -/
noncomputable def residualize (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ)) :
    (R → ℝ) →ₗ[ℝ] (R → ℝ) :=
  LinearMap.id - c.proj H

/-- Applying the residual maker subtracts the weighted projection from the
original array. -/
@[simp] lemma residualize_apply (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    (X : R → ℝ) :
    c.residualize H X = X - c.proj H X := by
  simp [residualize]

/-- The residualized scalar array `X̃ := M_H X`. -/
noncomputable def tildeX (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    (X : R → ℝ) : R → ℝ :=
  c.residualize H X

/-- The residualized scalar array is the original array minus its weighted
projection onto the nuisance subspace. -/
@[simp] lemma tildeX_eq (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    (X : R → ℝ) :
    c.tildeX H X = X - c.proj H X := by
  simp [tildeX]

/-- **Key orthogonality.** The residual `M_H X` is `c.ip`-orthogonal to
every element of `H`. -/
lemma residualize_in_orthogonal (c : WeightedSupport R)
    (H : Submodule ℝ (R → ℝ)) (X : R → ℝ) {h : R → ℝ} (hH : h ∈ H) :
    c.ip (c.tildeX H X) h = 0 := by
  simp only [tildeX_eq]
  exact c.proj_orthogonal H X hH

/-- If `X ∈ H` then `X̃ = M_H X` vanishes on `c.observed`. -/
lemma residualize_self_of_mem (c : WeightedSupport R)
    (H : Submodule ℝ (R → ℝ)) {X : R → ℝ} (hX : X ∈ H)
    (r : R) (hr : r ∈ c.observed) :
    c.tildeX H X r = 0 := by
  simp only [tildeX_eq, Pi.sub_apply]
  rw [c.proj_apply_of_mem H hX r hr]
  ring

/-- Idempotence of `M_H` on the observed indices: `M_H (M_H X) = M_H X` on
`c.observed`. -/
lemma residualize_idem_apply (c : WeightedSupport R)
    (H : Submodule ℝ (R → ℝ)) (X : R → ℝ)
    (r : R) (hr : r ∈ c.observed) :
    c.residualize H (c.residualize H X) r = c.residualize H X r := by
  simp only [residualize_apply, Pi.sub_apply]
  have hkey : c.proj H (X - c.proj H X) r = 0 := by
    set Z : R → ℝ := X - c.proj H X
    set W : R → ℝ := c.proj H Z
    have hWmem : W ∈ H := c.proj_mem H Z
    have h1 : c.ip Z W = 0 := c.proj_orthogonal H X hWmem
    have h2 : c.ip (Z - W) W = 0 := c.proj_orthogonal H Z hWmem
    have h3 : c.ip W W = 0 := by
      have hZ : Z = (Z - W) + W := (sub_add_cancel Z W).symm
      have hsplit : c.ip Z W = c.ip (Z - W) W + c.ip W W := by
        calc c.ip Z W
            = c.ip ((Z - W) + W) W := by rw [← hZ]
          _ = c.ip (Z - W) W + c.ip W W := c.ip_add_left _ _ _
      have hsum : c.ip (Z - W) W + c.ip W W = 0 := hsplit ▸ h1
      have : c.ip W W = 0 := by
        have := hsum
        rw [h2, zero_add] at this
        exact this
      exact this
    have hzero : ∀ s ∈ c.observed, W s = 0 :=
      (c.ip_self_eq_zero_iff W).mp h3
    exact hzero r hr
  change (X - c.proj H X) r - c.proj H (X - c.proj H X) r =
      (X - c.proj H X) r
  rw [hkey, sub_zero]

/-! ### Vector-form residualization -/

variable {K : ℕ}

/-- Column-by-column residualization for vector arrays `X : Fin K → (R → ℝ)`. -/
noncomputable def tildeXVec (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    (X : Fin K → R → ℝ) : Fin K → R → ℝ :=
  fun k => c.tildeX H (X k)

/-- The residualized vector array applies scalar residualization to the chosen
column. -/
@[simp] lemma tildeXVec_apply (c : WeightedSupport R)
    (H : Submodule ℝ (R → ℝ)) (X : Fin K → R → ℝ) (k : Fin K) :
    c.tildeXVec H X k = c.tildeX H (X k) := rfl

end WeightedSupport
end Panel.Weighted
end Causalean
