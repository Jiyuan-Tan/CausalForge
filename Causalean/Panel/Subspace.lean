/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Panel nuisance subspace aliases

For `c : Cells I T` and a linear subspace `H : Submodule ℝ ((I × T) → ℝ)`,
the weighted inner product, orthogonal projection, residual maker, and
residualized regressor operations are provided by the generic weighted-support
substrate. This file exposes the panel-level `Cells` aliases used by downstream
panel APIs: `V`, `proj`, `residualize`, `tildeX`, `tildeXVec`, and the main
orthogonality and idempotence lemmas.
-/

import Causalean.Panel.InnerProduct
import Causalean.Panel.Weighted.Subspace

/-! # Panel Subspace Aliases

This file exposes panel-level names for weighted orthogonal projection,
residualization, and cell-array spaces. It keeps the panel regression API
connected to the generic weighted subspace construction used throughout the
library while preserving convenient `Cells.*` names for projection,
residual-maker, residualized-regressor, orthogonality, and idempotence facts. -/

namespace Causalean
namespace Panel
namespace Cells

/-- Cell-array space: scalar-valued arrays on `I × T`. -/
abbrev V (I T : Type*) : Type _ := (I × T) → ℝ

variable {I T : Type*}
variable [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]

-- Most projection / residualization / tildeX declarations live under
-- `Causalean.Panel.Weighted.WeightedSupport.*` and are inherited through the
-- `Cells := WeightedSupport (I × T)` abbreviation.

-- Bare-name aliases under `Cells` namespace for downstream files that
-- reference these by fully-qualified name `Cells.proj`, `Cells.tildeX`,
-- etc. (rather than through dot-notation, which already resolves
-- transparently through the abbreviation).

/-- Bare-name alias for `c.proj`.  Definitionally equal to
`Causalean.Panel.Weighted.WeightedSupport.proj`. -/
noncomputable def proj (c : Cells I T) (H : Submodule ℝ (V I T)) :
    V I T →ₗ[ℝ] V I T :=
  Causalean.Panel.Weighted.WeightedSupport.proj c H

/-- The panel projection alias is definitionally equal to the generic weighted
support projection. -/
lemma proj_eq_weighted (c : Cells I T) (H : Submodule ℝ (V I T)) :
    proj c H = Causalean.Panel.Weighted.WeightedSupport.proj c H := rfl

/-- Bare-name alias for `c.residualize`.  Definitionally equal to
`Causalean.Panel.Weighted.WeightedSupport.residualize`. -/
noncomputable def residualize (c : Cells I T) (H : Submodule ℝ (V I T)) :
    V I T →ₗ[ℝ] V I T :=
  LinearMap.id - c.proj H

/-- The panel residual-maker alias is definitionally equal to the generic
weighted support residual maker. -/
lemma residualize_eq_weighted (c : Cells I T) (H : Submodule ℝ (V I T)) :
    residualize c H = Causalean.Panel.Weighted.WeightedSupport.residualize c H := rfl

/-- Bare-name alias for `c.tildeX`.  Same body as
`Causalean.Panel.Weighted.WeightedSupport.tildeX` (defined as `residualize H X`)
so that `unfold tildeX` exposes the residualized form. -/
noncomputable def tildeX (c : Cells I T) (H : Submodule ℝ (V I T))
    (X : V I T) : V I T :=
  c.residualize H X

/-- The panel residualized-array alias is definitionally equal to the generic
weighted support residualized array. -/
lemma tildeX_eq_weighted (c : Cells I T) (H : Submodule ℝ (V I T))
    (X : V I T) :
    tildeX c H X = Causalean.Panel.Weighted.WeightedSupport.tildeX c H X := rfl

variable {K : ℕ}

/-- Bare-name alias for `c.tildeXVec`.  Same body as
`Causalean.Panel.Weighted.WeightedSupport.tildeXVec` so that `unfold tildeXVec`
exposes the column-by-column form. -/
noncomputable def tildeXVec (c : Cells I T) (H : Submodule ℝ (V I T))
    (X : Fin K → V I T) : Fin K → V I T :=
  fun k => c.tildeX H (X k)

/-- The panel column-wise residualization alias is definitionally equal to the
generic weighted support column-wise residualization. -/
lemma tildeXVec_eq_weighted (c : Cells I T) (H : Submodule ℝ (V I T))
    (X : Fin K → V I T) :
    tildeXVec c H X = Causalean.Panel.Weighted.WeightedSupport.tildeXVec c H X := rfl

/-! ### Lemma aliases under the `Cells` namespace

These re-export the corresponding `WeightedSupport.*` lemmas under the
`Cells` namespace so that downstream files can reference them as
`Cells.tildeX_eq`, `Cells.residualize_in_orthogonal`, etc., either by
fully-qualified name (in `simp`-set hints, in proof scripts) or by
dot-notation. -/

/-- Residualizing a panel array subtracts its nuisance-space projection. -/
@[simp] lemma tildeX_eq (c : Cells I T) (H : Submodule ℝ (V I T))
    (X : V I T) :
    c.tildeX H X = X - c.proj H X :=
  Causalean.Panel.Weighted.WeightedSupport.tildeX_eq c H X

/-- Applying the panel residual maker subtracts the nuisance-space projection. -/
@[simp] lemma residualize_apply (c : Cells I T) (H : Submodule ℝ (V I T))
    (X : V I T) :
    c.residualize H X = X - c.proj H X :=
  Causalean.Panel.Weighted.WeightedSupport.residualize_apply c H X

/-- Column-wise residualization residualizes each regressor column separately. -/
@[simp] lemma tildeXVec_apply (c : Cells I T) (H : Submodule ℝ (V I T))
    (X : Fin K → V I T) (k : Fin K) :
    c.tildeXVec H X k = c.tildeX H (X k) :=
  Causalean.Panel.Weighted.WeightedSupport.tildeXVec_apply c H X k

/-- Residualized arrays are orthogonal to every nuisance-space array under the
panel weighted inner product. -/
lemma residualize_in_orthogonal (c : Cells I T)
    (H : Submodule ℝ (V I T)) (X : V I T) {h : V I T} (hH : h ∈ H) :
    c.ip (c.tildeX H X) h = 0 :=
  Causalean.Panel.Weighted.WeightedSupport.residualize_in_orthogonal c H X hH

/-- A nuisance-space array residualizes to zero on observed cells. -/
lemma residualize_self_of_mem (c : Cells I T)
    (H : Submodule ℝ (V I T)) {X : V I T} (hX : X ∈ H)
    (r : I × T) (hr : r ∈ c.observed) :
    c.tildeX H X r = 0 :=
  Causalean.Panel.Weighted.WeightedSupport.residualize_self_of_mem c H hX r hr

/-- Applying the panel residual maker twice agrees with applying it once on
observed cells. -/
lemma residualize_idem_apply (c : Cells I T)
    (H : Submodule ℝ (V I T)) (X : V I T)
    (r : I × T) (hr : r ∈ c.observed) :
    c.residualize H (c.residualize H X) r = c.residualize H X r :=
  Causalean.Panel.Weighted.WeightedSupport.residualize_idem_apply c H X r hr

/-- The chosen panel projection of an array lies in the nuisance subspace. -/
lemma proj_mem (c : Cells I T) (H : Submodule ℝ (V I T)) (X : V I T) :
    c.proj H X ∈ H :=
  Causalean.Panel.Weighted.WeightedSupport.proj_mem c H X

/-- The projection residual is orthogonal to every nuisance-space array under
the panel weighted inner product. -/
lemma proj_orthogonal (c : Cells I T) (H : Submodule ℝ (V I T))
    (X : V I T) {h : V I T} (hH : h ∈ H) :
    c.ip (X - c.proj H X) h = 0 :=
  Causalean.Panel.Weighted.WeightedSupport.proj_orthogonal c H X hH

/-- Projecting a nuisance-space array returns the same values on observed
cells. -/
lemma proj_apply_of_mem (c : Cells I T) (H : Submodule ℝ (V I T))
    {Y : V I T} (hY : Y ∈ H) (r : I × T) (hr : r ∈ c.observed) :
    c.proj H Y r = Y r :=
  Causalean.Panel.Weighted.WeightedSupport.proj_apply_of_mem c H hY r hr

/-- Any nuisance-space candidate with the projection orthogonality condition
matches the chosen projection on observed cells. -/
lemma proj_apply_eq_of_mem_orthogonal (c : Cells I T)
    (H : Submodule ℝ (V I T))
    (X : V I T) {Y : V I T} (hY : Y ∈ H)
    (horth : ∀ h ∈ H, c.ip (X - Y) h = 0)
    (r : I × T) (hr : r ∈ c.observed) :
    c.proj H X r = Y r :=
  Causalean.Panel.Weighted.WeightedSupport.proj_apply_eq_of_mem_orthogonal c H X hY horth r hr

/-- Applying the chosen panel projection twice agrees with applying it once on
observed cells. -/
lemma proj_idem_apply (c : Cells I T) (H : Submodule ℝ (V I T))
    (X : V I T) (r : I × T) (hr : r ∈ c.observed) :
    c.proj H (c.proj H X) r = c.proj H X r :=
  Causalean.Panel.Weighted.WeightedSupport.proj_idem_apply c H X r hr

end Cells
end Panel
end Causalean
