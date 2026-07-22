/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The identified interval of a linear target over a convex set

This is the payoff of the support-function spine.  When the feasible set `C` is
**convex** and the target is the **linear functional** `x ↦ ⟪d, x⟫`, the sharp
identified set of the target value is the closed interval

    [ -supportFn C (-d), supportFn C d ].

The lower endpoint `-supportFn C (-d)` is the infimum (worst case) and the upper
endpoint `supportFn C d` is the supremum (best case) of the functional over the
nuisance set `C`.  Sharpness — that *every* intermediate value is attained — is
exactly order-connectedness of the image, which holds because the linear image of
a convex set is convex (hence an interval) in `ℝ`.

This generalises the one-dimensional `IdentifiedInterval` engine of
`PartialID/Basic.lean`: `identifiedInterval_eq_image` shows the scalar engine's
identified set *is* this linear image, so concrete theorems may consume either
vocabulary.

## Main results

* `neg_supportFn_neg_le` — the lower endpoint bounds the functional from below.
* `linearImage_subset_Icc` — the identified set sits inside `[-h(-d), h(d)]`.
* `linearImage_ordConnected` — convexity makes the identified set order-connected.
* `linearImage_eq_Icc` — *sharp* interval, given the endpoints are attained.
* `linearImage_eq_Icc_of_isCompact` — sharp interval for a compact convex set
  (endpoints automatically attained; the workhorse for finite-dimensional sets).
* `width` / `width_nonneg` — the width `h(d) + h(-d) ≥ 0` of the identified set.
* `width_eq_zero_iff` — **point identification**: zero width iff the target is
  constant on `C`.
* `identifiedInterval_eq_image` — bridge to the scalar `IdentifiedInterval` engine.
-/

import Causalean.PO.ID.Partial.SupportFunction.Basic
import Causalean.PO.ID.Partial.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Order.Compact

/-! # Support-Function Identified Intervals

This file characterizes the sharp interval of values attained by a linear target over a
convex feasible set. It connects the support-function description of the lower and upper
endpoints to the scalar identified-interval machinery used elsewhere in the
partial-identification library. -/

open scoped RealInnerProductSpace

namespace Causalean
namespace PartialID

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Lower endpoint bound.**  If `⟪-d, ·⟫` is bounded above on `C`, then the lower
endpoint `-supportFn C (-d)` is a lower bound for the functional `⟪d, ·⟫`. -/
theorem neg_supportFn_neg_le {C : Set E} {d : E} {x : E} (hx : x ∈ C)
    (hbdd' : BddAbove ((fun x => ⟪-d, x⟫) '' C)) :
    -supportFn C (-d) ≤ ⟪d, x⟫ := by
  have h := le_supportFn (d := -d) hx hbdd'
  rw [inner_neg_left] at h
  linarith

/-- **Outer bound.**  The identified set of the linear target lies inside the
support interval `[-supportFn C (-d), supportFn C d]`. -/
theorem linearImage_subset_Icc {C : Set E} {d : E}
    (hbdd : BddAbove ((fun x => ⟪d, x⟫) '' C))
    (hbdd' : BddAbove ((fun x => ⟪-d, x⟫) '' C)) :
    (fun x => ⟪d, x⟫) '' C ⊆ Set.Icc (-supportFn C (-d)) (supportFn C d) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨neg_supportFn_neg_le hx hbdd', le_supportFn hx hbdd⟩

/-- **Order-connectedness.**  The linear image of a convex set is convex in `ℝ`,
hence order-connected: the identified set has "no gaps". -/
theorem linearImage_ordConnected {C : Set E} {d : E} (hC : Convex ℝ C) :
    ((fun x => ⟪d, x⟫) '' C).OrdConnected := by
  have hlin : IsLinearMap ℝ (fun x => ⟪d, x⟫) :=
    { map_add := fun x y => inner_add_right d x y
      map_smul := fun c x => real_inner_smul_right d x c }
  exact (hC.is_linear_image hlin).ordConnected

/-- **Sharp identified interval (attainment form).**  For a convex `C` whose
target endpoints are both attained, the identified set is *exactly* the support
interval. -/
theorem linearImage_eq_Icc {C : Set E} {d : E} (hC : Convex ℝ C)
    (hbdd : BddAbove ((fun x => ⟪d, x⟫) '' C))
    (hbdd' : BddAbove ((fun x => ⟪-d, x⟫) '' C))
    (hUmem : supportFn C d ∈ (fun x => ⟪d, x⟫) '' C)
    (hLmem : -supportFn C (-d) ∈ (fun x => ⟪d, x⟫) '' C) :
    (fun x => ⟪d, x⟫) '' C = Set.Icc (-supportFn C (-d)) (supportFn C d) :=
  Set.Subset.antisymm (linearImage_subset_Icc hbdd hbdd')
    ((linearImage_ordConnected hC).out hLmem hUmem)

/-- **Sharp identified interval (compact convex form).**  The workhorse: a
nonempty compact convex feasible set gives the sharp interval outright, since a
continuous functional attains its sup and inf on a compact set and is bounded. -/
theorem linearImage_eq_Icc_of_isCompact {C : Set E} {d : E}
    (hcomp : IsCompact C) (hC : Convex ℝ C) (hne : C.Nonempty) :
    (fun x => ⟪d, x⟫) '' C = Set.Icc (-supportFn C (-d)) (supportFn C d) := by
  have hcont : Continuous (fun x => ⟪d, x⟫) :=
    continuous_inner.comp (continuous_const.prodMk continuous_id)
  have hcont' : Continuous (fun x => ⟪-d, x⟫) :=
    continuous_inner.comp (continuous_const.prodMk continuous_id)
  have hbdd : BddAbove ((fun x => ⟪d, x⟫) '' C) := hcomp.bddAbove_image hcont.continuousOn
  have hbdd' : BddAbove ((fun x => ⟪-d, x⟫) '' C) := hcomp.bddAbove_image hcont'.continuousOn
  obtain ⟨xU, hxU, hU⟩ := hcomp.exists_sSup_image_eq hne hcont.continuousOn
  obtain ⟨xL, hxL, hL⟩ := hcomp.exists_sSup_image_eq hne hcont'.continuousOn
  refine linearImage_eq_Icc hC hbdd hbdd' ?_ ?_
  · exact ⟨xU, hxU, hU.symm⟩
  · refine ⟨xL, hxL, ?_⟩
    have hsup : supportFn C (-d) = ⟪-d, xL⟫ := hL
    change ⟪d, xL⟫ = -supportFn C (-d)
    rw [hsup, inner_neg_left]; ring

/-- The **width** of the identified set: `supportFn C d + supportFn C (-d)`, i.e.
the upper endpoint minus the lower endpoint. -/
noncomputable def width (C : Set E) (d : E) : ℝ := supportFn C d + supportFn C (-d)

/-- The identified width is nonnegative. -/
theorem width_nonneg {C : Set E} {d : E} (hne : C.Nonempty)
    (hbdd : BddAbove ((fun x => ⟪d, x⟫) '' C))
    (hbdd' : BddAbove ((fun x => ⟪-d, x⟫) '' C)) :
    0 ≤ width C d := by
  obtain ⟨x, hx⟩ := hne
  have h1 := le_supportFn hx hbdd
  have h2 := le_supportFn (d := -d) hx hbdd'
  rw [inner_neg_left] at h2
  simp only [width]; linarith

/-- **Point identification.**  The identified set collapses to a point (zero
width) iff the target functional is constant on `C` (equal to its support value). -/
theorem width_eq_zero_iff {C : Set E} {d : E} (hne : C.Nonempty)
    (hbdd : BddAbove ((fun x => ⟪d, x⟫) '' C))
    (hbdd' : BddAbove ((fun x => ⟪-d, x⟫) '' C)) :
    width C d = 0 ↔ ∀ x ∈ C, ⟪d, x⟫ = supportFn C d := by
  constructor
  · intro hw x hx
    have hle : ⟪d, x⟫ ≤ supportFn C d := le_supportFn hx hbdd
    have hge : -supportFn C (-d) ≤ ⟪d, x⟫ := neg_supportFn_neg_le hx hbdd'
    have : -supportFn C (-d) = supportFn C d := by simp only [width] at hw; linarith
    linarith
  · intro hconst
    -- supportFn C (-d) = -supportFn C d, since ⟪-d,x⟫ = -(supportFn C d) on C
    have hneg : supportFn C (-d) = -supportFn C d := by
      apply le_antisymm
      · refine supportFn_le hne ?_
        intro x hx
        rw [inner_neg_left, hconst x hx]
      · obtain ⟨x, hx⟩ := hne
        have := le_supportFn (d := -d) hx hbdd'
        rw [inner_neg_left, hconst x hx] at this
        linarith
    simp only [width, hneg]; ring

/-- **Bridge to the scalar engine.**  The scalar `IdentifiedInterval` of an
objective over the membership predicate `(· ∈ C)` is exactly the set-image of the
objective.  Specialised to `obj = ⟪d, ·⟫`, this identifies the scalar engine's
output with the linear image studied here. -/
theorem identifiedInterval_eq_image {α : Type*} (obj : α → ℝ) (C : Set α) :
    IdentifiedInterval obj (· ∈ C) = obj '' C := by
  ext y
  simp only [IdentifiedInterval, Set.mem_range, Set.mem_image, Subtype.exists]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

end PartialID
end Causalean
