/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Lee bounds: principal-stratum events

The latent (counterfactual) events `alwaysSelected = {Sel(0)=true, Sel(1)=true}`
and `helpedSelected = {Sel(0)=false, Sel(1)=true}`.  Under monotone sample
selection, these two events partition the latent selected set
`{Sel(1)=true}`, and the "selected under control" event `{Sel(0)=true}`
collapses (a.s.) to `alwaysSelected` because `{Sel(0)=true, Sel(1)=false}`
has measure zero.

This file proves the two key event-equality lemmas via leaf-level
measure-theoretic rewrites.
-/

import Causalean.PO.ID.Partial.Lee.Setup

/-! # Lee Principal Strata

This file defines the latent principal strata for Lee sample-selection bounds.
It proves measurability and the monotone-selection event identities that relate
the always-selected and treatment-induced-selected strata to observed and
counterfactual selected sets. -/

namespace Causalean
namespace PO

open MeasureTheory

namespace POLeeSystem

variable {P : POSystem} (S : POLeeSystem P)

/-- The always-selected stratum contains units who would be selected under both
control and treatment.

Equivalently, it is the counterfactual event `Sel(0) = true ∧ Sel(1) = true`. -/
def alwaysSelected : Set P.Ω :=
  {ω | S.SelOfA false ω = true ∧ S.SelOfA true ω = true}

/-- The helped-selected stratum contains units selected under treatment but not
under control.

Equivalently, it is the counterfactual event `Sel(0) = false ∧ Sel(1) = true`. -/
def helpedSelected : Set P.Ω :=
  {ω | S.SelOfA false ω = false ∧ S.SelOfA true ω = true}

/-- The harmed-selected stratum contains units selected under control but not
under treatment.

Under monotone sample selection, this stratum has probability zero. -/
def harmedSelected : Set P.Ω :=
  {ω | S.SelOfA false ω = true ∧ S.SelOfA true ω = false}

/-! ### Measurability -/

/-- The always-selected stratum is measurable. -/
lemma measurableSet_alwaysSelected : MeasurableSet S.alwaysSelected := by
  refine MeasurableSet.inter ?_ ?_
  · exact (S.measurable_SelOfA false) (measurableSet_singleton true)
  · exact (S.measurable_SelOfA true) (measurableSet_singleton true)

/-- The helped-selected stratum is measurable. -/
lemma measurableSet_helpedSelected : MeasurableSet S.helpedSelected := by
  refine MeasurableSet.inter ?_ ?_
  · exact (S.measurable_SelOfA false) (measurableSet_singleton false)
  · exact (S.measurable_SelOfA true) (measurableSet_singleton true)

/-- The harmed-selected stratum is measurable. -/
lemma measurableSet_harmedSelected : MeasurableSet S.harmedSelected := by
  refine MeasurableSet.inter ?_ ?_
  · exact (S.measurable_SelOfA false) (measurableSet_singleton true)
  · exact (S.measurable_SelOfA true) (measurableSet_singleton false)

/-- The latent selected-under-treatment set contains units who would be selected
if treated.

This is the set `{Sel(1) = true}` as a measurable set. -/
def selOfATrueSet : Set P.Ω := {ω | S.SelOfA true ω = true}

/-- The selected-under-treatment latent set is measurable. -/
lemma measurableSet_selOfATrueSet : MeasurableSet S.selOfATrueSet :=
  (S.measurable_SelOfA true) (measurableSet_singleton true)

/-- The latent selected-under-control set contains units who would be selected
if untreated.

This is the set `{Sel(0) = true}` as a measurable set. -/
def selOfAFalseSet : Set P.Ω := {ω | S.SelOfA false ω = true}

/-- The selected-under-control latent set is measurable. -/
lemma measurableSet_selOfAFalseSet : MeasurableSet S.selOfAFalseSet :=
  (S.measurable_SelOfA false) (measurableSet_singleton true)

/-- `selOfATrueSet = alwaysSelected ∪ helpedSelected` as a pure set equality
(no a.s. needed -- the two RHS sets are disjoint and cover the LHS by case
analysis on `SelOfA false ω : Bool`). -/
lemma selOfATrueSet_eq_alwaysSelected_union_helpedSelected :
    S.selOfATrueSet = S.alwaysSelected ∪ S.helpedSelected := by
  ext ω
  simp only [selOfATrueSet, alwaysSelected, helpedSelected, Set.mem_setOf_eq,
    Set.mem_union]
  constructor
  · intro h
    rcases (S.SelOfA false ω).eq_false_or_eq_true with h0 | h0
    · exact Or.inl ⟨h0, h⟩
    · exact Or.inr ⟨h0, h⟩
  · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h

/-- `alwaysSelected` and `helpedSelected` are disjoint. -/
lemma disjoint_alwaysSelected_helpedSelected :
    Disjoint S.alwaysSelected S.helpedSelected := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext ω
  refine ⟨?_, fun h => absurd h (Set.notMem_empty _)⟩
  rintro ⟨⟨h1, _⟩, ⟨h2, _⟩⟩
  exact absurd (h1.symm.trans h2) (by decide)

/-! ### Monotone-selection identities

These are the two key a.s. identities the main Lee-bounds proof consumes.
Both are leaf-level measure-theoretic rewrites: monotone selection states
`SelOfA false ω ≤ SelOfA true ω` a.s., which forces `harmedSelected` to be
null, and the two displayed equalities follow.

Note: `MonotoneSelection` lives in `Assumptions.lean`; we take the raw a.s.
predicate `(∀ᵐ ω, S.SelOfA false ω ≤ S.SelOfA true ω)` as a hypothesis here
to keep this file dependency-free of `Assumptions.lean`. -/

/-- Under monotone sample selection, the harmed stratum has measure zero. -/
lemma harmedSelected_ae_empty
    (hMono : ∀ᵐ ω ∂P.μ, S.SelOfA false ω ≤ S.SelOfA true ω) :
    P.μ S.harmedSelected = 0 := by
  -- Monotonicity says that on a co-null set, SelOfA false ω ≤ SelOfA true ω
  -- (with ≤ on Bool meaning false ≤ true and false ≤ false and true ≤ true,
  -- but NOT true ≤ false). On harmedSelected, SelOfA false = true and
  -- SelOfA true = false, contradicting the inequality. So
  -- harmedSelected ⊆ {ω | ¬(SelOfA false ω ≤ SelOfA true ω)} which is null.
  -- Use `measure_mono_null` against the complement of the a.s. set, plus
  -- `Bool.not_le` (or a direct case split) to discharge the implication.
  have hNull : P.μ {ω | ¬ S.SelOfA false ω ≤ S.SelOfA true ω} = 0 := by
    rwa [ae_iff] at hMono
  exact MeasureTheory.measure_mono_null (by
    intro ω hω
    rcases hω with ⟨h0, h1⟩
    simp [h0, h1]) hNull

/-- Under monotone sample selection, `{Sel(0)=true} =ᵐ alwaysSelected`. -/
lemma selOfAFalseSet_ae_eq_alwaysSelected
    (hMono : ∀ᵐ ω ∂P.μ, S.SelOfA false ω ≤ S.SelOfA true ω) :
    S.selOfAFalseSet =ᵐ[P.μ] S.alwaysSelected := by
  -- The target equality is `{ω | SelOfA false ω = true} =ᵐ alwaysSelected`.
  --   alwaysSelected ⊆ {Sel(0)=true} is purely set-level (the first
  --     conjunct of alwaysSelected is exactly Sel(0)=true).
  --   For the reverse direction, on the co-null set where Sel(0) ≤ Sel(1),
  --     Sel(0)=true ⇒ Sel(1)=true (since true ≤ Sel(1) forces Sel(1)=true on Bool),
  --     so {Sel(0)=true} ⊆ alwaysSelected on that co-null set.
  -- Proof recipe: use `Filter.EventuallyEq` (i.e. `=ᵐ[μ]`) in the form
  -- `Set.eventuallyEq_iff_indicator` or just the symmetric-difference null
  -- characterisation, then bound the offending sym-diff by a subset of the
  -- complement of the a.s. set from `hMono`.
  filter_upwards [hMono] with ω hω
  apply propext
  simp only [selOfAFalseSet, alwaysSelected]
  constructor
  · intro hsel
    exact ⟨hsel, by
      have hsel' : S.SelOfA false ω = true := hsel
      cases htrue : S.SelOfA true ω
      · have hle : true ≤ false := by
          simpa [hsel', htrue] using hω
        exact False.elim ((by decide : ¬ (true ≤ false)) hle)
      · rfl⟩
  · intro h
    exact h.1


end POLeeSystem

end PO
end Causalean
