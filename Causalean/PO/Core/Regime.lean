/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Intervention Regimes for the Bare Potential Outcome Framework

Represents `r = (X, x)` from Basic Concepts.tex, def:po-system.  A regime
names a finite target set of variables together with an assignment of
values on that set.  No graph and no SCM structure is assumed.
-/

import Causalean.Mathlib.MeasureTheory.FinsetValues

/-! # Intervention Regimes

This file defines finite intervention regimes for the potential-outcome
framework. A regime records the variables fixed by an intervention and the
assigned value for each fixed variable, without assuming a graph or structural
causal model. -/

namespace Causalean
namespace PO

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]

/-- An intervention regime specifies a finite set of targeted variables and an
assigned value in the corresponding value space for each targeted variable.

Implementation note: this is the code object `Regime`, corresponding to
`r = (target, assign)` in def:po-system. -/
structure Regime (V : Type*) [DecidableEq V] [Fintype V]
    (X : V → Type*) [∀ v, MeasurableSpace (X v)] where
  target : Finset V
  assign : ∀ v : V, v ∈ target → X v

namespace Regime

/-- The empty intervention regime fixes no variables and therefore has no
assignments.

Implementation note: this is the empty regime `r_∅` from def:po-system and
def:po-consistency. -/
def empty : Regime V X where
  target := ∅
  assign := fun v hv => (Finset.notMem_empty v hv).elim

/-- Two intervention regimes are disjoint exactly when their target sets have no
variable in common. -/
def Disjoint (r₁ r₂ : Regime V X) : Prop := _root_.Disjoint r₁.target r₂.target

/-- The disjoint union of two compatible intervention regimes targets the union
of their target sets and uses the assignment from the unique component regime
that targets each variable.

Implementation note: this is the disjoint union `r₁ ⊔ r₂` from
def:po-consistency and def:po-from-scm. -/
noncomputable def sqcup (r₁ r₂ : Regime V X) (_h : r₁.Disjoint r₂) :
    Regime V X where
  target := r₁.target ∪ r₂.target
  assign := fun v hv =>
    if h1 : v ∈ r₁.target then r₁.assign v h1
    else r₂.assign v (by
      rcases Finset.mem_union.mp hv with h₁ | h₂
      · exact (h1 h₁).elim
      · exact h₂)

/-- The empty intervention regime has no target variables. -/
@[simp] lemma empty_target : (empty : Regime V X).target = ∅ := rfl

/-- The empty intervention regime is disjoint from every regime on its right. -/
lemma empty_disjoint_right (r : Regime V X) : (empty : Regime V X).Disjoint r := by
  simp [Disjoint, empty]

/-- Every regime is disjoint from the empty intervention regime on its right. -/
lemma empty_disjoint_left (r : Regime V X) : r.Disjoint (empty : Regime V X) := by
  simp [Disjoint, empty]

/-- The target of the disjoint union of two regimes is the union of their target sets. -/
@[simp] lemma sqcup_target (r₁ r₂ : Regime V X) (h : r₁.Disjoint r₂) :
    (r₁.sqcup r₂ h).target = r₁.target ∪ r₂.target := rfl

/-- `sqcup` agrees with `r₁` whenever `v ∈ r₁.target`. -/
lemma sqcup_assign_pos (r₁ r₂ : Regime V X) (h : r₁.Disjoint r₂)
    (v : V) (hv : v ∈ (r₁.sqcup r₂ h).target) (h1 : v ∈ r₁.target) :
    (r₁.sqcup r₂ h).assign v hv = r₁.assign v h1 := by
  simp [Regime.sqcup, h1]

/-- `sqcup` agrees with `r₂` whenever `v ∉ r₁.target` (and hence `v ∈ r₂.target`). -/
lemma sqcup_assign_neg (r₁ r₂ : Regime V X) (h : r₁.Disjoint r₂)
    (v : V) (hv : v ∈ (r₁.sqcup r₂ h).target)
    (h1 : v ∉ r₁.target) (h2 : v ∈ r₂.target) :
    (r₁.sqcup r₂ h).assign v hv = r₂.assign v h2 := by
  simp [Regime.sqcup, h1]

/-- Extensionality for `Regime`: equal targets and pointwise-equal assignments. -/
theorem ext {r₁ r₂ : Regime V X}
    (htgt : r₁.target = r₂.target)
    (hassign : ∀ v (h₁ : v ∈ r₁.target) (h₂ : v ∈ r₂.target),
        r₁.assign v h₁ = r₂.assign v h₂) :
    r₁ = r₂ := by
  obtain ⟨t₁, a₁⟩ := r₁
  obtain ⟨t₂, a₂⟩ := r₂
  subst htgt
  congr 1
  funext v hv
  exact hassign v hv hv

/-- A singleton intervention regime fixes exactly one variable to the supplied
value. -/
def single (v : V) (x : X v) : Regime V X where
  target := {v}
  assign := fun _ hw => (Finset.mem_singleton.mp hw).symm ▸ x

/-- The singleton intervention regime targets exactly the one variable it fixes. -/
@[simp] theorem single_target (v : V) (x : X v) :
    (single v x : Regime V X).target = {v} := rfl

/-- Evaluating the singleton intervention assignment at its target returns the supplied value. -/
theorem single_assign_self (v : V) (x : X v) :
    (single v x : Regime V X).assign v (Finset.mem_singleton_self _) = x := rfl

/-- Singleton intervention regimes on two distinct variables are disjoint. -/
theorem single_disjoint_single {v w : V} (hvw : v ≠ w) (x : X v) (y : X w) :
    (single v x : Regime V X).Disjoint (single w y) := by
  simp [Disjoint, single, hvw]

/-- A singleton intervention regime is disjoint from any regime that does not
target its variable. -/
theorem single_disjoint_of_not_mem {v : V} (x : X v) (r : Regime V X)
    (h : v ∉ r.target) : (single v x : Regime V X).Disjoint r := by
  simp [Disjoint, single, Finset.disjoint_singleton_left, h]

/-- Any regime that does not target a variable is disjoint from the singleton
intervention on that variable. -/
theorem disjoint_single_of_not_mem {v : V} (x : X v) (r : Regime V X)
    (h : v ∉ r.target) : r.Disjoint (single v x : Regime V X) := by
  simp [Disjoint, single, Finset.disjoint_singleton_right, h]

/-! ### Multi-stage regimes from a list of assignments -/

/-- Lookup in a list of variable-value assignments returns the listed value for
a variable that appears among the listed labels.

Implementation note: lookup is defined recursively so the list need not have
duplicate-free labels for definitional well-formedness; uniqueness is exposed
via the lemmas below. -/
def listLookup : (l : List ((v : V) × X v)) → (v : V) →
    v ∈ l.map Sigma.fst → X v
  | [], v, hv => by simp at hv
  | ⟨w, x⟩ :: rest, v, hv =>
      if h : v = w then h ▸ x
      else
        listLookup rest v (by
          rcases (List.mem_cons.mp hv) with hv | hv
          · exact (h hv).elim
          · exact hv)

/-- A duplicate-free list of variable-value assignments determines the
intervention regime that targets exactly the listed variables and assigns each
target its listed value. -/
def ofList (l : List ((v : V) × X v)) (_h : (l.map Sigma.fst).Nodup) :
    Regime V X where
  target := (l.map Sigma.fst).toFinset
  assign := fun v hv => listLookup l v (List.mem_toFinset.mp hv)

/-- The target of a regime built from a duplicate-free list is the finite set
of listed variables. -/
@[simp] theorem ofList_target (l : List ((v : V) × X v))
    (h : (l.map Sigma.fst).Nodup) :
    (ofList l h).target = (l.map Sigma.fst).toFinset := rfl

/-- Building a regime from the empty list gives the empty intervention regime. -/
@[simp] theorem ofList_nil (h : ([] : List ((v : V) × X v)).map Sigma.fst |>.Nodup) :
    (ofList [] h : Regime V X) = empty := by
  congr 1

/-- The target of a regime built from a nonempty list inserts the head variable
into the target from the tail. -/
@[simp] theorem ofList_cons_target {v : V} {x : X v}
    {rest : List ((v : V) × X v)}
    (h : ((⟨v, x⟩ :: rest : List ((v : V) × X v)).map Sigma.fst).Nodup) :
    (ofList (⟨v, x⟩ :: rest) h).target =
      insert v (rest.map Sigma.fst).toFinset := by
  simp [ofList]

omit [Fintype V] [(v : V) → MeasurableSpace (X v)] in
/-- Looking up the head variable of a dependent assignment list returns the head value. -/
theorem listLookup_cons_self {v : V} {x : X v}
    {rest : List ((v : V) × X v)}
    (hv : v ∈ ((⟨v, x⟩ :: rest : List ((v : V) × X v)).map Sigma.fst)) :
    listLookup (⟨v, x⟩ :: rest) v hv = x := by
  simp [listLookup]

omit [Fintype V] [(v : V) → MeasurableSpace (X v)] in
/-- Looking up a different variable skips the head of a dependent assignment
list and continues in the tail. -/
theorem listLookup_cons_of_ne {v w : V} {x : X w}
    {rest : List ((v : V) × X v)} (hvw : v ≠ w)
    (hv : v ∈ ((⟨w, x⟩ :: rest : List ((v : V) × X v)).map Sigma.fst))
    (hv' : v ∈ rest.map Sigma.fst) :
    listLookup (⟨w, x⟩ :: rest) v hv = listLookup rest v hv' := by
  simp [listLookup, hvw]

end Regime

end PO
end Causalean
