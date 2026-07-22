/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Induced Subgraph Utilities for Identification

Thin layer on top of `Graph/Induce.lean`: defines ancestral closure and
a convenient abbreviation for producing the induced subgraph of a
`SWIGGraph`. After the April 2026 unification, the induced subgraph is
itself a `SWIGGraph`, so this file no longer needs a separate
`SubSWIGGraph` type.

## Main definitions

* `SWIGGraph.isAncestrallyClosed` — predicate stating every observed
  parent of a node in `G.observed` is itself in `G.observed`.
* `InducedFrom` — abbreviation for `G.induce R`, matching the `G_R`
  notation in the tex.

## References

* Basic Concepts.tex, Definition 2.11 (Induced subgraph), Proposition
  2.19 (ancestrally-closed hypothesis).
-/

import Causalean.Graph.Induce

/-! # Induced Subgraphs for Identification

This file provides graph-level utilities for restricting a SWIG to selected
observed nodes in graphical identification arguments. It defines
`SWIGGraph.isAncestrallyClosed`, the `InducedFrom` abbreviation for `G.induce R`,
and the descendant/non-descendant sets `properDescIn` and `nonDescIn` used in
Tian-style fixing arguments, together with their basic disjointness and coverage
lemmas. -/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SWIGGraph

variable (G : SWIGGraph N)

/-- A graph is ancestrally closed when every observed parent of an observed node is also observed.

This is the graph condition used when restricting identification arguments to an
induced observed subgraph. -/
def isAncestrallyClosed : Prop :=
  ∀ v ∈ G.observed, ∀ u ∈ G.dag.parents v,
    (∃ n : N, u = SWIGNode.random n) → u ∈ G.observed

/-- Ancestral closure of a finite SWIG graph is decidable. -/
instance decIsAncestrallyClosed : Decidable G.isAncestrallyClosed := by
  unfold isAncestrallyClosed
  infer_instance

end SWIGGraph

/-- The induced subgraph restricts a SWIG graph to the selected observed nodes.

This is the graph restriction used for identification subproblems. -/
abbrev InducedFrom (G : SWIGGraph N) (R : Finset (SWIGNode N)) : SWIGGraph N :=
  G.induce R

namespace SWIGGraph

variable (G : SWIGGraph N)

/-- This set contains the proper descendants of a node inside an induced SWIG subgraph.

The descendant relation used here is already irreflexive, so the node itself is
not included. -/
def properDescIn (R : Finset (SWIGNode N)) (v₀ : SWIGNode N) :
    Finset (SWIGNode N) :=
  (G.induce R).dag.descendants v₀

/-- This set contains the selected nodes that are neither the target node nor its proper descendants in the induced subgraph.

It is the non-descendant conditioning set used in Tian's Lemma 1 convention. -/
def nonDescIn (R : Finset (SWIGNode N)) (v₀ : SWIGNode N) :
    Finset (SWIGNode N) :=
  (R.erase v₀) \ (G.induce R).dag.descendants v₀

/-- A node is not a proper descendant of itself inside the induced subgraph. -/
lemma v₀_not_mem_properDescIn (G : SWIGGraph N) (R : Finset (SWIGNode N))
    (v₀ : SWIGNode N) : v₀ ∉ G.properDescIn R v₀ := by
  simp only [properDescIn, DAG.mem_descendants]
  exact DAG.isAncestor_irrefl _ _

/-- The target node is not in its induced non-descendant set because it is explicitly removed. -/
lemma v₀_not_mem_nonDescIn (G : SWIGGraph N) (R : Finset (SWIGNode N))
    (v₀ : SWIGNode N) : v₀ ∉ G.nonDescIn R v₀ := by
  simp [nonDescIn]

/-- Every proper descendant inside the induced subgraph lies in the selected set with the target node removed. -/
lemma properDescIn_subset_erase (G : SWIGGraph N) (R : Finset (SWIGNode N))
    (v₀ : SWIGNode N) :
    G.properDescIn R v₀ ⊆ R.erase v₀ := by
  intro w hw
  simp only [properDescIn, DAG.mem_descendants] at hw
  rw [Finset.mem_erase]
  exact ⟨fun heq => DAG.isAncestor_irrefl _ v₀ (heq ▸ hw),
         G.induce_isAncestor_mem_R R hw⟩

/-- Every induced non-descendant lies in the selected set with the target node removed. -/
lemma nonDescIn_subset_erase (G : SWIGGraph N) (R : Finset (SWIGNode N))
    (v₀ : SWIGNode N) :
    G.nonDescIn R v₀ ⊆ R.erase v₀ :=
  Finset.sdiff_subset

/-- Every induced non-descendant lies in the selected set. -/
lemma nonDescIn_subset (G : SWIGGraph N) (R : Finset (SWIGNode N))
    (v₀ : SWIGNode N) :
    G.nonDescIn R v₀ ⊆ R :=
  (G.nonDescIn_subset_erase R v₀).trans (R.erase_subset v₀)

/-- The proper-descendant set and non-descendant set are disjoint inside the selected nodes. -/
lemma properDescIn_disjoint_nonDescIn (G : SWIGGraph N)
    (R : Finset (SWIGNode N)) (v₀ : SWIGNode N) :
    Disjoint (G.properDescIn R v₀) (G.nonDescIn R v₀) := by
  simp only [properDescIn, nonDescIn]
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_sdiff] at hx'
  exact hx'.2 hx

/-- Proper descendants together with non-descendants cover the selected nodes except for the target node.

This is the coverage identity used in the graph split for Tian's Lemma 1. -/
lemma properDescIn_union_nonDescIn_eq_erase
    (G : SWIGGraph N) (R : Finset (SWIGNode N)) (v₀ : SWIGNode N)
    (hv₀ : v₀ ∈ R) :
    G.properDescIn R v₀ ∪ G.nonDescIn R v₀ = R.erase v₀ := by
  ext x
  simp only [Finset.mem_union, Finset.mem_erase, properDescIn, nonDescIn,
             DAG.mem_descendants, Finset.mem_sdiff]
  constructor
  · -- (⊆): both parts are subsets of R.erase v₀
    intro hx
    rcases hx with hx | ⟨⟨hne, hxR⟩, _⟩
    · exact ⟨fun heq => DAG.isAncestor_irrefl _ v₀ (heq ▸ hx),
             G.induce_isAncestor_mem_R R hx⟩
    · exact ⟨hne, hxR⟩
  · -- (⊇): x ∈ R.erase v₀ → in properDescIn or nonDescIn
    intro ⟨hne, hxR⟩
    by_cases hdesc : (G.induce R).dag.isAncestor v₀ x
    · left; exact hdesc
    · right
      exact ⟨⟨hne, hxR⟩, hdesc⟩

end SWIGGraph

end Causalean
