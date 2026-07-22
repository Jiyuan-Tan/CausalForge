/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Induced Subgraph of a SWIG Graph

Defines `SWIGGraph.induce`, the graph-level restriction to an observed
subset `R`. The induced graph is itself a `SWIGGraph`, exploiting the
weakened `dag_edges_classified` invariant.

## Main definitions

* `SWIGGraph.induce G R` — restrict `G.observed` to `R ∩ observed`,
  drop any `fixed` node whose `iotaMap` image no longer lies in the
  restricted observed set, keep exactly the latent roots that point into the
  restricted observed set, and filter edges to those with both endpoints in the
  new active set.

## References

* Basic Concepts.tex, Definition 2.11 (Induced subgraph)
-/

import Causalean.Graph.SWIG

/-! # Induced SWIG Subgraphs

This file defines graph-level restriction of a Single World Intervention Graph
to an observed subset. The construction keeps the relevant observed nodes,
retains only fixed nodes whose random counterparts remain observed, retains only
latent roots that feed those observed nodes, and filters edges to the resulting
active vertex set.

The auxiliary `inducedEdge` and `inducedDag` restrict the ambient DAG while
preserving its topological order. The main constructor `SWIGGraph.induce` builds
the restricted SWIG and proves all structural invariants; `inducedDag_edge_iff`
and the parent/child subset lemmas expose the relationship with the ambient
graph. The theorem `induce_isAncestor_mem_R` shows that every nontrivial
descendant in an induced subgraph lies in the retained observed support `R`. -/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SWIGGraph

variable (G : SWIGGraph N)

-- ============================================================
-- Induced edge relation and restricted DAG
-- ============================================================

/-- The edge relation of `G.dag` restricted to a given `active`
    vertex set: keep an edge iff both endpoints are in `active`. -/
def inducedEdge (active : Finset (SWIGNode N)) (u v : SWIGNode N) : Prop :=
  G.dag.edge u v ∧ u ∈ active ∧ v ∈ active

/-- Whether an edge remains after restricting to an active vertex set is decidable. -/
instance inducedEdge_decidable (active : Finset (SWIGNode N)) :
    DecidableRel (G.inducedEdge active) := by
  intro u v
  unfold inducedEdge
  infer_instance

/-- The DAG obtained by filtering `G.dag`'s edges to those with both
    endpoints in `active`. Acyclicity follows from the parent graph via the
    parent's topological order (every restricted edge is an original edge). -/
def inducedDag (active : Finset (SWIGNode N)) : DAG (SWIGNode N) where
  edge := G.inducedEdge active
  decEdge := G.inducedEdge_decidable active
  acyclic := DAG.acyclic_of_topoOrder (τ := G.dag.topoOrder)
    (fun u v h => G.dag.topoOrder_lt u v h.1)

/-- An edge in the restricted DAG is exactly an original edge whose endpoints are active. -/
lemma inducedDag_edge_iff (active : Finset (SWIGNode N)) (u v : SWIGNode N) :
    (G.inducedDag active).edge u v ↔
      G.dag.edge u v ∧ u ∈ active ∧ v ∈ active := Iff.rfl

/-- Every parent in the restricted DAG is also a parent in the original graph. -/
lemma inducedDag_parents_subset (active : Finset (SWIGNode N)) (v : SWIGNode N) :
    (G.inducedDag active).parents v ⊆ G.dag.parents v := by
  intro u hu
  have h := (G.inducedDag active).mem_parents.mp hu
  exact G.dag.mem_parents.mpr h.1

/-- Every child in the restricted DAG is also a child in the original graph. -/
lemma inducedDag_children_subset (active : Finset (SWIGNode N)) (u : SWIGNode N) :
    (G.inducedDag active).children u ⊆ G.dag.children u := by
  intro v hv
  have h := (G.inducedDag active).mem_children.mp hv
  exact G.dag.mem_children.mpr h.1

/-- If `(G.inducedDag active).isAncestor u v`, then `v ∈ active`. -/
lemma inducedDag_isAncestor_mem_active (active : Finset (SWIGNode N)) {u v : SWIGNode N}
    (h : (G.inducedDag active).isAncestor u v) : v ∈ active := by
  induction h with
  | edge he => exact ((G.inducedDag_edge_iff active _ _).mp he).2.2
  | trans _ he _ => exact ((G.inducedDag_edge_iff active _ _).mp he).2.2

/-- If `isAncestor u v`, then `v` has at least one parent (the last edge on the path). -/
lemma inducedDag_isAncestor_has_parent (active : Finset (SWIGNode N)) {u v : SWIGNode N}
    (h : (G.inducedDag active).isAncestor u v) :
    (G.inducedDag active).parents v ≠ ∅ := by
  intro hempty
  have hmem : ∀ w, w ∉ (G.inducedDag active).parents v :=
    fun w => (Finset.eq_empty_iff_forall_notMem.mp hempty) w
  induction h with
  | edge he => exact hmem u ((G.inducedDag active).mem_parents.mpr he)
  | trans _ he _ => exact hmem _ ((G.inducedDag active).mem_parents.mpr he)

-- ============================================================
-- The induce operation
-- ============================================================

/-- **Induce a sub-SWIG on a subset `R`.** The new `observed` is
    `R ∩ observed`; the new `fixed` drops any fixed node whose
    `iotaMap` image was removed; the new `unobserved` keeps exactly the
    original latent roots with an edge into the retained observed set; the DAG
    keeps only edges with both endpoints in the new active set.

    This operation lands back in `SWIGGraph` because the new
    `dag_edges_classified` invariant is preserved under edge removal. -/
def induce (R : Finset (SWIGNode N)) : SWIGGraph N :=
  let newObserved : Finset (SWIGNode N) := R ∩ G.observed
  let newFixed : Finset (SWIGNode N) := G.fixed.filter (fun s => iotaMap s ∈ newObserved)
  let newUnobserved : Finset (SWIGNode N) :=
    G.unobserved.filter (fun u => ∃ v ∈ newObserved, G.dag.edge u v)
  let newActive : Finset (SWIGNode N) := newFixed ∪ newObserved ∪ newUnobserved
  { dag := G.inducedDag newActive
    fixed := newFixed
    observed := newObserved
    unobserved := newUnobserved
    fixed_is_fixed := by
      intro s hs
      exact G.fixed_is_fixed s ((Finset.mem_filter.mp hs).1)
    observed_is_random := by
      intro v hv
      exact G.observed_is_random v (Finset.mem_inter.mp hv).2
    unobserved_is_random := by
      intro u hu
      exact G.unobserved_is_random u (Finset.mem_filter.mp hu).1
    obs_unobs_disjoint := by
      rw [Finset.disjoint_left]
      intro u huObs huUnobs
      exact (Finset.disjoint_left.mp G.obs_unobs_disjoint
        (Finset.inter_subset_right huObs) (Finset.mem_filter.mp huUnobs).1).elim
    dag_edges_classified := by
      intro u v huv
      -- Unfold the induced edge: both endpoints lie in `newActive`.
      have hu : u ∈ newActive := huv.2.1
      have hv : v ∈ newActive := huv.2.2
      -- `newActive = newFixed ∪ newObserved ∪ newUnobserved`, which equals
      -- `newFixed ∪ newObserved ∪ unobserved` in the induced graph.
      refine ⟨?_, ?_⟩
      · -- Rearrange: newFixed ∪ newObserved ∪ unobserved = (newFixed ∪ newObserved) ∪ unobserved
        simpa [newActive] using hu
      · simpa [newActive] using hv
    fixed_image_in_observed := by
      intro s hs
      exact (Finset.mem_filter.mp hs).2
    fixed_are_roots := by
      intro s hs
      -- parents in the induced DAG ⊆ parents in G.dag = ∅
      have hsFixed : s ∈ G.fixed := (Finset.mem_filter.mp hs).1
      have hGroot : G.dag.parents s = ∅ := G.fixed_are_roots s hsFixed
      have hsub := G.inducedDag_parents_subset newActive s
      rw [hGroot] at hsub
      exact Finset.subset_empty.mp hsub
    unobs_are_roots := by
      intro u hu
      have hGroot : G.dag.parents u = ∅ := G.unobs_are_roots u (Finset.mem_filter.mp hu).1
      have hsub := G.inducedDag_parents_subset newActive u
      rw [hGroot] at hsub
      exact Finset.subset_empty.mp hsub
    fixed_outside_fixed_isolated := by
      intro n hnNotFixed
      -- Case split: is `.fixed n` in the old `G.fixed`?
      by_cases horig : SWIGNode.fixed n ∈ G.fixed
      · -- It is in the old fixed set, but dropped by the filter. Show its
        -- edges in the induced DAG are empty because `.fixed n ∉ newActive`.
        have hnotActive : SWIGNode.fixed n ∉ newActive := by
          intro hin
          rcases Finset.mem_union.mp hin with hin | hin
          · rcases Finset.mem_union.mp hin with hin | hin
            · exact hnNotFixed hin
            · -- .fixed n ∈ newObserved ⊆ G.observed, but observed nodes
              -- are `.random _`, contradicting .fixed form.
              have hinObs : SWIGNode.fixed n ∈ G.observed :=
                (Finset.mem_inter.mp hin).2
              obtain ⟨_, hm⟩ := G.observed_is_random _ hinObs
              cases hm
          · -- .fixed n ∈ G.unobserved — contradiction (unobserved are random)
            obtain ⟨_, hm⟩ := G.unobserved_is_random _ (Finset.mem_filter.mp hin).1
            cases hm
        refine ⟨?_, ?_⟩
        · -- No parents: any parent would come with an edge, requiring
          -- `.fixed n ∈ newActive`.
          rw [Finset.eq_empty_iff_forall_notMem]
          intro w hw
          have hedge := ((G.inducedDag newActive).mem_parents.mp hw)
          exact hnotActive hedge.2.2
        · rw [Finset.eq_empty_iff_forall_notMem]
          intro w hw
          have hedge := ((G.inducedDag newActive).mem_children.mp hw)
          exact hnotActive hedge.2.1
      · -- `.fixed n` was never in G.fixed: use G.fixed_outside_fixed_isolated.
        have hGiso := G.fixed_outside_fixed_isolated n horig
        refine ⟨?_, ?_⟩
        · have hsub := G.inducedDag_parents_subset newActive (SWIGNode.fixed n)
          rw [hGiso.1] at hsub
          exact Finset.subset_empty.mp hsub
        · have hsub := G.inducedDag_children_subset newActive (SWIGNode.fixed n)
          rw [hGiso.2] at hsub
          exact Finset.subset_empty.mp hsub
    all_children_in_observed := by
      -- hu : u ∈ newUnobserved ∪ newFixed ∪ newObserved (the struct invariant's
      -- old-to-new field substitution), which parses as
      -- (G.unobserved ∪ newFixed) ∪ newObserved.
      intro u hu v hv
      have hedge := (G.inducedDag newActive).mem_children.mp hv
      have hvActive : v ∈ newActive := hedge.2.2
      have hvChildOrig : v ∈ G.dag.children u := G.dag.mem_children.mpr hedge.1
      -- Lift u into the old classified set.
      have huOld : u ∈ G.unobserved ∪ G.fixed ∪ G.observed := by
        rcases Finset.mem_union.mp hu with hu' | hu'
        · rcases Finset.mem_union.mp hu' with hu' | hu'
          · -- u ∈ G.unobserved
            exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mp hu').1)
          · -- u ∈ newFixed ⊆ G.fixed
            have : u ∈ G.fixed := (Finset.mem_filter.mp hu').1
            exact Finset.mem_union_left _ (Finset.mem_union_right _ this)
        · -- u ∈ newObserved ⊆ G.observed
          have : u ∈ G.observed := (Finset.mem_inter.mp hu').2
          exact Finset.mem_union_right _ this
      have hvOldObs : v ∈ G.observed := G.all_children_in_observed u huOld hvChildOrig
      -- Combine: v ∈ newActive and v ∈ G.observed. Rule out newFixed and
      -- G.unobserved to land in newObserved.
      -- newActive parses as (newFixed ∪ newObserved) ∪ G.unobserved.
      rcases Finset.mem_union.mp hvActive with hv' | hv'
      · rcases Finset.mem_union.mp hv' with hv' | hv'
        · -- v ∈ newFixed → v is `.fixed _`, but v ∈ G.observed → v is `.random _`.
          have hvFixed : v ∈ G.fixed := (Finset.mem_filter.mp hv').1
          obtain ⟨m, hm⟩ := G.fixed_is_fixed _ hvFixed
          obtain ⟨k, hk⟩ := G.observed_is_random _ hvOldObs
          rw [hm] at hk
          cases hk
        · -- v ∈ newObserved — done.
          exact hv'
      · -- v ∈ G.unobserved contradicts v ∈ G.observed via disjointness.
        exact (Finset.disjoint_left.mp G.obs_unobs_disjoint hvOldObs
          (Finset.mem_filter.mp hv').1).elim }

/-- In the induced subgraph `G.induce R`, any vertex that is a descendant
    of some other vertex must lie in `R`.

    **Proof idea**: A descendant `w` has a parent in the induced DAG (the
    last edge of the `isAncestor` path), so `w` is not a root.  Since
    `(G.induce R).fixed_are_roots` and `(G.induce R).unobs_are_roots`
    make all fixed and unobserved nodes roots, `w` must lie in
    `newObserved = R ∩ G.observed ⊆ R`. -/
lemma induce_isAncestor_mem_R (R : Finset (SWIGNode N)) {u v : SWIGNode N}
    (h : (G.induce R).dag.isAncestor u v) : v ∈ R := by
  -- v has at least one parent in the induced DAG
  have hpar : (G.induce R).dag.parents v ≠ ∅ :=
    G.inducedDag_isAncestor_has_parent _ h
  -- v is in the active set of the induced DAG
  have hactive : v ∈ (G.fixed.filter (fun s => iotaMap s ∈ R ∩ G.observed)) ∪
      (R ∩ G.observed) ∪
        (G.unobserved.filter (fun u => ∃ w ∈ R ∩ G.observed, G.dag.edge u w)) :=
    G.inducedDag_isAncestor_mem_active _ h
  -- v is not fixed (fixed nodes are roots, but v has a parent)
  have hnotFixed : v ∉ G.fixed.filter (fun s => iotaMap s ∈ R ∩ G.observed) := by
    intro hv
    have := (G.induce R).fixed_are_roots v hv
    exact hpar this
  -- v is not unobserved (unobserved nodes are roots, but v has a parent)
  have hnotUnobs :
      v ∉ G.unobserved.filter (fun u => ∃ w ∈ R ∩ G.observed, G.dag.edge u w) := by
    intro hv
    have := (G.induce R).unobs_are_roots v hv
    exact hpar this
  -- So v ∈ R ∩ G.observed ⊆ R
  rcases Finset.mem_union.mp hactive with hv | hv
  · rcases Finset.mem_union.mp hv with hv | hv
    · exact absurd hv hnotFixed
    · exact (Finset.mem_inter.mp hv).1
  · exact absurd hv hnotUnobs

end SWIGGraph

end Causalean
