/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Monolithic Split operation on SWIG graphs (multi-target, one-shot)

This file defines a *monolithic* multi-target split operation on SWIG graphs,
realizing Definition 8 (multi-target generalized intervention) as a single
one-shot graph construction rather than an iterated single-target split.

## Motivation

Iterating a single-target split (replace one target's outgoing edges, repeat)
over the target set would be mathematically equivalent, but produces parent
sets that agree with the base graph only *propositionally* at non-intervened
vertices — blocking rfl-level reductions in cross-SCM bridge lemmas such as
`Causalean/SCM/Do/Rule3.lean:fixSet_evalMap_nonAnc_compat`.

The monolithic `splitMono` reroutes all `.random D → w` edges (for `D ∈ X`) to
`.fixed D → w` in a single pass.  Parent sets, observed/unobserved/fixed
partitions, and `structFun` bookkeeping on top collapse by `rfl` at vertices
that are not targeted, eliminating the list-induction cast threading.

## Main definitions

* `splitMonoEdgeRel` — edge relation after monolithic split
* `splitMonoTopo`    — topological order for the split DAG
* `splitMonoDAG`     — the DAG on `SWIGNode N` after split
* `SWIGGraph.splitMono` — SWIG graph after monolithic split
* `SWIGGraph.splitMono_parents_char` — parent-set characterization
* `SWIGGraph.splitMono_parents_eq_of_no_fixed_parent` — key lemma:
  under "no `.fixed D` (D ∈ X) is a parent of v", parents collapse to `G.dag.parents v`.

## References

* Basic Concepts.tex, Definition 8 (multi-target generalized intervention).
-/

import Causalean.Graph.SWIG

/-! # Monolithic Multi-Target SWIG Split

This file defines the one-shot split of a Single World Intervention Graph at a
finite set of intervention targets. The construction reroutes every outgoing
edge from a targeted random node `.random D` to its fixed counterpart `.fixed D`
in one graph transformation, while preserving the observed and unobserved node
sets and adding the fixed copies of the targets to the fixed set.

The main definitions are:

* `splitMonoEdgeRel` — the edge relation after rerouting all targeted outgoing
  edges;
* `splitMonoTopo` and `splitMonoDAG` — the topological order and DAG proof for
  the rerouted graph;
* `SWIGGraph.splitMono` — the packaged SWIG graph after the split;
* `splitMono_parents_char` — an exact parent-set characterization; and
* `splitMono_parents_eq_of_no_fixed_parent` — the parent-set coincidence lemma
  used by the SCM Rule 3 evaluation-map compatibility bridge.

The operation is monolithic rather than an iterated single-target split so that
parents at unaffected vertices reduce definitionally in downstream SCM
bookkeeping. -/

namespace Causalean

namespace SWIGGraph

variable {N : Type*} [DecidableEq N] [Fintype N]

-- ============================================================
-- Monolithic split edge relation
-- ============================================================

/-- Edge relation after monolithically splitting every node `D ∈ X`.

    From Definition 8 (multi-target generalized intervention):
    For every `D ∈ X`, each outgoing edge `(random D, w)` is replaced by
    `(fixed D, w)`; incoming edges to `random D` are retained; all other edges
    unchanged.

    - For `D ∈ X`: `.random D` loses outgoing edges; `.fixed D` inherits them.
    - For `D ∉ X`: edges from `.random D` and `.fixed d` are retained verbatim.
-/
def splitMonoEdgeRel (dagEdge : SWIGNode N → SWIGNode N → Prop) (X : Finset N) :
    SWIGNode N → SWIGNode N → Prop
  | .random u, b => if u ∈ X then False else dagEdge (.random u) b
  | .fixed d, b => if d ∈ X then dagEdge (.random d) b else dagEdge (.fixed d) b

/-- The monolithic split edge relation is decidable whenever the original edge relation is
decidable. -/
instance splitMonoEdgeRel_decidable (dagEdge : SWIGNode N → SWIGNode N → Prop)
    [DecidableRel dagEdge] (X : Finset N) :
    DecidableRel (splitMonoEdgeRel dagEdge X) := by
  intro a b
  cases a with
  | random u =>
    simp only [splitMonoEdgeRel]
    by_cases h : u ∈ X
    · simp [h]; exact instDecidableFalse
    · simp [h]; infer_instance
  | fixed d =>
    simp only [splitMonoEdgeRel]
    by_cases h : d ∈ X
    · simp [h]; infer_instance
    · simp [h]; infer_instance

-- ============================================================
-- Monolithic split topological order
-- ============================================================

/-- Topological order for the monolithically-split DAG.

    - Every `.random u` gets odd value `2 * topoOrder (.random u) + 1`.
    - For `d ∈ X`: `.fixed d` gets even value `2 * topoOrder (.random d)`
      (same as `.random d` minus one), placing it just before `.random d`'s
      old topo slot so it can precede all of its new children.
    - For `d ∉ X`: `.fixed d` keeps odd value `2 * topoOrder (.fixed d) + 1`. -/
noncomputable def splitMonoTopo (G : SWIGGraph N) (X : Finset N) : SWIGNode N → ℕ
  | .random u => 2 * G.dag.topoOrder (SWIGNode.random u) + 1
  | .fixed d =>
      if d ∈ X then 2 * G.dag.topoOrder (SWIGNode.random d)
      else 2 * G.dag.topoOrder (SWIGNode.fixed d) + 1

-- ============================================================
-- Monolithic split DAG
-- ============================================================

/-- The monolithically-split DAG: the DAG on `SWIGNode N` obtained by
    rerouting all `.random D → w` edges (for `D ∈ X`) to `.fixed D → w`
    in a single pass.  Requires each `.fixed D` (D ∈ X) to be a root
    (isolated) in the original `G.dag`. -/
def splitMonoDAG (G : SWIGGraph N) (X : Finset N)
    (_hIso : ∀ D ∈ X, G.dag.parents (SWIGNode.fixed D) = ∅) :
    DAG (SWIGNode N) where
  edge := splitMonoEdgeRel G.dag.edge X
  decEdge := splitMonoEdgeRel_decidable G.dag.edge X
  acyclic := DAG.acyclic_of_topoOrder (τ := splitMonoTopo G X) (by
    intro u v h
    cases u with
    | random u =>
      simp only [splitMonoEdgeRel] at h
      by_cases hu : u ∈ X
      · simp [hu] at h
      · have hOld : G.dag.edge (SWIGNode.random u) v := by simpa [hu] using h
        have hltOld := G.dag.topoOrder_lt _ _ hOld
        -- v is not a .fixed node with d ∈ X, because in G.dag there are no
        -- edges into .fixed d (by fixed_are_roots / fixed_outside_fixed_isolated).
        cases v with
        | random v =>
          simp [splitMonoTopo]; omega
        | fixed d =>
          -- edge .random u → .fixed d in G.dag: impossible since
          -- .fixed d has no parents in G.dag (root/isolated)
          exfalso
          by_cases hd_in_fix : SWIGNode.fixed d ∈ G.fixed
          · have hroot : G.dag.parents (SWIGNode.fixed d) = ∅ :=
              G.fixed_are_roots _ hd_in_fix
            have : SWIGNode.random u ∈ G.dag.parents (SWIGNode.fixed d) :=
              G.dag.mem_parents.mpr hOld
            simpa [hroot] using this
          · have hiso := G.fixed_outside_fixed_isolated d hd_in_fix
            have : SWIGNode.random u ∈ G.dag.parents (SWIGNode.fixed d) :=
              G.dag.mem_parents.mpr hOld
            simpa [hiso.1] using this
    | fixed d =>
      simp only [splitMonoEdgeRel] at h
      by_cases hd : d ∈ X
      · have hOld : G.dag.edge (SWIGNode.random d) v := by simpa [hd] using h
        have hltOld := G.dag.topoOrder_lt _ _ hOld
        cases v with
        | random v =>
          simp [splitMonoTopo, hd]; omega
        | fixed d' =>
          exfalso
          by_cases hd'_in_fix : SWIGNode.fixed d' ∈ G.fixed
          · have hroot : G.dag.parents (SWIGNode.fixed d') = ∅ :=
              G.fixed_are_roots _ hd'_in_fix
            have : SWIGNode.random d ∈ G.dag.parents (SWIGNode.fixed d') :=
              G.dag.mem_parents.mpr hOld
            simpa [hroot] using this
          · have hiso := G.fixed_outside_fixed_isolated d' hd'_in_fix
            have : SWIGNode.random d ∈ G.dag.parents (SWIGNode.fixed d') :=
              G.dag.mem_parents.mpr hOld
            simpa [hiso.1] using this
      · have hOld : G.dag.edge (SWIGNode.fixed d) v := by simpa [hd] using h
        have hltOld := G.dag.topoOrder_lt _ _ hOld
        cases v with
        | random v =>
          simp [splitMonoTopo, hd]; omega
        | fixed d' =>
          exfalso
          by_cases hd'_in_fix : SWIGNode.fixed d' ∈ G.fixed
          · have hroot : G.dag.parents (SWIGNode.fixed d') = ∅ :=
              G.fixed_are_roots _ hd'_in_fix
            have : SWIGNode.fixed d ∈ G.dag.parents (SWIGNode.fixed d') :=
              G.dag.mem_parents.mpr hOld
            simpa [hroot] using this
          · have hiso := G.fixed_outside_fixed_isolated d' hd'_in_fix
            have : SWIGNode.fixed d ∈ G.dag.parents (SWIGNode.fixed d') :=
              G.dag.mem_parents.mpr hOld
            simpa [hiso.1] using this)

-- ============================================================
-- The monolithic multi-target split operation
-- ============================================================

/-- **Monolithic multi-target split.** (Definition 8, one-shot form.)

    Given `G : SWIGGraph N` and `X : Finset N` with
    - `hObs : ∀ D ∈ X, .random D ∈ G.observed`
    - `hFix : ∀ D ∈ X, .fixed D ∉ G.fixed`
    produce a `SWIGGraph` where every `.random D → w` edge (D ∈ X) is rerouted
    to `.fixed D → w` in a single pass.

    Preserves `observed` and `unobserved` by `rfl`; enlarges
    `fixed` by `X.image SWIGNode.fixed`. -/
def splitMono (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed) :
    SWIGGraph N where
  dag := G.splitMonoDAG X (fun D hD =>
    (G.fixed_outside_fixed_isolated D (hFix D hD)).1)
  fixed := G.fixed ∪ X.image SWIGNode.fixed
  observed := G.observed
  unobserved := G.unobserved
  fixed_is_fixed := by
    intro s hs
    rcases Finset.mem_union.mp hs with hs_old | hs_new
    · exact G.fixed_is_fixed s hs_old
    · rcases Finset.mem_image.mp hs_new with ⟨d, _, rfl⟩
      exact ⟨d, rfl⟩
  observed_is_random := G.observed_is_random
  unobserved_is_random := G.unobserved_is_random
  obs_unobs_disjoint := G.obs_unobs_disjoint
  dag_edges_classified := by
    intro u v huv
    -- huv : splitMonoEdgeRel G.dag.edge X u v
    have hsplit : splitMonoEdgeRel G.dag.edge X u v := huv
    cases u with
    | random a =>
      by_cases ha : a ∈ X
      · -- random a loses outgoing edges
        exfalso
        simp [splitMonoEdgeRel, ha] at hsplit
      · have hold : G.dag.edge (SWIGNode.random a) v := by
          simpa [splitMonoEdgeRel, ha] using hsplit
        have hcls := G.dag_edges_classified _ _ hold
        refine ⟨?_, ?_⟩
        · rcases Finset.mem_union.mp hcls.1 with h | h
          · rcases Finset.mem_union.mp h with h | h
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ h))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
          · exact Finset.mem_union_right _ h
        · rcases Finset.mem_union.mp hcls.2 with h | h
          · rcases Finset.mem_union.mp h with h | h
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ h))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
          · exact Finset.mem_union_right _ h
    | fixed d =>
      by_cases hd : d ∈ X
      · -- Moved edge: .fixed d → v originates from .random d → v in G.dag.
        have hold : G.dag.edge (SWIGNode.random d) v := by
          simpa [splitMonoEdgeRel, hd] using hsplit
        have hd_obs : SWIGNode.random d ∈ G.observed := hObs d hd
        have hvObs : v ∈ G.observed :=
          G.all_children_in_observed (SWIGNode.random d)
            (Finset.mem_union_right _ hd_obs)
            (G.dag.mem_children.mpr hold)
        refine ⟨?_, ?_⟩
        · -- .fixed d ∈ new fixed via X.image
          have : SWIGNode.fixed d ∈ X.image SWIGNode.fixed :=
            Finset.mem_image.mpr ⟨d, hd, rfl⟩
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ this))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvObs)
      · have hold : G.dag.edge (SWIGNode.fixed d) v := by
          simpa [splitMonoEdgeRel, hd] using hsplit
        have hcls := G.dag_edges_classified _ _ hold
        refine ⟨?_, ?_⟩
        · rcases Finset.mem_union.mp hcls.1 with h | h
          · rcases Finset.mem_union.mp h with h | h
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ h))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
          · exact Finset.mem_union_right _ h
        · rcases Finset.mem_union.mp hcls.2 with h | h
          · rcases Finset.mem_union.mp h with h | h
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_union_left _ h))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
          · exact Finset.mem_union_right _ h
  fixed_image_in_observed := by
    intro s hs
    rcases Finset.mem_union.mp hs with hs_old | hs_new
    · exact G.fixed_image_in_observed s hs_old
    · rcases Finset.mem_image.mp hs_new with ⟨d, hd, rfl⟩
      simpa [iotaMap] using hObs d hd
  fixed_are_roots := by
    intro s hs
    -- No parents of s in the split DAG: every edge x → s in splitMonoEdgeRel
    -- reduces to an edge into s in G.dag, which is empty (by root/isolation).
    have hNoG : ∀ x : SWIGNode N, ¬ G.dag.edge x s := by
      intro x hxE
      rcases Finset.mem_union.mp hs with hs_old | hs_new
      · have hroot : G.dag.parents s = ∅ := G.fixed_are_roots s hs_old
        have : x ∈ G.dag.parents s := G.dag.mem_parents.mpr hxE
        simpa [hroot] using this
      · rcases Finset.mem_image.mp hs_new with ⟨D, hD, rfl⟩
        have hroot : G.dag.parents (SWIGNode.fixed D) = ∅ :=
          (G.fixed_outside_fixed_isolated D (hFix D hD)).1
        have : x ∈ G.dag.parents (SWIGNode.fixed D) := G.dag.mem_parents.mpr hxE
        simpa [hroot] using this
    ext x
    constructor
    · intro hxPar
      have hxEdge : splitMonoEdgeRel G.dag.edge X x s :=
        (G.splitMonoDAG X (fun D hD =>
          (G.fixed_outside_fixed_isolated D (hFix D hD)).1)).mem_parents.mp hxPar
      exfalso
      cases x with
      | random u =>
        by_cases hu : u ∈ X
        · simp [splitMonoEdgeRel, hu] at hxEdge
        · have : G.dag.edge (SWIGNode.random u) s := by
            simpa [splitMonoEdgeRel, hu] using hxEdge
          exact hNoG _ this
      | fixed d =>
        by_cases hd : d ∈ X
        · have : G.dag.edge (SWIGNode.random d) s := by
            simpa [splitMonoEdgeRel, hd] using hxEdge
          exact hNoG _ this
        · have : G.dag.edge (SWIGNode.fixed d) s := by
            simpa [splitMonoEdgeRel, hd] using hxEdge
          exact hNoG _ this
    · intro hxPar
      simpa using hxPar
  unobs_are_roots := by
    intro u hu
    have hrootOld : G.dag.parents u = ∅ := G.unobs_are_roots u hu
    ext x
    constructor
    · intro hxPar
      have hxEdge : splitMonoEdgeRel G.dag.edge X x u :=
        (G.splitMonoDAG X _).mem_parents.mp hxPar
      exfalso
      cases x with
      | random n =>
        by_cases hn : n ∈ X
        · simp [splitMonoEdgeRel, hn] at hxEdge
        · have : G.dag.edge (SWIGNode.random n) u := by
            simpa [splitMonoEdgeRel, hn] using hxEdge
          have : SWIGNode.random n ∈ G.dag.parents u := G.dag.mem_parents.mpr this
          simpa [hrootOld] using this
      | fixed d =>
        by_cases hd : d ∈ X
        · have : G.dag.edge (SWIGNode.random d) u := by
            simpa [splitMonoEdgeRel, hd] using hxEdge
          have : SWIGNode.random d ∈ G.dag.parents u := G.dag.mem_parents.mpr this
          simpa [hrootOld] using this
        · have : G.dag.edge (SWIGNode.fixed d) u := by
            simpa [splitMonoEdgeRel, hd] using hxEdge
          have : SWIGNode.fixed d ∈ G.dag.parents u := G.dag.mem_parents.mpr this
          simpa [hrootOld] using this
    · intro hxPar
      simpa using hxPar
  fixed_outside_fixed_isolated := by
    intro n hn
    -- hn : .fixed n ∉ G.fixed ∪ X.image .fixed, so .fixed n ∉ G.fixed AND n ∉ X
    have hn_old : SWIGNode.fixed n ∉ G.fixed := by
      intro hmem
      exact hn (Finset.mem_union_left _ hmem)
    have hn_notX : n ∉ X := by
      intro hmem
      exact hn (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, hmem, rfl⟩))
    have hIsoOld := G.fixed_outside_fixed_isolated n hn_old
    refine ⟨?_, ?_⟩
    · -- parents ∅
      ext x
      constructor
      · intro hxPar
        have hxEdge : splitMonoEdgeRel G.dag.edge X x (SWIGNode.fixed n) :=
          (G.splitMonoDAG X _).mem_parents.mp hxPar
        exfalso
        cases x with
        | random u =>
          by_cases hu : u ∈ X
          · simp [splitMonoEdgeRel, hu] at hxEdge
          · have : G.dag.edge (SWIGNode.random u) (SWIGNode.fixed n) := by
              simpa [splitMonoEdgeRel, hu] using hxEdge
            have : SWIGNode.random u ∈ G.dag.parents (SWIGNode.fixed n) :=
              G.dag.mem_parents.mpr this
            simpa [hIsoOld.1] using this
        | fixed d =>
          by_cases hd : d ∈ X
          · have : G.dag.edge (SWIGNode.random d) (SWIGNode.fixed n) := by
              simpa [splitMonoEdgeRel, hd] using hxEdge
            have : SWIGNode.random d ∈ G.dag.parents (SWIGNode.fixed n) :=
              G.dag.mem_parents.mpr this
            simpa [hIsoOld.1] using this
          · have : G.dag.edge (SWIGNode.fixed d) (SWIGNode.fixed n) := by
              simpa [splitMonoEdgeRel, hd] using hxEdge
            have : SWIGNode.fixed d ∈ G.dag.parents (SWIGNode.fixed n) :=
              G.dag.mem_parents.mpr this
            simpa [hIsoOld.1] using this
      · intro hxPar
        simpa using hxPar
    · -- children ∅
      ext x
      constructor
      · intro hxCh
        have hxEdge : splitMonoEdgeRel G.dag.edge X (SWIGNode.fixed n) x :=
          (G.splitMonoDAG X _).mem_children.mp hxCh
        have : G.dag.edge (SWIGNode.fixed n) x := by
          simpa [splitMonoEdgeRel, hn_notX] using hxEdge
        have : x ∈ G.dag.children (SWIGNode.fixed n) := G.dag.mem_children.mpr this
        simpa [hIsoOld.2] using this
      · intro hxCh
        simpa using hxCh
  all_children_in_observed := by
    intro u hu w hw
    have hwEdge : splitMonoEdgeRel G.dag.edge X u w :=
      (G.splitMonoDAG X _).mem_children.mp hw
    -- In every branch the new edge reduces to a G-edge whose target `w` is in observed.
    cases u with
    | random a =>
      by_cases ha : a ∈ X
      · exfalso
        simp [splitMonoEdgeRel, ha] at hwEdge
      · have hold : G.dag.edge (SWIGNode.random a) w := by
          simpa [splitMonoEdgeRel, ha] using hwEdge
        -- `.random a` is observed or unobserved in G; apply G's closure.
        have hu_old : SWIGNode.random a ∈ G.unobserved ∪ G.fixed ∪ G.observed := by
          rcases Finset.mem_union.mp hu with hu' | huObs
          · rcases Finset.mem_union.mp hu' with huUnobs | huFixNew
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ huUnobs)
            · -- huFixNew : .random a ∈ G.fixed ∪ X.image .fixed
              rcases Finset.mem_union.mp huFixNew with huFix | huImg
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ huFix)
              · exfalso
                rcases Finset.mem_image.mp huImg with ⟨d, _, hfix_eq⟩
                cases hfix_eq
          · exact Finset.mem_union_right _ huObs
        have := G.all_children_in_observed _ hu_old (G.dag.mem_children.mpr hold)
        exact this
    | fixed d =>
      by_cases hd : d ∈ X
      · have hold : G.dag.edge (SWIGNode.random d) w := by
          simpa [splitMonoEdgeRel, hd] using hwEdge
        have hd_obs : SWIGNode.random d ∈ G.observed := hObs d hd
        exact G.all_children_in_observed (SWIGNode.random d)
          (Finset.mem_union_right _ hd_obs) (G.dag.mem_children.mpr hold)
      · have hold : G.dag.edge (SWIGNode.fixed d) w := by
          simpa [splitMonoEdgeRel, hd] using hwEdge
        -- .fixed d is in new fixed iff in G.fixed (since d ∉ X rules out the image branch).
        have hu_old : SWIGNode.fixed d ∈ G.unobserved ∪ G.fixed ∪ G.observed := by
          rcases Finset.mem_union.mp hu with hu' | huObs
          · rcases Finset.mem_union.mp hu' with huUnobs | huFixNew
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ huUnobs)
            · rcases Finset.mem_union.mp huFixNew with huFix | huImg
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ huFix)
              · exfalso
                rcases Finset.mem_image.mp huImg with ⟨d', hd'X, hfix_eq⟩
                have : d = d' := SWIGNode.fixed.inj hfix_eq.symm
                exact hd (this ▸ hd'X)
          · exact Finset.mem_union_right _ huObs
        exact G.all_children_in_observed _ hu_old (G.dag.mem_children.mpr hold)

-- ============================================================
-- Interface lemmas
-- ============================================================

/-- Monolithic splitting preserves the observed node set. -/
@[simp] lemma splitMono_observed (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed) :
    (G.splitMono X hObs hFix).observed = G.observed := rfl

/-- Monolithic splitting preserves the unobserved node set. -/
@[simp] lemma splitMono_unobserved (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed) :
    (G.splitMono X hObs hFix).unobserved = G.unobserved := rfl

/-- Monolithic splitting adds the fixed copies of the target variables to the fixed node set. -/
@[simp] lemma splitMono_fixed (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed) :
    (G.splitMono X hObs hFix).fixed = G.fixed ∪ X.image SWIGNode.fixed := rfl

-- ============================================================
-- Parent set characterization
-- ============================================================

/-- **Characterization of parents in `splitMono`.**

    For `v : SWIGNode N`, a node `x` is a parent of `v` in `G.splitMono X` iff
    either `x` is a parent of `v` in `G.dag` *and* `x` is not a `.random D`
    for some `D ∈ X`, or `x = .fixed D` for some `D ∈ X` with `.random D` a
    parent of `v` in `G.dag`. -/
theorem splitMono_parents_char (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (v : SWIGNode N) :
    ∀ x : SWIGNode N,
      x ∈ (G.splitMono X hObs hFix).dag.parents v ↔
        (x ∈ G.dag.parents v ∧ ∀ D ∈ X, x ≠ SWIGNode.random D) ∨
        (∃ D ∈ X, x = SWIGNode.fixed D ∧ SWIGNode.random D ∈ G.dag.parents v) := by
  intro x
  -- Bridge to edge relation.
  have hiff : x ∈ (G.splitMono X hObs hFix).dag.parents v ↔
      splitMonoEdgeRel G.dag.edge X x v :=
    (G.splitMono X hObs hFix).dag.mem_parents
  rw [hiff]
  cases x with
  | random u =>
    simp only [splitMonoEdgeRel]
    by_cases hu : u ∈ X
    · constructor
      · intro h; simp [hu] at h
      · rintro (⟨hPar, hNoRand⟩ | ⟨D, hD, hEq, _⟩)
        · exact absurd rfl (hNoRand u hu)
        · exact absurd hEq (by intro h; cases h)
    · constructor
      · intro hEdge
        have hEdgeG : G.dag.edge (SWIGNode.random u) v := by
          rw [if_neg hu] at hEdge; exact hEdge
        refine Or.inl ⟨G.dag.mem_parents.mpr hEdgeG, ?_⟩
        intro D hD heq
        have : u = D := SWIGNode.random.inj heq
        exact hu (this ▸ hD)
      · rintro (⟨hPar, _⟩ | ⟨D, _, hEq, _⟩)
        · rw [if_neg hu]; exact G.dag.mem_parents.mp hPar
        · exact absurd hEq (by intro h; cases h)
  | fixed d =>
    simp only [splitMonoEdgeRel]
    by_cases hd : d ∈ X
    · constructor
      · intro hEdge
        have hEdgeG : G.dag.edge (SWIGNode.random d) v := by
          rw [if_pos hd] at hEdge; exact hEdge
        exact Or.inr ⟨d, hd, rfl, G.dag.mem_parents.mpr hEdgeG⟩
      · rintro (⟨hPar, _⟩ | ⟨D, hD, hEq, hRD⟩)
        · exfalso
          have hfix_notin : SWIGNode.fixed d ∉ G.fixed := hFix d hd
          have hiso := (G.fixed_outside_fixed_isolated d hfix_notin).2
          have hch : v ∈ G.dag.children (SWIGNode.fixed d) :=
            G.dag.mem_children.mpr (G.dag.mem_parents.mp hPar)
          simpa [hiso] using hch
        · have : d = D := SWIGNode.fixed.inj hEq
          subst this
          rw [if_pos hd]; exact G.dag.mem_parents.mp hRD
    · constructor
      · intro hEdge
        have hEdgeG : G.dag.edge (SWIGNode.fixed d) v := by
          rw [if_neg hd] at hEdge; exact hEdge
        refine Or.inl ⟨G.dag.mem_parents.mpr hEdgeG, ?_⟩
        intro D hD heq
        exact absurd heq (by intro h; cases h)
      · rintro (⟨hPar, _⟩ | ⟨D, hD, hEq, _⟩)
        · rw [if_neg hd]; exact G.dag.mem_parents.mp hPar
        · have : d = D := SWIGNode.fixed.inj hEq
          exact absurd (this ▸ hD) hd

/-- **Parent-set coincidence at non-`.fixed`-targeted vertices.**

    If no `.fixed D` (for `D ∈ X`) is a parent of `v` in the monolithic split
    graph `G.splitMono X`, then `v`'s parent set there equals `v`'s parent set
    in `G`.

    This is the key graph-level input to the Rule 3 evalMap-compat bridge
    (`Causalean/SCM/Do/Rule3.lean:fixSet_evalMap_nonAnc_compat`). -/
theorem splitMono_parents_eq_of_no_fixed_parent (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (v : SWIGNode N)
    (hNoFP : ∀ D ∈ X,
      SWIGNode.fixed D ∉ (G.splitMono X hObs hFix).dag.parents v) :
    (G.splitMono X hObs hFix).dag.parents v = G.dag.parents v := by
  -- Under hNoFP, no .random D (D ∈ X) can be a parent of v in G.dag either,
  -- because if it were, splitMono_parents_char would place .fixed D in parents — contradiction.
  have hNoRD : ∀ D ∈ X, SWIGNode.random D ∉ G.dag.parents v := by
    intro D hD hRD
    apply hNoFP D hD
    exact (splitMono_parents_char G X hObs hFix v (SWIGNode.fixed D)).mpr
      (Or.inr ⟨D, hD, rfl, hRD⟩)
  ext x
  rw [splitMono_parents_char G X hObs hFix v x]
  constructor
  · rintro (⟨hP, _⟩ | ⟨D, hD, rfl, hRD⟩)
    · exact hP
    · exact absurd hRD (hNoRD D hD)
  · intro hP
    left
    refine ⟨hP, ?_⟩
    intro D hD heq
    subst heq
    exact hNoRD D hD hP

/-- **Congruence of `splitMono` under `SWIGGraph.Equivalent`.**

    If two SWIG graphs are `Equivalent`, then their monolithic splits at the
    same set `X` are also `Equivalent`. -/
theorem Equivalent.splitMono_congr
    {G₁ G₂ : SWIGGraph N} (h : Equivalent G₁ G₂)
    (X : Finset N)
    (hObs₁ : ∀ D ∈ X, SWIGNode.random D ∈ G₁.observed)
    (hFix₁ : ∀ D ∈ X, SWIGNode.fixed D ∉ G₁.fixed)
    (hObs₂ : ∀ D ∈ X, SWIGNode.random D ∈ G₂.observed)
    (hFix₂ : ∀ D ∈ X, SWIGNode.fixed D ∉ G₂.fixed) :
    Equivalent (G₁.splitMono X hObs₁ hFix₁) (G₂.splitMono X hObs₂ hFix₂) := by
  obtain ⟨hEdge, hFix_eq, hObs_eq, hUnobs_eq⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) Edge iff: 4-way case split on (random/fixed) × (∈ X / ∉ X).
    intro u v
    cases u with
    | random u =>
      simp only [splitMono, splitMonoDAG, splitMonoEdgeRel]
      by_cases hu : u ∈ X
      · simp [hu]
      · simp [hu]
        exact hEdge _ _
    | fixed d =>
      simp only [splitMono, splitMonoDAG, splitMonoEdgeRel]
      by_cases hd : d ∈ X
      · simp [hd]
        exact hEdge _ _
      · simp [hd]
        exact hEdge _ _
  · -- (2) Fixed sets: G.fixed ∪ X.image .fixed = G₂.fixed ∪ X.image .fixed
    simp only [splitMono_fixed]
    rw [hFix_eq]
  · -- (3) Observed: preserved by rfl.
    simp only [splitMono_observed]
    exact hObs_eq
  · -- (4) Unobserved: preserved by rfl.
    simp only [splitMono_unobserved]
    exact hUnobs_eq

end SWIGGraph

end Causalean
