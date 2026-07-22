/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.Induce
import Causalean.Graph.DSep.Ancestral

/-! # d-Separation Transport for Induced SWIGs

This file collects graph-only bridges that compare d-separation in an induced
SWIG with d-separation in the ambient SWIG. The main bridge is tailored to
ancestral induced graphs: active paths between observed vertices cannot use
vertices outside the ancestral support, except for fixed nodes, which are
handled by placing all fixed nodes in the conditioning set.

The support lemmas prove idempotence of ancestral closure, preservation of
ancestor paths and collider activations inside an ancestral induced SWIG, and
non-membership of fixed nodes on relevant observed-endpoint active paths. The
main theorem `SWIGGraph.dSep_union_fixed_of_induce_dSep` lifts d-separation from
`(G.induce R).dag` to the ambient `G.dag` after adjoining all fixed nodes to the
conditioning set.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace DAG

variable (G : DAG (SWIGNode N))

/-- A proper ancestor gives the target a parent. -/
private lemma isAncestor_has_parent {u v : SWIGNode N} (h : G.isAncestor u v) :
    G.parents v ≠ ∅ := by
  intro hempty
  have hmem : ∀ w, w ∉ G.parents v :=
    fun w => (Finset.eq_empty_iff_forall_notMem.mp hempty) w
  induction h with
  | edge he => exact hmem u (G.mem_parents.mpr he)
  | trans _ he _ => exact hmem _ (G.mem_parents.mpr he)

/-- Taking the ancestors of an ancestral set gives back the same set.

This certifies that post-intervention ancestral query supports are already ancestrally closed. -/
theorem ancestralSet_idem (S : Finset (SWIGNode N)) :
    G.ancestralSet (G.ancestralSet S) = G.ancestralSet S := by
  apply Finset.Subset.antisymm
  · intro u hu
    rw [ancestralSet, Finset.mem_union] at hu
    rcases hu with hu | hu
    · exact hu
    · rw [ancestorsSet, Finset.mem_filter] at hu
      obtain ⟨_, v, hv, huv⟩ := hu
      rw [ancestralSet, Finset.mem_union] at hv
      rcases hv with hvS | hvAnc
      · exact G.mem_ancestralSet_of_isAncestor hvS huv
      · rw [ancestorsSet, Finset.mem_filter] at hvAnc
        obtain ⟨_, w, hwS, hvw⟩ := hvAnc
        exact G.mem_ancestralSet_of_isAncestor hwS (G.isAncestor_trans huv hvw)
  · exact G.subset_ancestralSet (G.ancestralSet S)

end DAG

namespace SWIGGraph

variable (G : SWIGGraph N)

/-- Observed SWIG vertices are not members of the fixed intervention set. -/
private lemma not_mem_fixed_of_mem_observed {v : SWIGNode N}
    (hv : v ∈ G.observed) : v ∉ G.fixed := by
  intro hfix
  obtain ⟨n, hn⟩ := G.fixed_is_fixed v hfix
  obtain ⟨m, hm⟩ := G.observed_is_random v hv
  rw [hn] at hm
  cases hm

/-- No vertex can be a proper ancestor of a fixed intervention root. -/
private lemma not_isAncestor_to_fixed_mem {s : SWIGNode N}
    (hs : s ∈ G.fixed) (u : SWIGNode N) :
    ¬ G.dag.isAncestor u s := by
  intro hanc
  exact (G.dag.isAncestor_has_parent hanc) (G.fixed_are_roots s hs)

/-- A vertex in `R` that is not fixed and has an incident edge belongs to the
active vertex set used by `G.induce R`. -/
private lemma mem_induce_active_of_mem_R_of_not_fixed_of_incident
    {R : Finset (SWIGNode N)} {v : SWIGNode N}
    (hvR : v ∈ R) (hvNotFixed : v ∉ G.fixed)
    (hinc : ∃ w ∈ R, G.dag.edge v w ∨ G.dag.edge w v) :
    v ∈ (G.fixed.filter (fun s => iotaMap s ∈ R ∩ G.observed)) ∪
        (R ∩ G.observed) ∪
          (G.unobserved.filter (fun u => ∃ z ∈ R ∩ G.observed, G.dag.edge u z)) := by
  obtain ⟨w, hwR, hinc | hinc⟩ := hinc
  · have hcls := (G.dag_edges_classified v w hinc).1
    rcases Finset.mem_union.mp hcls with hleft | hunobs
    · rcases Finset.mem_union.mp hleft with hfix | hobs
      · exact (hvNotFixed hfix).elim
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨hvR, hobs⟩))
    · have hwObs : w ∈ G.observed :=
        G.all_children_in_observed v
          (Finset.mem_union_left _ (Finset.mem_union_left _ hunobs))
          (G.dag.mem_children.mpr hinc)
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hunobs, ⟨w, Finset.mem_inter.mpr ⟨hwR, hwObs⟩, hinc⟩⟩)
  · have hcls := (G.dag_edges_classified w v hinc).2
    rcases Finset.mem_union.mp hcls with hleft | hunobs
    · rcases Finset.mem_union.mp hleft with hfix | hobs
      · exact (hvNotFixed hfix).elim
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨hvR, hobs⟩))
    · have : w ∈ G.dag.parents v := G.dag.mem_parents.mpr hinc
      simp [G.unobs_are_roots v hunobs] at this

/-- A vertex in `R` with a parent is active in the induced graph. -/
private lemma mem_induce_active_of_mem_R_of_has_parent
    {R : Finset (SWIGNode N)} {v : SWIGNode N}
    (hvR : v ∈ R) (hpar : G.dag.parents v ≠ ∅) :
    v ∈ (G.fixed.filter (fun s => iotaMap s ∈ R ∩ G.observed)) ∪
        (R ∩ G.observed) ∪
          (G.unobserved.filter (fun u => ∃ z ∈ R ∩ G.observed, G.dag.edge u z)) := by
  have hvNotFixed : v ∉ G.fixed := by
    intro hfix
    exact hpar (G.fixed_are_roots v hfix)
  have hne : (G.dag.parents v).Nonempty := Finset.nonempty_iff_ne_empty.mpr hpar
  obtain ⟨u, hu⟩ := hne
  have huv : G.dag.edge u v := G.dag.mem_parents.mp hu
  have hcls := (G.dag_edges_classified u v huv).2
  rcases Finset.mem_union.mp hcls with hleft | hunobs
  · rcases Finset.mem_union.mp hleft with hfix | hobs
    · exact (hvNotFixed hfix).elim
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvR, hobs⟩))
  · have : u ∈ G.dag.parents v := G.dag.mem_parents.mpr huv
    simp [G.unobs_are_roots v hunobs] at this

/-- Ambient edges between active vertices are precisely induced edges. -/
private lemma induced_edge_of_edge_of_active
    {R : Finset (SWIGNode N)} {u v : SWIGNode N}
    (he : G.dag.edge u v)
    (hu : u ∈ (G.fixed.filter (fun s => iotaMap s ∈ R ∩ G.observed)) ∪
        (R ∩ G.observed) ∪
          (G.unobserved.filter (fun x => ∃ z ∈ R ∩ G.observed, G.dag.edge x z)))
    (hv : v ∈ (G.fixed.filter (fun s => iotaMap s ∈ R ∩ G.observed)) ∪
        (R ∩ G.observed) ∪
          (G.unobserved.filter (fun x => ∃ z ∈ R ∩ G.observed, G.dag.edge x z))) :
    (G.induce R).dag.edge u v := by
  change (G.inducedDag
    ((G.fixed.filter (fun s => iotaMap s ∈ R ∩ G.observed)) ∪
      (R ∩ G.observed) ∪
        (G.unobserved.filter (fun x => ∃ z ∈ R ∩ G.observed, G.dag.edge x z)))).edge u v
  exact (G.inducedDag_edge_iff _ u v).mpr ⟨he, hu, hv⟩

/-- A directed ambient ancestor path whose start already has a parent survives
inside an ancestral induced SWIG. -/
private lemma induced_isAncestor_of_isAncestor_to_R_with_parent
    {R : Finset (SWIGNode N)} {u v : SWIGNode N}
    (hR : G.dag.ancestralSet R = R)
    (hanc : G.dag.isAncestor u v) (hvR : v ∈ R)
    (hupar : G.dag.parents u ≠ ∅) :
    (G.induce R).dag.isAncestor u v := by
  revert hvR
  induction hanc with
  | edge he =>
      rename_i b
      intro hvR
      have huR_anc : u ∈ G.dag.ancestralSet R :=
        G.dag.mem_ancestralSet_of_isAncestor hvR (DAG.isAncestor.edge he)
      have huR : u ∈ R := by simpa [hR] using huR_anc
      have hvpar : G.dag.parents b ≠ ∅ := by
        intro hempty
        have : u ∈ G.dag.parents b := G.dag.mem_parents.mpr he
        simp [hempty] at this
      have huAct := G.mem_induce_active_of_mem_R_of_has_parent huR hupar
      have hvAct := G.mem_induce_active_of_mem_R_of_has_parent hvR hvpar
      exact DAG.isAncestor.edge
        (G.induced_edge_of_edge_of_active he huAct hvAct)
  | trans h₁ he ih =>
      rename_i b c
      intro hvR
      have hwR_anc : b ∈ G.dag.ancestralSet R :=
        G.dag.mem_ancestralSet_of_isAncestor hvR (DAG.isAncestor.edge he)
      have hwR : b ∈ R := by simpa [hR] using hwR_anc
      have hInd₁ := ih hwR
      have hwpar : G.dag.parents b ≠ ∅ := G.dag.isAncestor_has_parent h₁
      have hvpar : G.dag.parents c ≠ ∅ := by
        intro hempty
        have : b ∈ G.dag.parents c := G.dag.mem_parents.mpr he
        simp [hempty] at this
      have hwAct := G.mem_induce_active_of_mem_R_of_has_parent hwR hwpar
      have hvAct := G.mem_induce_active_of_mem_R_of_has_parent hvR hvpar
      exact DAG.isAncestor.trans hInd₁
        (G.induced_edge_of_edge_of_active he hwAct hvAct)

/-- For a non-fixed vertex, membership in the ancestral set of
`X ∪ Y ∪ (Z ∪ fixed)` reduces to membership in the ancestral support `R`. -/
private lemma mem_R_of_ancestor_union_not_fixed
    {R X Y Z : Finset (SWIGNode N)}
    (hX : X ⊆ R ∩ G.observed) (hY : Y ⊆ R ∩ G.observed)
    (hZ : Z ⊆ R ∩ G.observed)
    (hR : G.dag.ancestralSet R = R)
    {v : SWIGNode N}
    (hvAnc : v ∈ G.dag.ancestralSet (X ∪ Y ∪ (Z ∪ G.fixed)))
    (hvNotFixed : v ∉ G.fixed) : v ∈ R := by
  rcases Finset.mem_union.mp hvAnc with hvBase | hvAnc'
  · rcases Finset.mem_union.mp hvBase with hvXY | hvZF
    · rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact (Finset.mem_inter.mp (hX hvX)).1
      · exact (Finset.mem_inter.mp (hY hvY)).1
    · rcases Finset.mem_union.mp hvZF with hvZ | hvF
      · exact (Finset.mem_inter.mp (hZ hvZ)).1
      · exact (hvNotFixed hvF).elim
  · simp only [DAG.ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hvAnc'
    obtain ⟨w, hw, hvw⟩ := hvAnc'
    rcases Finset.mem_union.mp hw with hwXY | hwZF
    · rcases Finset.mem_union.mp hwXY with hwX | hwY
      · have hvR_anc : v ∈ G.dag.ancestralSet R :=
          G.dag.mem_ancestralSet_of_isAncestor (Finset.mem_inter.mp (hX hwX)).1 hvw
        simpa [hR] using hvR_anc
      · have hvR_anc : v ∈ G.dag.ancestralSet R :=
          G.dag.mem_ancestralSet_of_isAncestor (Finset.mem_inter.mp (hY hwY)).1 hvw
        simpa [hR] using hvR_anc
    · rcases Finset.mem_union.mp hwZF with hwZ | hwF
      · have hvR_anc : v ∈ G.dag.ancestralSet R :=
          G.dag.mem_ancestralSet_of_isAncestor (Finset.mem_inter.mp (hZ hwZ)).1 hvw
        simpa [hR] using hvR_anc
      · exact ((G.not_isAncestor_to_fixed_mem hwF v) hvw).elim

/-- A collider activation witness for `Z ∪ fixed` whose collider has a parent
is already a collider activation witness for `Z` in the induced graph. -/
private lemma induced_bbZAncestors_of_ambient_union_fixed
    {R Z : Finset (SWIGNode N)} {m : SWIGNode N}
    (hZ : Z ⊆ R ∩ G.observed)
    (hR : G.dag.ancestralSet R = R)
    (hmpar : G.dag.parents m ≠ ∅)
    (hmAnc : m ∈ G.dag.bbZAncestors (Z ∪ G.fixed)) :
    m ∈ (G.induce R).dag.bbZAncestors Z := by
  unfold DAG.bbZAncestors DAG.ancestralSet at hmAnc ⊢
  rcases Finset.mem_union.mp hmAnc with hmBase | hmAnc'
  · rcases Finset.mem_union.mp hmBase with hmZ | hmF
    · exact Finset.mem_union_left _ hmZ
    · exact (hmpar (G.fixed_are_roots m hmF)).elim
  · simp only [DAG.ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmAnc' ⊢
    obtain ⟨w, hw, hmw⟩ := hmAnc'
    rcases Finset.mem_union.mp hw with hwZ | hwF
    · apply Finset.mem_union_right
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hwZ,
        G.induced_isAncestor_of_isAncestor_to_R_with_parent hR hmw
          (Finset.mem_inter.mp (hZ hwZ)).1 hmpar⟩
    · exact ((G.not_isAncestor_to_fixed_mem hwF m) hmw).elim

/-- Nodes on an active path given `Z ∪ fixed` between observed endpoints are
not members of the fixed intervention set. -/
private lemma activePath_node_not_fixed
    {R X Y Z : Finset (SWIGNode N)} {x y v : SWIGNode N} {p : List (SWIGNode N)}
    (hX : X ⊆ R ∩ G.observed) (hY : Y ⊆ R ∩ G.observed)
    (hxX : x ∈ X) (hyY : y ∈ Y)
    (hlen : p.length ≥ 2)
    (hact : G.dag.IsActivePath (Z ∪ G.fixed) p)
    (hhead : p.head? = some x) (hlast : p.getLast? = some y)
    (hv : v ∈ p) : v ∉ G.fixed := by
  rw [List.mem_iff_get] at hv
  obtain ⟨i, rfl⟩ := hv
  by_cases hi0 : i.val = 0
  · have hpne : p ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hhead_get : p.get ⟨0, by omega⟩ = x := by
      have h := List.head?_eq_some_head hpne
      rw [h] at hhead
      have hx_eq : p.head hpne = x := Option.some_inj.mp hhead
      rw [← hx_eq]
      simp [List.head_eq_getElem hpne]
    have hidx : i = ⟨0, by omega⟩ := Fin.ext hi0
    rw [hidx, hhead_get]
    exact G.not_mem_fixed_of_mem_observed (Finset.mem_inter.mp (hX hxX)).2
  · by_cases hilast : i.val = p.length - 1
    · have hpne : p ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hlast_get : p.get ⟨p.length - 1, by omega⟩ = y := by
        have h := List.getLast?_eq_some_getLast hpne
        rw [h] at hlast
        have hy_eq : p.getLast hpne = y := Option.some_inj.mp hlast
        rw [← hy_eq]
        exact (List.getLast_eq_getElem hpne).symm
      have hidx : i = ⟨p.length - 1, by omega⟩ := Fin.ext hilast
      rw [hidx, hlast_get]
      exact G.not_mem_fixed_of_mem_observed (Finset.mem_inter.mp (hY hyY)).2
    · have htri : (i.val - 1) + 2 < p.length := by omega
      have hclause := hact.2 (i.val - 1) htri
      have hrew₁ : i.val - 1 + 1 = i.val := by omega
      simp only [hrew₁] at hclause
      set l := p.get ⟨i.val - 1, by omega⟩ with hl
      set m := p.get ⟨i.val, i.isLt⟩ with hm
      set r := p.get ⟨i.val - 1 + 2, htri⟩ with hr
      by_cases hcoll : G.dag.IsCollider l m r
      · rw [if_pos hcoll] at hclause
        intro hmfix
        have hpar : l ∈ G.dag.parents m := G.dag.mem_parents.mpr hcoll.1
        have hroot := G.fixed_are_roots m hmfix
        simp [hroot] at hpar
      · rw [if_neg hcoll] at hclause
        intro hmfix
        exact hclause (Finset.mem_union_right _ hmfix)

/-- D-separation in an ancestral induced SWIG lifts to the ambient SWIG once
fixed intervention nodes are included in the conditioning set.

The classical contrapositive proof takes an ambient active path between observed
endpoints, uses ancestral closure to keep its non-fixed vertices inside the
induced support, and uses the extra fixed-node conditioning to rule out active
paths that pass through fixed roots. The remaining bookkeeping is to translate
each surviving ambient edge into the induced edge relation, including collider
activation witnesses whose directed descendant paths remain inside the
ancestral support. -/
theorem dSep_union_fixed_of_induce_dSep
    (R X Y Z : Finset (SWIGNode N))
    (hX : X ⊆ R ∩ G.observed) (hY : Y ⊆ R ∩ G.observed)
    (hZ : Z ⊆ R ∩ G.observed)
    (hR : G.dag.ancestralSet R = R)
    (h : (G.induce R).dag.dSep X Y Z) :
    G.dag.dSep X Y (Z ∪ G.fixed) := by
  rcases h with ⟨hXY, hXZ, hYZ, hReach⟩
  refine ⟨hXY, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hxX hxZf
    rcases Finset.mem_union.mp hxZf with hxZ | hxF
    · exact Finset.disjoint_left.mp hXZ hxX hxZ
    · exact G.not_mem_fixed_of_mem_observed ((Finset.mem_inter.mp (hX hxX)).2) hxF
  · rw [Finset.disjoint_left]
    intro y hyY hyZf
    rcases Finset.mem_union.mp hyZf with hyZ | hyF
    · exact Finset.disjoint_left.mp hYZ hyY hyZ
    · exact G.not_mem_fixed_of_mem_observed ((Finset.mem_inter.mp (hY hyY)).2) hyF
  rw [Finset.disjoint_left]
  intro y hyReach hyY
  rw [G.dag.bbReachableVertices_iff_activePath] at hyReach
  obtain ⟨x, hxX, p, hlen, hact, hhead, hlast⟩ := hyReach
  have hnotFixed : ∀ v ∈ p, v ∉ G.fixed := by
    intro v hv
    exact G.activePath_node_not_fixed hX hY hxX hyY hlen hact hhead hlast hv
  have hnodeR : ∀ v ∈ p, v ∈ R := by
    intro v hv
    have hvAnc : v ∈ G.dag.ancestralSet (X ∪ Y ∪ (Z ∪ G.fixed)) :=
      G.dag.activePath_nodes_are_ancestors hxX hyY hact hhead hlast v hv
    exact G.mem_R_of_ancestor_union_not_fixed hX hY hZ hR hvAnc (hnotFixed v hv)
  let active : Finset (SWIGNode N) :=
    (G.fixed.filter (fun s => iotaMap s ∈ R ∩ G.observed)) ∪
      (R ∩ G.observed) ∪
        (G.unobserved.filter (fun u => ∃ z ∈ R ∩ G.observed, G.dag.edge u z))
  have hactive_of_incident :
      ∀ {v : SWIGNode N}, v ∈ p →
        (∃ w ∈ R, G.dag.edge v w ∨ G.dag.edge w v) → v ∈ active := by
    intro v hv hinc
    exact G.mem_induce_active_of_mem_R_of_not_fixed_of_incident
      (hnodeR v hv) (hnotFixed v hv) hinc
  have hIndEdge :
      ∀ {u v : SWIGNode N}, G.dag.edge u v → u ∈ active → v ∈ active →
        (G.induce R).dag.edge u v := by
    intro u v huv hu hv
    exact G.induced_edge_of_edge_of_active huv hu hv
  have hactInd : (G.induce R).dag.IsActivePath Z p := by
    refine ⟨?_, ?_⟩
    · intro i hi
      let u := p.get ⟨i, by omega⟩
      let v := p.get ⟨i + 1, hi⟩
      have huMem : u ∈ p := List.get_mem _ _
      have hvMem : v ∈ p := List.get_mem _ _
      rcases hact.1 i hi with huv | hvu
      · have huAct : u ∈ active := hactive_of_incident huMem
          ⟨v, hnodeR v hvMem, Or.inl huv⟩
        have hvAct : v ∈ active := hactive_of_incident hvMem
          ⟨u, hnodeR u huMem, Or.inr huv⟩
        exact Or.inl (hIndEdge huv huAct hvAct)
      · have huAct : u ∈ active := hactive_of_incident huMem
          ⟨v, hnodeR v hvMem, Or.inr hvu⟩
        have hvAct : v ∈ active := hactive_of_incident hvMem
          ⟨u, hnodeR u huMem, Or.inl hvu⟩
        exact Or.inr (hIndEdge hvu hvAct huAct)
    · intro i hi
      let l := p.get ⟨i, by omega⟩
      let m := p.get ⟨i + 1, by omega⟩
      let r := p.get ⟨i + 2, hi⟩
      have hlMem : l ∈ p := List.get_mem _ _
      have hmMem : m ∈ p := List.get_mem _ _
      have hrMem : r ∈ p := List.get_mem _ _
      have hambClause := hact.2 i hi
      by_cases hcollInd : (G.induce R).dag.IsCollider l m r
      · rw [if_pos hcollInd]
        have hlmAmb : G.dag.edge l m := by
          change (G.inducedDag active).edge l m ∧
              (G.inducedDag active).edge r m at hcollInd
          exact ((G.inducedDag_edge_iff active l m).mp hcollInd.1).1
        have hrmAmb : G.dag.edge r m := by
          change (G.inducedDag active).edge l m ∧
              (G.inducedDag active).edge r m at hcollInd
          exact ((G.inducedDag_edge_iff active r m).mp hcollInd.2).1
        have hcollAmb : G.dag.IsCollider l m r := ⟨hlmAmb, hrmAmb⟩
        rw [if_pos hcollAmb] at hambClause
        have hmpar : G.dag.parents m ≠ ∅ := by
          intro hempty
          have : l ∈ G.dag.parents m := G.dag.mem_parents.mpr hlmAmb
          simp [hempty] at this
        exact G.induced_bbZAncestors_of_ambient_union_fixed hZ hR hmpar hambClause
      · rw [if_neg hcollInd]
        intro hmZ
        by_cases hcollAmb : G.dag.IsCollider l m r
        · have hlAct : l ∈ active := hactive_of_incident hlMem
            ⟨m, hnodeR m hmMem, Or.inl hcollAmb.1⟩
          have hmAct : m ∈ active := hactive_of_incident hmMem
            ⟨l, hnodeR l hlMem, Or.inr hcollAmb.1⟩
          have hrAct : r ∈ active := hactive_of_incident hrMem
            ⟨m, hnodeR m hmMem, Or.inl hcollAmb.2⟩
          have hcollInd' : (G.induce R).dag.IsCollider l m r :=
            ⟨hIndEdge hcollAmb.1 hlAct hmAct,
              hIndEdge hcollAmb.2 hrAct hmAct⟩
          exact hcollInd hcollInd'
        · rw [if_neg hcollAmb] at hambClause
          exact hambClause (Finset.mem_union_left _ hmZ)
  have hyReachInd : y ∈ (G.induce R).dag.bbReachableVertices Z X := by
    rw [(G.induce R).dag.bbReachableVertices_iff_activePath]
    exact ⟨x, hxX, p, hlen, hactInd, hhead, hlast⟩
  exact Finset.disjoint_left.mp hReach hyReachInd hyY

end SWIGGraph

end Causalean
