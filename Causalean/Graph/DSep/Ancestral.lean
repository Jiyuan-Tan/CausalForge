/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Ancestral reduction of d-separation

This file proves the classical *ancestral reduction* result: every vertex on an
active path between `X` and `Y` given `Z` lies inside the ancestral set
`ancestralSet (X ∪ Y ∪ Z)`. It also provides finset corollaries used when
reasoning about Bayes Ball witnesses.

The endpoint corollary exposed downstream is

    `bbReachableVertices_inter_subset_ancestralSet :
        (G.bbReachableVertices Z X) ∩ Y ⊆ G.ancestralSet (X ∪ Y ∪ Z)`

It says only that a reachable target endpoint already lies in the ancestral set
because it is in `Y`. The stronger active-path witness statement is
`activePath_witness_subset_ancestralSet`.

## Main results

* `DAG.activePath_nodes_are_ancestors` — every node on an active `X-Y` path,
  given `Z`, lies in `ancestralSet (X ∪ Y ∪ Z)`. (Core ancestral lemma.)
* `DAG.bbReachableVertices_inter_subset_ancestralSet` — endpoint inclusion for
  reachable targets in finset form.

## References

* Pearl (2009), Causality (2nd ed.), §1.2.3 (ancestral graphs)
* Verma & Pearl (1990), *Equivalence and synthesis of causal models*
-/

import Causalean.Graph.DSep.Separation

/-! # Ancestral Reduction for d-Separation

This file proves that active paths relevant to a d-separation query can be
restricted to the ancestral set of the source, target, and conditioning
vertices. The resulting finset lemmas distinguish the trivial reachable-target
endpoint inclusion from the stronger statement about all nodes on a witnessing
active path. -/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

-- ============================================================
-- Auxiliary lemmas about `ancestralSet`
-- ============================================================

/-- `S ⊆ ancestralSet S`: every member is in its own ancestral set. -/
lemma subset_ancestralSet (S : Finset V) : S ⊆ G.ancestralSet S := by
  intro v hv
  exact Finset.mem_union_left _ hv

/-- `ancestralSet` is monotone in its argument. -/
lemma ancestralSet_mono {S T : Finset V} (h : S ⊆ T) :
    G.ancestralSet S ⊆ G.ancestralSet T := by
  intro v hv
  rcases Finset.mem_union.mp hv with hvS | hvA
  · exact Finset.mem_union_left _ (h hvS)
  · simp only [ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hvA
    obtain ⟨w, hwS, haw⟩ := hvA
    exact Finset.mem_union_right _
      (by simp only [ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w, h hwS, haw⟩)

/-- If `u` is an ancestor of some vertex `w ∈ S`, then `u ∈ ancestralSet S`. -/
lemma mem_ancestralSet_of_isAncestor
    {u w : V} {S : Finset V} (hwS : w ∈ S) (h : G.isAncestor u w) :
    u ∈ G.ancestralSet S := by
  apply Finset.mem_union_right
  simp only [ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨w, hwS, h⟩

/-- `bbZAncestors Z ⊆ ancestralSet S` whenever `Z ⊆ S`. Used to lift a
    collider-activation witness `m ∈ bbZAncestors Z` into the larger
    `ancestralSet (X ∪ Y ∪ Z)`. -/
lemma bbZAncestors_subset_ancestralSet_of_subset
    {Z S : Finset V} (hZS : Z ⊆ S) :
    G.bbZAncestors Z ⊆ G.ancestralSet S := by
  unfold bbZAncestors
  exact G.ancestralSet_mono hZS

-- ============================================================
-- Reading edges off an active path
-- ============================================================

/-- A non-collider triple `(l, m, r)` has at least one outgoing edge from `m`. -/
lemma nonCollider_has_outgoing
    {l m r : V} (hadj_lm : G.UAdj l m) (hadj_mr : G.UAdj m r)
    (hnc : ¬ G.IsCollider l m r) :
    G.edge m l ∨ G.edge m r := by
  -- IsCollider l m r := G.edge l m ∧ G.edge r m
  -- ¬ collider means ¬ edge l m ∨ ¬ edge r m.
  -- Combined with UAdj giving edge ∨ reverse, deduce one outgoing.
  unfold IsCollider at hnc
  push_neg at hnc
  rcases hadj_lm with hlm | hml
  · -- edge l m: then ¬ edge r m (else collider). So edge m r (by UAdj m r).
    have hnr : ¬ G.edge r m := hnc hlm
    rcases hadj_mr with hmr | hrm
    · exact Or.inr hmr
    · exact absurd hrm hnr
  · -- edge m l: outgoing on the left.
    exact Or.inl hml

/-- If an edge points into the ancestral set of `S`, then its tail is also in
    the ancestral set of `S`. -/
private lemma mem_ancestralSet_of_edge_to_mem
    {u v : V} {S : Finset V} (huv : G.edge u v)
    (hv : v ∈ G.ancestralSet S) :
    u ∈ G.ancestralSet S := by
  rcases Finset.mem_union.mp hv with hvS | hvA
  · exact G.mem_ancestralSet_of_isAncestor hvS (isAncestor.edge huv)
  · apply Finset.mem_union_right
    simp only [ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hvA ⊢
    obtain ⟨w, hwS, hvw⟩ := hvA
    exact ⟨w, hwS, G.isAncestor_trans (isAncestor.edge huv) hvw⟩

/-- Walking right along a directed edge in an active path reaches either the
    endpoint or an active collider; in both cases the starting node is in the
    target ancestral set. -/
private theorem walk_right_witness
    {S Z : Finset V} {p : List V} {y : V}
    (hZS : Z ⊆ S) (hyS : y ∈ S)
    (hp : G.IsActivePath Z p) (hlast : p.getLast? = some y)
    (j : ℕ) (hj : j + 1 < p.length)
    (hedge : G.edge (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, hj⟩)) :
    p.get ⟨j, by omega⟩ ∈ G.ancestralSet S := by
  by_cases hnext_last : j + 1 = p.length - 1
  · have hpos : 0 < p.length := by omega
    have hpne : p ≠ [] := List.ne_nil_of_length_pos hpos
    have hlast_get : p.get ⟨p.length - 1, by omega⟩ = y := by
      have h := List.getLast?_eq_some_getLast hpne
      rw [h] at hlast
      have hy_eq : p.getLast hpne = y := Option.some_inj.mp hlast
      rw [← hy_eq]
      exact (List.getLast_eq_getElem hpne).symm
    apply G.mem_ancestralSet_of_edge_to_mem hedge
    have hidx : (⟨j + 1, hj⟩ : Fin p.length) = ⟨p.length - 1, by omega⟩ :=
      Fin.ext hnext_last
    rw [hidx, hlast_get]
    exact G.subset_ancestralSet S hyS
  · have htri : j + 2 < p.length := by omega
    have hcoll_clause := hp.2 j htri
    set l := p.get ⟨j, by omega⟩ with hl_def
    set m := p.get ⟨j + 1, by omega⟩ with hm_def
    set r := p.get ⟨j + 2, htri⟩ with hr_def
    by_cases hcoll : G.IsCollider l m r
    · rw [if_pos hcoll] at hcoll_clause
      apply G.mem_ancestralSet_of_edge_to_mem hedge
      exact G.bbZAncestors_subset_ancestralSet_of_subset hZS hcoll_clause
    · rw [if_neg hcoll] at hcoll_clause
      have hadj_next := hp.1 (j + 1) htri
      have hmr : G.edge (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, htri⟩) := by
        have hlm : G.edge l m := by
          simpa [hl_def, hm_def] using hedge
        rcases hadj_next with hmr | hrm
        · exact hmr
        · exfalso
          apply hcoll
          exact ⟨hlm, by simpa [hm_def, hr_def] using hrm⟩
      have hm_anc : p.get ⟨j + 1, by omega⟩ ∈ G.ancestralSet S :=
        walk_right_witness hZS hyS hp hlast (j + 1) htri hmr
      exact G.mem_ancestralSet_of_edge_to_mem hedge hm_anc
termination_by p.length - 1 - j
decreasing_by omega

/-- Symmetric leftward version of `walk_right_witness`. -/
private theorem walk_left_witness
    {S Z : Finset V} {p : List V} {x : V}
    (hZS : Z ⊆ S) (hxS : x ∈ S)
    (hp : G.IsActivePath Z p) (hhead : p.head? = some x)
    (j : ℕ) (hjpos : 0 < j) (hj : j < p.length)
    (hedge : G.edge (p.get ⟨j, hj⟩) (p.get ⟨j - 1, by omega⟩)) :
    p.get ⟨j, hj⟩ ∈ G.ancestralSet S := by
  by_cases hprev_first : j - 1 = 0
  · have hpos : 0 < p.length := by omega
    have hpne : p ≠ [] := List.ne_nil_of_length_pos hpos
    have hhead_get : p.get ⟨0, hpos⟩ = x := by
      have h := List.head?_eq_some_head hpne
      rw [h] at hhead
      have hx_eq : p.head hpne = x := Option.some_inj.mp hhead
      rw [← hx_eq]
      simp [List.head_eq_getElem hpne]
    apply G.mem_ancestralSet_of_edge_to_mem hedge
    have hidx : (⟨j - 1, by omega⟩ : Fin p.length) = ⟨0, hpos⟩ :=
      Fin.ext hprev_first
    rw [hidx, hhead_get]
    exact G.subset_ancestralSet S hxS
  · have htri : (j - 2) + 2 < p.length := by omega
    have hcoll_clause := hp.2 (j - 2) htri
    have hprev_adj : (j - 2) + 1 < p.length := by omega
    have hprev : j - 1 < p.length := by omega
    set l := p.get ⟨j - 2, by omega⟩ with hl_def
    set m := p.get ⟨j - 1, hprev⟩ with hm_def
    set r := p.get ⟨j, hj⟩ with hr_def
    have hprev_rew : j - 2 + 1 = j - 1 := by omega
    have hcur_rew : j - 2 + 2 = j := by omega
    simp only [hprev_rew, hcur_rew] at hcoll_clause
    by_cases hcoll : G.IsCollider l m r
    · rw [if_pos hcoll] at hcoll_clause
      apply G.mem_ancestralSet_of_edge_to_mem hedge
      exact G.bbZAncestors_subset_ancestralSet_of_subset hZS hcoll_clause
    · rw [if_neg hcoll] at hcoll_clause
      have hadj_prev := hp.1 (j - 2) hprev_adj
      have hml : G.edge (p.get ⟨j - 1, hprev⟩) (p.get ⟨j - 2, by omega⟩) := by
        have hrm : G.edge r m := by
          simpa [hr_def, hm_def] using hedge
        have hmid_eq : (⟨j - 2 + 1, hprev_adj⟩ : Fin p.length) =
            ⟨j - 1, hprev⟩ := Fin.ext (by omega)
        rcases hadj_prev with hlm | hml
        · exfalso
          apply hcoll
          exact ⟨by simpa [hl_def, hm_def, hmid_eq] using hlm, hrm⟩
        · simpa [hmid_eq] using hml
      have hm_anc : p.get ⟨j - 1, hprev⟩ ∈ G.ancestralSet S :=
        walk_left_witness hZS hxS hp hhead (j - 1) (by omega) hprev hml
      exact G.mem_ancestralSet_of_edge_to_mem hedge hm_anc
termination_by j
decreasing_by omega

-- ============================================================
-- Core: every node on an active path is in the ancestral set
-- ============================================================

/-- Walking forward from a non-collider in an active path, we either reach the
    end of the path (giving an ancestor witness in `Y` via the endpoint) or
    we hit a collider node (which is in `bbZAncestors Z` and hence in the
    ancestral set). In either case, the starting node is an ancestor of some
    member of `X ∪ Y ∪ Z`, hence in `ancestralSet (X ∪ Y ∪ Z)`.

    The proof tracks a directed sub-path forward or backward from each
    interior non-collider until it hits an endpoint or an active collider. -/
private theorem walk_forward_witness
    {X Y Z : Finset V} {p : List V} {x y : V}
    (hxX : x ∈ X) (hyY : y ∈ Y)
    (hp : G.IsActivePath Z p)
    (hhead : p.head? = some x) (hlast : p.getLast? = some y)
    (i : ℕ) (hi : i < p.length) :
    p.get ⟨i, hi⟩ ∈ G.ancestralSet (X ∪ Y ∪ Z) := by
  -- Endpoint cases close immediately. Interior non-colliders walk along an
  -- outgoing edge until they reach an endpoint or an active collider.
  have hpos : 0 < p.length := by omega
  have hpne : p ≠ [] := List.ne_nil_of_length_pos hpos
  by_cases hi0 : i = 0
  · -- i = 0: p.get 0 = x ∈ X
    have hhead_get : p.get ⟨0, hpos⟩ = x := by
      have h := List.head?_eq_some_head hpne
      rw [h] at hhead
      have hx_eq : p.head hpne = x := Option.some_inj.mp hhead
      rw [← hx_eq]
      simp [List.head_eq_getElem hpne]
    have hi_eq : (⟨i, hi⟩ : Fin p.length) = ⟨0, hpos⟩ := Fin.ext hi0
    rw [hi_eq, hhead_get]
    apply G.subset_ancestralSet
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hxX)
  · -- i ≥ 1
    by_cases hiend : i = p.length - 1
    · -- last position: p.get (p.length-1) = y ∈ Y
      have hlast_get : p.get ⟨p.length - 1, by omega⟩ = y := by
        have h := List.getLast?_eq_some_getLast hpne
        rw [h] at hlast
        have hy_eq : p.getLast hpne = y := Option.some_inj.mp hlast
        rw [← hy_eq]
        exact (List.getLast_eq_getElem hpne).symm
      have hi_eq : (⟨i, hi⟩ : Fin p.length) = ⟨p.length - 1, by omega⟩ :=
        Fin.ext hiend
      rw [hi_eq, hlast_get]
      apply G.subset_ancestralSet
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hyY)
    · -- 0 < i < p.length - 1: interior node. Two sub-cases on collider/non-collider.
      -- Set up the triple (p.get (i-1), p.get i, p.get (i+1)).
      have hi_ge_1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hi_succ : i + 1 < p.length := by omega
      -- The collider/non-collider clause from IsActivePath at index i-1.
      have hk_idx : (i - 1) + 2 < p.length := by omega
      have hcoll_clause := hp.2 (i - 1) hk_idx
      -- Reindex i-1+1 = i, i-1+2 = i+1.
      have hi_rew : i - 1 + 1 = i := by omega
      have hi2_rew : i - 1 + 2 = i + 1 := by omega
      simp only [hi_rew, hi2_rew] at hcoll_clause
      set l := p.get ⟨i - 1, by omega⟩ with hl_def
      set m := p.get ⟨i, hi⟩ with hm_def
      set r := p.get ⟨i + 1, hi_succ⟩ with hr_def
      by_cases hcoll : G.IsCollider l m r
      · -- Collider case: m ∈ bbZAncestors Z ⊆ ancestralSet (X ∪ Y ∪ Z).
        rw [if_pos hcoll] at hcoll_clause
        -- hcoll_clause : m ∈ G.bbZAncestors Z
        have hZsub : Z ⊆ X ∪ Y ∪ Z := by
          intro v hv; exact Finset.mem_union_right _ hv
        exact G.bbZAncestors_subset_ancestralSet_of_subset hZsub hcoll_clause
      · -- Non-collider case: walk in the outgoing direction.
        have hadj_lm : G.UAdj l m := by
          have h := hp.1 (i - 1) (by omega)
          simpa [hl_def, hm_def, hi_rew] using h
        have hadj_mr : G.UAdj m r := by
          have h := hp.1 i hi_succ
          simpa [hm_def, hr_def] using h
        have hZsub : Z ⊆ X ∪ Y ∪ Z := by
          intro v hv; exact Finset.mem_union_right _ hv
        rcases G.nonCollider_has_outgoing hadj_lm hadj_mr hcoll with hml | hmr
        · have hxS : x ∈ X ∪ Y ∪ Z :=
            Finset.mem_union_left _ (Finset.mem_union_left _ hxX)
          exact G.walk_left_witness hZsub hxS hp hhead i (by omega) hi
            (by simpa [hm_def, hl_def] using hml)
        · have hyS : y ∈ X ∪ Y ∪ Z :=
            Finset.mem_union_left _ (Finset.mem_union_right _ hyY)
          exact G.walk_right_witness hZsub hyS hp hlast i hi_succ
            (by simpa [hm_def, hr_def] using hmr)

/-- **Active-path nodes lie in the ancestral set.**

    For any active path `p` from `x ∈ X` to `y ∈ Y` given `Z`, every node on
    `p` is in `ancestralSet (X ∪ Y ∪ Z)`. This is the main classical lemma
    used to justify ancestral reduction of d-separation.

    The per-index witness is supplied by `walk_forward_witness`. -/
theorem activePath_nodes_are_ancestors
    {X Y Z : Finset V} {x y : V} {p : List V}
    (hxX : x ∈ X) (hyY : y ∈ Y)
    (hp : G.IsActivePath Z p)
    (hhead : p.head? = some x) (hlast : p.getLast? = some y) :
    ∀ v ∈ p, v ∈ G.ancestralSet (X ∪ Y ∪ Z) := by
  intro v hv
  -- Convert `v ∈ p` to an index witness, then invoke `walk_forward_witness`.
  rw [List.mem_iff_get] at hv
  obtain ⟨i, hieq⟩ := hv
  rw [← hieq]
  exact G.walk_forward_witness hxX hyY hp hhead hlast i.val i.isLt

-- ============================================================
-- Endpoint corollary: BFS-reachable vertex in Y is in the ancestral set
-- ============================================================

/-- **BFS-reachable target lands in the ancestral set.**

    If `v ∈ bbReachableVertices Z X` and `v ∈ Y`, then `v ∈ ancestralSet
    (X ∪ Y ∪ Z)`. The endpoint `v` is in `Y ⊆ X ∪ Y ∪ Z ⊆ ancestralSet
    (X ∪ Y ∪ Z)` directly — no path-walk needed.

    The deeper "every internal node of the witnessing path lies in the
    ancestral set" is captured separately by
    `activePath_witness_subset_ancestralSet`. -/
theorem bbReachableVertices_inter_subset_ancestralSet
    (X Y Z : Finset V) :
    (G.bbReachableVertices Z X) ∩ Y ⊆ G.ancestralSet (X ∪ Y ∪ Z) := by
  intro v hv
  rw [Finset.mem_inter] at hv
  obtain ⟨_, hvY⟩ := hv
  -- v ∈ Y ⊆ X ∪ Y ∪ Z ⊆ ancestralSet (X ∪ Y ∪ Z): trivial endpoint inclusion.
  apply G.subset_ancestralSet
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hvY)

-- ============================================================
-- Inner-node version: any *intermediate* node of an active X-Y path is
-- in the ancestral set. This is the genuinely informative form.
-- ============================================================

/-- **Active-path inner nodes lie in the ancestral set** (informative form).

    Specialization of `activePath_nodes_are_ancestors` to a witness
    expressed via `bbReachableVertices`. If `v ∈ Y` is BFS-reachable from
    `X` given `Z`, then for every node `w` along the witnessing active
    path, `w ∈ ancestralSet (X ∪ Y ∪ Z)`. -/
theorem activePath_witness_subset_ancestralSet
    {X Y Z : Finset V} {v : V}
    (hvR : v ∈ G.bbReachableVertices Z X) (hvY : v ∈ Y) :
    ∃ (p : List V) (x : V), x ∈ X ∧ p.length ≥ 2 ∧
      G.IsActivePath Z p ∧ p.head? = some x ∧ p.getLast? = some v ∧
      ∀ w ∈ p, w ∈ G.ancestralSet (X ∪ Y ∪ Z) := by
  -- Pull an active path witness from `bbReachableVertices_iff_activePath`,
  -- then apply `activePath_nodes_are_ancestors`.
  obtain ⟨x, hxX, p, hlen, hact, hhead, hlast⟩ :=
    (G.bbReachableVertices_iff_activePath X Z v).mp hvR
  exact ⟨p, x, hxX, hlen, hact, hhead, hlast,
    G.activePath_nodes_are_ancestors hxX hvY hact hhead hlast⟩

-- ============================================================
-- Ancestral intersection from d-separation (graph-theoretic core)
-- ============================================================

/-- A *forward*-directed path avoiding `Z` is an active path given `Z`.
    "Forward-directed" means each edge points from the *earlier* index to the
    *later* index. Every interior vertex is then a non-collider (incoming +
    outgoing), and by the avoidance hypothesis none is in `Z`. -/
theorem isActivePath_of_directed
    {Z : Finset V} {p : List V}
    (hdir : ∀ (i : ℕ) (hi : i + 1 < p.length),
        G.edge (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩))
    (hZ : ∀ x ∈ p, x ∉ Z) :
    G.IsActivePath Z p := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · -- Adjacency: G.edge p[i] p[i+1] gives UAdj.
    exact Or.inl (hdir i hi)
  · -- Non-collider: edge from p[i+1] to p[i+2], so ¬ edge p[i+2] p[i+1].
    simp only
    have hmr : G.edge (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) :=
      hdir (i + 1) hi
    have hrm_false : ¬ G.edge (p.get ⟨i + 2, hi⟩) (p.get ⟨i + 1, by omega⟩) :=
      G.asymm hmr
    have hnotcoll : ¬ G.IsCollider (p.get ⟨i, by omega⟩)
                      (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) := by
      intro ⟨_, h2⟩; exact hrm_false h2
    rw [if_neg hnotcoll]
    exact hZ _ (List.get_mem _ _)

/-- An ancestor `u` of some `v ∈ S`, with `u ∉ ancestralSet Z`, gives a
    forward-directed *active path* from `u` to `v` given `Z`. The internal
    nodes of the path are also ancestors of `v` (hence members of
    `ancestralSet S` for any `S ∋ v`). -/
private theorem exists_activePath_of_ancestor_avoiding
    {Z : Finset V} {u v : V} (huv : G.isAncestor u v)
    (huZ : u ∉ G.ancestralSet Z) :
    ∃ (p : List V), p.length ≥ 2 ∧ p.head? = some u ∧ p.getLast? = some v ∧
      G.IsActivePath Z p := by
  obtain ⟨p, hlen, hhead, hlast, hedge, hZavoid⟩ :=
    G.exists_directedPath_avoiding huv huZ
  exact ⟨p, hlen, hhead, hlast, G.isActivePath_of_directed hedge hZavoid⟩

/-- **Fork-path active-ness.** If `xp` is a directed path from `u` to `x`
    avoiding `Z` and `yp` is a directed path from `u` to `y` avoiding `Z`,
    and `u ∉ Z`, then the path `xp.reverse ++ yp.tail` is an active path
    from `x` to `y` given `Z` (with `u` as a fork at the seam). -/
private theorem fork_isActivePath
    {Z : Finset V} {u x y : V} {xp yp : List V}
    (hxp_len : xp.length ≥ 2) (hxp_head : xp.head? = some u)
    (hxp_last : xp.getLast? = some x)
    (hxp_edge : ∀ (i : ℕ) (hi : i + 1 < xp.length),
        G.edge (xp.get ⟨i, by omega⟩) (xp.get ⟨i + 1, hi⟩))
    (hxp_Z : ∀ z ∈ xp, z ∉ Z)
    (hyp_len : yp.length ≥ 2) (hyp_head : yp.head? = some u)
    (hyp_last : yp.getLast? = some y)
    (hyp_edge : ∀ (i : ℕ) (hi : i + 1 < yp.length),
        G.edge (yp.get ⟨i, by omega⟩) (yp.get ⟨i + 1, hi⟩))
    (hyp_Z : ∀ z ∈ yp, z ∉ Z) :
    let p := xp.reverse ++ yp.tail
    p.length ≥ 2 ∧ p.head? = some x ∧ p.getLast? = some y ∧
      G.IsActivePath Z p := by
  -- yp.head = u, yp.tail = yp without u
  have hyp_ne : yp ≠ [] := by
    intro h; rw [h] at hyp_len; simp at hyp_len
  have hxp_ne : xp ≠ [] := by
    intro h; rw [h] at hxp_len; simp at hxp_len
  have hxpRev_ne : xp.reverse ≠ [] := by simp [hxp_ne]
  -- yp.head hyp_ne = u
  have hyp_head_eq : yp.head hyp_ne = u := by
    have h := List.head?_eq_some_head hyp_ne
    rw [hyp_head] at h
    exact (Option.some_inj.mp h.symm)
  -- xp.getLast hxp_ne = x
  have hxp_last_eq : xp.getLast hxp_ne = x := by
    have h := List.getLast?_eq_some_getLast hxp_ne
    rw [hxp_last] at h
    exact (Option.some_inj.mp h.symm)
  -- xp.head hxp_ne = u
  have hxp_head_eq : xp.head hxp_ne = u := by
    have h := List.head?_eq_some_head hxp_ne
    rw [hxp_head] at h
    exact (Option.some_inj.mp h.symm)
  -- yp.getLast hyp_ne = y
  have hyp_last_eq : yp.getLast hyp_ne = y := by
    have h := List.getLast?_eq_some_getLast hyp_ne
    rw [hyp_last] at h
    exact (Option.some_inj.mp h.symm)
  -- yp = u :: yp.tail
  have hyp_decomp : yp = u :: yp.tail := by
    conv_lhs => rw [← List.cons_head_tail hyp_ne]
    rw [hyp_head_eq]
  -- yp.tail length = yp.length - 1
  have hyp_tail_len : yp.tail.length = yp.length - 1 := List.length_tail
  -- yp.tail nonempty since yp.length ≥ 2
  have hyp_tail_ne : yp.tail ≠ [] := by
    rw [← List.length_pos_iff, hyp_tail_len]; omega
  set p := xp.reverse ++ yp.tail with hp_def
  have hp_len_eq : p.length = xp.length + yp.length - 1 := by
    simp only [hp_def, List.length_append, List.length_reverse,
      hyp_tail_len]
    omega
  have hp_len : p.length ≥ 2 := by rw [hp_len_eq]; omega
  -- head p = head xp.reverse = last xp = x
  have hp_head : p.head? = some x := by
    simp only [hp_def, List.head?_append_of_ne_nil _ hxpRev_ne,
               List.head?_reverse]
    rw [hxp_last]
  -- last p = last yp.tail = last yp = y
  have hp_last : p.getLast? = some y := by
    have hlast_tail : yp.tail.getLast? = some y := by
      -- yp = [u] ++ yp.tail, so getLast? = yp.tail.getLast? when yp.tail ≠ [].
      have heq : yp = [u] ++ yp.tail := by simpa using hyp_decomp
      have := List.getLast?_append_of_ne_nil [u] hyp_tail_ne
      rw [← heq] at this
      rw [← this]; exact hyp_last
    simp only [hp_def, List.getLast?_append, hlast_tail]
    rfl
  refine ⟨hp_len, hp_head, hp_last, ?_⟩
  -- Now show `IsActivePath Z p`.
  -- Layout: p[k] = xp.reverse[k] = xp[xp.length - 1 - k] for k < xp.length.
  --         p[k] = yp.tail[k - xp.length] = yp[k - xp.length + 1] for k ≥ xp.length.
  -- The seam is at k = xp.length - 1 (= u, since xp.reverse[xp.length-1] = xp[0] = u),
  -- and k = xp.length is yp.tail[0] = yp[1].
  set R := xp.length with hR_def
  have hxpRev_len : xp.reverse.length = R := List.length_reverse
  have hp_len_eq2 : p.length = R + yp.tail.length := by
    simp only [hp_def, List.length_append, hxpRev_len]
  have hp_L : ∀ (k : ℕ) (hkR : k < R),
      p.get ⟨k, by rw [hp_len_eq2]; omega⟩ =
      xp.get ⟨R - 1 - k, by omega⟩ := by
    intro k hkR
    have hk_rev : k < xp.reverse.length := by rw [hxpRev_len]; exact hkR
    simp only [hp_def, List.get_eq_getElem,
      List.getElem_append_left (h := hk_rev), List.getElem_reverse]
    change xp[xp.length - 1 - k] = xp[R - 1 - k]
    congr 1
  have hp_R : ∀ (k : ℕ) (hkL : R ≤ k) (hk : k < p.length),
      p.get ⟨k, hk⟩ =
      yp.get ⟨k - R + 1, by
        rw [hp_len_eq2, hyp_tail_len] at hk; omega⟩ := by
    intro k hkL hk
    have hk_rev : xp.reverse.length ≤ k := by rw [hxpRev_len]; exact hkL
    have htail_idx_lt : k - xp.reverse.length < yp.tail.length := by
      rw [hxpRev_len, hyp_tail_len]
      rw [hp_len_eq2, hyp_tail_len] at hk; omega
    have htail_yp_idx_lt : k - R + 1 < yp.length := by
      rw [hp_len_eq2, hyp_tail_len] at hk; omega
    -- yp.tail[j] = yp[j+1] via cons decomposition
    have hyp_tail_get : ∀ (j : ℕ) (hj1 : j < yp.tail.length) (hj2 : j + 1 < yp.length),
        yp.tail[j]'hj1 = yp[j + 1]'hj2 := by
      intro j hj1 hj2
      have : yp[j + 1] = (u :: yp.tail)[j + 1]'(by rw [← hyp_decomp]; exact hj2) := by
        congr 1
      rw [this]
      simp [List.getElem_cons_succ]
    -- Compute p.get
    have hpget : p.get ⟨k, hk⟩ = yp.tail[k - xp.reverse.length]'htail_idx_lt := by
      simp only [hp_def, List.get_eq_getElem,
        List.getElem_append_right hk_rev]
    rw [hpget]
    have hidx_eq : k - xp.reverse.length = k - R := by rw [hxpRev_len]
    rw [show yp.tail[k - xp.reverse.length]'htail_idx_lt =
         yp.tail[k - R]'(by rw [← hidx_eq]; exact htail_idx_lt) from
      by congr 1]
    rw [hyp_tail_get (k - R) (by rw [hyp_tail_len]; omega) htail_yp_idx_lt]
    simp [List.get_eq_getElem]
  -- xp[0] = u
  have hxp_get_0 : xp.get ⟨0, by omega⟩ = u := by
    rw [List.get_eq_getElem, List.getElem_zero]
    exact hxp_head_eq
  -- u ∉ Z (since u ∈ xp via head)
  have hu_notZ : u ∉ Z := by
    apply hxp_Z
    rw [← hxp_head_eq]
    exact List.head_mem hxp_ne
  refine ⟨?_, ?_⟩
  · -- Adjacency: G.UAdj p[i] p[i+1]
    intro i hi
    rw [hp_len_eq2] at hi
    by_cases hA1 : i + 1 < R
    · -- A1: both in xp.reverse. Reversed-directed edge.
      have hiR : i < R := by omega
      rw [hp_L i hiR, hp_L (i + 1) hA1]
      have hedge_idx : R - 2 - i + 1 < R := by omega
      have hedge := hxp_edge (R - 2 - i) hedge_idx
      have heq : R - 2 - i + 1 = R - 1 - i := by omega
      rw [show (⟨R - 2 - i + 1, hedge_idx⟩ : Fin xp.length) =
          ⟨R - 1 - i, by omega⟩ from Fin.ext heq] at hedge
      have heq2 : R - 1 - (i + 1) = R - 2 - i := by omega
      rw [show (⟨R - 1 - (i + 1), by omega⟩ : Fin xp.length) =
          ⟨R - 2 - i, by omega⟩ from Fin.ext heq2]
      exact Or.inr hedge
    · push_neg at hA1
      by_cases hA2 : i + 1 = R
      · -- A2: seam i = R - 1. p[R-1] = xp[0] = u. p[R] = yp.tail[0] = yp[1].
        have hi_eq : i = R - 1 := by omega
        subst hi_eq
        have hiR : R - 1 < R := by omega
        rw [hp_L (R - 1) hiR]
        have hi1L : R ≤ R - 1 + 1 := by omega
        have hi1_lt : R - 1 + 1 < p.length := by rw [hp_len_eq2]; exact hi
        rw [hp_R (R - 1 + 1) hi1L hi1_lt]
        have h_xidx : R - 1 - (R - 1) = 0 := by omega
        rw [show (⟨R - 1 - (R - 1), by omega⟩ : Fin xp.length) =
            ⟨0, by omega⟩ from Fin.ext h_xidx]
        rw [hxp_get_0]
        have h_yidx : R - 1 + 1 - R + 1 = 1 := by omega
        rw [show (⟨R - 1 + 1 - R + 1, by
              rw [hp_len_eq2, hyp_tail_len] at hi1_lt; omega⟩ : Fin yp.length) =
            ⟨1, by omega⟩ from Fin.ext h_yidx]
        -- Goal: G.UAdj u yp[1]. Use hyp_edge at 0: G.edge yp[0] yp[1] = G.edge u yp[1].
        have hedge0 := hyp_edge 0 (by omega)
        have hyp0 : yp.get ⟨0, by omega⟩ = u := by
          rw [List.get_eq_getElem, List.getElem_zero]
          exact hyp_head_eq
        rw [hyp0] at hedge0
        exact Or.inl hedge0
      · -- A3: both in yp.tail. i ≥ R.
        have hiL : R ≤ i := by omega
        have hi1L : R ≤ i + 1 := by omega
        have hi_lt : i < p.length := by rw [hp_len_eq2]; omega
        have hi1_lt : i + 1 < p.length := by rw [hp_len_eq2]; exact hi
        rw [hp_R i hiL hi_lt, hp_R (i + 1) hi1L hi1_lt]
        -- Goal: G.UAdj yp[i-R+1] yp[(i+1)-R+1]. Use hyp_edge at i - R + 1.
        have hidx : (i - R + 1) + 1 < yp.length := by
          rw [hyp_tail_len] at hi; omega
        have hedge := hyp_edge (i - R + 1) hidx
        have heq : (i - R + 1) + 1 = (i + 1) - R + 1 := by omega
        rw [show (⟨(i - R + 1) + 1, hidx⟩ : Fin yp.length) =
            ⟨(i + 1) - R + 1, by omega⟩ from Fin.ext heq] at hedge
        exact Or.inl hedge
  · -- Collider condition
    intro i hi
    rw [hp_len_eq2] at hi
    by_cases hC1 : i + 2 < R
    · -- C1: all three in xp.reverse. Reversed-directed: middle is non-collider.
      have hiR : i < R := by omega
      have hi1R : i + 1 < R := by omega
      rw [hp_L i hiR, hp_L (i + 1) hi1R, hp_L (i + 2) hC1]
      -- middle: xp[R - 1 - (i+1)] = xp[R - 2 - i]. Edge from middle to left.
      have h_midx : R - 1 - (i + 1) = R - 2 - i := by omega
      rw [show (⟨R - 1 - (i + 1), by omega⟩ : Fin xp.length) =
          ⟨R - 2 - i, by omega⟩ from Fin.ext h_midx]
      have hedge_idx : R - 2 - i + 1 < R := by omega
      have hedge := hxp_edge (R - 2 - i) hedge_idx
      have heq : R - 2 - i + 1 = R - 1 - i := by omega
      rw [show (⟨R - 2 - i + 1, hedge_idx⟩ : Fin xp.length) =
          ⟨R - 1 - i, by omega⟩ from Fin.ext heq] at hedge
      have hnotColl : ¬ G.IsCollider (xp.get ⟨R - 1 - i, by omega⟩)
          (xp.get ⟨R - 2 - i, by omega⟩)
          (xp.get ⟨R - 1 - (i + 2), by omega⟩) := by
        intro ⟨hLM, _⟩
        exact G.asymm hedge hLM
      simp only [hnotColl, if_false]
      apply hxp_Z
      exact List.get_mem _ _
    · push_neg at hC1
      by_cases hC2 : i + 2 = R
      · -- C2: i = R - 2. Triple straddles seam: left and middle in xp.reverse, right at seam.
        have hi_eq : i = R - 2 := by omega
        subst hi_eq
        have hiR : R - 2 < R := by omega
        have hi1R : R - 2 + 1 < R := by omega
        have hi2L : R ≤ R - 2 + 2 := by omega
        have hi2_lt : R - 2 + 2 < p.length := by rw [hp_len_eq2]; exact hi
        rw [hp_L (R - 2) hiR, hp_L (R - 2 + 1) hi1R,
            hp_R (R - 2 + 2) hi2L hi2_lt]
        -- Middle: xp[R - 1 - (R - 2 + 1)] = xp[0] = u
        have h_midx : R - 1 - (R - 2 + 1) = 0 := by omega
        rw [show (⟨R - 1 - (R - 2 + 1), by omega⟩ : Fin xp.length) =
            ⟨0, by omega⟩ from Fin.ext h_midx]
        rw [hxp_get_0]
        -- Non-collider: edge from u to xp[1] (hxp_edge at 0), so ¬ edge xp[1] u.
        have hedge := hxp_edge 0 (by omega)
        rw [hxp_get_0] at hedge
        have h_lidx : R - 1 - (R - 2) = 1 := by omega
        rw [show (⟨R - 1 - (R - 2), by omega⟩ : Fin xp.length) =
            ⟨1, by omega⟩ from Fin.ext h_lidx]
        have hnotColl : ¬ G.IsCollider (xp.get ⟨1, by omega⟩) u
            (yp.get ⟨R - 2 + 2 - R + 1, by
              rw [hp_len_eq2, hyp_tail_len] at hi2_lt; omega⟩) := by
          intro ⟨hLM, _⟩
          exact G.asymm hedge hLM
        simp only [hnotColl, if_false]
        exact hu_notZ
      · by_cases hC3 : i + 1 = R
        · -- C3: seam at middle. i = R - 1.
          -- Triple: xp.reverse[R-1] = u, yp.tail[0] = yp[1], yp.tail[1] = yp[2].
          have hi_eq : i = R - 1 := by omega
          subst hi_eq
          have hiR : R - 1 < R := by omega
          have hi1L : R ≤ R - 1 + 1 := by omega
          have hi2L : R ≤ R - 1 + 2 := by omega
          have hi1_lt : R - 1 + 1 < p.length := by rw [hp_len_eq2]; omega
          have hi2_lt : R - 1 + 2 < p.length := by rw [hp_len_eq2]; exact hi
          rw [hp_L (R - 1) hiR, hp_R (R - 1 + 1) hi1L hi1_lt,
              hp_R (R - 1 + 2) hi2L hi2_lt]
          have h_lidx : R - 1 - (R - 1) = 0 := by omega
          rw [show (⟨R - 1 - (R - 1), by omega⟩ : Fin xp.length) =
              ⟨0, by omega⟩ from Fin.ext h_lidx]
          rw [hxp_get_0]
          -- middle index: yp[(R-1+1) - R + 1] = yp[1]
          have h_midx : R - 1 + 1 - R + 1 = 1 := by omega
          have hyp_1_lt : 1 < yp.length := by omega
          rw [show (⟨R - 1 + 1 - R + 1, by
                rw [hp_len_eq2, hyp_tail_len] at hi1_lt; omega⟩ : Fin yp.length) =
              ⟨1, hyp_1_lt⟩ from Fin.ext h_midx]
          -- right index: yp[(R-1+2) - R + 1] = yp[2]
          have h_ridx : R - 1 + 2 - R + 1 = 2 := by omega
          have hyp_2_lt : 2 < yp.length := by
            rw [hp_len_eq2, hyp_tail_len] at hi2_lt; omega
          rw [show (⟨R - 1 + 2 - R + 1, by
                rw [hp_len_eq2, hyp_tail_len] at hi2_lt; omega⟩ : Fin yp.length) =
              ⟨2, hyp_2_lt⟩ from Fin.ext h_ridx]
          -- Non-collider: edge from yp[1] to yp[2] (hyp_edge at 1), so ¬ edge yp[2] yp[1].
          have hedge := hyp_edge 1 (by omega)
          have hyp_2_lt' : 1 + 1 < yp.length := by omega
          rw [show (⟨1 + 1, hyp_2_lt'⟩ : Fin yp.length) =
              ⟨2, hyp_2_lt⟩ from Fin.ext rfl] at hedge
          have hnotColl : ¬ G.IsCollider u (yp.get ⟨1, hyp_1_lt⟩) (yp.get ⟨2, hyp_2_lt⟩) := by
            intro ⟨_, hRM⟩
            exact G.asymm hedge hRM
          simp only [hnotColl, if_false]
          -- yp[1] ∈ yp, so yp[1] ∉ Z by hyp_Z
          apply hyp_Z
          exact List.get_mem _ _
        · -- C4: all three in yp.tail. i ≥ R.
          have hiL : R ≤ i := by omega
          have hi1L : R ≤ i + 1 := by omega
          have hi2L : R ≤ i + 2 := by omega
          have hi_lt : i < p.length := by rw [hp_len_eq2]; omega
          have hi1_lt : i + 1 < p.length := by rw [hp_len_eq2]; omega
          have hi2_lt : i + 2 < p.length := by rw [hp_len_eq2]; exact hi
          rw [hp_R i hiL hi_lt, hp_R (i + 1) hi1L hi1_lt, hp_R (i + 2) hi2L hi2_lt]
          have hj_len : i - R + 1 + 2 < yp.length := by
            rw [hyp_tail_len] at hi; omega
          have h_midx : (i + 1) - R + 1 = i - R + 1 + 1 := by omega
          have h_ridx : (i + 2) - R + 1 = i - R + 1 + 2 := by omega
          rw [show (⟨(i + 1) - R + 1, by omega⟩ : Fin yp.length) =
              ⟨i - R + 1 + 1, by omega⟩ from Fin.ext h_midx]
          rw [show (⟨(i + 2) - R + 1, by omega⟩ : Fin yp.length) =
              ⟨i - R + 1 + 2, hj_len⟩ from Fin.ext h_ridx]
          -- Non-collider: edge from yp[(i-R+1)+1] to yp[(i-R+1)+2].
          have hedge := hyp_edge (i - R + 1 + 1) hj_len
          have hnotColl : ¬ G.IsCollider (yp.get ⟨i - R + 1, by
                rw [hyp_tail_len] at hi; omega⟩)
              (yp.get ⟨i - R + 1 + 1, by omega⟩) (yp.get ⟨i - R + 1 + 2, hj_len⟩) := by
            intro ⟨_, hRM⟩
            exact G.asymm hedge hRM
          simp only [hnotColl, if_false]
          apply hyp_Z
          exact List.get_mem _ _

/-- **Ancestral intersection from d-separation.** If `X` and `Y` are
    d-separated by `Z` in `G`, and `X` and `Y` are disjoint, then any common
    member of the ancestral closures of `X` and `Y` lies in the ancestral
    closure of `Z`.

    The disjointness assumption rules out the degenerate case `u ∈ X ∩ Y`
    (which would already contradict `dSep` only if BFS-reachability includes
    sources in its target — a subtlety we sidestep). The main consumer
    (`fullCondIndep_singleton_of_dSep`) supplies disjointness easily since the
    source set is a singleton `{a}` disjoint from the target `Y`. -/
theorem ancestralSet_inter_subset_ancestralSet_of_dSep
    {X Y Z : Finset V} (hdSep : G.dSep X Y Z)
    (hXY : Disjoint X Y) :
    G.ancestralSet X ∩ G.ancestralSet Y ⊆ G.ancestralSet Z := by
  intro u hu
  rw [Finset.mem_inter] at hu
  obtain ⟨huX, huY⟩ := hu
  -- Proceed by contradiction.
  by_contra huZ
  -- Unfold membership in ancestralSet for each side.
  have huX' : u ∈ X ∨ ∃ x ∈ X, G.isAncestor u x := by
    simp only [ancestralSet, Finset.mem_union, ancestorsSet,
      Finset.mem_filter, Finset.mem_univ, true_and] at huX
    rcases huX with h | ⟨x, hxX, hax⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, hxX, hax⟩
  have huY' : u ∈ Y ∨ ∃ y ∈ Y, G.isAncestor u y := by
    simp only [ancestralSet, Finset.mem_union, ancestorsSet,
      Finset.mem_filter, Finset.mem_univ, true_and] at huY
    rcases huY with h | ⟨y, hyY, hay⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, hyY, hay⟩
  -- Convert dSep to: no active path from X to Y given Z.
  have hNoPath : ∀ (x y : V), x ∈ X → y ∈ Y →
      ¬ ∃ (p : List V), p.length ≥ 2 ∧ G.IsActivePath Z p ∧
        p.head? = some x ∧ p.getLast? = some y := by
    intro x y hxX hyY ⟨p, hlen, hact, hhead, hlast⟩
    -- y ∈ bbReachableVertices Z X, but dSep says it's disjoint from Y.
    have hyR : y ∈ G.bbReachableVertices Z X := by
      rw [G.bbReachableVertices_iff_activePath]
      exact ⟨x, hxX, p, hlen, hact, hhead, hlast⟩
    exact (Finset.disjoint_left.mp hdSep.2.2.2) hyR hyY
  -- Build the active path. Three cases on (huX', huY').
  rcases huX' with hxIs | ⟨x, hxX, hax⟩
  · -- u ∈ X. Use directed path u → ... → y for some y ∈ Y.
    rcases huY' with hyIs | ⟨y, hyY, hay⟩
    · -- u ∈ X ∩ Y, contradicting disjointness.
      exact absurd hyIs ((Finset.disjoint_left.mp hXY) hxIs)
    · obtain ⟨p, hplen, hphead, hplast, hpact⟩ :=
        G.exists_activePath_of_ancestor_avoiding hay huZ
      exact hNoPath u y hxIs hyY ⟨p, hplen, hpact, hphead, hplast⟩
  · -- u is a strict ancestor of x ∈ X.
    obtain ⟨xp, hxp_len, hxp_head, hxp_last, hxp_edge, hxp_Z⟩ :=
      G.exists_directedPath_avoiding hax huZ
    rcases huY' with hyIs | ⟨y, hyY, hay⟩
    · -- u ∈ Y. The directed path xp (u → ... → x) is itself an active path
      -- from u to x; reverse it via the public `isActivePath_reverse`.
      have hxp_act_fwd : G.IsActivePath Z xp :=
        G.isActivePath_of_directed hxp_edge hxp_Z
      have hxp_act : G.IsActivePath Z xp.reverse := G.isActivePath_reverse hxp_act_fwd
      have hxp_rev_len : xp.reverse.length ≥ 2 := by
        rw [List.length_reverse]; exact hxp_len
      have hxp_rev_head : xp.reverse.head? = some x := by
        rw [List.head?_reverse]; exact hxp_last
      have hxp_rev_last : xp.reverse.getLast? = some u := by
        rw [List.getLast?_reverse]; exact hxp_head
      exact hNoPath x u hxX hyIs ⟨xp.reverse, hxp_rev_len, hxp_act, hxp_rev_head, hxp_rev_last⟩
    · -- u is a strict ancestor of both x ∈ X and y ∈ Y. Build the fork.
      obtain ⟨yp, hyp_len, hyp_head, hyp_last, hyp_edge, hyp_Z⟩ :=
        G.exists_directedPath_avoiding hay huZ
      obtain ⟨hp_len, hp_head, hp_last, hp_act⟩ :=
        G.fork_isActivePath hxp_len hxp_head hxp_last hxp_edge hxp_Z
          hyp_len hyp_head hyp_last hyp_edge hyp_Z
      exact hNoPath x y hxX hyY ⟨_, hp_len, hp_act, hp_head, hp_last⟩

end DAG

end Causalean
