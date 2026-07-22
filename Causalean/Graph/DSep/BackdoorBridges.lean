/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Backdoor bridge lemmas (graph-layer)

Graph-theoretic bridge lemmas used by `SCM/ID/Backdoor.lean`.

## Main results

* `DAG.dSep_union_roots_right` — adjoining root vertices to the conditioning
  set preserves d-separation.
-/

import Causalean.Graph.DSep.Separation

/-! # Backdoor Graph Bridges

This file contains graph-level lemmas for backdoor identification arguments. The
main theorem `DAG.dSep_union_roots_right` shows that adding root vertices
disjoint from the query variables to the conditioning set preserves
d-separation. The proof uses active-path semantics: a conditioned root can only
appear as a non-collider fork on an interior path, so it blocks rather than opens
paths. -/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

-- ============================================================
-- A root has no ancestors
-- ============================================================

/-- A vertex with no incoming edges has no proper ancestors. -/
private lemma not_isAncestor_of_root {r : V}
    (hr : ∀ u, ¬ G.edge u r) (u : V) : ¬ G.isAncestor u r := by
  intro h
  cases h with
  | edge he => exact hr _ he
  | trans _ he => exact hr _ he

-- ============================================================
-- Adding roots to the conditioning set preserves d-separation
-- ============================================================

/-- **Adding root nodes (no incoming edges) to the conditioning set preserves
    d-separation.**

    If every `r ∈ R` has no incoming edges in `G` and `R` is disjoint from
    `X, Y`, then `G.dSep X Y Z → G.dSep X Y (Z ∪ R)`.

    **Proof idea.** On any undirected path from `X` to `Y`, an interior vertex
    `r ∈ R` can only participate as a "fork" `· ← r → ·` (both incident edges
    outgoing, since `r` has no incoming edges). A fork is a non-collider, and
    non-colliders in the conditioning set block the path. Hence no `r ∈ R`
    can appear on an active path (endpoints are in `X, Y`, disjoint from `R`),
    so any path active given `Z ∪ R` is also active given `Z`. -/
theorem dSep_union_roots_right {X Y Z R : Finset V}
    (hXY_sep : G.dSep X Y Z)
    (hRoots : ∀ r ∈ R, ∀ u, ¬ G.edge u r)
    (hRX : Disjoint R X) (hRY : Disjoint R Y) :
    G.dSep X Y (Z ∪ R) := by
  rcases hXY_sep with ⟨hXY, hXZ, hYZ, hReach⟩
  refine ⟨hXY, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hvX hvZR
    rcases Finset.mem_union.mp hvZR with hvZ | hvR
    · exact Finset.disjoint_left.mp hXZ hvX hvZ
    · exact Finset.disjoint_left.mp hRX hvR hvX
  · rw [Finset.disjoint_left]
    intro v hvY hvZR
    rcases Finset.mem_union.mp hvZR with hvZ | hvR
    · exact Finset.disjoint_left.mp hYZ hvY hvZ
    · exact Finset.disjoint_left.mp hRY hvR hvY
  rw [Finset.disjoint_left] at hReach ⊢
  intro v hv_ZR hvY
  rw [G.bbReachableVertices_iff_activePath] at hv_ZR
  obtain ⟨x, hxX, p, hlen, hact, hhead, hlast⟩ := hv_ZR
  obtain ⟨hadj, hcoll⟩ := hact
  -- Helper: the interior vertex condition, parametrized by the triple's left index.
  -- For a triple (i, i+1, i+2), middle `p[i+1]` is not a collider and not in Z ∪ R.
  -- If `p[i+1] ∈ R`, the "not in Z ∪ R" fails, contradiction.
  have hNoR_interior : ∀ (i : ℕ) (hi : i + 2 < p.length),
      p.get ⟨i + 1, by omega⟩ ∉ R := by
    intro i hi hmem
    have hc := hcoll i hi
    set l := p.get ⟨i, by omega⟩
    set m := p.get ⟨i + 1, by omega⟩
    set r := p.get ⟨i + 2, hi⟩
    have hnoInL : ¬ G.edge l m := hRoots _ hmem l
    have hnc : ¬ G.IsCollider l m r := fun h => hnoInL h.1
    simp only [hnc, if_false] at hc
    exact hc (Finset.mem_union_right _ hmem)
  -- Rebuild active path given Z.
  have hact_Z : G.IsActivePath Z p := by
    refine ⟨hadj, ?_⟩
    intro i hi
    have hc := hcoll i hi
    set l := p.get ⟨i, by omega⟩
    set m := p.get ⟨i + 1, by omega⟩
    set r := p.get ⟨i + 2, hi⟩
    have hm_notR : m ∉ R := hNoR_interior i hi
    by_cases hColl : G.IsCollider l m r
    · -- Collider case.
      simp only [hColl, if_true] at hc
      simp only [hColl, if_true]
      -- `hc : m ∈ bbZAncestors (Z ∪ R)`.  Want `m ∈ bbZAncestors Z`.
      -- bbZAncestors = ancestralSet = S ∪ ancestorsSet S
      simp only [bbZAncestors, ancestralSet] at hc ⊢
      rcases Finset.mem_union.mp hc with hZR | hmAnc
      · rcases Finset.mem_union.mp hZR with hZ | hR
        · exact Finset.mem_union_left _ hZ
        · exact absurd hR hm_notR
      · simp only [ancestorsSet, Finset.mem_filter, Finset.mem_univ,
          true_and] at hmAnc
        obtain ⟨w, hwZR, hma⟩ := hmAnc
        rcases Finset.mem_union.mp hwZR with hwZ | hwR
        · refine Finset.mem_union_right _ ?_
          simp only [ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w, hwZ, hma⟩
        · exact absurd hma (G.not_isAncestor_of_root (hRoots w hwR) m)
    · -- Non-collider case.
      simp only [hColl, if_false] at hc
      simp only [hColl, if_false]
      exact fun hmZ => hc (Finset.mem_union_left _ hmZ)
  -- Close: active path given Z witnesses bbReachable Z X, contradicting hXY_sep.
  have hvReachZ : v ∈ G.bbReachableVertices Z X := by
    rw [G.bbReachableVertices_iff_activePath]
    exact ⟨x, hxX, p, hlen, hact_Z, hhead, hlast⟩
  exact hReach hvReachZ hvY

end DAG

end Causalean
