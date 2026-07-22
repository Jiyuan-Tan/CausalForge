/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Active Paths

This file defines active paths (trails) in DAGs and proves path surgery lemmas
needed for the source-to-conditioning transfer in d-separation.

## Main definitions

* `DAG.UAdj` — undirected adjacency
* `DAG.IsCollider` — collider at a triple
* `DAG.IsActivePath` — active (unblocked) path given a conditioning set
* `DAG.HasActivePath` — existence of an active path between two vertex sets

## Main results

* `DAG.isActivePath_reverse` — reversing an active path gives an active path
* `DAG.hasActivePath_symm` — active-path existence is symmetric
* `DAG.bbReachableVertices_iff_activePath` — BFS ↔ active-path equivalence

## References

* Basic Concepts.tex, Definitions 2-3 (Blocked path, d-separation)
* Shachter (1998), Bayes Ball algorithm
-/

import Causalean.Graph.DSep.BayesBall

/-! # Active Paths

This file defines active paths in directed acyclic graphs relative to a
conditioning set. It records undirected adjacency (`UAdj`), collider triples
(`IsCollider`), path activity (`IsActivePath`), and active-path existence between
sets (`HasActivePath`).

The main path lemmas prove reversal symmetry (`isActivePath_reverse`,
`hasActivePath_symm`), directed-path activity helpers, suffix extraction for
source-to-conditioning transfer, and the Bayes Ball correctness theorem
`bbReachableVertices_iff_activePath`, which identifies computed reachability
with existence of an active path. -/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

-- ============================================================
-- Active trail (path-based d-separation)
-- ============================================================

/-- An undirected edge in the DAG: either `G.edge u v` or `G.edge v u`. -/
def UAdj (u v : V) : Prop := G.edge u v ∨ G.edge v u

/-- Undirected adjacency is decidable whenever the directed edge relation is decidable. -/
instance decUAdj (u v : V) : Decidable (G.UAdj u v) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Whether vertex `m` is a collider on the triple `(l, m, r)`:
    both edges point toward `m`, i.e., `G.edge l m ∧ G.edge r m`. -/
def IsCollider (l m r : V) : Prop := G.edge l m ∧ G.edge r m

/-- Collider status of a triple is decidable whenever the directed edge relation is decidable. -/
instance decIsCollider (l m r : V) : Decidable (G.IsCollider l m r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A path (list of vertices) is **active** (unblocked) given conditioning set `Z` if:
    - consecutive vertices are undirected-adjacent
    - for every intermediate triple `(pᵢ, pᵢ₊₁, pᵢ₊₂)`:
      - if `pᵢ₊₁` is a collider: `pᵢ₊₁ ∈ G.bbZAncestors Z`
      - if `pᵢ₊₁` is not a collider: `pᵢ₊₁ ∉ Z`

    Defined index-wise to make reversal straightforward. -/
def IsActivePath (Z : Finset V) (p : List V) : Prop :=
  -- All consecutive pairs are adjacent
  (∀ (i : ℕ) (hi : i + 1 < p.length),
    G.UAdj (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩)) ∧
  -- All intermediate vertices satisfy the collider/non-collider condition
  (∀ (i : ℕ) (hi : i + 2 < p.length),
    let l := p.get ⟨i, by omega⟩
    let m := p.get ⟨i + 1, by omega⟩
    let r := p.get ⟨i + 2, hi⟩
    if G.IsCollider l m r then m ∈ G.bbZAncestors Z else m ∉ Z)

/-- There exists an active path from some vertex in `X` to some vertex in `Y`. -/
def HasActivePath (X Y Z : Finset V) : Prop :=
  ∃ (p : List V), p.length ≥ 2 ∧
    G.IsActivePath Z p ∧
    p.head? ∈ (X.image some) ∧
    p.getLast? ∈ (Y.image some)

/-- Undirected adjacency is symmetric: if two vertices are adjacent, they remain adjacent in the
opposite order. -/
theorem UAdj_symm {u v : V} (h : G.UAdj u v) : G.UAdj v u := Or.comm.mp h

omit [DecidableEq V] [Fintype V] in
/-- Helper: `List.get` on a reversed list accesses the mirror index. -/
private theorem get_rev (p : List V) (i : ℕ) (hi : i < p.reverse.length) :
    p.reverse.get ⟨i, hi⟩ =
    p.get ⟨p.length - 1 - i, by rw [List.length_reverse] at hi; omega⟩ :=
  List.get_reverse' p ⟨i, hi⟩ _

/-- Active paths are symmetric: reversing an active path is also active.

    The proof uses the index-based definition: index `i` in the reversed list
    corresponds to index `p.length - 1 - i` in the original list. Adjacency
    is symmetric (`UAdj_symm`) and collider status swaps the outer vertices
    (`And.comm`). -/
theorem isActivePath_reverse {Z : Finset V} {p : List V}
    (h : G.IsActivePath Z p) : G.IsActivePath Z p.reverse := by
  obtain ⟨hadj, hcoll⟩ := h
  set n := p.length
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · -- Adjacency: p.reverse[i] and p.reverse[i+1] are UAdj
    have hn : i + 1 < n := by rw [List.length_reverse] at hi; exact hi
    rw [get_rev, get_rev]
    -- p[n-1-i] and p[n-1-(i+1)] = p[n-2-i] are UAdj
    -- From hadj: p[n-2-i] and p[n-2-i+1] = p[n-1-i] are UAdj
    have hj : n - 1 - (i + 1) + 1 < n := by omega
    have := hadj (n - 1 - (i + 1)) hj
    have heq1 : n - 1 - (i + 1) + 1 = n - 1 - i := by omega
    rw [show (⟨n - 1 - (i + 1) + 1, hj⟩ : Fin p.length) =
      ⟨n - 1 - i, by omega⟩ from Fin.ext heq1] at this
    exact G.UAdj_symm this
  · -- Collider condition: triple (p.reverse[i], p.reverse[i+1], p.reverse[i+2])
    have hn : i + 2 < n := by rw [List.length_reverse] at hi; exact hi
    rw [get_rev, get_rev, get_rev]
    -- The triple (i, i+1, i+2) in the reverse corresponds to
    -- (n-1-i, n-2-i, n-3-i) in the original, which is the reversed triple
    -- (n-3-i, n-2-i, n-1-i). Use hcoll at index (n-3-i) with And.comm.
    have hj : p.length - 3 - i + 2 < p.length := by omega
    have horig := hcoll (p.length - 3 - i) hj
    simp only [IsCollider] at horig ⊢
    -- The indices in horig are (n-3-i, n-3-i+1, n-3-i+2) = (n-3-i, n-2-i, n-1-i)
    -- The goal indices are (n-1-i, n-2-i, n-3-i) via get_rev
    -- These are the same vertices but the outer pair is swapped
    -- First, show the Fin values match: n-3-i+k and n-1-(i+2-k) are the same
    have heq0 : (⟨p.length - 3 - i, by omega⟩ : Fin p.length) =
                ⟨p.length - 1 - (i + 2), by omega⟩ := Fin.ext (by simp; omega)
    have heq1 : (⟨p.length - 3 - i + 1, by omega⟩ : Fin p.length) =
                ⟨p.length - 1 - (i + 1), by omega⟩ := Fin.ext (by simp; omega)
    have heq2 : (⟨p.length - 3 - i + 2, hj⟩ : Fin p.length) =
                ⟨p.length - 1 - i, by omega⟩ := Fin.ext (by simp; omega)
    simp only [heq0, heq1, heq2] at horig
    -- horig and goal differ only by And.comm in the if-condition.
    -- Introduce abbreviations for the three vertices to avoid Fin issues.
    set a := p.get ⟨p.length - 1 - (i + 2), by omega⟩
    set b := p.get ⟨p.length - 1 - (i + 1), by omega⟩
    set c := p.get ⟨p.length - 1 - i, by omega⟩
    -- horig : if (G.edge a b ∧ G.edge c b) then b ∈ ... else b ∉ ...
    -- goal  : if (G.edge c b ∧ G.edge a b) then b ∈ ... else b ∉ ...
    -- Split on the condition; And.comm relates the two.
    by_cases hab : G.edge a b ∧ G.edge c b
    · simp only [hab] at horig
      simp only [hab.symm, horig]
    · simp only [hab, ite_false] at horig
      have : ¬(G.edge c b ∧ G.edge a b) := fun h => hab h.symm
      simp only [this, ite_false]
      exact horig

/-- A reversed directed path avoiding `Z` is an active path given `Z`.
    "Reversed directed" means each edge points from the *later* index to the
    *earlier* index (i.e., the list enumerates the path in the direction opposite
    to the edges). Every interior vertex is then a non-collider, and by the
    avoidance hypothesis none is in `Z`. -/
private theorem isActivePath_of_reversed_directed
    {Z : Finset V} {p : List V}
    (hdir : ∀ (i : ℕ) (hi : i + 1 < p.length),
        G.edge (p.get ⟨i + 1, hi⟩) (p.get ⟨i, by omega⟩))
    (hZ : ∀ x ∈ p, x ∉ Z) :
    G.IsActivePath Z p := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · -- Adjacency: hdir says G.edge p[i+1] p[i], so p[i] and p[i+1] are UAdj
    exact Or.inr (hdir i hi)
  · -- Collider condition. Let l = p[i], m = p[i+1], r = p[i+2].
    -- hdir at index i:   G.edge m l  (so NOT edge l m, by asymm)
    -- hdir at index i+1: G.edge r m
    -- IsCollider l m r requires G.edge l m ∧ G.edge r m; first conjunct fails.
    simp only
    have hml : G.edge (p.get ⟨i + 1, by omega⟩) (p.get ⟨i, by omega⟩) :=
      hdir i (by omega)
    have hlm_false : ¬ G.edge (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) :=
      G.asymm hml
    have hnotcoll : ¬ G.IsCollider (p.get ⟨i, by omega⟩)
                      (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) := by
      intro ⟨h1, _⟩; exact hlm_false h1
    rw [if_neg hnotcoll]
    -- Need p[i+1] ∉ Z, which follows from hZ
    exact hZ _ (List.get_mem _ _)

-- ============================================================
-- Active path surgery helpers
-- ============================================================

section SurgeryHelpers

/-- Largest `i < n` satisfying a decidable predicate `P`, if any. -/
noncomputable def lastIdxLt (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Option ℕ :=
  if h : ((Finset.range n).filter P).Nonempty then
    some (((Finset.range n).filter P).max' h)
  else none

/-- If the last index below a bound exists, it is below the bound, satisfies the predicate, and no
larger index below the bound satisfies it. -/
theorem lastIdxLt_eq_some {n : ℕ} {P : ℕ → Prop} [DecidablePred P] {i : ℕ}
    (h : lastIdxLt n P = some i) :
    i < n ∧ P i ∧ ∀ j, i < j → j < n → ¬ P j := by
  unfold lastIdxLt at h
  split_ifs at h with hne
  · injection h with heq
    subst heq
    have hi_mem : ((Finset.range n).filter P).max' hne ∈ (Finset.range n).filter P :=
      Finset.max'_mem _ hne
    rw [Finset.mem_filter, Finset.mem_range] at hi_mem
    refine ⟨hi_mem.1, hi_mem.2, ?_⟩
    intro j hj hjn hPj
    have hjmem : j ∈ (Finset.range n).filter P := by
      rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hjn, hPj⟩
    have := Finset.le_max' _ j hjmem
    omega

/-- If there is no last index below a bound satisfying a predicate, then no index below the bound
satisfies the predicate. -/
theorem lastIdxLt_eq_none {n : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (h : lastIdxLt n P = none) :
    ∀ i, i < n → ¬ P i := by
  intro i hi hPi
  have hmem : i ∈ (Finset.range n).filter P := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hi, hPi⟩
  have hne : ((Finset.range n).filter P).Nonempty := ⟨i, hmem⟩
  simp [lastIdxLt, hne] at h

end SurgeryHelpers

/-- **Suffix-step for source-to-cond transfer.**

    Given an active path `p` from `x ∈ X` to `w` given `Z ∪ S` of length ≥ 2,
    produce a suffix `q` (possibly the whole path) such that:
    * `q` is still an active path from some `x' ∈ X ∪ S` to `w` given `Z ∪ S`,
    * every strictly interior vertex of `q` lies outside `S`. -/
theorem take_suffix_at_last_S
    {X Z S : Finset V} {p : List V} {x w : V}
    (hxX : x ∈ X) (hlen : p.length ≥ 2)
    (hact : G.IsActivePath (Z ∪ S) p)
    (hhead : p.head? = some x) (hlast : p.getLast? = some w) :
    ∃ (x' : V) (q : List V), x' ∈ X ∪ S ∧ q.length ≥ 2 ∧
      G.IsActivePath (Z ∪ S) q ∧ q.head? = some x' ∧ q.getLast? = some w ∧
      (∀ (k : ℕ) (_hk1 : 0 < k) (hk2 : k + 1 < q.length),
          q.get ⟨k, by omega⟩ ∉ S) := by
  -- Interior-S-index set: i : Fin p.length with i+1 < p.length and p.get i ∈ S.
  let IS : Finset (Fin p.length) :=
    Finset.univ.filter (fun i => i.val + 1 < p.length ∧ p.get i ∈ S)
  by_cases hIS : IS.Nonempty
  · -- Cut at the maximum.
    let i₀ : Fin p.length := IS.max' hIS
    have hi₀_mem : i₀ ∈ IS := Finset.max'_mem _ hIS
    have hi₀_filt : i₀.val + 1 < p.length ∧ p.get i₀ ∈ S := by
      have := hi₀_mem
      simp only [IS, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    let q : List V := p.drop i₀.val
    refine ⟨p.get i₀, q, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_union_right _ hi₀_filt.2
    · show q.length ≥ 2
      simp only [q, List.length_drop]
      omega
    · -- G.IsActivePath (Z ∪ S) q — shift indices
      obtain ⟨hadj, hcoll⟩ := hact
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have hq_len : q.length = p.length - i₀.val := by
          simp only [q, List.length_drop]
        have hi' : i₀.val + i + 1 < p.length := by
          rw [hq_len] at hi; omega
        have hq_i : q.get ⟨i, by omega⟩ = p.get ⟨i₀.val + i, by omega⟩ := by
          simp [q, List.getElem_drop]
        have hq_i1 : q.get ⟨i + 1, hi⟩ = p.get ⟨i₀.val + (i + 1), by omega⟩ := by
          simp [q, List.getElem_drop]
        rw [hq_i, hq_i1]
        have hadj' := hadj (i₀.val + i) (by omega)
        convert hadj' using 2
      · have hq_len : q.length = p.length - i₀.val := by
          simp only [q, List.length_drop]
        have hi' : i₀.val + i + 2 < p.length := by
          rw [hq_len] at hi; omega
        have hq_i : q.get ⟨i, by omega⟩ = p.get ⟨i₀.val + i, by omega⟩ := by
          simp [q, List.getElem_drop]
        have hq_i1 : q.get ⟨i + 1, by omega⟩ = p.get ⟨i₀.val + (i + 1), by omega⟩ := by
          simp [q, List.getElem_drop]
        have hq_i2 : q.get ⟨i + 2, hi⟩ = p.get ⟨i₀.val + (i + 2), by omega⟩ := by
          simp [q, List.getElem_drop]
        rw [hq_i, hq_i1, hq_i2]
        have hcoll' := hcoll (i₀.val + i) (by omega)
        convert hcoll' using 2
    · -- q.head? = some (p.get i₀)
      have hq_ne : q ≠ [] := by
        simp only [q, ne_eq, List.drop_eq_nil_iff]
        omega
      have : q.head? = some (q.head hq_ne) := List.head?_eq_some_head hq_ne
      rw [this]
      congr 1
      simp only [q]
      rw [List.head_drop]
      rfl
    · -- q.getLast? = p.getLast? = some w
      have hq_ne : q ≠ [] := by
        simp only [q, ne_eq, List.drop_eq_nil_iff]
        omega
      have hp_ne : p ≠ [] := by
        intro hnil; rw [hnil] at hlen; simp at hlen
      rw [List.getLast?_eq_some_getLast hq_ne]
      rw [List.getLast?_eq_some_getLast hp_ne] at hlast
      simp only [q]
      rw [List.getLast_drop]
      exact hlast
    · -- strict interior q has no S-vertex
      intro k hk1 hk2 hkS
      have hq_len : q.length = p.length - i₀.val := by
        simp only [q, List.length_drop]
      have hq_k : q.get ⟨k, by omega⟩ = p.get ⟨i₀.val + k, by rw [hq_len] at hk2; omega⟩ := by
        simp [q, List.getElem_drop]
      rw [hq_k] at hkS
      have hidx_lt : i₀.val + k < p.length := by rw [hq_len] at hk2; omega
      have hmem_IS : (⟨i₀.val + k, hidx_lt⟩ : Fin p.length) ∈ IS := by
        simp only [IS, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, hkS⟩
        rw [hq_len] at hk2; omega
      have hle := Finset.le_max' _ _ hmem_IS
      change i₀.val + k ≤ i₀.val at hle
      omega
  · -- No interior S-vertex. Take q := p.
    refine ⟨x, p, Finset.mem_union_left _ hxX, hlen, hact, hhead, hlast, ?_⟩
    intro k hk1 hk2 hkS
    apply hIS
    refine ⟨⟨k, by omega⟩, ?_⟩
    simp only [IS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hk2, hkS⟩

/-- If `q` is active given `Z ∪ S`, strict-interior vertices are outside `S`,
    and every interior collider of `q` is `Z`-activated (not merely `S`-activated),
    then `q` is active given `Z` alone. -/
theorem isActivePath_Z_of_no_S_only_collider
    {Z S : Finset V} {q : List V}
    (hact : G.IsActivePath (Z ∪ S) q)
    (_hInterior : ∀ (k : ℕ) (_hk1 : 0 < k) (hk2 : k + 1 < q.length),
        q.get ⟨k, by omega⟩ ∉ S)
    (hNoSOnly : ∀ (i : ℕ) (hi : i + 2 < q.length),
        G.IsCollider (q.get ⟨i, by omega⟩) (q.get ⟨i + 1, by omega⟩) (q.get ⟨i + 2, hi⟩) →
        q.get ⟨i + 1, by omega⟩ ∈ G.bbZAncestors Z) :
    G.IsActivePath Z q := by
  obtain ⟨hadj, hcoll⟩ := hact
  refine ⟨hadj, fun i hi => ?_⟩
  -- Let m := q.get ⟨i+1, _⟩. Two cases: collider or not.
  simp only
  by_cases hC : G.IsCollider (q.get ⟨i, by omega⟩)
      (q.get ⟨i + 1, by omega⟩) (q.get ⟨i + 2, hi⟩)
  · -- Collider: use hNoSOnly
    rw [if_pos hC]
    exact hNoSOnly i hi hC
  · -- Non-collider: use the (Z ∪ S)-activity to conclude m ∉ Z ∪ S, hence m ∉ Z.
    rw [if_neg hC]
    have := hcoll i hi
    simp only [if_neg hC] at this
    -- this : q.get ⟨i + 1, _⟩ ∉ Z ∪ S
    intro hZ
    exact this (Finset.mem_union_left _ hZ)

/-- `HasActivePath` is symmetric in `X` and `Y`. -/
theorem hasActivePath_symm (X Y Z : Finset V) :
    G.HasActivePath X Y Z → G.HasActivePath Y X Z := by
  rintro ⟨p, hlen, hact, hhead, hlast⟩
  refine ⟨p.reverse, ?_, G.isActivePath_reverse hact, ?_, ?_⟩
  · simp only [List.length_reverse]; exact hlen
  · rwa [List.head?_reverse]
  · rwa [List.getLast?_reverse]

-- ============================================================
-- Connection between BFS and active paths (the key equivalence)
-- ============================================================

/-- A Bayes-Ball direction matches the orientation of the last edge of a path:
`fromParent` means the previous vertex is a parent of the current one, while
`fromChild` means the previous vertex is a child of the current one. -/
private def StateMatchesEdge (u w : V) : BBDir → Prop
  | BBDir.fromParent => G.edge u w
  | BBDir.fromChild => G.edge w u

private theorem bbInit_of_stateMatchesEdge
    {X : Finset V} {x w : V} {d : BBDir}
    (hxX : x ∈ X) (hdir : G.StateMatchesEdge x w d) :
    (w, d) ∈ G.bbInit X := by
  cases d
  · rw [bbInit, Finset.mem_biUnion]
    refine ⟨x, hxX, ?_⟩
    exact Finset.mem_union_left _
      (Finset.mem_map.mpr ⟨w, G.mem_children.mpr hdir, rfl⟩)
  · rw [bbInit, Finset.mem_biUnion]
    refine ⟨x, hxX, ?_⟩
    exact Finset.mem_union_right _
      (Finset.mem_map.mpr ⟨w, G.mem_parents.mpr hdir, rfl⟩)

private theorem bbStep_of_active_triple
    {Z : Finset V} {u w z : V} {d dz : BBDir}
    (hin : G.StateMatchesEdge u w d)
    (hout : G.StateMatchesEdge w z dz)
    (htri : if G.IsCollider u w z then w ∈ G.bbZAncestors Z else w ∉ Z) :
    (z, dz) ∈ G.bbStep Z (w, d) := by
  cases d <;> cases dz
  · -- parent -> child: non-collider, so `w ∉ Z`, then children are allowed.
    simp only [StateMatchesEdge] at hin hout
    have hnotcoll : ¬ G.IsCollider u w z := by
      intro hC
      exact G.asymm hout hC.2
    have hwZ : w ∉ Z := by simpa [hnotcoll] using htri
    simp [bbStep, hwZ, mem_children, hout]
  · -- parent -> parent: collider, so parents are allowed when `w` is conditioned
    -- or ancestor-activated.
    simp only [StateMatchesEdge] at hin hout
    have hcoll : G.IsCollider u w z := ⟨hin, hout⟩
    have hanc : w ∈ G.bbZAncestors Z := by simpa [hcoll] using htri
    by_cases hwZ : w ∈ Z
    · simp [bbStep, hwZ, mem_parents, hout]
    · simp [bbStep, hwZ, hanc, mem_parents, hout]
  · -- child -> child: non-collider, so `w ∉ Z`, then children are allowed.
    simp only [StateMatchesEdge] at hin hout
    have hnotcoll : ¬ G.IsCollider u w z := by
      intro hC
      exact G.asymm hin hC.1
    have hwZ : w ∉ Z := by simpa [hnotcoll] using htri
    simp [bbStep, hwZ, mem_children, hout]
  · -- child -> parent: non-collider, so `w ∉ Z`, then parents are allowed.
    simp only [StateMatchesEdge] at hin hout
    have hnotcoll : ¬ G.IsCollider u w z := by
      intro hC
      exact G.asymm hin hC.1
    have hwZ : w ∉ Z := by simpa [hnotcoll] using htri
    simp [bbStep, hwZ, mem_parents, hout]

private theorem active_triple_of_bbStep
    {Z : Finset V} {u w z : V} {d dz : BBDir}
    (hin : G.StateMatchesEdge u w d)
    (hstep : (z, dz) ∈ G.bbStep Z (w, d)) :
    G.StateMatchesEdge w z dz ∧
      (if G.IsCollider u w z then w ∈ G.bbZAncestors Z else w ∉ Z) := by
  cases d <;> cases dz
  · simp only [StateMatchesEdge] at hin ⊢
    have hout : G.edge w z := by
      by_cases hwZ : w ∈ Z
      · simp [bbStep, hwZ] at hstep
      · by_cases hanc : w ∈ G.bbZAncestors Z
        · simpa [bbStep, hwZ, hanc, mem_children, mem_parents] using hstep
        · simpa [bbStep, hwZ, hanc, mem_children, mem_parents] using hstep
    have hwZ : w ∉ Z := by
      by_contra hwZ
      simp [bbStep, hwZ] at hstep
    have hnotcoll : ¬ G.IsCollider u w z := by
      intro hC
      exact G.asymm hout hC.2
    exact ⟨hout, by simp [hnotcoll, hwZ]⟩
  · simp only [StateMatchesEdge] at hin ⊢
    have hout : G.edge z w := by
      by_cases hwZ : w ∈ Z
      · simpa [bbStep, hwZ, mem_parents] using hstep
      · by_cases hanc : w ∈ G.bbZAncestors Z
        · simpa [bbStep, hwZ, hanc, mem_parents, mem_children] using hstep
        · simp [bbStep, hwZ, hanc, mem_children] at hstep
    have hcoll : G.IsCollider u w z := ⟨hin, hout⟩
    have hanc : w ∈ G.bbZAncestors Z := by
      by_cases hwZ : w ∈ Z
      · simp [bbZAncestors, ancestralSet, hwZ]
      · by_contra hanc
        simp [bbStep, hwZ, hanc, mem_children] at hstep
    exact ⟨hout, by simp [hcoll, hanc]⟩
  · simp only [StateMatchesEdge] at hin ⊢
    have hout : G.edge w z := by
      by_cases hwZ : w ∈ Z
      · simp [bbStep, hwZ] at hstep
      · simpa [bbStep, hwZ, mem_children, mem_parents] using hstep
    have hwZ : w ∉ Z := by
      by_contra hwZ
      simp [bbStep, hwZ] at hstep
    have hnotcoll : ¬ G.IsCollider u w z := by
      intro hC
      exact G.asymm hin hC.1
    exact ⟨hout, by simp [hnotcoll, hwZ]⟩
  · simp only [StateMatchesEdge] at hin ⊢
    have hout : G.edge z w := by
      by_cases hwZ : w ∈ Z
      · simp [bbStep, hwZ] at hstep
      · simpa [bbStep, hwZ, mem_parents, mem_children] using hstep
    have hwZ : w ∉ Z := by
      by_contra hwZ
      simp [bbStep, hwZ] at hstep
    have hnotcoll : ¬ G.IsCollider u w z := by
      intro hC
      exact G.asymm hin hC.1
    exact ⟨hout, by simp [hnotcoll, hwZ]⟩

/-- Prepending an active triple to an active path keeps the path active. -/
theorem isActivePath_cons_of_active_triple
    {Z : Finset V} {z w u : V} {r : List V}
    (hadj : G.UAdj z w)
    (htri : if G.IsCollider z w u then w ∈ G.bbZAncestors Z else w ∉ Z)
    (hact : G.IsActivePath Z (w :: u :: r)) :
    G.IsActivePath Z (z :: w :: u :: r) := by
  obtain ⟨hadj_old, hcoll_old⟩ := hact
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · cases i with
    | zero =>
        simpa using hadj
    | succ i =>
        have h := hadj_old i (by
          simpa [Nat.add_assoc] using hi)
        simpa using h
  · cases i with
    | zero =>
        simpa using htri
    | succ i =>
        have h := hcoll_old i (by
          simpa [Nat.add_assoc] using hi)
        simpa [Nat.add_assoc] using h

private theorem active_triple_swap_outer
    {Z : Finset V} {u w z : V}
    (h : if G.IsCollider u w z then w ∈ G.bbZAncestors Z else w ∉ Z) :
    if G.IsCollider z w u then w ∈ G.bbZAncestors Z else w ∉ Z := by
  simp only [IsCollider] at h ⊢
  by_cases hC : G.edge u w ∧ G.edge z w
  · have hC' : G.edge z w ∧ G.edge u w := hC.symm
    simpa [hC'] using h
  · have hC' : ¬(G.edge z w ∧ G.edge u w) := fun h' => hC h'.symm
    simpa [hC, hC'] using h

private theorem uAdj_reverse_of_stateMatchesEdge
    {u w : V} {d : BBDir} (h : G.StateMatchesEdge u w d) :
    G.UAdj w u := by
  cases d
  · exact Or.inr h
  · exact Or.inl h

private theorem isActivePath_pair
    {Z : Finset V} {a b : V} (h : G.UAdj a b) :
    G.IsActivePath Z [a, b] := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · match i, hi with
    | 0, _ => simpa using h
  · have hlt : i + 2 < 2 := by simpa using hi
    omega

/-- A reachable Bayes-Ball state carries an active path back to some source.
The path is stored in reverse order because `bbStep` prepends naturally. -/
private def StateHasReverseActivePath (X Z : Finset V) (s : BBState V) : Prop :=
  ∃ (x : V), x ∈ X ∧ ∃ (u : V) (r : List V),
    G.StateMatchesEdge u s.1 s.2 ∧
    G.IsActivePath Z (s.1 :: u :: r) ∧
    (s.1 :: u :: r).getLast? = some x

private theorem bbReachable_state_has_reverse_activePath
    (X Z : Finset V) {s : BBState V} (hs : s ∈ G.bbReachable Z X) :
    G.StateHasReverseActivePath X Z s := by
  classical
  let S : Finset (BBState V) :=
    Finset.univ.filter (fun s => G.StateHasReverseActivePath X Z s)
  have hinit : G.bbInit X ⊆ S := by
    intro s hs
    rcases s with ⟨w, d⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    cases d
    · simp only [bbInit, Finset.mem_biUnion, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk, Prod.mk.injEq, reduceCtorEq] at hs
      obtain ⟨x, hxX, hxw⟩ := hs
      rcases hxw with hchild | hparent
      · obtain ⟨a, ha, haw, _⟩ := hchild
        subst w
        have hxw_edge : G.edge x a := G.mem_children.mp ha
        refine ⟨x, hxX, x, [], hxw_edge, ?_, rfl⟩
        exact G.isActivePath_pair (Or.inr hxw_edge)
      · obtain ⟨a, _ha, _haw, hbad⟩ := hparent
        cases hbad
    · simp only [bbInit, Finset.mem_biUnion, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk, Prod.mk.injEq, reduceCtorEq] at hs
      obtain ⟨x, hxX, hwx⟩ := hs
      rcases hwx with hchild | hparent
      · obtain ⟨a, _ha, _haw, hbad⟩ := hchild
        cases hbad
      · obtain ⟨a, ha, haw, _⟩ := hparent
        subst w
        have hwx_edge : G.edge a x := G.mem_parents.mp ha
        refine ⟨x, hxX, x, [], hwx_edge, ?_, rfl⟩
        exact G.isActivePath_pair (Or.inl hwx_edge)
  have hstep : ∀ s ∈ S, G.bbStep Z s ⊆ S := by
    intro s hs t ht
    rcases s with ⟨w, d⟩
    rcases t with ⟨z, dz⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    obtain ⟨x, hxX, u, r, hdir, hact, hlast⟩ := hs
    have hdata := G.active_triple_of_bbStep hdir ht
    have hadj : G.UAdj z w := G.uAdj_reverse_of_stateMatchesEdge hdata.1
    have htri : (if G.IsCollider z w u then w ∈ G.bbZAncestors Z else w ∉ Z) :=
      G.active_triple_swap_outer hdata.2
    refine ⟨x, hxX, w, u :: r, hdata.1, ?_, ?_⟩
    · exact G.isActivePath_cons_of_active_triple hadj htri hact
    · simpa using hlast
  have hsub : G.bbReachable Z X ⊆ S :=
    G.bbReachable_minimal Z X S hinit hstep
  have hsS := hsub hs
  simpa [S] using hsS

private theorem isActivePath_cons_tail
    {Z : Finset V} {u w : V} {r : List V}
    (h : G.IsActivePath Z (u :: w :: r)) :
    G.IsActivePath Z (w :: r) := by
  obtain ⟨hadj, hcoll⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h' := hadj (i + 1) (by
      simpa [Nat.add_assoc] using Nat.succ_lt_succ hi)
    simpa using h'
  · have h' := hcoll (i + 1) (by
      simpa [Nat.add_assoc] using Nat.succ_lt_succ hi)
    simpa [Nat.add_assoc] using h'

private theorem bbReachableVertices_of_activePath_walk
    {X Z : Finset V} {u w : V} {r : List V} {d : BBDir}
    (hs : (w, d) ∈ G.bbReachable Z X)
    (hdir : G.StateMatchesEdge u w d)
    (hact : G.IsActivePath Z (u :: w :: r)) :
    ∀ {v : V}, (w :: r).getLast? = some v → v ∈ G.bbReachableVertices Z X := by
  induction r generalizing u w d with
  | nil =>
      intro v hlast
      simp only [List.getLast?_singleton] at hlast
      injection hlast with hv
      subst v
      exact Finset.mem_image.mpr ⟨(w, d), hs, rfl⟩
  | cons z r ih =>
      intro v hlast
      have hadj_wz : G.UAdj w z := by
        have h := hact.1 1 (by simp)
        simpa using h
      have htri : (if G.IsCollider u w z then w ∈ G.bbZAncestors Z else w ∉ Z) := by
        have h := hact.2 0 (by simp)
        simpa using h
      have htail : G.IsActivePath Z (w :: z :: r) :=
        G.isActivePath_cons_tail hact
      rcases hadj_wz with hwz | hzw
      · have hstep : (z, BBDir.fromParent) ∈ G.bbStep Z (w, d) :=
          G.bbStep_of_active_triple hdir hwz htri
        have hs' : (z, BBDir.fromParent) ∈ G.bbReachable Z X :=
          (G.bbReachable_bbStep_subset Z X hs) hstep
        exact ih hs' hwz htail (by simpa using hlast)
      · have hstep : (z, BBDir.fromChild) ∈ G.bbStep Z (w, d) :=
          G.bbStep_of_active_triple hdir hzw htri
        have hs' : (z, BBDir.fromChild) ∈ G.bbReachable Z X :=
          (G.bbReachable_bbStep_subset Z X hs) hstep
        exact ih hs' hzw htail (by simpa using hlast)

private theorem bbReachableVertices_of_activePath_cons
    {X Z : Finset V} {x w : V} {r : List V} {v : V}
    (hxX : x ∈ X) (hact : G.IsActivePath Z (x :: w :: r))
    (hlast : (x :: w :: r).getLast? = some v) :
    v ∈ G.bbReachableVertices Z X := by
  have hadj_xw : G.UAdj x w := by
    have h := hact.1 0 (by simp)
    simpa using h
  rcases hadj_xw with hxw | hwx
  · have hs0 : (w, BBDir.fromParent) ∈ G.bbReachable Z X :=
      G.bbReachable_init_subset Z X (G.bbInit_of_stateMatchesEdge hxX hxw)
    exact G.bbReachableVertices_of_activePath_walk hs0 hxw hact (by simpa using hlast)
  · have hs0 : (w, BBDir.fromChild) ∈ G.bbReachable Z X :=
      G.bbReachable_init_subset Z X (G.bbInit_of_stateMatchesEdge hxX hwx)
    exact G.bbReachableVertices_of_activePath_walk hs0 hwx hact (by simpa using hlast)

/-- The BFS computation is correct: a vertex is in `bbReachableVertices Z X`
    if and only if there is an active path from some `x ∈ X` to `v` given `Z`.

    This is the Bayes Ball correctness theorem. The proof requires showing that
    the BFS fixed point captures exactly the vertices reachable via active trails.

    Forward direction (soundness): every BFS-reachable vertex has an active path.
    Backward direction (completeness): every vertex with an active path is BFS-reachable. -/
theorem bbReachableVertices_iff_activePath (X Z : Finset V) (v : V) :
    v ∈ G.bbReachableVertices Z X ↔
    ∃ (x : V), x ∈ X ∧ ∃ (p : List V), p.length ≥ 2 ∧
      G.IsActivePath Z p ∧ p.head? = some x ∧ p.getLast? = some v := by
  constructor
  · intro hv
    rw [bbReachableVertices] at hv
    obtain ⟨s, hs, hsv⟩ := Finset.mem_image.mp hv
    rcases s with ⟨w, d⟩
    change w = v at hsv
    subst w
    obtain ⟨x, hxX, u, r, _hdir, hact, hlast⟩ :=
      G.bbReachable_state_has_reverse_activePath X Z hs
    refine ⟨x, hxX, (v :: u :: r).reverse, ?_, ?_, ?_, ?_⟩
    · simp
    · exact G.isActivePath_reverse hact
    · rwa [List.head?_reverse]
    · rw [List.getLast?_reverse]
      rfl
  · rintro ⟨x, hxX, p, hlen, hact, hhead, hlast⟩
    cases p with
    | nil =>
        simp at hlen
    | cons a p' =>
        cases p' with
        | nil =>
            simp at hlen
        | cons b r =>
            simp only [List.head?_cons] at hhead
            injection hhead with ha
            subst a
            exact G.bbReachableVertices_of_activePath_cons hxX hact hlast

end DAG

end Causalean
