/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# d-Separation

This file defines d-separation for DAGs and proves its key structural properties.

## Main definitions

* `DAG.dSep` — d-separation predicate (decidable)

## Main results

* `DAG.dSep_subset_left` — d-sep monotone in the source set
* `DAG.bbZAncestors_union_eq` — ancestral set distributes over union
* `DAG.activePath_transfer_cond_to_source` — path-level source-to-cond transfer
* `DAG.dSep_source_to_cond` — move sources into the conditioning set
* `DAG.dSep_symm` — symmetry of d-separation

## References

* Basic Concepts.tex, Definitions 2-3 (Blocked path, d-separation)
-/

import Causalean.Graph.DSep.ActivePath

/-! # d-Separation

This file defines d-separation in a finite directed acyclic graph as pairwise
disjointness of the query sets together with absence of Bayes Ball reachability
from the source set to the target set given a conditioning set. It proves
structural properties used by the global Markov and identification layers:
monotonicity in source and target sets, the union rule for collider-activation
ancestors (`bbZAncestors_union_eq`), directed-path extraction avoiding a
conditioning set, source-to-conditioning transfer (`dSep_source_to_cond`),
transfer to edge subgraphs (`dSep_mono_conditioningSet`), and symmetry. -/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

-- ============================================================
-- d-Separation
-- ============================================================

/-- The source, target, and conditioning sets are d-separated when they are
    pairwise disjoint and no target vertex is Bayes-Ball-reachable from the
    source set after conditioning.

    The query sets `X`, `Y`, and `Z` must be pairwise disjoint, and every
    Bayes-Ball active path from `X` to `Y` must be blocked by `Z`. -/
def dSep (X Y Z : Finset V) : Prop :=
  Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧
    Disjoint (G.bbReachableVertices Z X) Y

/-- D-separation is decidable by computing Bayes Ball reachability and checking disjointness. -/
instance decDSep (X Y Z : Finset V) : Decidable (G.dSep X Y Z) :=
  by
    unfold dSep
    infer_instance

-- ============================================================
-- d-Separation monotonicity (graph-only)
-- ============================================================

/-- d-separation is monotone in `X`: smaller source sets preserve d-separation. -/
theorem dSep_subset_left {X X' Y Z : Finset V}
    (hXX' : X' ⊆ X) (h : G.dSep X Y Z) : G.dSep X' Y Z := by
  rcases h with ⟨hXY, hXZ, hYZ, hReach⟩
  exact ⟨Disjoint.mono_left hXX' hXY, Disjoint.mono_left hXX' hXZ, hYZ,
    Disjoint.mono_left (G.bbReachableVertices_mono_source hXX') hReach⟩

/-- d-separation is monotone in `Y`: shrinking the target set preserves d-separation. -/
theorem dSep_subset_right {X Y Y' Z : Finset V}
    (hYY' : Y' ⊆ Y) (h : G.dSep X Y Z) : G.dSep X Y' Z := by
  rcases h with ⟨hXY, hXZ, hYZ, hReach⟩
  exact ⟨Disjoint.mono_right hYY' hXY, hXZ, Disjoint.mono_left hYY' hYZ,
    Disjoint.mono_right hYY' hReach⟩

/-- **Ancestral-set distributes over union.**

    `bbZAncestors (Z ∪ S) = bbZAncestors Z ∪ bbZAncestors S` as finsets.
    Used to split a collider-activation witness for `Z ∪ S` into a `Z`-side
    and an `S`-side witness. -/
theorem bbZAncestors_union_eq (Z S : Finset V) :
    G.bbZAncestors (Z ∪ S) = G.bbZAncestors Z ∪ G.bbZAncestors S := by
  ext v
  simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hZS | ⟨w, hwZS, haw⟩)
    · rcases hZS with hZ | hS
      · exact Or.inl (Or.inl hZ)
      · exact Or.inr (Or.inl hS)
    · rcases hwZS with hwZ | hwS
      · exact Or.inl (Or.inr ⟨w, hwZ, haw⟩)
      · exact Or.inr (Or.inr ⟨w, hwS, haw⟩)
  · rintro ((hZ | ⟨w, hwZ, haw⟩) | (hS | ⟨w, hwS, haw⟩))
    · exact Or.inl (Or.inl hZ)
    · exact Or.inr ⟨w, Or.inl hwZ, haw⟩
    · exact Or.inl (Or.inr hS)
    · exact Or.inr ⟨w, Or.inr hwS, haw⟩

/-- If `u` is an ancestor of `v` and `u ∉ ancestralSet Z`, there is a list
    `u = p₀, p₁, …, pₖ = v` (`k ≥ 1`) of directed edges all avoiding `Z`. -/
theorem exists_directedPath_avoiding
    {u v : V} (huv : G.isAncestor u v)
    {Z : Finset V} (huZ : u ∉ G.ancestralSet Z) :
    ∃ (p : List V), p.length ≥ 2 ∧ p.head? = some u ∧ p.getLast? = some v ∧
      (∀ (i : ℕ) (hi : i + 1 < p.length),
        G.edge (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩)) ∧
      (∀ x ∈ p, x ∉ Z) := by
  induction huv with
  | edge he =>
    rename_i u v
    refine ⟨[u, v], ?_, rfl, rfl, ?_, ?_⟩
    · simp
    · intro i hi
      -- p.length = 2, so i + 1 < 2 means i = 0
      match i, hi with
      | 0, _ => exact he
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hxu | hxv
      · -- u ∉ Z because Z ⊆ ancestralSet Z
        subst hxu
        intro hxZ
        exact huZ (Finset.mem_union_left _ hxZ)
      · -- v ∉ Z: else u ∈ ancestorsSet Z ⊆ ancestralSet Z
        subst hxv
        intro hvZ
        apply huZ
        apply Finset.mem_union_right
        simp only [ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨_, hvZ, isAncestor.edge he⟩
  | trans h₁ he' ih =>
    rename_i u w v
    obtain ⟨p, hlen, hhead, hlast, hedge, hZ⟩ := ih
    -- p is a u→w path. Build p ++ [v].
    refine ⟨p ++ [v], ?_, ?_, ?_, ?_, ?_⟩
    · -- length ≥ 2
      rw [List.length_append, List.length_singleton]; omega
    · -- head? of p ++ [v] = head? of p = some u (p nonempty)
      have hne : p ≠ [] := by
        intro hp; rw [hp] at hlen; simp at hlen
      rw [List.head?_append_of_ne_nil _ hne]
      exact hhead
    · -- getLast? of p ++ [v] = some v
      simp [List.getLast?_append]
    · -- edge condition
      intro i hi
      have hlen' : (p ++ [v]).length = p.length + 1 := by
        rw [List.length_append, List.length_singleton]
      have hi' : i + 1 < p.length + 1 := by rw [← hlen']; exact hi
      -- Convert .get to [i]
      change G.edge ((p ++ [v])[i]) ((p ++ [v])[i + 1])
      by_cases hlt : i + 1 < p.length
      · -- both indices in p-part
        have hi0 : i < p.length := by omega
        have e1 : (p ++ [v])[i]'(by omega) = p[i]'hi0 := by
          rw [List.getElem_append]; simp [hi0]
        have e2 : (p ++ [v])[i + 1]'(by omega) = p[i + 1]'hlt := by
          rw [List.getElem_append]; simp [hlt]
        rw [e1, e2]
        have := hedge i hlt
        -- convert .get to [i] for hedge
        simpa [List.get_eq_getElem] using this
      · -- seam: i + 1 = p.length
        push_neg at hlt
        have heq : i + 1 = p.length := by omega
        have hplen_pos : 0 < p.length := by omega
        have hi0 : i < p.length := by omega
        have hne : p ≠ [] := List.ne_nil_of_length_pos hplen_pos
        -- p[p.length - 1] = w (from hlast)
        have hlast_w : p[p.length - 1]'(by omega) = w := by
          have h1 : p.getLast? = some (p.getLast hne) :=
            List.getLast?_eq_some_getLast hne
          rw [hlast] at h1
          have : p.getLast hne = w := by
            exact (Option.some_inj.mp h1.symm)
          rw [← this]
          exact (List.getLast_eq_getElem hne).symm
        have hi_eq : i = p.length - 1 := by omega
        have e1 : (p ++ [v])[i]'(by omega) = p[i]'hi0 := by
          rw [List.getElem_append]; simp [hi0]
        have e2 : (p ++ [v])[i + 1]'(by omega) = v := by
          rw [List.getElem_append]
          simp [heq]
        have e3 : p[i]'hi0 = w := by
          have : p[i]'hi0 = p[p.length - 1]'(by omega) := by
            congr 1
          rw [this, hlast_w]
        rw [e1, e2, e3]
        exact he'
    · -- avoidance
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hxp | hxv
      · exact hZ x hxp
      · rw [List.mem_singleton] at hxv
        subst hxv
        intro hvZ
        apply huZ
        apply Finset.mem_union_right
        simp only [ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨x, hvZ, ?_⟩
        exact G.isAncestor_trans h₁ (isAncestor.edge he')

/-- **Path-level source-to-cond transfer.**

    Given an active path `p` from `x ∈ X` to `w` given `Z ∪ S`, there exists
    an active path `p'` from some `x' ∈ X ∪ S` to `w` given `Z`.

    **Proof sketch.**

    Let `q` be the suffix of `p` starting at the *last* vertex of `p` that
    lies in `S`; if no vertex of `p` lies in `S`, take `q := p`. Then
    * `head q ∈ X ∪ S` (either the original `x ∈ X`, or an `S`-vertex);
    * the interior of `q` contains no vertex of `S`.

    Classify each interior vertex `m` of `q`:
    * **Non-collider on `q`.** From `p`-activity, `m ∉ Z ∪ S`, hence `m ∉ Z`. ✓
    * **Collider on `q`.** By `bbZAncestors_union_eq`,
      `m ∈ bbZAncestors Z ∨ m ∈ bbZAncestors S`.
      * If `m ∈ bbZAncestors Z`, the collider is already `Z`-activated.
      * Else `m ∈ bbZAncestors S \ bbZAncestors Z`. Since `m` is interior of `q`
        we have `m ∉ S`, so `m` is a proper ancestor of some `s ∈ S`. Pick the
        last such "`S`-only activated" collider `m*` on `q`. Along any directed
        path `m* → v₁ → … → s ∈ S` no interior vertex lies in `Z` (otherwise
        `m* ∈ bbZAncestors Z`), and the terminal `s ∉ Z` for the same reason.

        **Reroute.** Replace the prefix `[head q, …, m*]` of `q` by the reversed
        directed path `[s, v_{k−1}, …, v₁, m*]`. The new path:
        * has head `s ∈ S ⊆ X ∪ S`; tail still `w`;
        * interior of the new prefix: directed, so each `vᵢ` is a non-collider;
          each `vᵢ ∉ Z` by choice of the directed path.
        * `m*` at the join becomes a non-collider (one incoming edge from the
          `q`-side, one outgoing edge `m* → v₁`), and `m* ∉ Z` since `m*` was a
          collider on the originally active `q` (so `m* ∉ Z ∪ S`).
        * interior after `m*` is unchanged; any collider there lies in
          `bbZAncestors Z` by choice of `m*` as the *last* `S`-only one.

    Formalized by a 4-way index case split (`r.reverse` interior, the two seam
    triples at the `m*` join, and `qTail` interior), using asymmetry of `G.edge`
    for the reversed-directed portion and maximality of `j_star` on the `qTail`
    side. -/
private theorem activePath_transfer_cond_to_source
    {X Z S : Finset V} {p : List V} {x w : V}
    (hxX : x ∈ X) (hlen : p.length ≥ 2)
    (hact : G.IsActivePath (Z ∪ S) p)
    (hhead : p.head? = some x) (hlast : p.getLast? = some w) :
    ∃ (x' : V) (p' : List V), x' ∈ X ∪ S ∧ p'.length ≥ 2 ∧
      G.IsActivePath Z p' ∧ p'.head? = some x' ∧ p'.getLast? = some w := by
  classical
  -- Step A: Take suffix at last S-vertex. Strict interior of q has no S-vertex.
  obtain ⟨x₁, q, hx₁XS, hqlen, hqact, hqhead, hqlast, hqInterior⟩ :=
    G.take_suffix_at_last_S hxX hlen hact hhead hlast
  -- Case split on existence of an S-only-activated collider in q's strict interior.
  by_cases hExists : ∃ (i : ℕ) (hi : i + 2 < q.length),
      G.IsCollider (q.get ⟨i, by omega⟩) (q.get ⟨i + 1, by omega⟩) (q.get ⟨i + 2, hi⟩) ∧
      q.get ⟨i + 1, by omega⟩ ∉ G.bbZAncestors Z
  · -- Case B: reroute via directed ancestor path.
    -- Pick the LARGEST strict-interior index j_star of q at which there is an
    -- "S-only activated" collider (activated in bbZAncestors (Z ∪ S) via
    -- bbZAncestors S but NOT already in bbZAncestors Z). Use Finset.max'.
    let IColl : Finset ℕ :=
      (Finset.range q.length).filter (fun i =>
        ∃ (hi : i + 2 < q.length),
          G.IsCollider (q.get ⟨i, by omega⟩) (q.get ⟨i + 1, by omega⟩)
              (q.get ⟨i + 2, hi⟩) ∧
          q.get ⟨i + 1, by omega⟩ ∉ G.bbZAncestors Z)
    have hIColl_ne : IColl.Nonempty := by
      obtain ⟨i, hi, hC, hNotZ⟩ := hExists
      refine ⟨i, ?_⟩
      simp only [IColl, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hi, hC, hNotZ⟩
    let j_star : ℕ := IColl.max' hIColl_ne
    have hj_star_mem : j_star ∈ IColl := Finset.max'_mem _ hIColl_ne
    have hj_star_spec : j_star < q.length ∧
        ∃ (hj : j_star + 2 < q.length),
          G.IsCollider (q.get ⟨j_star, by omega⟩)
            (q.get ⟨j_star + 1, by omega⟩) (q.get ⟨j_star + 2, hj⟩) ∧
          q.get ⟨j_star + 1, by omega⟩ ∉ G.bbZAncestors Z := by
      have := hj_star_mem
      simp only [IColl, Finset.mem_filter, Finset.mem_range] at this
      exact this
    obtain ⟨_hj_lt_len, hj_lt, hj_coll, hm_notZ⟩ := hj_star_spec
    set m_star : V := q.get ⟨j_star + 1, by omega⟩ with hm_star_def
    -- m_star is a strict-interior vertex, so m_star ∉ S (from hqInterior).
    have hm_notS : m_star ∉ S := hqInterior (j_star + 1) (by omega) (by omega)
    -- m_star ∈ bbZAncestors (Z ∪ S) comes from the (Z ∪ S)-activity at the collider.
    have hm_coll_ZUS : m_star ∈ G.bbZAncestors (Z ∪ S) := by
      obtain ⟨_hqadj, hqcoll⟩ := hqact
      have hval := hqcoll j_star hj_lt
      simp only at hval
      rw [if_pos hj_coll] at hval
      exact hval
    -- Since m_star ∉ bbZAncestors Z, by bbZAncestors_union_eq, m_star ∈ bbZAncestors S.
    have hm_S_anc : m_star ∈ G.bbZAncestors S := by
      have hsplit : m_star ∈ G.bbZAncestors Z ∪ G.bbZAncestors S := by
        rw [← G.bbZAncestors_union_eq]; exact hm_coll_ZUS
      rw [Finset.mem_union] at hsplit
      rcases hsplit with hZ | hS
      · exact absurd hZ hm_notZ
      · exact hS
    -- Unfold bbZAncestors S = S ∪ ancestorsSet S. Since m_star ∉ S,
    -- m_star is a proper ancestor of some s ∈ S.
    have hm_ancset_S : ∃ s ∈ S, G.isAncestor m_star s := by
      have hmem : m_star ∈ G.ancestralSet S := hm_S_anc
      simp only [ancestralSet, Finset.mem_union] at hmem
      rcases hmem with h | h
      · exact absurd h hm_notS
      · simp only [ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact h
    obtain ⟨s, hsS, hmAncs⟩ := hm_ancset_S
    -- m_star ∉ ancestralSet Z = bbZAncestors Z.
    have hm_notAncZ : m_star ∉ G.ancestralSet Z := hm_notZ
    -- Get a directed path m_star → ... → s avoiding Z.
    obtain ⟨r, hr_len, hr_head, hr_last, hr_edges, hr_avoid⟩ :=
      G.exists_directedPath_avoiding hmAncs hm_notAncZ
    -- Build q' := r.reverse ++ q.drop (j_star + 2).
    let qTail : List V := q.drop (j_star + 2)
    let qPrime : List V := r.reverse ++ qTail
    have hr_ne : r ≠ [] := by
      intro h; rw [h] at hr_len; simp at hr_len
    have hrRev_ne : r.reverse ≠ [] := by
      simp [hr_ne]
    have hqTail_ne : qTail ≠ [] := by
      simp only [qTail, ne_eq, List.drop_eq_nil_iff]; omega
    -- Head of qPrime = s (head of r.reverse = last of r = s).
    have hqPrime_head : qPrime.head? = some s := by
      simp only [qPrime, List.head?_append_of_ne_nil _ hrRev_ne,
                 List.head?_reverse]
      exact hr_last
    -- Last of qPrime = last of qTail = w.
    have hqTail_last : qTail.getLast? = some w := by
      have hq_ne : q ≠ [] := by
        intro h; rw [h] at hqlen; simp at hqlen
      rw [List.getLast?_eq_some_getLast hqTail_ne]
      rw [List.getLast?_eq_some_getLast hq_ne] at hqlast
      simp only [qTail]
      rw [List.getLast_drop]
      exact hqlast
    have hqPrime_last : qPrime.getLast? = some w := by
      simp only [qPrime, List.getLast?_append, hqTail_last]
      rfl
    -- Length ≥ 2.
    have hqPrime_len : qPrime.length ≥ 2 := by
      have hrl : r.reverse.length ≥ 2 := by
        rw [List.length_reverse]; exact hr_len
      have htl : qTail.length ≥ 1 := List.length_pos_iff.mpr hqTail_ne
      simp only [qPrime, List.length_append]
      omega
    -- Head s ∈ X ∪ S.
    have hs_XS : s ∈ X ∪ S := Finset.mem_union_right _ hsS
    refine ⟨s, qPrime, hs_XS, hqPrime_len, ?_, hqPrime_head, hqPrime_last⟩
    -- The remaining goal: G.IsActivePath Z qPrime.
    -- Structure (deferred — indices are finicky):
    --   (A) inside r.reverse (strict interior): edges are reversed-directed,
    --       so non-colliders; vertices avoid Z by hr_avoid.
    --   (B) seam at r.reverse boundary: last vertex of r.reverse = r.head = m_star.
    --       First vertex of qTail = q.get ⟨j_star + 2, _⟩.
    --       Adjacency at the seam: q-side is G.UAdj (m_star, q[j_star+2]) from hqact.
    --       Collider triple at index r.length - 2 (inside r.reverse, ending at m_star):
    --         m_star = r.head; predecessor in r.reverse = r[1]; successor is
    --         q[j_star+2]. Asymmetry rules out collider (r.head → r[1] means the
    --         edge points OUT of m_star; no way to have edge q[j_star+2] → m_star
    --         AND edge r[1] → m_star both as required, since the former goes out).
    --         Actually the non-collider guard needs m_star ∉ Z — from hm_notAncZ.
    --       Collider triple at index r.length - 1 (m_star, q[j_star+2], q[j_star+3]):
    --         adjacency m_star-q[j_star+2] (UAdj from hqact). For collider status use
    --         maximality of j_star to show q[j_star+2] (the m of this triple) isn't
    --         an S-only activated collider in the ORIGINAL q — if it is a collider,
    --         it must already lie in bbZAncestors Z; otherwise it must ∉ Z ∪ S.
    --   (C) inside qTail proper (indices ≥ r.length): translated triples from q at
    --       indices ≥ j_star + 2. By maximality of j_star, any collider there is
    --       in bbZAncestors Z already; non-colliders avoid Z ∪ S, hence avoid Z.
    -- ACTIVE-PATH VERIFICATION for qPrime = r.reverse ++ q.drop (j_star + 2).
    -- Index layout: qPrime[k] = r[R-1-k] for k < R := r.length; qPrime[k] =
    -- q[j_star + 2 + (k - R)] for k ≥ R. Cases on (i vs R).
    obtain ⟨hqadj, hqcoll⟩ := hqact
    have hrrev_len : r.reverse.length = r.length := List.length_reverse
    have hqTail_len_eq : qTail.length = q.length - (j_star + 2) := by
      simp only [qTail, List.length_drop]
    have hqP_len_eq : qPrime.length = r.length + qTail.length := by
      simp only [qPrime, List.length_append, hrrev_len]
    have hm_notZ_simple : m_star ∉ Z := fun h =>
      hm_notZ (Finset.mem_union_left _ h)
    -- r.get ⟨0, _⟩ = m_star
    have hr_get_0 : r.get ⟨0, by omega⟩ = m_star := by
      have h1 : r.head? = some (r.head hr_ne) := List.head?_eq_some_head hr_ne
      rw [hr_head] at h1
      have hhead_eq : r.head hr_ne = m_star := Option.some_inj.mp h1.symm
      rw [← hhead_eq]
      rw [List.get_eq_getElem, List.getElem_zero]
    -- Maximality of j_star: any j' > j_star with a collider has middle ∈ bbZAncestors Z
    have hmax : ∀ (j' : ℕ) (hj' : j' + 2 < q.length) (_hlt : j_star < j')
        (_hcol : G.IsCollider (q.get ⟨j', by omega⟩) (q.get ⟨j' + 1, by omega⟩)
                             (q.get ⟨j' + 2, hj'⟩)),
        q.get ⟨j' + 1, by omega⟩ ∈ G.bbZAncestors Z := by
      intro j' hj' hlt hcol
      by_contra hnotZ
      have hmem : j' ∈ IColl := by
        simp only [IColl, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hj', hcol, hnotZ⟩
      have hle := Finset.le_max' _ _ hmem
      change j' ≤ j_star at hle
      omega
    -- qPrime on left part (k < r.length): qPrime[k] = r[r.length - 1 - k]
    have hqP_L : ∀ (k : ℕ) (hkR : k < r.length),
        qPrime.get ⟨k, by rw [hqP_len_eq]; omega⟩ =
        r.get ⟨r.length - 1 - k, by omega⟩ := by
      intro k hkR
      have hk_rev : k < r.reverse.length := by rw [hrrev_len]; exact hkR
      simp only [qPrime, List.get_eq_getElem,
        List.getElem_append_left (h := hk_rev), List.getElem_reverse]
    -- qPrime on right part (r.length ≤ k): qPrime[k] = q[j_star + 2 + (k - r.length)]
    have hqP_R : ∀ (k : ℕ) (hkL : r.length ≤ k) (hk : k < qPrime.length),
        qPrime.get ⟨k, hk⟩ =
        q.get ⟨j_star + 2 + (k - r.length), by
          rw [hqP_len_eq, hqTail_len_eq] at hk; omega⟩ := by
      intro k hkL hk
      have hk_rev : r.reverse.length ≤ k := by rw [hrrev_len]; exact hkL
      simp only [qPrime, List.get_eq_getElem,
        List.getElem_append_right hk_rev, qTail, List.getElem_drop, hrrev_len]
    -- Main split: adjacency and collider condition
    refine ⟨?_, ?_⟩
    · -- Adjacency: G.UAdj qPrime[i] qPrime[i+1]
      intro i hi
      rw [hqP_len_eq] at hi
      by_cases hA1 : i + 1 < r.length
      · -- A1: both in r.reverse
        have hiR : i < r.length := by omega
        rw [hqP_L i hiR, hqP_L (i + 1) hA1]
        -- hr_edges at index r.length - 2 - i: G.edge r[r.length-2-i] r[r.length-1-i]
        have hedge_idx : r.length - 2 - i + 1 < r.length := by omega
        have hedge := hr_edges (r.length - 2 - i) hedge_idx
        have heq : r.length - 2 - i + 1 = r.length - 1 - i := by omega
        rw [show (⟨r.length - 2 - i + 1, hedge_idx⟩ : Fin r.length) =
            ⟨r.length - 1 - i, by omega⟩ from Fin.ext heq] at hedge
        have heq2 : r.length - 1 - (i + 1) = r.length - 2 - i := by omega
        rw [show (⟨r.length - 1 - (i + 1), by omega⟩ : Fin r.length) =
            ⟨r.length - 2 - i, by omega⟩ from Fin.ext heq2]
        exact Or.inr hedge
      · push_neg at hA1  -- r.length ≤ i + 1
        by_cases hA2 : i + 1 = r.length
        · -- A2: seam: i = r.length - 1
          have hi_eq : i = r.length - 1 := by omega
          subst hi_eq
          have hiR : r.length - 1 < r.length := by omega
          rw [hqP_L (r.length - 1) hiR]
          have hi1L : r.length ≤ r.length - 1 + 1 := by omega
          have hi1_lt : r.length - 1 + 1 < qPrime.length := by
            rw [hqP_len_eq]; exact hi
          rw [hqP_R (r.length - 1 + 1) hi1L hi1_lt]
          -- Goal: G.UAdj r[R-1-(R-1)] q[j_star+2+((R-1+1)-R)] after simplification.
          -- Simplify indices
          have h_ridx : r.length - 1 - (r.length - 1) = 0 := by omega
          have h_qidx : j_star + 2 + (r.length - 1 + 1 - r.length) = j_star + 2 := by omega
          rw [show (⟨r.length - 1 - (r.length - 1), by omega⟩ : Fin r.length) =
              ⟨0, by omega⟩ from Fin.ext h_ridx]
          rw [show (⟨j_star + 2 + (r.length - 1 + 1 - r.length), by
                rw [hqP_len_eq, hqTail_len_eq] at hi1_lt; omega⟩ : Fin q.length) =
              ⟨j_star + 2, hj_lt⟩ from Fin.ext h_qidx]
          rw [hr_get_0]
          -- Goal: G.UAdj m_star (q.get ⟨j_star + 2, hj_lt⟩)
          -- From hqadj at index j_star + 1: G.UAdj q[j_star+1] q[j_star+2]
          have hadj := hqadj (j_star + 1) (by omega)
          have : q.get ⟨j_star + 1, by omega⟩ = m_star := hm_star_def.symm
          rw [this] at hadj
          convert hadj using 2
        · -- A3: both in qTail. i ≥ r.length.
          have hiL : r.length ≤ i := by omega
          have hi1L : r.length ≤ i + 1 := by omega
          have hi_lt : i < qPrime.length := by rw [hqP_len_eq]; omega
          have hi1_lt : i + 1 < qPrime.length := by rw [hqP_len_eq]; exact hi
          rw [hqP_R i hiL hi_lt, hqP_R (i + 1) hi1L hi1_lt]
          -- Goal: G.UAdj q[j_star+2+(i-R)] q[j_star+2+(i+1-R)]
          -- Use hqadj at q-index j_star + 2 + (i - r.length)
          have hqidx : j_star + 2 + (i - r.length) + 1 < q.length := by
            rw [hqTail_len_eq] at hi; omega
          have hadj := hqadj (j_star + 2 + (i - r.length)) hqidx
          have heq2 : j_star + 2 + (i - r.length) + 1 = j_star + 2 + (i + 1 - r.length) := by
            omega
          rw [show (⟨j_star + 2 + (i - r.length) + 1, hqidx⟩ : Fin q.length) =
              ⟨j_star + 2 + (i + 1 - r.length), by omega⟩ from Fin.ext heq2] at hadj
          exact hadj
    · -- Collider condition
      intro i hi
      rw [hqP_len_eq] at hi
      -- Four cases on (i vs r.length): C1..C4
      by_cases hC1 : i + 2 < r.length
      · -- C1: all three in r.reverse. Non-collider (asymmetry).
        have hiR : i < r.length := by omega
        have hi1R : i + 1 < r.length := by omega
        rw [hqP_L i hiR, hqP_L (i + 1) hi1R, hqP_L (i + 2) hC1]
        -- Middle vertex m = r[r.length - 2 - i]. It's in r, so ∉ Z.
        have h_midx : r.length - 1 - (i + 1) = r.length - 2 - i := by omega
        rw [show (⟨r.length - 1 - (i + 1), by omega⟩ : Fin r.length) =
            ⟨r.length - 2 - i, by omega⟩ from Fin.ext h_midx]
        -- Non-collider: G.edge r[r.length-2-i] r[r.length-1-i] from hr_edges
        have hedge_idx : r.length - 2 - i + 1 < r.length := by omega
        have hedge := hr_edges (r.length - 2 - i) hedge_idx
        have heq : r.length - 2 - i + 1 = r.length - 1 - i := by omega
        rw [show (⟨r.length - 2 - i + 1, hedge_idx⟩ : Fin r.length) =
            ⟨r.length - 1 - i, by omega⟩ from Fin.ext heq] at hedge
        -- If IsCollider ℓ m r_v then G.edge ℓ m, but G.edge m ℓ holds (hedge), contradiction.
        have hnotColl : ¬ G.IsCollider (r.get ⟨r.length - 1 - i, by omega⟩)
            (r.get ⟨r.length - 2 - i, by omega⟩)
            (r.get ⟨r.length - 1 - (i + 2), by omega⟩) := by
          intro ⟨hLM, _⟩
          exact G.asymm hedge hLM
        simp only [hnotColl, if_false]
        -- m ∉ Z: m is in r, so by hr_avoid.
        apply hr_avoid
        exact List.get_mem _ _
      · push_neg at hC1  -- r.length ≤ i + 2
        by_cases hC2 : i + 2 = r.length
        · -- C2: i + 2 = r.length, so middle and left are in r.reverse, right at seam.
          have hi_eq : i = r.length - 2 := by omega
          subst hi_eq
          have hiR : r.length - 2 < r.length := by omega
          have hi1R : r.length - 2 + 1 < r.length := by omega
          have hi2_lt : r.length - 2 + 2 < qPrime.length := by rw [hqP_len_eq]; exact hi
          have hi2L : r.length ≤ r.length - 2 + 2 := by omega
          rw [hqP_L (r.length - 2) hiR, hqP_L (r.length - 2 + 1) hi1R,
              hqP_R (r.length - 2 + 2) hi2L hi2_lt]
          -- Middle: r[r.length - 1 - (r.length - 2 + 1)] = r[0] = m_star.
          have h_midx : r.length - 1 - (r.length - 2 + 1) = 0 := by omega
          rw [show (⟨r.length - 1 - (r.length - 2 + 1), by omega⟩ : Fin r.length) =
              ⟨0, by omega⟩ from Fin.ext h_midx]
          rw [hr_get_0]
          -- Non-collider: G.edge m_star r[1] from hr_edges at 0, so ¬ G.edge r[1] m_star.
          have hedge := hr_edges 0 (by omega)
          -- hedge : G.edge r[0] r[1]
          rw [hr_get_0] at hedge
          -- Goal contains r[r.length - 1 - (r.length - 2)] = r[1]
          have h_lidx : r.length - 1 - (r.length - 2) = 1 := by omega
          rw [show (⟨r.length - 1 - (r.length - 2), by omega⟩ : Fin r.length) =
              ⟨1, by omega⟩ from Fin.ext h_lidx]
          -- Non-collider
          have hnotColl : ¬ G.IsCollider (r.get ⟨1, by omega⟩) m_star
              (q.get ⟨j_star + 2 + (r.length - 2 + 2 - r.length), by
                rw [hqP_len_eq, hqTail_len_eq] at hi2_lt
                omega⟩) := by
            intro ⟨hLM, _⟩
            exact G.asymm hedge hLM
          simp only [hnotColl, if_false]
          exact hm_notZ_simple
        · -- C3 or C4 based on i + 1 vs r.length
          by_cases hC3 : i + 1 = r.length
          · -- C3: seam in middle. i = r.length - 1.
            have hi_eq : i = r.length - 1 := by omega
            subst hi_eq
            have hiR : r.length - 1 < r.length := by omega
            have hi1L : r.length ≤ r.length - 1 + 1 := by omega
            have hi2L : r.length ≤ r.length - 1 + 2 := by omega
            have hi1_lt : r.length - 1 + 1 < qPrime.length := by rw [hqP_len_eq]; omega
            have hi2_lt : r.length - 1 + 2 < qPrime.length := by rw [hqP_len_eq]; exact hi
            rw [hqP_L (r.length - 1) hiR, hqP_R (r.length - 1 + 1) hi1L hi1_lt,
                hqP_R (r.length - 1 + 2) hi2L hi2_lt]
            -- Left (in r): r[r.length - 1 - (r.length - 1)] = r[0] = m_star
            have h_lidx : r.length - 1 - (r.length - 1) = 0 := by omega
            rw [show (⟨r.length - 1 - (r.length - 1), by omega⟩ : Fin r.length) =
                ⟨0, by omega⟩ from Fin.ext h_lidx]
            rw [hr_get_0]
            -- Middle: q[j_star + 2 + (r.length - 1 + 1 - r.length)] = q[j_star + 2]
            have h_midx : j_star + 2 + (r.length - 1 + 1 - r.length) = j_star + 2 := by omega
            rw [show (⟨j_star + 2 + (r.length - 1 + 1 - r.length), by
                  rw [hqP_len_eq, hqTail_len_eq] at hi1_lt
                  omega⟩ : Fin q.length) =
                ⟨j_star + 2, hj_lt⟩ from Fin.ext h_midx]
            -- Right: q[j_star + 2 + (r.length - 1 + 2 - r.length)] = q[j_star + 3]
            have h_ridx : j_star + 2 + (r.length - 1 + 2 - r.length) = j_star + 3 := by omega
            have hj_star_3 : j_star + 3 < q.length := by
              rw [hqP_len_eq, hqTail_len_eq] at hi2_lt
              omega
            rw [show (⟨j_star + 2 + (r.length - 1 + 2 - r.length), by omega⟩ : Fin q.length) =
                ⟨j_star + 3, hj_star_3⟩ from Fin.ext h_ridx]
            -- Goal: if IsCollider m_star q[j_star+2] q[j_star+3] then q[j_star+2] ∈ bbZA Z else ∉ Z
            -- Use hqcoll at j_star + 1 (since q[j_star+1] = m_star)
            have hcoll_q := hqcoll (j_star + 1) (by omega)
            simp only at hcoll_q
            have hcast : q.get ⟨j_star + 1, by omega⟩ = m_star := hm_star_def.symm
            have hcast2 : q.get ⟨j_star + 1 + 1, by omega⟩ = q.get ⟨j_star + 2, hj_lt⟩ := by
              congr 1
            have hcast3 : q.get ⟨j_star + 1 + 2, by omega⟩ = q.get ⟨j_star + 3, hj_star_3⟩ := by
              congr 1
            rw [hcast, hcast2, hcast3] at hcoll_q
            by_cases hColl : G.IsCollider m_star (q.get ⟨j_star + 2, hj_lt⟩)
                              (q.get ⟨j_star + 3, hj_star_3⟩)
            · rw [if_pos hColl]
              -- Apply hmax at j' = j_star + 1
              -- Need to convert hColl into the form required by hmax.
              have hcolq : G.IsCollider (q.get ⟨j_star + 1, by omega⟩)
                  (q.get ⟨j_star + 1 + 1, by omega⟩)
                  (q.get ⟨j_star + 1 + 2, hj_star_3⟩) := by
                rw [hcast, hcast2]
                have hcast3' : q.get ⟨j_star + 1 + 2, hj_star_3⟩ =
                    q.get ⟨j_star + 3, hj_star_3⟩ := by congr 1
                rw [hcast3']
                exact hColl
              have hres := hmax (j_star + 1) hj_star_3 (by omega) hcolq
              rw [hcast2] at hres
              exact hres
            · rw [if_neg hColl]
              rw [if_neg hColl] at hcoll_q
              -- hcoll_q : q[j_star+2] ∉ Z ∪ S
              intro hZ
              exact hcoll_q (Finset.mem_union_left _ hZ)
          · -- C4: all three in qTail. i ≥ r.length.
            have hiL : r.length ≤ i := by omega
            have hi1L : r.length ≤ i + 1 := by omega
            have hi2L : r.length ≤ i + 2 := by omega
            have hi_lt : i < qPrime.length := by rw [hqP_len_eq]; omega
            have hi1_lt : i + 1 < qPrime.length := by rw [hqP_len_eq]; omega
            have hi2_lt : i + 2 < qPrime.length := by rw [hqP_len_eq]; exact hi
            rw [hqP_R i hiL hi_lt, hqP_R (i + 1) hi1L hi1_lt, hqP_R (i + 2) hi2L hi2_lt]
            -- Set j := j_star + 2 + (i - r.length)
            set j : ℕ := j_star + 2 + (i - r.length) with hj_def
            have hj_gt : j_star < j := by omega
            have hj_len : j + 2 < q.length := by
              rw [hqP_len_eq, hqTail_len_eq] at hi2_lt
              omega
            -- Rewrite indices to match j
            have h_midx : j_star + 2 + (i + 1 - r.length) = j + 1 := by omega
            have h_ridx : j_star + 2 + (i + 2 - r.length) = j + 2 := by omega
            rw [show (⟨j_star + 2 + (i + 1 - r.length), by omega⟩ : Fin q.length) =
                ⟨j + 1, by omega⟩ from Fin.ext h_midx]
            rw [show (⟨j_star + 2 + (i + 2 - r.length), by omega⟩ : Fin q.length) =
                ⟨j + 2, hj_len⟩ from Fin.ext h_ridx]
            have hcoll_q := hqcoll j hj_len
            simp only at hcoll_q
            by_cases hColl : G.IsCollider (q.get ⟨j, by omega⟩) (q.get ⟨j + 1, by omega⟩)
                              (q.get ⟨j + 2, hj_len⟩)
            · rw [if_pos hColl]
              exact hmax j hj_len hj_gt hColl
            · rw [if_neg hColl]
              rw [if_neg hColl] at hcoll_q
              intro hZ
              exact hcoll_q (Finset.mem_union_left _ hZ)
  · -- Case A: no S-only-activated collider, q itself is active given Z.
    push_neg at hExists
    refine ⟨x₁, q, hx₁XS, hqlen, ?_, hqhead, hqlast⟩
    apply G.isActivePath_Z_of_no_S_only_collider hqact hqInterior
    intro i hi hC
    exact hExists i hi hC

/-- **Source-to-conditioning transfer for d-separation.**

    Moving vertices from the source set `X` to the conditioning set `Z`
    preserves d-separation. Equivalently: `bbReachableVertices (Z ∪ S) X`
    is a subset of `bbReachableVertices Z (X ∪ S)`.

    **Intuition.** Conditioning on `S` (LHS) opens collider paths through
    ancestors-of-`S` but also blocks non-collider paths through `S`. Having
    `S` available as a source (RHS) reproduces the collider-opening effect via
    a directed detour to an `S`-descendant, while blocked non-colliders
    through `S` don't arise because the suffix we keep has no `S`-interior.

    Reduces to `activePath_transfer_cond_to_source` via the BFS↔active-path
    equivalence. -/
theorem dSep_source_to_cond {X Y Z S : Finset V}
    (hXS : Disjoint X S) (h : G.dSep (X ∪ S) Y Z) : G.dSep X Y (Z ∪ S) := by
  rcases h with ⟨hXUSY, hXUSZ, hYZ, hReach⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Disjoint.mono_left (Finset.subset_union_left (s₁ := X) (s₂ := S)) hXUSY
  · rw [Finset.disjoint_left]
    intro v hvX hvZS
    rcases Finset.mem_union.mp hvZS with hvZ | hvS
    · exact Finset.disjoint_left.mp hXUSZ (Finset.mem_union_left S hvX) hvZ
    · exact Finset.disjoint_left.mp hXS hvX hvS
  · rw [Finset.disjoint_left]
    intro v hvY hvZS
    rcases Finset.mem_union.mp hvZS with hvZ | hvS
    · exact Finset.disjoint_left.mp hYZ hvY hvZ
    · exact Finset.disjoint_left.mp hXUSY (Finset.mem_union_right X hvS) hvY
  · refine Disjoint.mono_left ?_ hReach
    intro w hw
    rw [G.bbReachableVertices_iff_activePath] at hw ⊢
    obtain ⟨x, hxX, p, hlen, hact, hhead, hlast⟩ := hw
    obtain ⟨x', p', hx'XS, hlen', hact', hhead', hlast'⟩ :=
      G.activePath_transfer_cond_to_source (X := X) (S := S)
        hxX hlen hact hhead hlast
    exact ⟨x', hx'XS, p', hlen', hact', hhead', hlast'⟩

private theorem isAncestor_mono_edge
    (G' : DAG V) (hEdge : ∀ u v : V, G'.edge u v → G.edge u v)
    {u v : V} (h : G'.isAncestor u v) : G.isAncestor u v := by
  induction h with
  | edge he => exact isAncestor.edge (hEdge _ _ he)
  | trans h₁ he ih => exact isAncestor.trans ih (hEdge _ _ he)

private theorem bbZAncestors_mono_edge
    (G' : DAG V) (hEdge : ∀ u v : V, G'.edge u v → G.edge u v)
    (Z : Finset V) :
    G'.bbZAncestors Z ⊆ G.bbZAncestors Z := by
  intro v hv
  simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rcases hv with hvZ | ⟨w, hwZ, hvw⟩
  · exact Or.inl hvZ
  · exact Or.inr ⟨w, hwZ, G.isAncestor_mono_edge G' hEdge hvw⟩

private theorem uAdj_mono_edge
    (G' : DAG V) (hEdge : ∀ u v : V, G'.edge u v → G.edge u v)
    {u v : V} (h : G'.UAdj u v) : G.UAdj u v := by
  rcases h with huv | hvu
  · exact Or.inl (hEdge _ _ huv)
  · exact Or.inr (hEdge _ _ hvu)

private theorem isCollider_of_supergraph
    (G' : DAG V) (hEdge : ∀ u v : V, G'.edge u v → G.edge u v)
    {l m r : V} (hadj_lm : G'.UAdj l m) (hadj_mr : G'.UAdj m r)
    (hcoll : G.IsCollider l m r) : G'.IsCollider l m r := by
  unfold IsCollider at hcoll ⊢
  obtain ⟨hlm, hrm⟩ := hcoll
  constructor
  · rcases hadj_lm with hlm' | hml'
    · exact hlm'
    · exact absurd (hEdge _ _ hml') (G.asymm hlm)
  · rcases hadj_mr with hmr' | hrm'
    · exact absurd (hEdge _ _ hmr') (G.asymm hrm)
    · exact hrm'

private theorem isActivePath_mono_edge
    (G' : DAG V) (hEdge : ∀ u v : V, G'.edge u v → G.edge u v)
    {Z : Finset V} {p : List V}
    (h : G'.IsActivePath Z p) : G.IsActivePath Z p := by
  obtain ⟨hadj, hcoll⟩ := h
  refine ⟨fun i hi => G.uAdj_mono_edge G' hEdge (hadj i hi), fun i hi => ?_⟩
  simp only
  by_cases hC : G.IsCollider (p.get ⟨i, by omega⟩)
      (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩)
  · rw [if_pos hC]
    have hC' : G'.IsCollider (p.get ⟨i, by omega⟩)
        (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) :=
      G.isCollider_of_supergraph G' hEdge (hadj i (by omega)) (hadj (i + 1) (by omega)) hC
    have hval := hcoll i hi
    simp only at hval
    rw [if_pos hC'] at hval
    exact G.bbZAncestors_mono_edge G' hEdge Z hval
  · rw [if_neg hC]
    have hnotC' : ¬ G'.IsCollider (p.get ⟨i, by omega⟩)
        (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) := by
      intro hC'
      exact hC ⟨hEdge _ _ hC'.1, hEdge _ _ hC'.2⟩
    have hval := hcoll i hi
    simp only at hval
    rwa [if_neg hnotC'] at hval

/-- **d-separation transfers from a supergraph to a subgraph.**

    If `G'` is obtained from `G` by *removing* edges
    (`∀ u v, G'.edge u v → G.edge u v`), and `G ⊨ X ⊥⊥ Y | Z`,
    then `G' ⊨ X ⊥⊥ Y | Z`.

    **Direction.** Fewer edges can only destroy active paths, never create new
    ones, so `G'`-BFS-reachability is a subset of `G`-BFS-reachability.

    **Usage in backdoor / Rule 3.** The split SWIG graph `G(x,z)` is a subgraph
    of `G(x)` (outgoing edges of `.random D` for `D ∈ Z` are removed). A
    d-sep hypothesis in `G(x)` therefore implies the same d-sep in `G(x,z)`.

    **Proof.** Shows `G'.bbZAncestors Z ⊆ G.bbZAncestors Z`
    (monotonicity of `ancestorsSet` in the edge relation, i.e. fewer edges give
    fewer ancestors) and then lifts via `bbReachableVertices_iff_activePath`:
    any `G'`-active path is `G`-active since each `G'`-adjacency is a
    `G`-adjacency and collider activation only grows (collider activation
    requires ancestor witnesses, which are weaker in `G'`). -/
theorem dSep_mono_conditioningSet {X Y Z : Finset V}
    (G' : DAG V)
    (hEdge : ∀ u v : V, G'.edge u v → G.edge u v)
    (h : G.dSep X Y Z) : G'.dSep X Y Z := by
  rcases h with ⟨hXY, hXZ, hYZ, hReach⟩
  refine ⟨hXY, hXZ, hYZ, ?_⟩
  refine Disjoint.mono_left ?_ hReach
  intro v hv
  rw [G'.bbReachableVertices_iff_activePath] at hv
  rw [G.bbReachableVertices_iff_activePath]
  obtain ⟨x, hxX, p, hlen, hact, hhead, hlast⟩ := hv
  exact ⟨x, hxX, p, hlen, G.isActivePath_mono_edge G' hEdge hact, hhead, hlast⟩

/-- d-separation is symmetric: if `X ⊥⊥ Y | Z` then `Y ⊥⊥ X | Z`.

    Proof strategy: by contrapositive, using the equivalence between the BFS
    computation and the existence of active paths. If `Y` is not d-separated
    from `X`, there is an active path from `Y` to `X`, which reversed gives
    an active path from `X` to `Y`, contradicting `dSep X Y Z`. -/
theorem dSep_symm (X Y Z : Finset V) (h : G.dSep X Y Z) :
    G.dSep Y X Z := by
  rcases h with ⟨hXY, hXZ, hYZ, hReach⟩
  refine ⟨hXY.symm, hYZ, hXZ, ?_⟩
  rw [Finset.disjoint_left] at hReach ⊢
  intro v hv hX
  -- v ∈ bbReachableVertices Z Y and v ∈ X
  -- By BFS correctness, there is an active path from some y ∈ Y to v
  rw [bbReachableVertices_iff_activePath] at hv
  obtain ⟨y, hy, p, hlen, hact, hhead, hlast⟩ := hv
  -- Reverse the path: active path from v to y
  have hact' := G.isActivePath_reverse hact
  -- y is reachable from v ∈ X via the reversed active path, so y ∈ bbReachableVertices Z X
  have hyReach : y ∈ G.bbReachableVertices Z X := by
    rw [bbReachableVertices_iff_activePath]
    exact ⟨v, hX, p.reverse, by simp only [List.length_reverse]; exact hlen,
      hact', by rwa [List.head?_reverse], by rwa [List.getLast?_reverse]⟩
  -- But h says nothing in bbReachableVertices Z X is in Y, contradicting y ∈ Y
  exact hReach hyReach hy

end DAG

end Causalean
