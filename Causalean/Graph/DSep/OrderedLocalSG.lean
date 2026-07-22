/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.DSep.Ancestral

/-! # Ordered-local semi-graphoid closure of a DAG

This file introduces a purely combinatorial inductive predicate `DAG.OrderedLocalSG`
on a DAG, recording which conditional-independence triples are derivable from the
*ordered-local basis* (each node is independent of its non-parent predecessors given
its parents) using only the semi-graphoid axioms (symmetry, decomposition, weak
union, contraction — no graphoid intersection). It then proves the graph theorem
`orderedLocalSG_of_dSep_with_fixed`: every d-separation is such a derivation.

This is the graph-level heart of the global Markov property. The probabilistic
content is added separately by interpreting a derivation as a conditional
independence under the joint distribution (`fullCondIndep_of_orderedLocalSG`), which
maps each constructor to the matching `FullCondIndep` semi-graphoid lemma. Splitting
the proof this way keeps all measure theory out of the graph induction.
-/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

-- ============================================================
-- § 1. The ordered-local semi-graphoid closure
-- ============================================================

/-- **Ordered-local semi-graphoid closure.** A conditional-independence claim
    between two random-node blocks, given a third block, belongs to this closure
    when it can be derived from the DAG's ordered-local Markov basis using only
    the semi-graphoid rules.

    The basis constructor `basis` is the ordered/local Markov statement: a node `v`
    is independent of any block `P` of its non-descendants (with its random parents
    removed) given its random parents `parents v ∩ R`. The remaining constructors are
    exactly the four semi-graphoid axioms; there is intentionally no graphoid
    `intersection` constructor. `nil` records the trivial independence of the empty
    source set from anything.

    This is the combinatorial skeleton that, once interpreted under the joint
    distribution, yields the global Markov property. -/
inductive OrderedLocalSG (G : DAG V) (R : Finset V) :
    Finset V → Finset V → Finset V → Prop
  | nil (Y Z : Finset V) (hY : Y ⊆ R) (hZ : Z ⊆ R) : OrderedLocalSG G R ∅ Y Z
  | basis (v : V) (hv : v ∈ R) (P : Finset V)
      (hP : P ⊆ R) (hND : P ⊆ G.nonDescendants v) (hPa : G.parents v ∩ R ⊆ P) :
      OrderedLocalSG G R {v} (P \ (G.parents v ∩ R)) (G.parents v ∩ R)
  | symm {X Y Z : Finset V} : OrderedLocalSG G R X Y Z → OrderedLocalSG G R Y X Z
  | decomp {X Y W Z : Finset V} :
      OrderedLocalSG G R X (Y ∪ W) Z → OrderedLocalSG G R X Y Z
  | weakUnion {X Y W Z : Finset V} :
      OrderedLocalSG G R X (Y ∪ W) Z → OrderedLocalSG G R X Y (Z ∪ W)
  | contract {X Y W Z : Finset V} :
      OrderedLocalSG G R X Y (Z ∪ W) → OrderedLocalSG G R X W Z →
      OrderedLocalSG G R X (Y ∪ W) Z

/-- Every triple appearing in an ordered-local derivation has all three sets
    contained in the ambient random set `R`. Used by the SCM interpretation to
    recover the `⊆ randomVars` side-conditions of `FullCondIndep`. -/
theorem OrderedLocalSG.subset_random {G : DAG V} {R X Y Z : Finset V}
    (h : G.OrderedLocalSG R X Y Z) : X ⊆ R ∧ Y ⊆ R ∧ Z ⊆ R := by
  induction h with
  | nil Y Z hY hZ => exact ⟨Finset.empty_subset _, hY, hZ⟩
  | basis v hv P hP hND hPa =>
      refine ⟨Finset.singleton_subset_iff.mpr hv, ?_, Finset.inter_subset_right⟩
      exact (Finset.sdiff_subset).trans hP
  | symm _ ih => exact ⟨ih.2.1, ih.1, ih.2.2⟩
  | decomp _ ih =>
      exact ⟨ih.1, (Finset.subset_union_left).trans ih.2.1, ih.2.2⟩
  | weakUnion _ ih =>
      refine ⟨ih.1, (Finset.subset_union_left).trans ih.2.1, ?_⟩
      exact Finset.union_subset ih.2.2 ((Finset.subset_union_right).trans ih.2.1)
  | contract _ _ ih1 ih2 =>
      exact ⟨ih1.1, Finset.union_subset ih1.2.1 ih2.2.1, ih2.2.2⟩

-- ============================================================
-- § 2. Topological-maximum selection in an ancestral set
-- ============================================================

/-- The lexicographic termination measure for the peel induction: the size of
    the query's ancestral set paired with the "topological height" of the random
    conditioning set `Zr` (the supremum of `topoOrder v + 1`, hence `0` when `Zr`
    is empty). When the topologically-maximal query node is moved out of `Zr` into
    the target, the first component stays equal while this height strictly drops —
    every node added to the condition is strictly topologically below the removed
    maximum. -/
private noncomputable def peelMeasure (G : DAG V) (X Y Zr Zf : Finset V) : ℕ × ℕ :=
  ((G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf)).card, Zr.sup (fun v => G.topoOrder v + 1))

-- ============================================================
-- § 2′. Topological-maximum selection in an ancestral set
-- ============================================================

/-- A topologically-maximal element of an ancestral set `ancestralSet Q` lies in
    the seed set `Q` itself: every element of an ancestral set is either in `Q`
    or a strict ancestor of some element of `Q`, and a strict ancestor has a
    strictly smaller topological order, so it cannot be the maximum. -/
private theorem topoMax_mem_seed {Q : Finset V} {n : V}
    (hn : n ∈ G.ancestralSet Q)
    (hmax : ∀ m ∈ G.ancestralSet Q, G.topoOrder m ≤ G.topoOrder n) :
    n ∈ Q := by
  simp only [ancestralSet, Finset.mem_union, ancestorsSet, Finset.mem_filter,
    Finset.mem_univ, true_and] at hn
  rcases hn with hnQ | ⟨w, hwQ, haw⟩
  · exact hnQ
  · -- `n` is a strict ancestor of `w ∈ Q`; but `w ∈ ancestralSet Q`, so
    -- `topoOrder w ≤ topoOrder n < topoOrder w`, contradiction.
    exfalso
    have hwAnc : w ∈ G.ancestralSet Q :=
      G.subset_ancestralSet Q (by exact hwQ)
    have h1 : G.topoOrder w ≤ G.topoOrder n := hmax w hwAnc
    have h2 : G.topoOrder n < G.topoOrder w := G.isAncestor_topoOrder_lt haw
    omega

/-- The ancestral set absorbs subsets of itself: if `Q' ⊆ ancestralSet Q` then
    `ancestralSet Q' ⊆ ancestralSet Q`. (Ancestral-set idempotence, one direction.) -/
private theorem ancestralSet_subset_of_subset_ancestralSet {Q Q' : Finset V}
    (h : Q' ⊆ G.ancestralSet Q) : G.ancestralSet Q' ⊆ G.ancestralSet Q := by
  intro u hu
  simp only [ancestralSet, Finset.mem_union, ancestorsSet, Finset.mem_filter,
    Finset.mem_univ, true_and] at hu ⊢
  rcases hu with huQ' | ⟨q', hq'Q', haq'⟩
  · have := h huQ'
    simpa only [ancestralSet, Finset.mem_union, ancestorsSet, Finset.mem_filter,
      Finset.mem_univ, true_and] using this
  · have hq' := h hq'Q'
    simp only [ancestralSet, Finset.mem_union, ancestorsSet, Finset.mem_filter,
      Finset.mem_univ, true_and] at hq'
    rcases hq' with hq'Q | ⟨q, hqQ, haq'q⟩
    · exact Or.inr ⟨q', hq'Q, haq'⟩
    · exact Or.inr ⟨q, hqQ, G.isAncestor_trans haq' haq'q⟩

/-- **Card strictly drops when peeling a topological maximum.** If `n` is the
    topological maximum of `ancestralSet Q`, lies in `Q`, and `Q'` is contained in
    `ancestralSet Q` but omits `n`, then `ancestralSet Q'` is a strict subset of
    `ancestralSet Q`, so its cardinality is strictly smaller. This is the first
    component of the termination measure for every card-dropping recursive call. -/
private theorem ancestralSet_card_lt_of_peel {Q Q' : Finset V} {n : V}
    (hnAnc : n ∈ G.ancestralSet Q)
    (hmax : ∀ m ∈ G.ancestralSet Q, G.topoOrder m ≤ G.topoOrder n)
    (hQ'sub : Q' ⊆ G.ancestralSet Q) (hnQ' : n ∉ Q') :
    (G.ancestralSet Q').card < (G.ancestralSet Q).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (G.ancestralSet_subset_of_subset_ancestralSet hQ'sub)]
  refine ⟨n, hnAnc, ?_⟩
  intro hnAnc'
  -- `n ∈ ancestralSet Q'` means either `n ∈ Q'` or `n` is a strict ancestor of some
  -- `q' ∈ Q' ⊆ ancestralSet Q`; the hypotheses rule out both cases.
  simp only [ancestralSet, Finset.mem_union, ancestorsSet, Finset.mem_filter,
    Finset.mem_univ, true_and] at hnAnc'
  rcases hnAnc' with hnQ'' | ⟨q', hq'Q', haq'⟩
  · exact hnQ' hnQ''
  · have hq'Anc : q' ∈ G.ancestralSet Q := hQ'sub hq'Q'
    have h1 : G.topoOrder q' ≤ G.topoOrder n := hmax q' hq'Anc
    have h2 : G.topoOrder n < G.topoOrder q' := G.isAncestor_topoOrder_lt haq'
    omega

/-- **Height strictly drops when a maximal conditioning node leaves the set.** If
    `n` is the topological maximum of `ancestralSet Q` and lies in `Zr`, while `S`
    is contained in `ancestralSet Q` and omits `n`, then the `topoOrder`-height of
    `S` is strictly below that of `Zr`. This is the second component of the
    termination measure for the equal-cardinality branch recursive calls. -/
private theorem sup_topoOrder_lt_of_peel {Q Zr S : Finset V} {n : V}
    (hmax : ∀ m ∈ G.ancestralSet Q, G.topoOrder m ≤ G.topoOrder n)
    (hnZr : n ∈ Zr) (hSsub : S ⊆ G.ancestralSet Q) (hnS : n ∉ S) :
    (S.sup (fun v => G.topoOrder v + 1)) < (Zr.sup (fun v => G.topoOrder v + 1)) := by
  have hZr_ge : G.topoOrder n + 1 ≤ Zr.sup (fun v => G.topoOrder v + 1) :=
    Finset.le_sup (f := fun v => G.topoOrder v + 1) hnZr
  have hS_le : S.sup (fun v => G.topoOrder v + 1) ≤ G.topoOrder n := by
    rw [Finset.sup_le_iff]
    intro s hs
    have hsAnc : s ∈ G.ancestralSet Q := hSsub hs
    have hle : G.topoOrder s ≤ G.topoOrder n := hmax s hsAnc
    have hne : s ≠ n := fun h => hnS (h ▸ hs)
    have : G.topoOrder s ≠ G.topoOrder n := fun h => hne (G.topoOrder_injective h)
    omega
  omega

-- ============================================================
-- § 3. d-separation surgery lemmas for the peel
-- ============================================================

/-- If `n` is d-separated from `Y` given any `D`, then no parent of `n` lies in
    `Y`: a parent `a ∈ Y` would give the length-2 active path `[n, a]` from `n`
    into `Y`, contradicting the separation. -/
private theorem parents_disjoint_of_dSep_singleton {n : V} {Y D : Finset V}
    (hdSep : G.dSep {n} Y D) : Disjoint (G.parents n) Y := by
  rw [Finset.disjoint_left]
  intro a haPar haY
  -- The path `[n, a]` is active given `D` (no interior vertex), from `n` to `a ∈ Y`.
  have hedge : G.edge a n := G.mem_parents.mp haPar
  have hact : G.IsActivePath D [n, a] := by
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · -- length 2 ⟹ i = 0; the only adjacency is `UAdj n a`, from `edge a n`.
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      exact Or.inr (by simpa using hedge)
    · -- length 2 ⟹ no interior triple
      simp only [List.length_cons, List.length_nil] at hi
      omega
  have hmem : a ∈ G.bbReachableVertices D {n} := by
    rw [G.bbReachableVertices_iff_activePath]
    exact ⟨n, Finset.mem_singleton_self n, [n, a], by simp, hact, rfl, rfl⟩
  exact (Finset.disjoint_left.mp hdSep.2.2.2 hmem) haY

/-- **Parents inherit a source's d-separation.** If a single node `n` is
    d-separated from `Y` given `D`, then every random parent `a` of `n` that is
    *not* already in `D` is also d-separated from `Y` given `D`.

    Graphically: an active `a → … → Y` path can be prepended with the edge
    `a → n` (giving `n, a, …, Y`); the new interior vertex `a` is a non-collider
    there (`a → n`, not `n → a`), and `a ∉ D`, so the extended path is active from
    `n` to `Y`, contradicting `dSep {n} Y D`. -/
private theorem dSep_parents_of_maximal_source {n : V} {Y D A0 : Finset V}
    (hdSep : G.dSep {n} Y D)
    (hA0_par : ∀ a ∈ A0, G.edge a n)
    (hA0_D : ∀ a ∈ A0, a ∉ D) :
    G.dSep A0 Y D := by
  refine ⟨?_, ?_, hdSep.2.2.1, ?_⟩
  · exact (G.parents_disjoint_of_dSep_singleton hdSep).mono_left (by
      intro a ha
      exact G.mem_parents.mpr (hA0_par a ha))
  · exact Finset.disjoint_left.mpr hA0_D
  rw [Finset.disjoint_left]
  intro y hyReach hyY
  -- Extract an active path `a → … → y` for some `a ∈ A0`.
  rw [G.bbReachableVertices_iff_activePath] at hyReach
  obtain ⟨a, haA0, p, hlen, hact, hhead, hlast⟩ := hyReach
  -- `p` has length ≥ 2 and head `a`, so `p = a :: u :: r`.
  obtain ⟨u, r, hp⟩ : ∃ u r, p = a :: u :: r := by
    match p, hlen, hhead with
    | _ :: u :: r, _, hhead =>
        exact ⟨u, r, by simp only [List.head?_cons, Option.some_inj] at hhead; subst hhead; rfl⟩
  subst hp
  -- Prepend `n` via the edge `a → n`; `a` is a non-collider in `(n, a, u)`.
  have hedge : G.edge a n := hA0_par a haA0
  have hnotcoll : ¬ G.IsCollider n a u := fun hC => G.asymm hedge hC.1
  have htri : (if G.IsCollider n a u then a ∈ G.bbZAncestors D else a ∉ D) := by
    rw [if_neg hnotcoll]; exact hA0_D a haA0
  have hact' : G.IsActivePath D (n :: a :: u :: r) :=
    G.isActivePath_cons_of_active_triple (Or.inr hedge) htri hact
  -- This new active path witnesses `y ∈ bbReachableVertices D {n}`, contradiction.
  have hyReach' : y ∈ G.bbReachableVertices D {n} := by
    rw [G.bbReachableVertices_iff_activePath]
    refine ⟨n, Finset.mem_singleton_self n, n :: a :: u :: r, by simp, hact', rfl, ?_⟩
    simpa using hlast
  exact (Finset.disjoint_left.mp hdSep.2.2.2 hyReach') hyY

/-- **Re-inserting a non-blocking node keeps a path active.** If `p` is active
    given `D` and `n` never sits as a *non-collider* on `p`, then `p` stays active
    given `insert n D`: adding `n` to the conditioning set can only widen collider
    activation (the ancestral set grows) and the only non-collider it could block
    is `n` itself, which is excluded by hypothesis. -/
private theorem isActivePath_insert_cond {D : Finset V} {p : List V} {n : V}
    (hact : G.IsActivePath D p)
    (hno : ∀ (i : ℕ) (hi : i + 2 < p.length),
      p.get ⟨i + 1, by omega⟩ = n →
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩)) :
    G.IsActivePath (insert n D) p := by
  obtain ⟨hadj, hcoll⟩ := hact
  refine ⟨hadj, fun i hi => ?_⟩
  have hval := hcoll i hi
  simp only at hval ⊢
  set l := p.get ⟨i, by omega⟩
  set m := p.get ⟨i + 1, by omega⟩
  set r := p.get ⟨i + 2, hi⟩
  by_cases hC : G.IsCollider l m r
  · rw [if_pos hC] at hval ⊢
    exact (G.ancestralSet_mono (Finset.subset_insert n D)) hval
  · rw [if_neg hC] at hval ⊢
    rw [Finset.mem_insert, not_or]
    refine ⟨fun hmn => hC (hno i hi hmn), hval⟩

/-- **A maximal random conditioning node can be dropped.** If `n ∈ Zr` is the
    topological maximum of the query's ancestral set, then deleting it from the
    conditioning set preserves d-separation of `X` and `Y`.

    Graphically: since `n` is topologically maximal among all ancestors of
    `X ∪ Y ∪ Zr ∪ Zf`, no proper descendant of `n` lies in that ancestral set, so
    on every active `X → Y` path the node `n` (if present) can only be a collider,
    and that collider is activated solely by `n` itself. Removing `n` from the
    conditioning set therefore closes every path through `n` and creates none. -/
private theorem dSep_erase_maximal_random_condition {X Y Zr Zf : Finset V} {n : V}
    (hnZr : n ∈ Zr)
    (hmax : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf),
      G.topoOrder m ≤ G.topoOrder n)
    (hdSep : G.dSep X Y (Zr ∪ Zf)) :
    G.dSep X Y ((Zr.erase n) ∪ Zf) := by
  refine ⟨hdSep.1, ?_, ?_, ?_⟩
  · exact hdSep.2.1.mono_right (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_erase] at hz ⊢
      rcases hz with hz | hz
      · exact Or.inl hz.2
      · exact Or.inr hz)
  · exact hdSep.2.2.1.mono_right (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_erase] at hz ⊢
      rcases hz with hz | hz
      · exact Or.inl hz.2
      · exact Or.inr hz)
  rw [Finset.disjoint_left]
  intro y hyReach hyY
  -- Active path `p : x → y` given `Z' ∪ Zf`.
  rw [G.bbReachableVertices_iff_activePath] at hyReach
  obtain ⟨x, hxX, p, hlen, hact, hhead, hlast⟩ := hyReach
  -- Every node of `p` lies in `ancestralSet Q` (Q = X∪Y∪Zr∪Zf).
  have hpAnc : ∀ v ∈ p, v ∈ G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf) := by
    intro v hv
    have := G.activePath_nodes_are_ancestors hxX hyY hact hhead hlast v hv
    refine G.ancestralSet_mono ?_ this
    intro z hz
    simp only [Finset.mem_union, Finset.mem_erase] at hz ⊢
    rcases hz with (h | h) | h | h
    exacts [Or.inl (Or.inl (Or.inl h)), Or.inl (Or.inl (Or.inr h)),
      Or.inl (Or.inr h.2), Or.inr h]
  -- `n` is never a non-collider on `p` (it would force a strictly-larger node).
  have hno : ∀ (i : ℕ) (hi : i + 2 < p.length),
      p.get ⟨i + 1, by omega⟩ = n →
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) := by
    intro i hi hmn
    by_contra hC
    obtain ⟨hadj, _⟩ := hact
    have hadj_lm := hadj i (by omega)
    have hadj_mr := hadj (i + 1) (by omega)
    -- Outgoing edge from `m = n` to a path neighbour.
    have hout := G.nonCollider_has_outgoing hadj_lm hadj_mr hC
    rcases hout with hedge | hedge <;> rw [hmn] at hedge
    · have hAnc := hpAnc _ (List.get_mem p ⟨i, by omega⟩)
      have h1 : G.topoOrder (p.get ⟨i, by omega⟩) ≤ G.topoOrder n := hmax _ hAnc
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge)
      omega
    · have hAnc := hpAnc _ (List.get_mem p ⟨i + 1 + 1, by omega⟩)
      have h1 : G.topoOrder (p.get ⟨i + 1 + 1, by omega⟩) ≤ G.topoOrder n := hmax _ hAnc
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge)
      omega
  -- Hence `p` is active given `insert n (Z' ∪ Zf) = Zr ∪ Zf`, contradicting `hdSep`.
  have hact' : G.IsActivePath (insert n (Zr.erase n ∪ Zf)) p :=
    G.isActivePath_insert_cond hact hno
  have hins : insert n (Zr.erase n ∪ Zf) = Zr ∪ Zf := by
    ext z; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (rfl | (⟨_, h⟩ | h) )
      exacts [Or.inl hnZr, Or.inl h, Or.inr h]
    · rintro (h | h)
      · by_cases hz : z = n
        · exact Or.inl hz
        · exact Or.inr (Or.inl ⟨hz, h⟩)
      · exact Or.inr (Or.inr h)
  rw [hins] at hact'
  have : y ∈ G.bbReachableVertices (Zr ∪ Zf) X := by
    rw [G.bbReachableVertices_iff_activePath]
    exact ⟨x, hxX, p, hlen, hact', hhead, hlast⟩
  exact (Finset.disjoint_left.mp hdSep.2.2.2 this) hyY

/-- **Lifting a path from a cross-condition to `insert n S`.** A path active given
    `S ∪ W` whose interior colliders are all activated by `S` alone, and on which
    `n` never sits as an interior non-collider, is active given `insert n S`:
    colliders stay activated (monotonicity), and non-collider middles, being outside
    `S ∪ W` and distinct from `n`, stay outside `insert n S`. -/
private theorem lift_crosscond_to_insert {S W : Finset V} {p : List V} {n : V}
    (hact : G.IsActivePath (S ∪ W) p)
    (hcollS : ∀ (i : ℕ) (hi : i + 2 < p.length),
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) →
      p.get ⟨i + 1, by omega⟩ ∈ G.ancestralSet S)
    (hno_n : ∀ (i : ℕ) (hi : i + 2 < p.length),
      p.get ⟨i + 1, by omega⟩ = n →
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩)) :
    G.IsActivePath (insert n S) p := by
  obtain ⟨hadj, hcoll⟩ := hact
  refine ⟨hadj, fun i hi => ?_⟩
  have hval := hcoll i hi
  simp only at hval ⊢
  set l := p.get ⟨i, by omega⟩ with hl
  set m := p.get ⟨i + 1, by omega⟩ with hm
  set r := p.get ⟨i + 2, hi⟩ with hr
  by_cases hC : G.IsCollider l m r
  · rw [if_pos hC] at hval ⊢
    show m ∈ G.bbZAncestors (insert n S)
    exact (G.ancestralSet_mono (Finset.subset_insert n S)) (hcollS i hi hC)
  · rw [if_neg hC] at hval ⊢
    rw [Finset.mem_insert, not_or]
    refine ⟨fun hmn => hC (hno_n i hi hmn), fun hmS => hval (Finset.mem_union_left _ hmS)⟩

/-- **The final edge of a path to a topological maximum points into it.** On an
    active path whose nodes all lie in an ancestral set with topological maximum
    `n`, if the path ends at `n` then its last edge points into `n`: a child of `n`
    on the path would be a strict descendant, hence a strictly larger node. -/
private theorem last_edge_into_max
    {D bigQ : Finset V} {p : List V} {n : V}
    (hp_len : p.length ≥ 2) (hact : G.IsActivePath D p) (hlast : p.getLast? = some n)
    (hpAnc : ∀ v ∈ p, v ∈ G.ancestralSet bigQ)
    (hmax : ∀ m ∈ G.ancestralSet bigQ, G.topoOrder m ≤ G.topoOrder n) :
    G.edge (p.get ⟨p.length - 2, by omega⟩) n := by
  -- The last adjacency is between `p[len-2]` and `p[len-1] = n`.
  have hadj := hact.1 (p.length - 2) (by omega)
  have hlast_get : p.get ⟨p.length - 2 + 1, by omega⟩ = n := by
    have hpne : p ≠ [] := by intro h; rw [h] at hp_len; simp at hp_len
    have h := List.getLast?_eq_some_getLast hpne
    rw [hlast] at h
    have hn_eq : p.getLast hpne = n := Option.some_inj.mp h.symm
    have hidx : (⟨p.length - 2 + 1, by omega⟩ : Fin p.length) = ⟨p.length - 1, by omega⟩ :=
      Fin.ext (show p.length - 2 + 1 = p.length - 1 by omega)
    rw [hidx, List.get_eq_getElem, ← hn_eq, List.getLast_eq_getElem]
  rw [hlast_get] at hadj
  -- `hadj : UAdj p[len-2] n`. Rule out `edge n p[len-2]` by topo-maximality.
  rcases hadj with hin | hout
  · exact hin
  · exfalso
    have hAnc := hpAnc _ (List.get_mem p ⟨p.length - 2, by omega⟩)
    have h1 : G.topoOrder (p.get ⟨p.length - 2, by omega⟩) ≤ G.topoOrder n := hmax _ hAnc
    have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hout)
    omega

/-- **Concatenating two active paths at a collider.** If `pa` is active given `Z`
    ending at `n`, `pb` is active given `Z` starting at `n`, the last edge of `pa`
    and the first edge of `pb` both point *into* `n` (so `n` becomes a collider at
    the seam), and `n ∈ Z`, then the glued path `pa ++ pb.tail` is an active path
    given `Z` from the head of `pa` to the last of `pb`. -/
private theorem activePath_join_at_collider
    {Z : Finset V} {n x y : V} {pa pb : List V}
    (hpa_len : pa.length ≥ 2) (hpa_head : pa.head? = some x)
    (hpa_last : pa.getLast? = some n) (hpa_act : G.IsActivePath Z pa)
    (hpb_len : pb.length ≥ 2) (hpb_head : pb.head? = some n)
    (hpb_last : pb.getLast? = some y) (hpb_act : G.IsActivePath Z pb)
    (hpa_in : G.edge (pa.get ⟨pa.length - 2, by omega⟩) n)
    (hpb_in : G.edge (pb.get ⟨1, by omega⟩) n)
    (hnZ : n ∈ Z) :
    let p := pa ++ pb.tail
    p.length ≥ 2 ∧ p.head? = some x ∧ p.getLast? = some y ∧
      G.IsActivePath Z p := by
  have hpa_ne : pa ≠ [] := by intro h; rw [h] at hpa_len; simp at hpa_len
  have hpb_ne : pb ≠ [] := by intro h; rw [h] at hpb_len; simp at hpb_len
  -- pb.head = n
  have hpb_head_eq : pb.head hpb_ne = n := by
    have h := List.head?_eq_some_head hpb_ne; rw [hpb_head] at h
    exact (Option.some_inj.mp h.symm)
  -- pa.getLast = n
  have hpa_last_eq : pa.getLast hpa_ne = n := by
    have h := List.getLast?_eq_some_getLast hpa_ne; rw [hpa_last] at h
    exact (Option.some_inj.mp h.symm)
  -- pa.head = x
  have hpa_head_eq : pa.head hpa_ne = x := by
    have h := List.head?_eq_some_head hpa_ne; rw [hpa_head] at h
    exact (Option.some_inj.mp h.symm)
  -- pb.getLast = y
  have hpb_last_eq : pb.getLast hpb_ne = y := by
    have h := List.getLast?_eq_some_getLast hpb_ne; rw [hpb_last] at h
    exact (Option.some_inj.mp h.symm)
  -- pb = n :: pb.tail
  have hpb_decomp : pb = n :: pb.tail := by
    conv_lhs => rw [← List.cons_head_tail hpb_ne]; rw [hpb_head_eq]
  have hpb_tail_len : pb.tail.length = pb.length - 1 := List.length_tail
  have hpb_tail_ne : pb.tail ≠ [] := by
    rw [← List.length_pos_iff, hpb_tail_len]; omega
  set p := pa ++ pb.tail with hp_def
  set R := pa.length with hR_def
  have hp_len_eq : p.length = R + pb.tail.length := by
    simp only [hp_def, List.length_append, ← hR_def]
  have hp_len : p.length ≥ 2 := by rw [hp_len_eq]; omega
  have hp_head : p.head? = some x := by
    have : p.head? = pa.head? := List.head?_append_of_ne_nil _ hpa_ne
    rw [this, hpa_head]
  have hp_last : p.getLast? = some y := by
    have hlast_tail : pb.tail.getLast? = some y := by
      have heq : pb = [n] ++ pb.tail := by simpa using hpb_decomp
      have := List.getLast?_append_of_ne_nil [n] hpb_tail_ne
      rw [← heq] at this; rw [← this]; exact hpb_last
    simp only [hp_def, List.getLast?_append, hlast_tail]; rfl
  refine ⟨hp_len, hp_head, hp_last, ?_⟩
  -- Index translation: p[k] = pa[k] for k < R; p[k] = pb[k-R+1] for k ≥ R.
  have hp_L : ∀ (k : ℕ) (hkR : k < R),
      p.get ⟨k, by rw [hp_len_eq]; omega⟩ = pa.get ⟨k, hkR⟩ := by
    intro k hkR
    simp only [hp_def, List.get_eq_getElem, List.getElem_append_left (h := hkR)]
  have hpb_tail_get : ∀ (j : ℕ) (hj1 : j < pb.tail.length) (hj2 : j + 1 < pb.length),
      pb.tail[j]'hj1 = pb[j + 1]'hj2 := by
    intro j hj1 hj2
    have : pb[j + 1] = (n :: pb.tail)[j + 1]'(by rw [← hpb_decomp]; exact hj2) := by congr 1
    rw [this]; simp [List.getElem_cons_succ]
  have hp_R : ∀ (k : ℕ) (hkL : R ≤ k) (hk : k < p.length),
      p.get ⟨k, hk⟩ = pb.get ⟨k - R + 1, by
        rw [hp_len_eq, hpb_tail_len] at hk; omega⟩ := by
    intro k hkL hk
    have hk_app : R ≤ k := hkL
    have htail_idx_lt : k - R < pb.tail.length := by
      rw [hp_len_eq] at hk; omega
    have hpget : p.get ⟨k, hk⟩ = pb.tail[k - R]'htail_idx_lt := by
      simp only [hp_def, List.get_eq_getElem]
      rw [List.getElem_append_right (by rw [← hR_def]; exact hk_app)]
    rw [hpget]
    rw [hpb_tail_get (k - R) htail_idx_lt (by rw [hpb_tail_len] at htail_idx_lt; omega)]
    simp [List.get_eq_getElem]
  -- pb[0] = n, pa[R-1] = n.
  have hpb_get_0 : pb.get ⟨0, by omega⟩ = n := by
    rw [List.get_eq_getElem, List.getElem_zero]; exact hpb_head_eq
  have hpa_get_last : pa.get ⟨R - 1, by omega⟩ = n := by
    rw [List.get_eq_getElem]
    have := List.getLast_eq_getElem hpa_ne
    rw [hpa_last_eq] at this
    rw [← this]
  refine ⟨?_, ?_⟩
  · -- Adjacency.
    intro i hi
    rw [hp_len_eq] at hi
    by_cases hA1 : i + 1 < R
    · -- Both in pa.
      have hiR : i < R := by omega
      rw [hp_L i hiR, hp_L (i + 1) hA1]
      exact hpa_act.1 i hA1
    · push_neg at hA1
      by_cases hA2 : i + 1 = R
      · -- Seam at i = R-1: UAdj(pa[R-1]=n, pb.tail[0]=pb[1]).
        have hi_eq : i = R - 1 := by omega
        subst hi_eq
        have hiR : R - 1 < R := by omega
        rw [hp_L (R - 1) hiR]
        have hi1L : R ≤ R - 1 + 1 := by omega
        have hi1_lt : R - 1 + 1 < p.length := by rw [hp_len_eq]; exact hi
        rw [hp_R (R - 1 + 1) hi1L hi1_lt]
        rw [hpa_get_last]
        have h_yidx : R - 1 + 1 - R + 1 = 1 := by omega
        rw [show (⟨R - 1 + 1 - R + 1, by
              rw [hp_len_eq, hpb_tail_len] at hi1_lt; omega⟩ : Fin pb.length) =
            ⟨1, by omega⟩ from Fin.ext h_yidx]
        -- UAdj n pb[1] from edge pb[1] → n.
        exact Or.inr hpb_in
      · -- Both in pb.tail. i ≥ R.
        have hiL : R ≤ i := by omega
        have hi1L : R ≤ i + 1 := by omega
        have hi_lt : i < p.length := by rw [hp_len_eq]; omega
        have hi1_lt : i + 1 < p.length := by rw [hp_len_eq]; exact hi
        rw [hp_R i hiL hi_lt, hp_R (i + 1) hi1L hi1_lt]
        have hidx : (i - R + 1) + 1 < pb.length := by omega
        have hadj := hpb_act.1 (i - R + 1) hidx
        have he : (i - R + 1) + 1 = (i + 1) - R + 1 := by omega
        rw [show (⟨(i - R + 1) + 1, hidx⟩ : Fin pb.length) =
            ⟨(i + 1) - R + 1, by omega⟩ from Fin.ext he] at hadj
        exact hadj
  · -- Collider condition.
    intro i hi
    rw [hp_len_eq] at hi
    by_cases hC1 : i + 2 < R
    · -- All three in pa.
      have hiR : i < R := by omega
      have hi1R : i + 1 < R := by omega
      rw [hp_L i hiR, hp_L (i + 1) hi1R, hp_L (i + 2) hC1]
      exact hpa_act.2 i hC1
    · push_neg at hC1
      by_cases hC2 : i + 2 = R
      · -- Seam collider: middle = pa[R-1] = n. Triple (pa[R-2], n, pb[1]).
        have hi_eq : i = R - 2 := by omega
        subst hi_eq
        have hiR : R - 2 < R := by omega
        have hi1R : R - 2 + 1 < R := by omega
        have hi2L : R ≤ R - 2 + 2 := by omega
        have hi2_lt : R - 2 + 2 < p.length := by rw [hp_len_eq]; exact hi
        rw [hp_L (R - 2) hiR, hp_L (R - 2 + 1) hi1R, hp_R (R - 2 + 2) hi2L hi2_lt]
        rw [show (⟨R - 2 + 1, by omega⟩ : Fin pa.length) = ⟨R - 1, by omega⟩ from
          Fin.ext (show R - 2 + 1 = R - 1 by omega)]
        rw [hpa_get_last]
        have h_ridx : R - 2 + 2 - R + 1 = 1 := by omega
        rw [show (⟨R - 2 + 2 - R + 1, by
              rw [hp_len_eq, hpb_tail_len] at hi2_lt; omega⟩ : Fin pb.length) =
            ⟨1, by omega⟩ from Fin.ext h_ridx]
        -- left = pa[R-2]; edge into n is hpa_in (pa[R-2]→n); right = pb[1], edge pb[1]→n.
        have hLeq : pa.get ⟨R - 2, by omega⟩ = pa.get ⟨pa.length - 2, by omega⟩ := by
          congr 1
        have hColl : G.IsCollider (pa.get ⟨R - 2, by omega⟩) n (pb.get ⟨1, by omega⟩) := by
          refine ⟨?_, hpb_in⟩
          rw [hLeq]; exact hpa_in
        rw [if_pos hColl]
        -- n ∈ bbZAncestors Z since n ∈ Z.
        show n ∈ G.bbZAncestors Z
        exact G.subset_ancestralSet Z hnZ
      · by_cases hC3 : i + 1 = R
        · -- Straddle: middle = pb.tail[0] = pb[1]. Triple (pa[R-1]=n, pb[1], pb[2]) = pb's index 0.
          have hi_eq : i = R - 1 := by omega
          subst hi_eq
          have hiR : R - 1 < R := by omega
          have hi1L : R ≤ R - 1 + 1 := by omega
          have hi2L : R ≤ R - 1 + 2 := by omega
          have hi1_lt : R - 1 + 1 < p.length := by rw [hp_len_eq]; omega
          have hi2_lt : R - 1 + 2 < p.length := by rw [hp_len_eq]; exact hi
          rw [hp_L (R - 1) hiR, hp_R (R - 1 + 1) hi1L hi1_lt, hp_R (R - 1 + 2) hi2L hi2_lt]
          rw [hpa_get_last]
          rw [show (⟨R - 1 + 1 - R + 1, by omega⟩ : Fin pb.length) =
              ⟨1, by omega⟩ from Fin.ext (show R - 1 + 1 - R + 1 = 1 by omega)]
          rw [show (⟨R - 1 + 2 - R + 1, by omega⟩ : Fin pb.length) =
              ⟨2, by omega⟩ from Fin.ext (show R - 1 + 2 - R + 1 = 2 by omega)]
          -- This matches pb's collider clause at index 0 (triple pb[0]=n, pb[1], pb[2]).
          have hpb0 := hpb_act.2 0 (by omega)
          rw [show (⟨0 + 1, by omega⟩ : Fin pb.length) = ⟨1, by omega⟩ from rfl,
              show (⟨0 + 2, by omega⟩ : Fin pb.length) = ⟨2, by omega⟩ from rfl] at hpb0
          rw [hpb_get_0] at hpb0
          exact hpb0
        · -- All three in pb.tail. i ≥ R.
          have hiL : R ≤ i := by omega
          have hi1L : R ≤ i + 1 := by omega
          have hi2L : R ≤ i + 2 := by omega
          have hi_lt : i < p.length := by rw [hp_len_eq]; omega
          have hi1_lt : i + 1 < p.length := by rw [hp_len_eq]; omega
          have hi2_lt : i + 2 < p.length := by rw [hp_len_eq]; exact hi
          rw [hp_R i hiL hi_lt, hp_R (i + 1) hi1L hi1_lt, hp_R (i + 2) hi2L hi2_lt]
          have hjlen : (i - R + 1) + 2 < pb.length := by omega
          have hpbcoll := hpb_act.2 (i - R + 1) hjlen
          rw [show (⟨(i - R + 1) + 1, by omega⟩ : Fin pb.length) =
              ⟨(i + 1) - R + 1, by omega⟩ from Fin.ext (show (i-R+1)+1 = (i+1)-R+1 by omega),
              show (⟨(i - R + 1) + 2, hjlen⟩ : Fin pb.length) =
              ⟨(i + 2) - R + 1, by omega⟩ from
                Fin.ext (show (i-R+1)+2 = (i+2)-R+1 by omega)] at hpbcoll
          exact hpbcoll

/-- **Concatenating two active paths at a non-collider.** If `pa` is active given
    `Z` ending at `m`, `pb` is active given `Z` starting at `m`, the first edge of
    `pb` points *out of* `m` (so `m` is a chain/fork point, not a collider), and
    `m ∉ Z`, then the glued path `pa ++ pb.tail` is active given `Z`. -/
theorem chain_join_active
    {Z : Finset V} {m x y : V} {pa pb : List V}
    (hpa_len : pa.length ≥ 2) (hpa_head : pa.head? = some x)
    (hpa_last : pa.getLast? = some m) (hpa_act : G.IsActivePath Z pa)
    (hpb_len : pb.length ≥ 2) (hpb_head : pb.head? = some m)
    (hpb_last : pb.getLast? = some y) (hpb_act : G.IsActivePath Z pb)
    (hseam_out : G.edge m (pb.get ⟨1, by omega⟩))
    (hmZ : m ∉ Z) :
    let p := pa ++ pb.tail
    p.length ≥ 2 ∧ p.head? = some x ∧ p.getLast? = some y ∧
      G.IsActivePath Z p := by
  have hpa_ne : pa ≠ [] := by intro h; rw [h] at hpa_len; simp at hpa_len
  have hpb_ne : pb ≠ [] := by intro h; rw [h] at hpb_len; simp at hpb_len
  -- pb.head = m
  have hpb_head_eq : pb.head hpb_ne = m := by
    have h := List.head?_eq_some_head hpb_ne; rw [hpb_head] at h
    exact (Option.some_inj.mp h.symm)
  -- pa.getLast = m
  have hpa_last_eq : pa.getLast hpa_ne = m := by
    have h := List.getLast?_eq_some_getLast hpa_ne; rw [hpa_last] at h
    exact (Option.some_inj.mp h.symm)
  -- pa.head = x
  have hpa_head_eq : pa.head hpa_ne = x := by
    have h := List.head?_eq_some_head hpa_ne; rw [hpa_head] at h
    exact (Option.some_inj.mp h.symm)
  -- pb.getLast = y
  have hpb_last_eq : pb.getLast hpb_ne = y := by
    have h := List.getLast?_eq_some_getLast hpb_ne; rw [hpb_last] at h
    exact (Option.some_inj.mp h.symm)
  -- pb = m :: pb.tail
  have hpb_decomp : pb = m :: pb.tail := by
    conv_lhs => rw [← List.cons_head_tail hpb_ne]; rw [hpb_head_eq]
  have hpb_tail_len : pb.tail.length = pb.length - 1 := List.length_tail
  have hpb_tail_ne : pb.tail ≠ [] := by
    rw [← List.length_pos_iff, hpb_tail_len]; omega
  set p := pa ++ pb.tail with hp_def
  set R := pa.length with hR_def
  have hp_len_eq : p.length = R + pb.tail.length := by
    simp only [hp_def, List.length_append, ← hR_def]
  have hp_len : p.length ≥ 2 := by rw [hp_len_eq]; omega
  have hp_head : p.head? = some x := by
    have : p.head? = pa.head? := List.head?_append_of_ne_nil _ hpa_ne
    rw [this, hpa_head]
  have hp_last : p.getLast? = some y := by
    have hlast_tail : pb.tail.getLast? = some y := by
      have heq : pb = [m] ++ pb.tail := by simpa using hpb_decomp
      have := List.getLast?_append_of_ne_nil [m] hpb_tail_ne
      rw [← heq] at this; rw [← this]; exact hpb_last
    simp only [hp_def, List.getLast?_append, hlast_tail]; rfl
  refine ⟨hp_len, hp_head, hp_last, ?_⟩
  -- Index translation: p[k] = pa[k] for k < R; p[k] = pb[k-R+1] for k ≥ R.
  have hp_L : ∀ (k : ℕ) (hkR : k < R),
      p.get ⟨k, by rw [hp_len_eq]; omega⟩ = pa.get ⟨k, hkR⟩ := by
    intro k hkR
    simp only [hp_def, List.get_eq_getElem, List.getElem_append_left (h := hkR)]
  have hpb_tail_get : ∀ (j : ℕ) (hj1 : j < pb.tail.length) (hj2 : j + 1 < pb.length),
      pb.tail[j]'hj1 = pb[j + 1]'hj2 := by
    intro j hj1 hj2
    have : pb[j + 1] = (m :: pb.tail)[j + 1]'(by rw [← hpb_decomp]; exact hj2) := by congr 1
    rw [this]; simp [List.getElem_cons_succ]
  have hp_R : ∀ (k : ℕ) (hkL : R ≤ k) (hk : k < p.length),
      p.get ⟨k, hk⟩ = pb.get ⟨k - R + 1, by
        rw [hp_len_eq, hpb_tail_len] at hk; omega⟩ := by
    intro k hkL hk
    have hk_app : R ≤ k := hkL
    have htail_idx_lt : k - R < pb.tail.length := by
      rw [hp_len_eq] at hk; omega
    have hpget : p.get ⟨k, hk⟩ = pb.tail[k - R]'htail_idx_lt := by
      simp only [hp_def, List.get_eq_getElem]
      rw [List.getElem_append_right (by rw [← hR_def]; exact hk_app)]
    rw [hpget]
    rw [hpb_tail_get (k - R) htail_idx_lt (by rw [hpb_tail_len] at htail_idx_lt; omega)]
    simp [List.get_eq_getElem]
  -- pb[0] = m, pa[R-1] = m.
  have hpb_get_0 : pb.get ⟨0, by omega⟩ = m := by
    rw [List.get_eq_getElem, List.getElem_zero]; exact hpb_head_eq
  have hpa_get_last : pa.get ⟨R - 1, by omega⟩ = m := by
    rw [List.get_eq_getElem]
    have := List.getLast_eq_getElem hpa_ne
    rw [hpa_last_eq] at this
    rw [← this]
  refine ⟨?_, ?_⟩
  · -- Adjacency.
    intro i hi
    rw [hp_len_eq] at hi
    by_cases hA1 : i + 1 < R
    · have hiR : i < R := by omega
      rw [hp_L i hiR, hp_L (i + 1) hA1]
      exact hpa_act.1 i hA1
    · push_neg at hA1
      by_cases hA2 : i + 1 = R
      · have hi_eq : i = R - 1 := by omega
        subst hi_eq
        have hiR : R - 1 < R := by omega
        rw [hp_L (R - 1) hiR]
        have hi1L : R ≤ R - 1 + 1 := by omega
        have hi1_lt : R - 1 + 1 < p.length := by rw [hp_len_eq]; exact hi
        rw [hp_R (R - 1 + 1) hi1L hi1_lt]
        rw [hpa_get_last]
        have h_yidx : R - 1 + 1 - R + 1 = 1 := by omega
        rw [show (⟨R - 1 + 1 - R + 1, by
              rw [hp_len_eq, hpb_tail_len] at hi1_lt; omega⟩ : Fin pb.length) =
            ⟨1, by omega⟩ from Fin.ext h_yidx]
        exact Or.inl hseam_out
      · have hiL : R ≤ i := by omega
        have hi1L : R ≤ i + 1 := by omega
        have hi_lt : i < p.length := by rw [hp_len_eq]; omega
        have hi1_lt : i + 1 < p.length := by rw [hp_len_eq]; exact hi
        rw [hp_R i hiL hi_lt, hp_R (i + 1) hi1L hi1_lt]
        have hidx : (i - R + 1) + 1 < pb.length := by omega
        have hadj := hpb_act.1 (i - R + 1) hidx
        have he : (i - R + 1) + 1 = (i + 1) - R + 1 := by omega
        rw [show (⟨(i - R + 1) + 1, hidx⟩ : Fin pb.length) =
            ⟨(i + 1) - R + 1, by omega⟩ from Fin.ext he] at hadj
        exact hadj
  · -- Collider condition.
    intro i hi
    rw [hp_len_eq] at hi
    by_cases hC1 : i + 2 < R
    · have hiR : i < R := by omega
      have hi1R : i + 1 < R := by omega
      rw [hp_L i hiR, hp_L (i + 1) hi1R, hp_L (i + 2) hC1]
      exact hpa_act.2 i hC1
    · push_neg at hC1
      by_cases hC2 : i + 2 = R
      · have hi_eq : i = R - 2 := by omega
        subst hi_eq
        have hiR : R - 2 < R := by omega
        have hi1R : R - 2 + 1 < R := by omega
        have hi2L : R ≤ R - 2 + 2 := by omega
        have hi2_lt : R - 2 + 2 < p.length := by rw [hp_len_eq]; exact hi
        rw [hp_L (R - 2) hiR, hp_L (R - 2 + 1) hi1R, hp_R (R - 2 + 2) hi2L hi2_lt]
        rw [show (⟨R - 2 + 1, by omega⟩ : Fin pa.length) = ⟨R - 1, by omega⟩ from
          Fin.ext (show R - 2 + 1 = R - 1 by omega)]
        rw [hpa_get_last]
        have h_ridx : R - 2 + 2 - R + 1 = 1 := by omega
        rw [show (⟨R - 2 + 2 - R + 1, by
              rw [hp_len_eq, hpb_tail_len] at hi2_lt; omega⟩ : Fin pb.length) =
            ⟨1, by omega⟩ from Fin.ext h_ridx]
        have hNotColl : ¬ G.IsCollider (pa.get ⟨R - 2, by omega⟩) m (pb.get ⟨1, by omega⟩) := by
          intro hColl
          exact (G.asymm hseam_out) hColl.2
        rw [if_neg hNotColl]
        exact hmZ
      · by_cases hC3 : i + 1 = R
        · have hi_eq : i = R - 1 := by omega
          subst hi_eq
          have hiR : R - 1 < R := by omega
          have hi1L : R ≤ R - 1 + 1 := by omega
          have hi2L : R ≤ R - 1 + 2 := by omega
          have hi1_lt : R - 1 + 1 < p.length := by rw [hp_len_eq]; omega
          have hi2_lt : R - 1 + 2 < p.length := by rw [hp_len_eq]; exact hi
          rw [hp_L (R - 1) hiR, hp_R (R - 1 + 1) hi1L hi1_lt, hp_R (R - 1 + 2) hi2L hi2_lt]
          rw [hpa_get_last]
          rw [show (⟨R - 1 + 1 - R + 1, by omega⟩ : Fin pb.length) =
              ⟨1, by omega⟩ from Fin.ext (show R - 1 + 1 - R + 1 = 1 by omega)]
          rw [show (⟨R - 1 + 2 - R + 1, by omega⟩ : Fin pb.length) =
              ⟨2, by omega⟩ from Fin.ext (show R - 1 + 2 - R + 1 = 2 by omega)]
          have hpb0 := hpb_act.2 0 (by omega)
          rw [show (⟨0 + 1, by omega⟩ : Fin pb.length) = ⟨1, by omega⟩ from rfl,
              show (⟨0 + 2, by omega⟩ : Fin pb.length) = ⟨2, by omega⟩ from rfl] at hpb0
          rw [hpb_get_0] at hpb0
          exact hpb0
        · have hiL : R ≤ i := by omega
          have hi1L : R ≤ i + 1 := by omega
          have hi2L : R ≤ i + 2 := by omega
          have hi_lt : i < p.length := by rw [hp_len_eq]; omega
          have hi1_lt : i + 1 < p.length := by rw [hp_len_eq]; omega
          have hi2_lt : i + 2 < p.length := by rw [hp_len_eq]; exact hi
          rw [hp_R i hiL hi_lt, hp_R (i + 1) hi1L hi1_lt, hp_R (i + 2) hi2L hi2_lt]
          have hjlen : (i - R + 1) + 2 < pb.length := by omega
          have hpbcoll := hpb_act.2 (i - R + 1) hjlen
          rw [show (⟨(i - R + 1) + 1, by omega⟩ : Fin pb.length) =
              ⟨(i + 1) - R + 1, by omega⟩ from Fin.ext (show (i-R+1)+1 = (i+1)-R+1 by omega),
              show (⟨(i - R + 1) + 2, hjlen⟩ : Fin pb.length) =
              ⟨(i + 2) - R + 1, by omega⟩ from
                Fin.ext (show (i-R+1)+2 = (i+2)-R+1 by omega)] at hpbcoll
          exact hpbcoll

/-- A forward-directed path whose *interior* vertices avoid `Z` is active given `Z`.
    Endpoints may lie in `Z` (they are never collider/non-collider middles). -/
theorem isActivePath_of_directed_interior
    {Z : Finset V} {p : List V}
    (hdir : ∀ (i : ℕ) (hi : i + 1 < p.length),
        G.edge (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩))
    (hZ : ∀ (i : ℕ) (hi : i + 2 < p.length), p.get ⟨i + 1, by omega⟩ ∉ Z) :
    G.IsActivePath Z p := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · exact Or.inl (hdir i hi)
  · simp only
    have hmr : G.edge (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) :=
      hdir (i + 1) hi
    have hrm_false : ¬ G.edge (p.get ⟨i + 2, hi⟩) (p.get ⟨i + 1, by omega⟩) :=
      G.asymm hmr
    have hnotcoll : ¬ G.IsCollider (p.get ⟨i, by omega⟩)
                      (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) := by
      intro ⟨_, h2⟩; exact hrm_false h2
    rw [if_neg hnotcoll]
    exact hZ i hi

/-- An ancestor `u` of `v` with `u ∉ ancestralSet Z` gives an active path from
    `u` to `v` given `Z`. (Local copy of the file-private
    `exists_activePath_of_ancestor_avoiding` in `Ancestral.lean`.) -/
private theorem exists_activePath_of_ancestor_avoiding
    {Z : Finset V} {u v : V} (huv : G.isAncestor u v)
    (huZ : u ∉ G.ancestralSet Z) :
    ∃ (p : List V), p.length ≥ 2 ∧ p.head? = some u ∧ p.getLast? = some v ∧
      G.IsActivePath Z p := by
  obtain ⟨p, hlen, hhead, hlast, hedge, hZavoid⟩ :=
    G.exists_directedPath_avoiding huv huZ
  exact ⟨p, hlen, hhead, hlast, G.isActivePath_of_directed hedge hZavoid⟩

/-- On a forward-directed path ending at `w`, the node at index `j` is `w` or a
    strict ancestor of `w`. (Downward walk along the directed edges.) -/
private theorem node_isAncestor_last_of_directed {q : List V} {w : V}
    (hlen : q.length ≥ 2) (hlast : q.getLast? = some w)
    (hedge : ∀ (i : ℕ) (hi : i + 1 < q.length),
      G.edge (q.get ⟨i, by omega⟩) (q.get ⟨i + 1, hi⟩))
    (j : ℕ) (hj : j < q.length) :
    G.isAncestor (q.get ⟨j, hj⟩) w ∨ q.get ⟨j, hj⟩ = w := by
  by_cases hjlast : j = q.length - 1
  · right
    have hqne : q ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    have hh := List.getLast?_eq_some_getLast hqne
    rw [hlast] at hh
    have hw_eq : q.getLast hqne = w := Option.some_inj.mp hh.symm
    have hidx : (⟨j, hj⟩ : Fin q.length) = ⟨q.length - 1, by omega⟩ := Fin.ext (by omega)
    rw [hidx, List.get_eq_getElem, ← hw_eq, List.getLast_eq_getElem]
  · have hj1 : j + 1 < q.length := by omega
    have he := hedge j hj1
    rcases node_isAncestor_last_of_directed hlen hlast hedge (j + 1) hj1 with h | h
    · exact Or.inl (G.isAncestor_trans (isAncestor.edge he) h)
    · exact Or.inl (h ▸ isAncestor.edge he)
termination_by q.length - j
decreasing_by omega

/-- **A directed descent to a topological non-maximum is active given `insert n S`.**
    If `c` is an ancestor of `w` (with `w` strictly topologically below `n`, hence not
    reachable through `n`), and `c ∉ ancestralSet S`, then there is an active path
    `c → w` given `insert n S`: take a directed path avoiding `S`; it cannot pass
    through `n` since `n` is not an ancestor of `w`, so it also avoids `insert n S`. -/
private theorem descent_active_insert {S : Finset V} {c w n : V}
    (hcw : G.isAncestor c w) (hcS : c ∉ G.ancestralSet S)
    (hwn : G.topoOrder w ≤ G.topoOrder n) :
    ∃ (q : List V) (hq2 : q.length ≥ 2), q.head? = some c ∧ q.getLast? = some w ∧
      G.IsActivePath (insert n S) q ∧ G.edge c (q.get ⟨1, by omega⟩) := by
  obtain ⟨q, hlen, hhead, hlast, hedge, hSavoid⟩ :=
    G.exists_directedPath_avoiding hcw hcS
  -- Interior nodes of `q` avoid `insert n S`: they avoid `S`, and are strict ancestors
  -- of `w` (topologically below `n`) hence never `n`.
  have hins : ∀ (i : ℕ) (hi : i + 2 < q.length), q.get ⟨i + 1, by omega⟩ ∉ insert n S := by
    intro i hi
    rw [Finset.mem_insert, not_or]
    refine ⟨?_, hSavoid _ (List.get_mem q ⟨i + 1, by omega⟩)⟩
    -- An interior node is a strict ancestor of `w` (it is not the last node), so it is
    -- `≠ n`: `n = q[i+1]` would give `isAncestor n w`, `topoOrder n < topoOrder w ≤ n`.
    intro hmn
    have hnode := G.node_isAncestor_last_of_directed hlen hlast hedge (i + 1) (by omega)
    rcases hnode with h | h
    · rw [hmn] at h
      have h2 := G.isAncestor_topoOrder_lt h; omega
    · -- `q[i+1] = w`, but `q[i+1]` is interior (`i+1 < q.length - 1`), while `w` is the
      -- last node; the directed edge `q[i+1] → q[i+2]` then makes `w` a strict ancestor
      -- of `w`, contradiction.
      have he := hedge (i + 1) (by omega)
      rw [h] at he
      have hnode2 := G.node_isAncestor_last_of_directed hlen hlast hedge (i + 2) (by omega)
      rcases hnode2 with h2 | h2
      · exact G.isAncestor_irrefl w (G.isAncestor_trans (isAncestor.edge he) h2)
      · exact G.irrefl w (h2 ▸ he)
  -- First edge points out of `c`: `edge c q[1]` from the directed structure.
  have hfirst : G.edge c (q.get ⟨1, by omega⟩) := by
    have he0 := hedge 0 (by omega)
    have hq0 : q.get ⟨0, by omega⟩ = c := by
      have hqne : q ≠ [] := by intro h; rw [h] at hlen; simp at hlen
      have hh := List.head?_eq_some_head hqne
      rw [hhead] at hh
      have : q.head hqne = c := Option.some_inj.mp hh.symm
      rw [List.get_eq_getElem, List.getElem_zero]; exact this
    rw [hq0] at he0
    exact he0
  exact ⟨q, hlen, hhead, hlast, G.isActivePath_of_directed_interior hedge hins, hfirst⟩

/-- A prefix of an active path is active. -/
private theorem isActivePath_take {Z : Finset V} {p : List V} {k : ℕ}
    (hact : G.IsActivePath Z p) : G.IsActivePath Z (p.take k) := by
  obtain ⟨hadj, hcoll⟩ := hact
  have hle : (p.take k).length ≤ p.length := by
    rw [List.length_take]; exact min_le_right k p.length
  have hget : ∀ (j : ℕ) (hj : j < (p.take k).length),
      (p.take k).get ⟨j, hj⟩ = p.get ⟨j, by omega⟩ := by
    intro j hj
    simp only [List.get_eq_getElem, List.getElem_take]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hget i (by omega), hget (i + 1) hi]
    exact hadj i (by omega)
  · rw [hget i (by omega), hget (i + 1) (by omega), hget (i + 2) hi]
    exact hcoll i (by omega)

/-- **Survive-or-splice for one side.** Given an active path `p` from `a ∈ A` to the
    topological maximum `n` given the cross-condition `S ∪ W`, with all nodes in the
    query ancestral set `bigQ`: either (splice) there is an active `A → W` path given
    `insert n S` — obtained by cutting at the closest-to-`a` `W`-only-activated
    collider and descending to `W` — or (survive) `p` itself lifts to an active
    `A → n` path given `insert n S` whose last edge points into `n`. -/
private theorem survive_or_splice {S A W bigQ : Finset V} {p : List V} {a n : V}
    (hbigQ : A ∪ {n} ∪ (S ∪ W) ⊆ bigQ)
    (hmax : ∀ m ∈ G.ancestralSet bigQ, G.topoOrder m ≤ G.topoOrder n)
    (haA : a ∈ A) (hlen : p.length ≥ 2) (hact : G.IsActivePath (S ∪ W) p)
    (hhead : p.head? = some a) (hlast : p.getLast? = some n) :
    (∃ (q : List V) (w : V), w ∈ W ∧ q.length ≥ 2 ∧ G.IsActivePath (insert n S) q ∧
        q.head? = some a ∧ q.getLast? = some w) ∨
    (∃ (q : List V) (hq2 : q.length ≥ 2), G.IsActivePath (insert n S) q ∧
        q.head? = some a ∧ q.getLast? = some n ∧
        G.edge (q.get ⟨q.length - 2, by omega⟩) n) := by
  -- Nodes of `p` lie in `ancestralSet bigQ`.
  have hpAnc : ∀ v ∈ p, v ∈ G.ancestralSet bigQ := by
    intro v hv
    have := G.activePath_nodes_are_ancestors haA (Finset.mem_singleton_self n) hact hhead hlast v hv
    exact G.ancestralSet_mono hbigQ this
  -- `n` is never an interior non-collider on `p` (topological maximality).
  have hno_n : ∀ (i : ℕ) (hi : i + 2 < p.length),
      p.get ⟨i + 1, by omega⟩ = n →
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) := by
    intro i hi hmn
    by_contra hC
    obtain ⟨hadj, _⟩ := hact
    have hout := G.nonCollider_has_outgoing (hadj i (by omega)) (hadj (i + 1) (by omega)) hC
    rcases hout with hedge | hedge <;> rw [hmn] at hedge
    · have h1 : G.topoOrder (p.get ⟨i, by omega⟩) ≤ G.topoOrder n :=
        hmax _ (hpAnc _ (List.get_mem p ⟨i, by omega⟩))
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge); omega
    · have h1 : G.topoOrder (p.get ⟨i + 1 + 1, by omega⟩) ≤ G.topoOrder n :=
        hmax _ (hpAnc _ (List.get_mem p ⟨i + 1 + 1, by omega⟩))
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge); omega
  -- Bad indices: interior colliders whose middle is NOT activated by `S` alone.
  classical
  let P : ℕ → Prop := fun i => ∃ (hi : i + 2 < p.length),
    G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) ∧
    p.get ⟨i + 1, by omega⟩ ∉ G.ancestralSet S
  let Bad : Finset ℕ := (Finset.range p.length).filter P
  by_cases hBad : Bad.Nonempty
  · -- ===== SPLICE branch =====
    refine Or.inl ?_
    set i₀ := Bad.min' hBad with hi₀_def
    have hi₀_mem : i₀ ∈ Bad := Bad.min'_mem hBad
    have hi₀_range : i₀ ∈ Finset.range p.length ∧ P i₀ := by
      have := hi₀_mem; simp only [Bad, Finset.mem_filter] at this; exact this
    obtain ⟨hi₀, hC₀, hcS₀⟩ := hi₀_range.2
    set c := p.get ⟨i₀ + 1, by omega⟩ with hc_def
    -- Minimality: every interior collider strictly before `i₀` is `S`-activated.
    have hmin : ∀ (j : ℕ) (hj : j + 2 < p.length), j < i₀ →
        G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩) →
        p.get ⟨j + 1, by omega⟩ ∈ G.ancestralSet S := by
      intro j hj hjlt hCj
      by_contra hnotanc
      have hjBad : j ∈ Bad := by
        simp only [Bad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hj, hCj, hnotanc⟩
      have := Bad.min'_le j hjBad
      rw [← hi₀_def] at this; omega
    -- The collider middle `c` is activated by `S ∪ W`.
    have hc_act : c ∈ G.ancestralSet (S ∪ W) := by
      have h := hact.2 i₀ hi₀
      simp only at h
      rw [if_pos hC₀] at h
      exact h
    -- Prefix `q1 := p.take (i₀ + 2)`, ending at `c`, active given `insert n S`.
    set q1 := p.take (i₀ + 2) with hq1_def
    have hq1_len : q1.length = i₀ + 2 := by
      rw [hq1_def, List.length_take]; omega
    have hq1_get : ∀ (j : ℕ) (hj : j < q1.length),
        q1.get ⟨j, hj⟩ = p.get ⟨j, by rw [hq1_len] at hj; omega⟩ := by
      intro j hj; simp only [hq1_def, List.get_eq_getElem, List.getElem_take]
    have hq1_act_SW : G.IsActivePath (S ∪ W) q1 := G.isActivePath_take hact
    have hq1_head : q1.head? = some a := by
      have hq1ne : q1 ≠ [] := by intro h; rw [h] at hq1_len; simp at hq1_len
      rw [List.head?_eq_some_head hq1ne]
      have hh0 : q1.head hq1ne = q1.get ⟨0, by omega⟩ := by
        rw [List.get_eq_getElem, ← List.head_eq_getElem]
      rw [hh0, hq1_get 0 (by omega)]
      have hpne : p ≠ [] := by intro h; rw [h] at hlen; simp at hlen
      have hh := List.head?_eq_some_head hpne; rw [hhead] at hh
      have hpa : p.head hpne = a := Option.some_inj.mp hh.symm
      rw [show p.get ⟨0, by omega⟩ = p.head hpne by
        rw [List.get_eq_getElem, ← List.head_eq_getElem], hpa]
    have hq1_last : q1.getLast? = some c := by
      have hq1ne : q1 ≠ [] := by intro h; rw [h] at hq1_len; simp at hq1_len
      rw [List.getLast?_eq_some_getLast hq1ne]
      have heq : q1.getLast hq1ne = q1.get ⟨q1.length - 1, by omega⟩ := by
        rw [List.get_eq_getElem, ← List.getLast_eq_getElem]
      rw [heq, hq1_get (q1.length - 1) (by omega)]
      have hidx : q1.length - 1 = i₀ + 1 := by omega
      simp only [hidx, hc_def]
    -- Lift `q1` to `insert n S`.
    have hq1_collS : ∀ (i : ℕ) (hi : i + 2 < q1.length),
        G.IsCollider (q1.get ⟨i, by omega⟩) (q1.get ⟨i + 1, by omega⟩) (q1.get ⟨i + 2, hi⟩) →
        q1.get ⟨i + 1, by omega⟩ ∈ G.ancestralSet S := by
      intro i hi hC
      simp only [hq1_get] at hC ⊢
      have hi_p : i + 2 < p.length := by rw [hq1_len] at hi; omega
      exact hmin i hi_p (by rw [hq1_len] at hi; omega) hC
    have hq1_no_n : ∀ (i : ℕ) (hi : i + 2 < q1.length),
        q1.get ⟨i + 1, by omega⟩ = n →
        G.IsCollider (q1.get ⟨i, by omega⟩) (q1.get ⟨i + 1, by omega⟩) (q1.get ⟨i + 2, hi⟩) := by
      intro i hi hmn
      simp only [hq1_get] at hmn ⊢
      exact hno_n i (by rw [hq1_len] at hi; omega) hmn
    have hq1_act : G.IsActivePath (insert n S) q1 :=
      G.lift_crosscond_to_insert hq1_act_SW hq1_collS hq1_no_n
    -- Peel `c`'s activation: `c ∈ W` or `c` is a strict ancestor of some `w0 ∈ W`.
    have hc_peel : c ∈ W ∨ ∃ w0 ∈ W, G.isAncestor c w0 := by
      simp only [ancestralSet, Finset.mem_union, ancestorsSet, Finset.mem_filter,
        Finset.mem_univ, true_and] at hc_act
      rcases hc_act with (hcS | hcW) | ⟨s, hsSW, hanc⟩
      · exact absurd (G.subset_ancestralSet S hcS) hcS₀
      · exact Or.inl hcW
      · rcases hsSW with hsS | hsW
        · exact absurd (G.mem_ancestralSet_of_isAncestor hsS hanc) hcS₀
        · exact Or.inr ⟨s, hsW, hanc⟩
    -- `c ∈ ancestralSet bigQ`, so `topoOrder c ≤ topoOrder n`; combined below.
    have hc_bigQ : c ∈ G.ancestralSet bigQ :=
      hpAnc c (List.get_mem p ⟨i₀ + 1, by omega⟩)
    rcases hc_peel with hcW | ⟨w0, hw0W, hcw0⟩
    · -- `c ∈ W`: the prefix `q1` already ends in `W`.
      exact ⟨q1, c, hcW, by rw [hq1_len]; omega, hq1_act, hq1_head, hq1_last⟩
    · -- Descend `c → w0 ∈ W` and splice.
      have hw0_bigQ : w0 ∈ G.ancestralSet bigQ :=
        G.subset_ancestralSet bigQ (hbigQ (by
          simp only [Finset.mem_union]; exact Or.inr (Or.inr hw0W)))
      have hw0n : G.topoOrder w0 ≤ G.topoOrder n := hmax w0 hw0_bigQ
      obtain ⟨dq, hdq2, hdq_head, hdq_last, hdq_act, hdq_first⟩ :=
        G.descent_active_insert hcw0 hcS₀ hw0n
      -- Splice `q1 ++ dq.tail` at the non-collider `c`.
      have hcne : c ∉ insert n S := by
        rw [Finset.mem_insert, not_or]
        refine ⟨?_, fun hcS => hcS₀ (G.subset_ancestralSet S hcS)⟩
        -- `c ≠ n`: `isAncestor c w0` with `topoOrder w0 ≤ topoOrder n` forces `c ≠ n`.
        intro hcn
        have h2 := G.isAncestor_topoOrder_lt hcw0
        rw [hcn] at h2; omega
      obtain ⟨_, hjoin_head, hjoin_last, hjoin_act⟩ :=
        G.chain_join_active (by rw [hq1_len]; omega) hq1_head hq1_last hq1_act
          hdq2 hdq_head hdq_last hdq_act hdq_first hcne
      refine ⟨q1 ++ dq.tail, w0, hw0W, ?_, hjoin_act, hjoin_head, hjoin_last⟩
      rw [List.length_append]; rw [hq1_len]; omega
  · -- ===== SURVIVE branch =====
    refine Or.inr ?_
    -- Every interior collider middle is `S`-activated (Bad empty).
    have hcollS : ∀ (i : ℕ) (hi : i + 2 < p.length),
        G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) →
        p.get ⟨i + 1, by omega⟩ ∈ G.ancestralSet S := by
      intro i hi hC
      by_contra hnotanc
      exact hBad ⟨i, by
        simp only [Bad, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hi, hC, hnotanc⟩⟩
    have hact' : G.IsActivePath (insert n S) p :=
      G.lift_crosscond_to_insert hact hcollS hno_n
    have hedge_in : G.edge (p.get ⟨p.length - 2, by omega⟩) n :=
      G.last_edge_into_max hlen hact hlast hpAnc hmax
    exact ⟨p, hlen, hact', hhead, hlast, hedge_in⟩

/-- **Maximal-condition branch split** (the single hardest graph step). If `X`
    and `Y` are d-separated by `insert n (Z' ∪ Zf)` with `n` topologically maximal
    in the query's ancestral set, then `n` is d-separated from one of the two
    sides given the remaining condition together with the other side.

    Graphically: topological maximality forces every edge of a relevant active
    path incident to `n` to point *into* `n`. If `n` were active for both `X` and
    `Y` simultaneously one could concatenate an `X → n` segment with an `n → Y`
    segment through the collider `n` (active since `n` is conditioned), yielding an
    active `X → Y` path — contradicting `dSep X Y (insert n …)`. Hence one of the
    two one-sided separations holds. -/
private theorem dSep_maximal_condition_branch {X Y Z' Zf : Finset V} {n : V}
    (hnZ' : n ∉ Z') (hnZf : n ∉ Zf)
    (hmax : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ (insert n Z') ∪ Zf),
      G.topoOrder m ≤ G.topoOrder n)
    (hdSep : G.dSep X Y (insert n Z' ∪ Zf)) :
    G.dSep X {n} ((Z' ∪ Y) ∪ Zf) ∨ G.dSep Y {n} ((Z' ∪ X) ∪ Zf) := by
  set S : Finset V := Z' ∪ Zf with hS_def
  -- Set bookkeeping: the three conditioning sets in terms of `S`.
  have hSY : (Z' ∪ Y) ∪ Zf = S ∪ Y := by
    rw [hS_def]; ext z; simp only [Finset.mem_union]; tauto
  have hSX : (Z' ∪ X) ∪ Zf = S ∪ X := by
    rw [hS_def]; ext z; simp only [Finset.mem_union]; tauto
  have hinsS : insert n Z' ∪ Zf = insert n S := by
    rw [hS_def]; ext z; simp only [Finset.mem_insert, Finset.mem_union]; tauto
  -- The query (`bigQ`) and topological maximality over it.
  set bigQ : Finset V := X ∪ Y ∪ insert n Z' ∪ Zf with hbigQ_def
  -- Inclusions of the per-side query sets into `bigQ`.
  have hbigQ_X : X ∪ {n} ∪ (S ∪ Y) ⊆ bigQ := by
    rw [hbigQ_def, hS_def]; intro z hz
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at hz ⊢; tauto
  have hbigQ_Y : Y ∪ {n} ∪ (S ∪ X) ⊆ bigQ := by
    rw [hbigQ_def, hS_def]; intro z hz
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at hz ⊢; tauto
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnotL, hnotR⟩ := hcon
  -- Failure of each disjunct gives `n` reachable from the respective source.
  have hreachX : n ∈ G.bbReachableVertices ((Z' ∪ Y) ∪ Zf) X := by
    by_contra hnReach
    apply hnotL
    refine ⟨?_, ?_, ?_, Finset.disjoint_singleton_right.mpr hnReach⟩
    · rw [Finset.disjoint_singleton_right]
      intro hnX
      exact Finset.disjoint_left.mp hdSep.2.1 hnX
        (Finset.mem_union_left _ (Finset.mem_insert_self n Z'))
    · rw [Finset.disjoint_left]
      intro x hxX hxCond
      simp only [Finset.mem_union] at hxCond
      rcases hxCond with (hxZ' | hxY) | hxZf
      · exact Finset.disjoint_left.mp hdSep.2.1 hxX
          (Finset.mem_union_left _ (Finset.mem_insert_of_mem hxZ'))
      · exact Finset.disjoint_left.mp hdSep.1 hxX hxY
      · exact Finset.disjoint_left.mp hdSep.2.1 hxX (Finset.mem_union_right _ hxZf)
    · rw [Finset.disjoint_singleton_left]
      intro hnCond
      simp only [Finset.mem_union] at hnCond
      rcases hnCond with (hnZ | hnY) | hnF
      · exact hnZ' hnZ
      · exact Finset.disjoint_left.mp hdSep.2.2.1 hnY
          (Finset.mem_union_left _ (Finset.mem_insert_self n Z'))
      · exact hnZf hnF
  have hreachY : n ∈ G.bbReachableVertices ((Z' ∪ X) ∪ Zf) Y := by
    by_contra hnReach
    apply hnotR
    refine ⟨?_, ?_, ?_, Finset.disjoint_singleton_right.mpr hnReach⟩
    · rw [Finset.disjoint_singleton_right]
      intro hnY
      exact Finset.disjoint_left.mp hdSep.2.2.1 hnY
        (Finset.mem_union_left _ (Finset.mem_insert_self n Z'))
    · rw [Finset.disjoint_left]
      intro y hyY hyCond
      simp only [Finset.mem_union] at hyCond
      rcases hyCond with (hyZ' | hyX) | hyZf
      · exact Finset.disjoint_left.mp hdSep.2.2.1 hyY
          (Finset.mem_union_left _ (Finset.mem_insert_of_mem hyZ'))
      · exact Finset.disjoint_left.mp hdSep.1 hyX hyY
      · exact Finset.disjoint_left.mp hdSep.2.2.1 hyY (Finset.mem_union_right _ hyZf)
    · rw [Finset.disjoint_singleton_left]
      intro hnCond
      simp only [Finset.mem_union] at hnCond
      rcases hnCond with (hnZ | hnX) | hnF
      · exact hnZ' hnZ
      · exact Finset.disjoint_left.mp hdSep.2.1 hnX
          (Finset.mem_union_left _ (Finset.mem_insert_self n Z'))
      · exact hnZf hnF
  rw [hSY, G.bbReachableVertices_iff_activePath] at hreachX
  rw [hSX, G.bbReachableVertices_iff_activePath] at hreachY
  obtain ⟨x, hxX, p1, hp1len, hp1act, hp1head, hp1last⟩ := hreachX
  obtain ⟨y, hyY, p2, hp2len, hp2act, hp2head, hp2last⟩ := hreachY
  have hmaxQ : ∀ m ∈ G.ancestralSet bigQ, G.topoOrder m ≤ G.topoOrder n := by
    rw [hbigQ_def]; exact hmax
  -- Any active `X → Y` path given `insert n S` contradicts `hdSep`.
  have hcontra_XY : ∀ (q : List V) (xa ya : V), xa ∈ X → ya ∈ Y →
      q.length ≥ 2 → G.IsActivePath (insert n S) q → q.head? = some xa →
      q.getLast? = some ya → False := by
    intro q xa ya hxaX hyaY hqlen hqact hqhead hqlast
    have hmem : ya ∈ G.bbReachableVertices (insert n S) X := by
      rw [G.bbReachableVertices_iff_activePath]
      exact ⟨xa, hxaX, q, hqlen, hqact, hqhead, hqlast⟩
    rw [← hinsS] at hmem
    exact (Finset.disjoint_left.mp hdSep.2.2.2 hmem) hyaY
  -- Process both sides with `survive_or_splice`.
  rcases G.survive_or_splice hbigQ_X hmaxQ hxX hp1len hp1act hp1head hp1last with
    ⟨q, w, hwY, hqlen, hqact, hqhead, hqlast⟩ | ⟨qx, hqx2, hqxact, hqxhead, hqxlast, hqxin⟩
  · -- Splice on the X-side: active `X → Y` path given `insert n S`.
    exact hcontra_XY q x w hxX hwY hqlen hqact hqhead hqlast
  · -- Survive on the X-side: active `X → n` path given `insert n S`, last edge into `n`.
    rcases G.survive_or_splice hbigQ_Y hmaxQ hyY hp2len hp2act hp2head hp2last with
      ⟨q', w', hw'X, hq'len, hq'act, hq'head, hq'last⟩ | ⟨qy, hqy2, hqyact, hqyhead, hqylast, hqyin⟩
    · -- Splice on the Y-side: active `Y → X` path; reverse to `X → Y`.
      have hrev_act : G.IsActivePath (insert n S) q'.reverse := G.isActivePath_reverse hq'act
      have hrev_len : q'.reverse.length ≥ 2 := by rw [List.length_reverse]; exact hq'len
      have hrev_head : q'.reverse.head? = some w' := by rw [List.head?_reverse]; exact hq'last
      have hrev_last : q'.reverse.getLast? = some y := by rw [List.getLast?_reverse]; exact hq'head
      exact hcontra_XY q'.reverse w' y hw'X hyY hrev_len hrev_act hrev_head hrev_last
    · -- Both survive: join `qx : x → n` with reverse of `qy : y → n` at the collider `n`.
      set pb := qy.reverse with hpb_def
      have hpb_act : G.IsActivePath (insert n S) pb := G.isActivePath_reverse hqyact
      have hpb_len : pb.length ≥ 2 := by rw [hpb_def, List.length_reverse]; exact hqy2
      have hpb_head : pb.head? = some n := by
        rw [hpb_def, List.head?_reverse]; exact hqylast
      have hpb_last : pb.getLast? = some y := by
        rw [hpb_def, List.getLast?_reverse]; exact hqyhead
      -- First edge of `pb` into `n`: `pb[1] = qy[qy.length - 2]`, and `qy[len-2] → n`.
      have hpb_in : G.edge (pb.get ⟨1, by omega⟩) n := by
        have hpb1 : pb.get ⟨1, by omega⟩ = qy.get ⟨qy.length - 2, by omega⟩ := by
          simp only [hpb_def, List.get_eq_getElem, List.getElem_reverse]
          congr 1
        rw [hpb1]; exact hqyin
      obtain ⟨_, hjhead, hjlast, hjact⟩ :=
        G.activePath_join_at_collider hqx2 hqxhead hqxlast hqxact hpb_len hpb_head hpb_last
          hpb_act hqxin hpb_in (Finset.mem_insert_self n S)
      exact hcontra_XY (qx ++ pb.tail) x y hxX hyY (by
        rw [List.length_append]; omega) hjact hjhead hjlast

/-- **A maximal fixed root can be dropped.** If `n ∈ Zf` is a fixed root (no
    parents) and is the topological maximum of the query's ancestral set, then
    deleting it from the conditioning set preserves d-separation of `X` and `Y`.

    Graphically: having no parents, `n` is never a collider, so it cannot be a
    collider-activated node on any active path; being topologically maximal it
    cannot be a non-collider passing point of a relevant `X → Y` path either.
    Removing it from the condition therefore changes no active path. -/
private theorem dSep_erase_maximal_fixed_root {X Y Zr Zf : Finset V} {n : V}
    (hnZf : n ∈ Zf)
    (hRoot : G.parents n = ∅)
    (hmax : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf),
      G.topoOrder m ≤ G.topoOrder n)
    (hdSep : G.dSep X Y (Zr ∪ Zf)) :
    G.dSep X Y (Zr ∪ (Zf.erase n)) := by
  refine ⟨hdSep.1, ?_, ?_, ?_⟩
  · exact hdSep.2.1.mono_right (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_erase] at hz ⊢
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr hz.2)
  · exact hdSep.2.2.1.mono_right (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_erase] at hz ⊢
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr hz.2)
  rw [Finset.disjoint_left]
  intro y hyReach hyY
  rw [G.bbReachableVertices_iff_activePath] at hyReach
  obtain ⟨x, hxX, p, hlen, hact, hhead, hlast⟩ := hyReach
  -- Every node of `p` lies in `ancestralSet Q` (Q = X∪Y∪Zr∪Zf).
  have hpAnc : ∀ v ∈ p, v ∈ G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf) := by
    intro v hv
    have := G.activePath_nodes_are_ancestors hxX hyY hact hhead hlast v hv
    refine G.ancestralSet_mono ?_ this
    intro z hz
    simp only [Finset.mem_union, Finset.mem_erase] at hz ⊢
    rcases hz with (h | h) | h | h
    exacts [Or.inl (Or.inl (Or.inl h)), Or.inl (Or.inl (Or.inr h)),
      Or.inl (Or.inr h), Or.inr h.2]
  -- `n` is never a non-collider on `p` (topological maximality, as in A2g).
  have hno : ∀ (i : ℕ) (hi : i + 2 < p.length),
      p.get ⟨i + 1, by omega⟩ = n →
      G.IsCollider (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) := by
    intro i hi hmn
    by_contra hC
    obtain ⟨hadj, _⟩ := hact
    have hout := G.nonCollider_has_outgoing (hadj i (by omega)) (hadj (i + 1) (by omega)) hC
    rcases hout with hedge | hedge <;> rw [hmn] at hedge
    · have h1 : G.topoOrder (p.get ⟨i, by omega⟩) ≤ G.topoOrder n :=
        hmax _ (hpAnc _ (List.get_mem p ⟨i, by omega⟩))
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge)
      omega
    · have h1 : G.topoOrder (p.get ⟨i + 1 + 1, by omega⟩) ≤ G.topoOrder n :=
        hmax _ (hpAnc _ (List.get_mem p ⟨i + 1 + 1, by omega⟩))
      have h2 := G.isAncestor_topoOrder_lt (isAncestor.edge hedge)
      omega
  have hact' : G.IsActivePath (insert n (Zr ∪ Zf.erase n)) p :=
    G.isActivePath_insert_cond hact hno
  have hins : insert n (Zr ∪ Zf.erase n) = Zr ∪ Zf := by
    ext z; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (rfl | h | ⟨_, h⟩)
      exacts [Or.inr hnZf, Or.inl h, Or.inr h]
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · by_cases hz : z = n
        · exact Or.inl hz
        · exact Or.inr (Or.inr ⟨hz, h⟩)
  rw [hins] at hact'
  have : y ∈ G.bbReachableVertices (Zr ∪ Zf) X := by
    rw [G.bbReachableVertices_iff_activePath]
    exact ⟨x, hxX, p, hlen, hact', hhead, hlast⟩
  exact (Finset.disjoint_left.mp hdSep.2.2.2 this) hyY

omit [Fintype V] in
/-- Set-bookkeeping for the branch termination: reinserting the peeled node `n`
    recovers the original query seed. Proved as a standalone lemma so it elaborates
    outside the heavy well-founded-recursion context. -/
private theorem branch_seed_eq {a b Zr c : Finset V} {n : V} (hn : n ∈ Zr) :
    a ∪ {n} ∪ (Zr.erase n ∪ b) ∪ c = a ∪ b ∪ Zr ∪ c := by
  ext x; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
  constructor
  · rintro (((h | h) | (h | h)) | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr (h ▸ hn))
    · exact Or.inl (Or.inr h.2)
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inr h
  · rintro (((h | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · by_cases hx : x = n
      · exact Or.inl (Or.inl (Or.inr hx))
      · exact Or.inl (Or.inr (Or.inl ⟨hx, h⟩))
    · exact Or.inr h

-- ============================================================
-- § 4. d-separation ⟹ ordered-local derivation (the crux)
-- ============================================================

/-- **d-separation yields an ordered-local derivation.** If `X` and `Y` are
    d-separated by `Zr ∪ Zf` in `G`, where `Zr` are random nodes and `Zf` are fixed
    roots, then the triple "`X` ⊥ `Y` given `Zr`" is derivable from the ordered-local
    basis via the semi-graphoid axioms — i.e. `OrderedLocalSG G R X Y Zr` holds.

    The conditioning set in the conclusion drops the fixed part `Zf`: fixed roots
    carry no randomness and are excluded from every `parents v ∩ R`, so the
    derivation discharges their blocking role graphically (a maximal fixed root is
    irrelevant to all relevant active paths; a non-maximal one is an ancestor of a
    random node and disappears when that node's basis statement conditions only on
    `parents v ∩ R`).

    Proved by well-founded induction on the ancestral set, peeling the
    topologically-maximal relevant node; this is the constructive form of the
    classical local-to-global Markov theorem. -/
theorem orderedLocalSG_of_dSep_with_fixed
    (R F X Y Zr Zf : Finset V)
    (hFixedRoots : ∀ f ∈ F, G.parents f = ∅)
    (hFR : Disjoint F R)
    (hX : X ⊆ R) (hY : Y ⊆ R) (hZr : Zr ⊆ R) (hZf : Zf ⊆ F)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Zr) (hYZ : Disjoint Y Zr)
    (hdSep : G.dSep X Y (Zr ∪ Zf)) :
    G.OrderedLocalSG R X Y Zr := by
  -- Trivial base case: an empty source set.
  rcases Finset.eq_empty_or_nonempty X with hXe | hXne
  · subst hXe; exact OrderedLocalSG.nil Y Zr hY hZr
  -- Abbreviate the query set and select a topological maximum of its ancestral set.
  set Q : Finset V := X ∪ Y ∪ Zr ∪ Zf with hQ_def
  have hQne : (G.ancestralSet Q).Nonempty := by
    obtain ⟨x, hx⟩ := hXne
    exact ⟨x, G.subset_ancestralSet Q (by
      simp only [hQ_def, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl hx)))⟩
  obtain ⟨n, hnAnc, hmax⟩ := Finset.exists_max_image (G.ancestralSet Q) G.topoOrder hQne
  have hnQ : n ∈ Q := G.topoMax_mem_seed hnAnc hmax
  -- Membership facts used across the cases.
  have hnR_of_mem : ∀ {S : Finset V}, S ⊆ R → n ∈ S → n ∉ F := by
    intro S hSR hnS hnF
    exact (Finset.disjoint_left.mp hFR hnF) (hSR hnS)
  -- Reusable inclusions for the termination (card-drop) arguments.
  have hQanc : Q ⊆ G.ancestralSet Q := G.subset_ancestralSet Q
  have hParAnc : G.parents n ⊆ G.ancestralSet Q := by
    intro a ha
    exact G.mem_ancestralSet_of_isAncestor hnQ (isAncestor.edge (G.mem_parents.mp ha))
  have hXsubQ : X ⊆ Q := by rw [hQ_def]; intro x hx; simp only [Finset.mem_union]; tauto
  have hYsubQ : Y ⊆ Q := by rw [hQ_def]; intro x hx; simp only [Finset.mem_union]; tauto
  have hZrsubQ : Zr ⊆ Q := by rw [hQ_def]; intro x hx; simp only [Finset.mem_union]; tauto
  have hZfsubQ : Zf ⊆ Q := by rw [hQ_def]; intro x hx; simp only [Finset.mem_union]; tauto
  have hXQ : X ⊆ G.ancestralSet Q := hXsubQ.trans hQanc
  have hYQ : Y ⊆ G.ancestralSet Q := hYsubQ.trans hQanc
  have hZrQ : Zr ⊆ G.ancestralSet Q := hZrsubQ.trans hQanc
  have hZfQ : Zf ⊆ G.ancestralSet Q := hZfsubQ.trans hQanc
  rw [hQ_def] at hnQ
  simp only [Finset.mem_union] at hnQ
  -- Case analysis on where the maximal node `n` sits.
  rcases hnQ with ((hnX | hnY) | hnZr) | hnZf
  · -- ===== Case n ∈ X =====
    set X' : Finset V := X.erase n with hX'_def
    set A : Finset V := G.parents n ∩ R with hA_def
    set C : Finset V := Zr ∪ X' with hC_def
    set A0 : Finset V := A \ C with hA0_def
    have hnX' : n ∉ X' := Finset.notMem_erase n X
    have hnZf : n ∉ Zf := fun h => (hnR_of_mem hX hnX) (hZf h)
    have hXins : X = insert n X' := (Finset.insert_erase hnX).symm
    have hX'R : X' ⊆ R := (Finset.erase_subset _ _).trans hX
    have hX'X : X' ⊆ X := Finset.erase_subset _ _
    have hnY : n ∉ Y := fun h => (Finset.disjoint_left.mp hXY hnX) h
    have hnZr : n ∉ Zr := fun h => (Finset.disjoint_left.mp hXZ hnX) h
    have hCR : C ⊆ R := Finset.union_subset hZr hX'R
    have hAR : A ⊆ R := Finset.inter_subset_right
    have hA0R : A0 ⊆ R := (Finset.sdiff_subset).trans hAR
    -- `n` is not an ancestor of any query node (topological maximality).
    have hND_Q : ∀ w ∈ Q, ¬ G.isAncestor n w := by
      intro w hwQ hanc
      have h1 : G.topoOrder w ≤ G.topoOrder n := hmax w (G.subset_ancestralSet Q hwQ)
      have h2 : G.topoOrder n < G.topoOrder w := G.isAncestor_topoOrder_lt hanc
      omega
    -- ihX': drop `n` from the source.
    have ihX' : G.OrderedLocalSG R X' Y Zr :=
      orderedLocalSG_of_dSep_with_fixed R F X' Y Zr Zf hFixedRoots hFR hX'R hY hZr hZf
        (hXY.mono_left hX'X) (hXZ.mono_left hX'X) hYZ (G.dSep_subset_left hX'X hdSep)
    -- `dSep {n} Y (C ∪ Zf)`.
    have hCZf_eq : C ∪ Zf = (Zr ∪ Zf) ∪ X' := by
      rw [hC_def]; ext x; simp only [Finset.mem_union]; tauto
    have hdSepN : G.dSep {n} Y (C ∪ Zf) := by
      rw [hCZf_eq]
      apply G.dSep_source_to_cond (X := {n}) (S := X')
      · exact Finset.disjoint_singleton_left.mpr hnX'
      · rw [show ({n} : Finset V) ∪ X' = X by rw [hXins, Finset.insert_eq]]
        exact hdSep
    -- Parents disjoint from `Y`; hence `A0` (⊆ parents) too.
    have hParY : Disjoint (G.parents n) Y := G.parents_disjoint_of_dSep_singleton hdSepN
    have hAY : Disjoint A Y := hParY.mono_left Finset.inter_subset_left
    -- A2f: parents inherit the separation.
    have hA0_par : ∀ a ∈ A0, G.edge a n := by
      intro a ha
      have : a ∈ A := (Finset.mem_sdiff.mp ha).1
      exact G.mem_parents.mp (Finset.mem_inter.mp this).1
    have hA0_D : ∀ a ∈ A0, a ∉ C ∪ Zf := by
      intro a ha haCZf
      rw [Finset.mem_union] at haCZf
      rcases haCZf with haC | haZf
      · exact (Finset.mem_sdiff.mp ha).2 haC
      · exact (Finset.disjoint_left.mp hFR (hZf haZf)) (hA0R ha)
    have hdSepA0 : G.dSep A0 Y (C ∪ Zf) :=
      G.dSep_parents_of_maximal_source hdSepN hA0_par hA0_D
    -- ihA0.
    have hA0Y : Disjoint A0 Y := (hAY.mono_left Finset.sdiff_subset)
    have hA0C : Disjoint A0 C := Finset.sdiff_disjoint
    have hYC : Disjoint Y C := by
      rw [hC_def, Finset.disjoint_union_right]
      exact ⟨hYZ, hXY.symm.mono_right hX'X⟩
    have ihA0 : G.OrderedLocalSG R A0 Y C :=
      orderedLocalSG_of_dSep_with_fixed R F A0 Y C Zf hFixedRoots hFR hA0R hY hCR hZf
        hA0Y hA0C hYC hdSepA0
    -- Basis at `n` with block `P = Y ∪ C ∪ A`.
    have hPR : Y ∪ C ∪ A ⊆ R := Finset.union_subset (Finset.union_subset hY hCR) hAR
    -- `Y ∪ C ⊆ Q` (used to inherit `¬ isAncestor n ·` from topo-maximality).
    have hYC_subQ : Y ∪ C ⊆ Q := by
      rw [hQ_def, hC_def]
      intro w hw
      simp only [Finset.mem_union] at hw ⊢
      rcases hw with hY' | hZr' | hX''
      · exact Or.inl (Or.inl (Or.inr hY'))
      · exact Or.inl (Or.inr hZr')
      · exact Or.inl (Or.inl (Or.inl (hX'X hX'')))
    have hPND : Y ∪ C ∪ A ⊆ G.nonDescendants n := by
      intro w hw
      rw [Finset.mem_union] at hw
      simp only [nonDescendants, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with hwYC | hwA
      · -- w ∈ Y ∪ C ⊆ Q: topo-maximal `n` is no ancestor of `w`, and `w ≠ n`.
        have hwQ : w ∈ Q := hYC_subQ hwYC
        refine ⟨hND_Q w hwQ, ?_⟩
        rintro rfl
        rw [Finset.mem_union, hC_def, Finset.mem_union] at hwYC
        rcases hwYC with h | h | h
        exacts [hnY h, hnZr h, hnX' h]
      · -- w ∈ A = parents n ∩ R: `n` cannot be an ancestor of its own parent.
        have hwPar : w ∈ G.parents n := (Finset.mem_inter.mp hwA).1
        have hedge : G.edge w n := G.mem_parents.mp hwPar
        refine ⟨fun hanc => ?_, fun hwn => G.irrefl n (hwn ▸ hedge)⟩
        exact G.isAncestor_irrefl n (G.isAncestor_trans hanc (isAncestor.edge hedge))
    have hAsubP : A ⊆ Y ∪ C ∪ A := Finset.subset_union_right
    have hPaR_sub : G.parents n ∩ R ⊆ Y ∪ C ∪ A := by rw [← hA_def]; exact hAsubP
    have hbasis := OrderedLocalSG.basis (G := G) (R := R) n (hX hnX) (Y ∪ C ∪ A) hPR hPND hPaR_sub
    -- `(Y ∪ C ∪ A) \ (parents n ∩ R) = Y ∪ (C \ A)`.
    have hsdiff_eq : (Y ∪ C ∪ A) \ (G.parents n ∩ R) = Y ∪ (C \ A) := by
      rw [← hA_def]; ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨(hY' | hC') | hA', hnA⟩
        · exact Or.inl hY'
        · exact Or.inr ⟨hC', hnA⟩
        · exact absurd hA' hnA
      · rintro (hY' | ⟨hC', hnA⟩)
        · exact ⟨Or.inl (Or.inl hY'), fun hA' => (Finset.disjoint_left.mp hAY hA') hY'⟩
        · exact ⟨Or.inl (Or.inr hC'), hnA⟩
    rw [hsdiff_eq, ← hA_def] at hbasis
    -- weakUnion: move `C \ A` into the condition; `A ∪ (C \ A) = C ∪ A0`.
    have hweak := OrderedLocalSG.weakUnion (W := C \ A) (Z := A) hbasis
    have hAC_eq : A ∪ (C \ A) = C ∪ A0 := by
      rw [hA0_def]; ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    rw [hAC_eq] at hweak
    -- hweak : {n} ⊥ Y | (C ∪ A0).  Fold with ihA0 to drop `A0`.
    have hstep2 : G.OrderedLocalSG R {n} Y C := by
      have h1 : G.OrderedLocalSG R Y {n} (C ∪ A0) := hweak.symm
      have h2 : G.OrderedLocalSG R Y A0 C := ihA0.symm
      have hc : G.OrderedLocalSG R Y ({n} ∪ A0) C := OrderedLocalSG.contract h1 h2
      exact (OrderedLocalSG.decomp (W := A0) hc).symm
    -- Final fold with ihX': `{n}∪X' = X`.
    have h1 : G.OrderedLocalSG R Y {n} (Zr ∪ X') := by rw [← hC_def]; exact hstep2.symm
    have h2 : G.OrderedLocalSG R Y X' Zr := ihX'.symm
    have hc : G.OrderedLocalSG R Y ({n} ∪ X') Zr := OrderedLocalSG.contract h1 h2
    rw [show ({n} : Finset V) ∪ X' = X by rw [hXins, Finset.insert_eq]] at hc
    exact hc.symm
  · -- ===== Case n ∈ Y =====  (mirror of the n ∈ X case with X ↔ Y)
    refine OrderedLocalSG.symm ?_
    have hdSepYX : G.dSep Y X (Zr ∪ Zf) := G.dSep_symm _ _ _ hdSep
    set Y' : Finset V := Y.erase n with hY'_def
    set A : Finset V := G.parents n ∩ R with hA_def
    set C : Finset V := Zr ∪ Y' with hC_def
    set A0 : Finset V := A \ C with hA0_def
    have hnY' : n ∉ Y' := Finset.notMem_erase n Y
    have hnZf : n ∉ Zf := fun h => (hnR_of_mem hY hnY) (hZf h)
    have hYins : Y = insert n Y' := (Finset.insert_erase hnY).symm
    have hY'R : Y' ⊆ R := (Finset.erase_subset _ _).trans hY
    have hY'Y : Y' ⊆ Y := Finset.erase_subset _ _
    have hnX : n ∉ X := fun h => (Finset.disjoint_left.mp hXY h) hnY
    have hnZr : n ∉ Zr := fun h => (Finset.disjoint_left.mp hYZ hnY) h
    have hCR : C ⊆ R := Finset.union_subset hZr hY'R
    have hAR : A ⊆ R := Finset.inter_subset_right
    have hA0R : A0 ⊆ R := (Finset.sdiff_subset).trans hAR
    have hND_Q : ∀ w ∈ Q, ¬ G.isAncestor n w := by
      intro w hwQ hanc
      have h1 : G.topoOrder w ≤ G.topoOrder n := hmax w (G.subset_ancestralSet Q hwQ)
      have h2 : G.topoOrder n < G.topoOrder w := G.isAncestor_topoOrder_lt hanc
      omega
    have ihY' : G.OrderedLocalSG R Y' X Zr :=
      orderedLocalSG_of_dSep_with_fixed R F Y' X Zr Zf hFixedRoots hFR hY'R hX hZr hZf
        (hXY.symm.mono_left hY'Y) (hYZ.mono_left hY'Y) hXZ (G.dSep_subset_left hY'Y hdSepYX)
    have hCZf_eq : C ∪ Zf = (Zr ∪ Zf) ∪ Y' := by
      rw [hC_def]; ext x; simp only [Finset.mem_union]; tauto
    have hdSepN : G.dSep {n} X (C ∪ Zf) := by
      rw [hCZf_eq]
      apply G.dSep_source_to_cond (X := {n}) (S := Y')
      · exact Finset.disjoint_singleton_left.mpr hnY'
      · rw [show ({n} : Finset V) ∪ Y' = Y by rw [hYins, Finset.insert_eq]]
        exact hdSepYX
    have hParX : Disjoint (G.parents n) X := G.parents_disjoint_of_dSep_singleton hdSepN
    have hAX : Disjoint A X := hParX.mono_left Finset.inter_subset_left
    have hA0_par : ∀ a ∈ A0, G.edge a n := by
      intro a ha
      have : a ∈ A := (Finset.mem_sdiff.mp ha).1
      exact G.mem_parents.mp (Finset.mem_inter.mp this).1
    have hA0_D : ∀ a ∈ A0, a ∉ C ∪ Zf := by
      intro a ha haCZf
      rw [Finset.mem_union] at haCZf
      rcases haCZf with haC | haZf
      · exact (Finset.mem_sdiff.mp ha).2 haC
      · exact (Finset.disjoint_left.mp hFR (hZf haZf)) (hA0R ha)
    have hdSepA0 : G.dSep A0 X (C ∪ Zf) :=
      G.dSep_parents_of_maximal_source hdSepN hA0_par hA0_D
    have hA0X : Disjoint A0 X := (hAX.mono_left Finset.sdiff_subset)
    have hA0C : Disjoint A0 C := Finset.sdiff_disjoint
    have hXC : Disjoint X C := by
      rw [hC_def, Finset.disjoint_union_right]
      exact ⟨hXZ, hXY.mono_right hY'Y⟩
    have ihA0 : G.OrderedLocalSG R A0 X C :=
      orderedLocalSG_of_dSep_with_fixed R F A0 X C Zf hFixedRoots hFR hA0R hX hCR hZf
        hA0X hA0C hXC hdSepA0
    have hPR : X ∪ C ∪ A ⊆ R := Finset.union_subset (Finset.union_subset hX hCR) hAR
    have hXC_subQ : X ∪ C ⊆ Q := by
      rw [hQ_def, hC_def]
      intro w hw
      simp only [Finset.mem_union] at hw ⊢
      rcases hw with hX' | hZr' | hY''
      · exact Or.inl (Or.inl (Or.inl hX'))
      · exact Or.inl (Or.inr hZr')
      · exact Or.inl (Or.inl (Or.inr (hY'Y hY'')))
    have hPND : X ∪ C ∪ A ⊆ G.nonDescendants n := by
      intro w hw
      rw [Finset.mem_union] at hw
      simp only [nonDescendants, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with hwXC | hwA
      · have hwQ : w ∈ Q := hXC_subQ hwXC
        refine ⟨hND_Q w hwQ, ?_⟩
        rintro rfl
        rw [Finset.mem_union, hC_def, Finset.mem_union] at hwXC
        rcases hwXC with h | h | h
        exacts [hnX h, hnZr h, hnY' h]
      · have hwPar : w ∈ G.parents n := (Finset.mem_inter.mp hwA).1
        have hedge : G.edge w n := G.mem_parents.mp hwPar
        refine ⟨fun hanc => ?_, fun hwn => G.irrefl n (hwn ▸ hedge)⟩
        exact G.isAncestor_irrefl n (G.isAncestor_trans hanc (isAncestor.edge hedge))
    have hPaR_sub : G.parents n ∩ R ⊆ X ∪ C ∪ A := by rw [← hA_def]; exact Finset.subset_union_right
    have hbasis := OrderedLocalSG.basis (G := G) (R := R) n (hY hnY) (X ∪ C ∪ A) hPR hPND hPaR_sub
    have hsdiff_eq : (X ∪ C ∪ A) \ (G.parents n ∩ R) = X ∪ (C \ A) := by
      rw [← hA_def]; ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨(hX' | hC') | hA', hnA⟩
        · exact Or.inl hX'
        · exact Or.inr ⟨hC', hnA⟩
        · exact absurd hA' hnA
      · rintro (hX' | ⟨hC', hnA⟩)
        · exact ⟨Or.inl (Or.inl hX'), fun hA' => (Finset.disjoint_left.mp hAX hA') hX'⟩
        · exact ⟨Or.inl (Or.inr hC'), hnA⟩
    rw [hsdiff_eq, ← hA_def] at hbasis
    have hweak := OrderedLocalSG.weakUnion (W := C \ A) (Z := A) hbasis
    have hAC_eq : A ∪ (C \ A) = C ∪ A0 := by
      rw [hA0_def]; ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    rw [hAC_eq] at hweak
    have hstep2 : G.OrderedLocalSG R {n} X C := by
      have h1 : G.OrderedLocalSG R X {n} (C ∪ A0) := hweak.symm
      have h2 : G.OrderedLocalSG R X A0 C := ihA0.symm
      have hc : G.OrderedLocalSG R X ({n} ∪ A0) C := OrderedLocalSG.contract h1 h2
      exact (OrderedLocalSG.decomp (W := A0) hc).symm
    have h1 : G.OrderedLocalSG R X {n} (Zr ∪ Y') := by rw [← hC_def]; exact hstep2.symm
    have h2 : G.OrderedLocalSG R X Y' Zr := ihY'.symm
    have hc : G.OrderedLocalSG R X ({n} ∪ Y') Zr := OrderedLocalSG.contract h1 h2
    rw [show ({n} : Finset V) ∪ Y' = Y by rw [hYins, Finset.insert_eq]] at hc
    exact hc.symm
  · -- ===== Case n ∈ Zr =====
    set Z' : Finset V := Zr.erase n with hZ'_def
    have hnZ' : n ∉ Z' := Finset.notMem_erase n Zr
    have hZrins : Zr = insert n Z' := (Finset.insert_erase hnZr).symm
    have hZ'R : Z' ⊆ R := (Finset.erase_subset _ _).trans hZr
    have hnX : n ∉ X := fun h => (Finset.disjoint_left.mp hXZ h) hnZr
    have hnY : n ∉ Y := fun h => (Finset.disjoint_left.mp hYZ h) hnZr
    have hnZf : n ∉ Zf := fun h => (hnR_of_mem hZr hnZr) (hZf h)
    have hmax' : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf),
        G.topoOrder m ≤ G.topoOrder n := by rw [← hQ_def]; exact hmax
    -- IH1: drop `n` from the random condition.
    have hdSep1 : G.dSep X Y (Z' ∪ Zf) :=
      G.dSep_erase_maximal_random_condition hnZr hmax' hdSep
    have ih1 : G.OrderedLocalSG R X Y Z' :=
      orderedLocalSG_of_dSep_with_fixed R F X Y Z' Zf hFixedRoots hFR hX hY hZ'R hZf
        hXY (hXZ.mono_right (Finset.erase_subset _ _)) (hYZ.mono_right (Finset.erase_subset _ _))
        hdSep1
    -- Branch lemma: separate `n` from one side.
    have hmaxBr : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ insert n Z' ∪ Zf),
        G.topoOrder m ≤ G.topoOrder n := by rw [← hZrins, ← hQ_def]; exact hmax
    have hdSepBr : G.dSep X Y (insert n Z' ∪ Zf) := by rw [← hZrins]; exact hdSep
    -- Disjointness shared by both recursive branch calls.
    have hXZ' : Disjoint X Z' := hXZ.mono_right (Finset.erase_subset _ _)
    have hYZ' : Disjoint Y Z' := hYZ.mono_right (Finset.erase_subset _ _)
    -- Rewrite the goal's `Zr` as `Z' ∪ {n}`.
    rw [hZrins, Finset.insert_eq, Finset.union_comm {n} Z']
    rcases G.dSep_maximal_condition_branch hnZ' hnZf hmaxBr hdSepBr with hLeft | hRight
    · -- Left branch: `dSep X {n} ((Z'∪Y)∪Zf)`.
      have hP1 : G.OrderedLocalSG R X {n} (Z' ∪ Y) :=
        orderedLocalSG_of_dSep_with_fixed R F X {n} (Z' ∪ Y) Zf hFixedRoots hFR hX
          (Finset.singleton_subset_iff.mpr (hZr hnZr)) (Finset.union_subset hZ'R hY) hZf
          (Finset.disjoint_singleton_right.mpr hnX)
          (by rw [Finset.disjoint_union_right]; exact ⟨hXZ', hXY⟩)
          (Finset.disjoint_singleton_left.mpr (by
            rw [Finset.mem_union]; rintro (h | h); exacts [hnZ' h, hnY h]))
          (by rw [show (Z' ∪ Y) ∪ Zf = (Z' ∪ Y) ∪ Zf from rfl]; exact hLeft)
      -- contraction(X; Ỹ={n}, W̃=Y, Z̃=Z') with ih1, then weak union.
      have hc : G.OrderedLocalSG R X ({n} ∪ Y) Z' := OrderedLocalSG.contract hP1 ih1
      rw [Finset.union_comm {n} Y] at hc
      exact OrderedLocalSG.weakUnion hc
    · -- Right branch: `dSep Y {n} ((Z'∪X)∪Zf)`.
      have hP1 : G.OrderedLocalSG R Y {n} (Z' ∪ X) :=
        orderedLocalSG_of_dSep_with_fixed R F Y {n} (Z' ∪ X) Zf hFixedRoots hFR hY
          (Finset.singleton_subset_iff.mpr (hZr hnZr)) (Finset.union_subset hZ'R hX) hZf
          (Finset.disjoint_singleton_right.mpr hnY)
          (by rw [Finset.disjoint_union_right]; exact ⟨hYZ', hXY.symm⟩)
          (Finset.disjoint_singleton_left.mpr (by
            rw [Finset.mem_union]; rintro (h | h); exacts [hnZ' h, hnX h]))
          hRight
      have hc : G.OrderedLocalSG R Y ({n} ∪ X) Z' := OrderedLocalSG.contract hP1 ih1.symm
      rw [Finset.union_comm {n} X] at hc
      exact (OrderedLocalSG.weakUnion hc).symm
  · -- ===== Case n ∈ Zf =====
    have hnF : n ∈ F := hZf hnZf
    have hRoot : G.parents n = ∅ := hFixedRoots n hnF
    have hmax' : ∀ m ∈ G.ancestralSet (X ∪ Y ∪ Zr ∪ Zf),
        G.topoOrder m ≤ G.topoOrder n := by rw [← hQ_def]; exact hmax
    have hdSep' : G.dSep X Y (Zr ∪ Zf.erase n) :=
      G.dSep_erase_maximal_fixed_root hnZf hRoot hmax' hdSep
    exact orderedLocalSG_of_dSep_with_fixed R F X Y Zr (Zf.erase n)
      hFixedRoots hFR hX hY hZr ((Finset.erase_subset _ _).trans hZf)
      hXY hXZ hYZ hdSep'
  termination_by peelMeasure G X Y Zr Zf
  decreasing_by
    -- Six calls drop `card (ancestralSet ·)` (first lex component); the two branch
    -- calls keep it equal and drop the `topoOrder`-height (second lex component).
    -- `cardDrop` discharges the former given a subset/avoidance pair.
    all_goals simp only [peelMeasure]
    -- (1) n ∈ X, ihX' on (X.erase n, Y, Zr, Zf): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · exact Finset.union_subset (Finset.union_subset (Finset.union_subset
          ((Finset.erase_subset _ _).trans hXQ) hYQ) hZrQ) hZfQ
      · simp only [Finset.mem_union, not_or]
        exact ⟨⟨⟨Finset.notMem_erase n X, hnY⟩, hnZr⟩, hnZf⟩
    -- (2) n ∈ X, ihA0 on (A0, Y, C, Zf): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · refine Finset.union_subset (Finset.union_subset (Finset.union_subset ?_ hYQ) ?_) hZfQ
        · exact (Finset.sdiff_subset.trans Finset.inter_subset_left).trans hParAnc
        · exact Finset.union_subset hZrQ ((Finset.erase_subset _ _).trans hXQ)
      · simp only [Finset.mem_union, not_or]
        refine ⟨⟨⟨?_, hnY⟩, ?_⟩, hnZf⟩
        · exact fun h => G.isAncestor_irrefl n
            (isAncestor.edge (G.mem_parents.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1))
        · exact ⟨hnZr, Finset.notMem_erase n X⟩
    -- (3) n ∈ Y, ihY' on (Y.erase n, X, Zr, Zf): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · exact Finset.union_subset (Finset.union_subset (Finset.union_subset
          ((Finset.erase_subset _ _).trans hYQ) hXQ) hZrQ) hZfQ
      · simp only [Finset.mem_union, not_or]
        exact ⟨⟨⟨Finset.notMem_erase n Y, hnX⟩, hnZr⟩, hnZf⟩
    -- (4) n ∈ Y, ihA0 on (A0, X, C, Zf): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · refine Finset.union_subset (Finset.union_subset (Finset.union_subset ?_ hXQ) ?_) hZfQ
        · exact (Finset.sdiff_subset.trans Finset.inter_subset_left).trans hParAnc
        · exact Finset.union_subset hZrQ ((Finset.erase_subset _ _).trans hYQ)
      · simp only [Finset.mem_union, not_or]
        refine ⟨⟨⟨?_, hnX⟩, ?_⟩, hnZf⟩
        · exact fun h => G.isAncestor_irrefl n
            (isAncestor.edge (G.mem_parents.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).1))
        · exact ⟨hnZr, Finset.notMem_erase n Y⟩
    -- (5) n ∈ Zr, ih1 on (X, Y, Zr.erase n, Zf): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · exact Finset.union_subset (Finset.union_subset (Finset.union_subset hXQ hYQ)
          ((Finset.erase_subset _ _).trans hZrQ)) hZfQ
      · simp only [Finset.mem_union, not_or]
        exact ⟨⟨⟨hnX, hnY⟩, Finset.notMem_erase n Zr⟩, hnZf⟩
    -- (6) n ∈ Zr, left branch P1 on (X, {n}, Z'∪Y, Zf): card EQUAL, height drops.
    · rw [branch_seed_eq (a := X) (b := Y) (c := Zf) hnZr]
      refine Prod.Lex.right _ ?_
      exact G.sup_topoOrder_lt_of_peel hmax hnZr
        (Finset.union_subset ((Finset.erase_subset _ _).trans hZrQ) hYQ)
        (by simp only [Finset.mem_union, not_or]; exact ⟨hnZ', hnY⟩)
    -- (7) n ∈ Zr, right branch P1 on (Y, {n}, Z'∪X, Zf): card EQUAL, height drops.
    · rw [branch_seed_eq (a := Y) (b := X) (c := Zf) hnZr,
        show X ∪ Y ∪ Zr ∪ Zf = Y ∪ X ∪ Zr ∪ Zf from by
          rw [Finset.union_comm X Y]]
      refine Prod.Lex.right _ ?_
      exact G.sup_topoOrder_lt_of_peel hmax hnZr
        (Finset.union_subset ((Finset.erase_subset _ _).trans hZrQ) hXQ)
        (by simp only [Finset.mem_union, not_or]; exact ⟨hnZ', hnX⟩)
    -- (8) n ∈ Zf, on (X, Y, Zr, Zf.erase n): card drops.
    · refine Prod.Lex.left _ _ (G.ancestralSet_card_lt_of_peel hnAnc hmax ?_ ?_)
      · exact Finset.union_subset (Finset.union_subset (Finset.union_subset hXQ hYQ) hZrQ)
          ((Finset.erase_subset _ _).trans hZfQ)
      · simp only [Finset.mem_union, not_or]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, Finset.notMem_erase n Zf⟩
        · exact fun h => (hnR_of_mem hX h) (hZf hnZf)
        · exact fun h => (hnR_of_mem hY h) (hZf hnZf)
        · exact fun h => (hnR_of_mem hZr h) (hZf hnZf)

/-- **Extending an active path by a directed arm at a non-collider seam.**

    If `pa` is an active path from `a` to `c` given `Z`, and `q` is a
    forward-directed path from `c` to `b` whose interior nodes avoid `Z`, with
    the seam node `c ∉ Z`, then `b` is Bayes-Ball reachable from `{a}` given `Z`.

    The directed arm leaves `c` (its first edge points out of `c`), so `c` is a
    chain/fork point — never a collider — at the seam, and the glued path stays
    active.  Public wrapper around `chain_join_active`. -/
theorem bbReachable_extend_directed_arm
    {Z : Finset V} {a c b : V} {pa q : List V}
    (hpa_len : pa.length ≥ 2) (hpa_head : pa.head? = some a)
    (hpa_last : pa.getLast? = some c) (hpa_act : G.IsActivePath Z pa)
    (hq_len : q.length ≥ 2) (hq_head : q.head? = some c) (hq_last : q.getLast? = some b)
    (hq_edge : ∀ (i : ℕ) (hi : i + 1 < q.length),
        G.edge (q.get ⟨i, by omega⟩) (q.get ⟨i + 1, hi⟩))
    (hq_int : ∀ (i : ℕ) (hi : i + 2 < q.length), q.get ⟨i + 1, by omega⟩ ∉ Z)
    (hcZ : c ∉ Z) :
    b ∈ G.bbReachableVertices Z ({a} : Finset V) := by
  have hq_act : G.IsActivePath Z q := G.isActivePath_of_directed_interior hq_edge hq_int
  have hqne : q ≠ [] := by intro h; rw [h] at hq_len; simp at hq_len
  -- First edge of `q` points out of `c`.
  have hq_head_eq : q.get ⟨0, by omega⟩ = c := by
    have h := List.head?_eq_some_head hqne
    rw [hq_head] at h
    rw [List.get_eq_getElem, List.getElem_zero]
    exact Option.some_inj.mp h.symm
  have hseam_out : G.edge c (q.get ⟨1, by omega⟩) := by
    have he := hq_edge 0 (by omega)
    rwa [hq_head_eq] at he
  obtain ⟨_, hjhead, hjlast, hjact⟩ :=
    G.chain_join_active hpa_len hpa_head hpa_last hpa_act hq_len hq_head hq_last hq_act
      hseam_out hcZ
  rw [G.bbReachableVertices_iff_activePath]
  exact ⟨a, Finset.mem_singleton_self a, pa ++ q.tail,
    by rw [List.length_append]; have := List.length_tail (l := q); omega,
    hjact, hjhead, hjlast⟩

end DAG

end Causalean
