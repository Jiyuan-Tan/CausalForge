/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.MarkovEquiv.Defs
import Causalean.Graph.DSep.Ancestral

/-! # Markov equivalence — the moralization criterion

This file develops the **moral graph** of a DAG and the classical *moralization criterion*
for d-separation. It proves that, for pairwise-disjoint source, target, and conditioning
sets, d-separation is equivalent to separation in the moral graph of the ancestral set.

* `DAG.MoralAdj G S u v` — `u` and `v` are adjacent in the moral graph restricted to a
  ground set `S`: they are skeleton-adjacent (`UAdj`) or "married", i.e. they have a common
  child inside `S`.
* `DAG.MoralConn G S Z u v` — `u` reaches `v` by a moral path inside `S` all of whose
  vertices avoid `Z`.
* `DAG.MoralSep G X Y Z` — no `x ∈ X` is moral-connected to any `y ∈ Y` inside the
  ancestral set `An(X ∪ Y ∪ Z)` while avoiding `Z`.
* `DAG.dSep_iff_moralSep` — **the criterion**: for pairwise-disjoint sets, d-separation is
  exactly moral separation in the ancestral set.

The file also proves that moral adjacency, moral steps, and moral connectivity are
invariants of a graph's skeleton together with its v-structures, for a fixed ground set.
The main Verma–Pearl hard direction used by the public umbrella theorem is assembled through
the covered-edge route in `Transfer.lean` and `Decompose.lean`.
-/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

/-- **Moral adjacency** within a ground set `S`: distinct vertices `u, v ∈ S` that are
either skeleton-adjacent or share a common child inside `S` ("married parents"). This is the
undirected edge relation of the moral graph of `G` restricted to `S`. -/
def MoralAdj (S : Finset V) (u v : V) : Prop :=
  u ≠ v ∧ u ∈ S ∧ v ∈ S ∧ (G.UAdj u v ∨ ∃ c ∈ S, G.edge u c ∧ G.edge v c)

/-- A single moral step inside `S` that avoids the conditioning set `Z` (both endpoints
outside `Z`). -/
def MoralStep (S Z : Finset V) (u v : V) : Prop :=
  G.MoralAdj S u v ∧ u ∉ Z ∧ v ∉ Z

/-- **Moral connectivity**: `u` reaches `v` by a (possibly empty) sequence of moral steps
inside `S`, every vertex of which avoids `Z`. -/
def MoralConn (S Z : Finset V) (u v : V) : Prop :=
  Relation.ReflTransGen (G.MoralStep S Z) u v

/-- **Moral separation**: no vertex of `X` is moral-connected to a vertex of `Y` inside the
ancestral set `An(X ∪ Y ∪ Z)` while avoiding `Z`. -/
def MoralSep (X Y Z : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ¬ G.MoralConn (G.ancestralSet (X ∪ Y ∪ Z)) Z x y

/-- Moral adjacency is symmetric: an undirected moral edge from `u` to `v` is also one
from `v` to `u`. -/
theorem moralAdj_symm {S : Finset V} {u v : V} (h : G.MoralAdj S u v) :
    G.MoralAdj S v u := by
  obtain ⟨hne, hu, hv, hdisj⟩ := h
  refine ⟨hne.symm, hv, hu, ?_⟩
  rcases hdisj with hadj | ⟨c, hc, huc, hvc⟩
  · exact Or.inl (G.UAdj_symm hadj)
  · exact Or.inr ⟨c, hc, hvc, huc⟩

-- ============================================================
-- Moral-connectivity plumbing
-- ============================================================

/-- A single moral step yields moral connectivity. -/
private theorem moralConn_of_step {S Z : Finset V} {u v : V}
    (h : G.MoralStep S Z u v) : G.MoralConn S Z u v :=
  Relation.ReflTransGen.single h

/-- Moral connectivity is transitive. -/
private theorem moralConn_trans {S Z : Finset V} {u v w : V}
    (h₁ : G.MoralConn S Z u v) (h₂ : G.MoralConn S Z v w) : G.MoralConn S Z u w :=
  Relation.ReflTransGen.trans h₁ h₂

/-- A skeleton edge between two non-`Z` vertices of `S` is a moral step. -/
private theorem moralStep_of_uAdj {S Z : Finset V} {u v : V}
    (hne : u ≠ v) (hu : u ∈ S) (hv : v ∈ S) (hadj : G.UAdj u v)
    (huZ : u ∉ Z) (hvZ : v ∉ Z) : G.MoralStep S Z u v :=
  ⟨⟨hne, hu, hv, Or.inl hadj⟩, huZ, hvZ⟩

/-- A married pair (common child `c ∈ S`) of distinct non-`Z` vertices of `S` is a
moral step. -/
private theorem moralStep_of_married {S Z : Finset V} {u v c : V}
    (hne : u ≠ v) (hu : u ∈ S) (hv : v ∈ S) (hc : c ∈ S)
    (huc : G.edge u c) (hvc : G.edge v c) (huZ : u ∉ Z) (hvZ : v ∉ Z) :
    G.MoralStep S Z u v :=
  ⟨⟨hne, hu, hv, Or.inr ⟨c, hc, huc, hvc⟩⟩, huZ, hvZ⟩

-- ============================================================
-- Active-path cons destructors (local copies, the originals are file-private)
-- ============================================================

/-- Head adjacency of a cons active path. -/
private theorem activePath_head_uAdj {Z : Finset V} {a b : V} {r : List V}
    (h : G.IsActivePath Z (a :: b :: r)) : G.UAdj a b := by
  have := h.1 0 (by simp)
  simpa using this

/-- The collider/non-collider clause at the head triple of a cons active path. -/
private theorem activePath_head_triple {Z : Finset V} {a b c : V} {r : List V}
    (h : G.IsActivePath Z (a :: b :: c :: r)) :
    if G.IsCollider a b c then b ∈ G.bbZAncestors Z else b ∉ Z := by
  have := h.2 0 (by simp)
  simpa using this

/-- The tail of a cons active path is active. -/
private theorem activePath_tail {Z : Finset V} {a b : V} {r : List V}
    (h : G.IsActivePath Z (a :: b :: r)) : G.IsActivePath Z (b :: r) := by
  obtain ⟨hadj, hcoll⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h' := hadj (i + 1) (by simpa [Nat.add_assoc] using Nat.succ_lt_succ hi)
    simpa using h'
  · have h' := hcoll (i + 1) (by simpa [Nat.add_assoc] using Nat.succ_lt_succ hi)
    simpa [Nat.add_assoc] using h'

/-- The `drop 2` of an active path `a :: b :: c :: r` is the active path `c :: r`. -/
private theorem activePath_drop2 {Z : Finset V} {a b c : V} {r : List V}
    (h : G.IsActivePath Z (a :: b :: c :: r)) : G.IsActivePath Z (c :: r) :=
  G.activePath_tail (G.activePath_tail h)

-- ============================================================
-- Direction 1: an active path induces a moral path (active ⇒ moral)
-- ============================================================

/-- **Active path ⇒ moral path (core induction).** If `p` is an active path given `Z`
of length ≥ 2, all of whose nodes lie in the ground set `S`, and both endpoints avoid
`Z`, then the head and last of `p` are moral-connected inside `S` avoiding `Z`.

The moral path threads the *non-collider* vertices of `p`: consecutive non-colliders are
skeleton-adjacent, and across a collider apex `b` (skipped) the two flanking parents are
married through `b ∈ S`. The proof is strong induction on `p.length`, peeling one vertex
(skeleton step) or two vertices (across a collider) from the front. -/
private theorem moralConn_of_activePath
    {S Z : Finset V} :
    ∀ (n : ℕ) {x y : V} {p : List V}, p.length ≤ n →
    G.IsActivePath Z p → p.length ≥ 2 →
    (∀ v ∈ p, v ∈ S) →
    p.head? = some x → p.getLast? = some y →
    x ∉ Z → y ∉ Z →
    G.MoralConn S Z x y := by
  intro n
  induction n with
  | zero => intro x y p hn _ hlen _ _ _ _ _; omega
  | succ n ih =>
    intro x y p hn hp hlen hnodes hhead hlast hxZ hyZ
    -- `p = a :: b :: r` with `a = x`.
    obtain ⟨a, b, r, rfl⟩ : ∃ a b r, p = a :: b :: r := by
      match p, hlen with
      | a :: b :: r, _ => exact ⟨a, b, r, rfl⟩
    have hax : a = x := by simpa using hhead
    subst hax
    clear hhead
    have haS : a ∈ S := hnodes a (by simp)
    have hbS : b ∈ S := hnodes b (by simp)
    have hadj_ab : G.UAdj a b := G.activePath_head_uAdj hp
    -- Branch on the remainder.
    match r, hp, hn, hnodes, hlast with
    | [], hp, hn, hnodes, hlast =>
        -- `p = [a, b]`: single skeleton step `a — b`, with `b = y`.
        have hby : b = y := by simpa using hlast
        subst hby
        have hne : a ≠ b := by
          rintro rfl
          rcases hadj_ab with h | h <;> exact G.irrefl a h
        exact G.moralConn_of_step (G.moralStep_of_uAdj hne haS hbS hadj_ab hxZ hyZ)
    | c :: r', hp, hn, hnodes, hlast =>
        have hcS : c ∈ S := hnodes c (by simp)
        have htri := G.activePath_head_triple hp
        by_cases hcoll : G.IsCollider a b c
        · -- Married step `a — c` across the collider apex `b`.
          rw [if_pos hcoll] at htri
          obtain ⟨hab_edge, hcb_edge⟩ := hcoll
          -- The married step (or reflexivity if `a = c`), then continue from `c`.
          have hstep : ∀ (hcZ : c ∉ Z), G.MoralConn S Z a c := by
            intro hcZ
            by_cases hne : a = c
            · subst hne; exact Relation.ReflTransGen.refl
            · exact G.moralConn_of_step
                (G.moralStep_of_married hne haS hcS hbS hab_edge hcb_edge hxZ hcZ)
          match r', hp, hn, hnodes, hlast with
          | [], hp, hn, hnodes, hlast =>
              -- `c` is the last node, so `c = y`; the married step is the whole path.
              have hcy : c = y := by simpa using hlast
              subst hcy
              exact hstep hyZ
          | d :: r'', hp, hn, hnodes, hlast =>
              -- triple `(b, c, d)`; `c` cannot be a collider (would clash with `b`).
              have htri2 := G.activePath_head_triple (G.activePath_tail hp)
              have hncoll2 : ¬ G.IsCollider b c d := by
                rintro ⟨hbc, _⟩
                exact G.asymm hcb_edge hbc
              rw [if_neg hncoll2] at htri2
              have hcZ : c ∉ Z := htri2
              have hrest : G.MoralConn S Z c y := by
                refine ih (p := c :: d :: r'') ?_ (G.activePath_drop2 hp) (by simp)
                  (fun v hv => hnodes v (by simp [hv])) rfl (by simpa using hlast) hcZ hyZ
                simp only [List.length_cons] at hn ⊢; omega
              exact G.moralConn_trans (hstep hcZ) hrest
        · -- Skeleton step `a — b`, then recurse on `b :: c :: r'`.
          rw [if_neg hcoll] at htri
          have hbZ : b ∉ Z := htri
          have hne : a ≠ b := by
            rintro rfl
            rcases hadj_ab with h | h <;> exact G.irrefl a h
          have hstep : G.MoralConn S Z a b :=
            G.moralConn_of_step (G.moralStep_of_uAdj hne haS hbS hadj_ab hxZ hbZ)
          have hrest : G.MoralConn S Z b y := by
            apply ih (p := b :: c :: r') (by simp at hn ⊢; omega) (G.activePath_tail hp)
              (by simp) (fun v hv => hnodes v (by simp [hv])) rfl (by simpa using hlast) hbZ hyZ
          exact G.moralConn_trans hstep hrest

-- ============================================================
-- Direction 2: a moral path induces a Bayes-Ball trail (moral ⇒ active)
--
-- We track a Bayes-Ball *state* `(t, d) ∈ bbReachable Z X` (or the source case
-- `t ∈ X`) as we walk the moral path, using the step semantics of `bbStep`.
-- ============================================================

/-- From a `bbReachable` state we can descend along an outgoing edge `w → c`
(when `w ∉ Z`), arriving at `c` from a parent. -/
private theorem bbReach_down {X Z : Finset V} {w c : V} {d : BBDir}
    (hs : (w, d) ∈ G.bbReachable Z X) (hwZ : w ∉ Z) (he : G.edge w c) :
    (c, BBDir.fromParent) ∈ G.bbReachable Z X := by
  apply G.bbReachable_bbStep_subset Z X hs
  cases d
  · -- fromParent, w ∉ Z: children are reachable (fromParent).
    simp only [bbStep, hwZ]
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_map.mpr ⟨c, G.mem_children.mpr he, rfl⟩
  · -- fromChild, w ∉ Z: children are reachable (fromParent).
    simp only [bbStep, hwZ]
    refine Finset.mem_union_right _ ?_
    exact Finset.mem_map.mpr ⟨c, G.mem_children.mpr he, rfl⟩

/-- From a `bbReachable` state arriving at `w` *from a child* (with `w ∉ Z`) we can
ascend along an incoming edge `p → w`, arriving at `p` from a child. -/
private theorem bbReach_up_fromChild {X Z : Finset V} {w p : V}
    (hs : (w, BBDir.fromChild) ∈ G.bbReachable Z X) (hwZ : w ∉ Z) (he : G.edge p w) :
    (p, BBDir.fromChild) ∈ G.bbReachable Z X := by
  apply G.bbReachable_bbStep_subset Z X hs
  simp only [bbStep, hwZ]
  refine Finset.mem_union_left _ ?_
  exact Finset.mem_map.mpr ⟨p, G.mem_parents.mpr he, rfl⟩

/-- From a `bbReachable` state arriving at `w` *from a parent*, if `w` is an
activated collider (`w ∈ An(Z)`) we can ascend along an incoming edge `p → w`. -/
private theorem bbReach_up_collider {X Z : Finset V} {w p : V}
    (hs : (w, BBDir.fromParent) ∈ G.bbReachable Z X)
    (hanc : w ∈ G.bbZAncestors Z) (he : G.edge p w) :
    (p, BBDir.fromChild) ∈ G.bbReachable Z X := by
  apply G.bbReachable_bbStep_subset Z X hs
  by_cases hwZ : w ∈ Z
  · simp only [bbStep, if_neg (show ¬ w ∉ Z by simpa using hwZ)]
    exact Finset.mem_map.mpr ⟨p, G.mem_parents.mpr he, rfl⟩
  · simp only [bbStep, hwZ, hanc, if_true]
    refine Finset.mem_union_right _ ?_
    exact Finset.mem_map.mpr ⟨p, G.mem_parents.mpr he, rfl⟩

/-- Initial states: a child of a source `x ∈ X` is reached from a parent. -/
private theorem bbReach_init_child {X Z : Finset V} {x c : V}
    (hx : x ∈ X) (he : G.edge x c) :
    (c, BBDir.fromParent) ∈ G.bbReachable Z X := by
  apply G.bbReachable_init_subset Z X
  rw [bbInit, Finset.mem_biUnion]
  exact ⟨x, hx, Finset.mem_union_left _ (Finset.mem_map.mpr ⟨c, G.mem_children.mpr he, rfl⟩)⟩

/-- Initial states: a parent of a source `x ∈ X` is reached from a child. -/
private theorem bbReach_init_parent {X Z : Finset V} {x p : V}
    (hx : x ∈ X) (he : G.edge p x) :
    (p, BBDir.fromChild) ∈ G.bbReachable Z X := by
  apply G.bbReachable_init_subset Z X
  rw [bbInit, Finset.mem_biUnion]
  exact ⟨x, hx, Finset.mem_union_right _ (Finset.mem_map.mpr ⟨p, G.mem_parents.mpr he, rfl⟩)⟩

/-- A descending directed path from `a` (reached as a Bayes-Ball state) to any descendant
`w` keeps the descended state Bayes-Ball reachable: every edge is a downward (parent→child)
non-collider step, and every node on the way avoids `Z` because `a ∉ G.ancestralSet Z`
(a `Z`-node descendant would put `a ∈ An(Z)`). -/
private theorem bbReach_descent {X Z : Finset V} {a w : V}
    (ha_reach : (a, BBDir.fromParent) ∈ G.bbReachable Z X)
    (haAncZ : a ∉ G.ancestralSet Z) (haw : G.isAncestor a w) :
    (w, BBDir.fromParent) ∈ G.bbReachable Z X := by
  -- Walk down the ancestor chain `a ⇝ w`. Each prefix node `c` has `a ⇝ c`, hence `c ∉ Z`.
  induction haw with
  | edge he =>
      have haZ : a ∉ Z := fun h => haAncZ (G.subset_ancestralSet Z h)
      exact G.bbReach_down ha_reach haZ he
  | trans hac hcb ih =>
      rename_i c b
      have hcZ : c ∉ Z := fun h => haAncZ (G.mem_ancestralSet_of_isAncestor h hac)
      exact G.bbReach_down ih hcZ hcb

/-- **Ascending refresh.** If a descendant `d` is reached *from a child* and `a` is an
ancestor of `d` with `a ∉ An(Z)`, then the ancestor `a` is also reached from a child: walk
*up* the directed chain `a ⇝ d`, each step a `fromChild → fromChild` parent move (legal since
every chain node avoids `Z`, a `Z`-node descendant of `a` would force `a ∈ An(Z)`).

This is what lets an apex stuck in the `fromParent` direction be "refreshed" to `fromChild`
by routing through a source in `X`: descend the apex into `X`, then re-ascend. -/
private theorem bbReach_ascent {X Z : Finset V} {a d : V}
    (haAncZ : a ∉ G.ancestralSet Z) (had : G.isAncestor a d) :
    (d, BBDir.fromChild) ∈ G.bbReachable Z X → (a, BBDir.fromChild) ∈ G.bbReachable Z X := by
  induction had with
  | edge he =>
      rename_i e
      intro hd_reach
      have hdZ : e ∉ Z := fun h => haAncZ (G.mem_ancestralSet_of_isAncestor h (isAncestor.edge he))
      exact G.bbReach_up_fromChild hd_reach hdZ he
  | trans haw hwd ih =>
      rename_i w e
      intro hd_reach
      have hdZ : e ∉ Z := fun h =>
        haAncZ (G.mem_ancestralSet_of_isAncestor h (isAncestor.trans haw hwd))
      exact ih (G.bbReach_up_fromChild hd_reach hdZ hwd)

/-- The vertex form of `bbReach_descent`: a descendant of a reached non-`An(Z)` state is a
Bayes-Ball reachable vertex. -/
private theorem bbReachableVertices_of_descent {X Z : Finset V} {a w : V}
    (ha_reach : (a, BBDir.fromParent) ∈ G.bbReachable Z X)
    (haAncZ : a ∉ G.ancestralSet Z) (haw : G.isAncestor a w) :
    w ∈ G.bbReachableVertices Z X :=
  Finset.mem_image.mpr ⟨(w, BBDir.fromParent), G.bbReach_descent ha_reach haAncZ haw, rfl⟩

/-- Membership in `An(A)` as either membership in the seed `A` (descend trivially) or being
a strict ancestor of a seed element. -/
private theorem ancestralSet_cases {A : Finset V} {a : V} (h : a ∈ G.ancestralSet A) :
    a ∈ A ∨ ∃ w ∈ A, G.isAncestor a w := by
  rcases Finset.mem_union.mp h with hA | hAnc
  · exact Or.inl hA
  · simp only [ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hAnc
    exact Or.inr hAnc

/-- An apex of the ancestral set `An(X ∪ Y ∪ Z)` that is *not* in `An(Z)` lies in `An(X)` or
in `An(Y)`: it descends (trivially or via a directed path) into `X` or into `Y`. -/
private theorem apex_descends_to_XY {X Y Z : Finset V} {a : V}
    (haS : a ∈ G.ancestralSet (X ∪ Y ∪ Z)) (haZ : a ∉ G.ancestralSet Z) :
    (a ∈ X ∨ ∃ w ∈ X, G.isAncestor a w) ∨ (a ∈ Y ∨ ∃ w ∈ Y, G.isAncestor a w) := by
  rcases G.ancestralSet_cases haS with hmem | ⟨w, hwW, haw⟩
  · -- `a ∈ X ∪ Y ∪ Z`. The `Z` case contradicts `a ∉ An(Z)`.
    rcases Finset.mem_union.mp hmem with hXY | hZ
    · rcases Finset.mem_union.mp hXY with hX | hY
      · exact Or.inl (Or.inl hX)
      · exact Or.inr (Or.inl hY)
    · exact absurd (G.subset_ancestralSet Z hZ) haZ
  · -- `a ⇝ w` with `w ∈ X ∪ Y ∪ Z`. The `Z` case contradicts `a ∉ An(Z)`.
    rcases Finset.mem_union.mp hwW with hXY | hZ
    · rcases Finset.mem_union.mp hXY with hX | hY
      · exact Or.inl (Or.inr ⟨w, hX, haw⟩)
      · exact Or.inr (Or.inr ⟨w, hY, haw⟩)
    · exact absurd (G.mem_ancestralSet_of_isAncestor hZ haw) haZ

/-- The trail-state invariant carried along the moral path in Direction 2: the current node
`t` is either a source (`t ∈ X`) or has been reached as a Bayes-Ball state in some direction. -/
private def Trail (X Z : Finset V) (t : V) : Prop :=
  t ∈ X ∨ (t, BBDir.fromParent) ∈ G.bbReachable Z X ∨ (t, BBDir.fromChild) ∈ G.bbReachable Z X

/-- From a trail-state at `t` (with `t ∉ Z`) and an outgoing edge `t → c`, we reach
`(c, fromParent)`. -/
private theorem trail_down {X Z : Finset V} {t c : V}
    (ht : G.Trail X Z t) (htZ : t ∉ Z) (he : G.edge t c) :
    (c, BBDir.fromParent) ∈ G.bbReachable Z X := by
  rcases ht with hX | hP | hC
  · exact G.bbReach_init_child hX he
  · exact G.bbReach_down hP htZ he
  · exact G.bbReach_down hC htZ he

/-- From a trail-state at `t` and an incoming edge `p → t`, with `t` either a source/from-child
state (turn allowed) or an activated collider (`t ∈ An(Z)`), we reach `(p, fromChild)`. -/
private theorem trail_up {X Z : Finset V} {t p : V}
    (ht : G.Trail X Z t) (htZ : t ∉ Z) (he : G.edge p t)
    (hcoll : (t, BBDir.fromParent) ∈ G.bbReachable Z X → t ∈ G.bbZAncestors Z) :
    (p, BBDir.fromChild) ∈ G.bbReachable Z X := by
  rcases ht with hX | hP | hC
  · exact G.bbReach_init_parent hX he
  · exact G.bbReach_up_collider hP (hcoll hP) he
  · exact G.bbReach_up_fromChild hC htZ he

/-- **X-source refresh.** If the apex `a` (with `a ∉ An(Z)`) lies in `An(X)`, then for any
incoming edge `c → a` the parent `c` is reached from a child. When `a ∈ X` the parent is
initial; otherwise descend `a` into a source `x' ∈ X` and re-ascend the directed chain to
recover `(a, fromChild)`, then step up to `c`. -/
private theorem apex_up_to_c_via_X {X Z : Finset V} {a c : V}
    (haZ : a ∉ G.ancestralSet Z) (he : G.edge c a)
    (hX : a ∈ X ∨ ∃ w ∈ X, G.isAncestor a w) :
    (c, BBDir.fromChild) ∈ G.bbReachable Z X := by
  have haZ' : a ∉ Z := fun h => haZ (G.subset_ancestralSet Z h)
  rcases hX with haX | ⟨x', hx'X, hax'⟩
  · -- `a ∈ X`: `c` is a parent of the source `a`.
    exact G.bbReach_init_parent haX he
  · -- `a ⇝ x' ∈ X`: refresh `(a, fromChild)`, then step up to `c`.
    have ha_fromChild : (a, BBDir.fromChild) ∈ G.bbReachable Z X := by
      cases hax' with
      | edge hax => exact G.bbReach_init_parent hx'X hax
      | trans haq hqx =>
          rename_i q
          have hq_reach : (q, BBDir.fromChild) ∈ G.bbReachable Z X :=
            G.bbReach_init_parent hx'X hqx
          exact G.bbReach_ascent haZ haq hq_reach
    exact G.bbReach_up_fromChild ha_fromChild haZ' he

/-- **Apex resolution.** A reached apex state `(a, fromParent)` with `a ∈ An(X∪Y∪Z) \ An(Z)`
and an incoming edge `c → a` is resolved in one of two ways. If `a ∈ An(Y)`, descend into `Y`
to expose a Bayes-Ball reachable target (d-connection). If `a ∈ An(X)`, refresh through an
`X`-source to reach the parent `c` from a child (continuing the trail). -/
private theorem apex_resolve {X Y Z : Finset V} {a c : V}
    (haReach : (a, BBDir.fromParent) ∈ G.bbReachable Z X)
    (haS : a ∈ G.ancestralSet (X ∪ Y ∪ Z)) (haZ : a ∉ G.ancestralSet Z)
    (he : G.edge c a) :
    (c, BBDir.fromChild) ∈ G.bbReachable Z X ∨ ∃ w ∈ Y, w ∈ G.bbReachableVertices Z X := by
  rcases G.apex_descends_to_XY haS haZ with hX | hY
  · -- `a ∈ An(X)`: refresh through an `X`-source and step up to `c`.
    exact Or.inl (G.apex_up_to_c_via_X haZ he hX)
  · -- `a ∈ An(Y)`: descend into `Y`.
    rcases hY with haY | ⟨w, hwY, haw⟩
    · exact Or.inr ⟨a, haY, Finset.mem_image.mpr ⟨_, haReach, rfl⟩⟩
    · exact Or.inr ⟨w, hwY, G.bbReachableVertices_of_descent haReach haZ haw⟩

/-- **Direction 2 core (`¬ MoralSep → ¬ dSep`, the trail builder).** Walking a moral path
from a trail-state, we either find a Bayes-Ball reachable vertex in `Y` (d-connection), or we
are blocked only at a married/collider apex `a ∈ An(X∪Y∪Z) \ An(Z)` that descends into `X`
(the endpoint-absorption obstruction).

The conclusion is exactly `¬ dSep` once the moral path ends in `Y`. -/
private theorem dconn_of_moralConn {X Y Z : Finset V}
    (hXY : Disjoint X Y) :
    ∀ {t y : V}, G.MoralConn (G.ancestralSet (X ∪ Y ∪ Z)) Z t y →
      G.Trail X Z t → t ∉ Z → y ∈ Y →
      ∃ w ∈ Y, w ∈ G.bbReachableVertices Z X := by
  intro t y hconn
  induction hconn using Relation.ReflTransGen.head_induction_on with
  | refl =>
      -- `t = y ∈ Y`: the trail-state at `y` is itself a reachable vertex (`y ∉ X` by disjointness).
      intro ht _ hyY
      rcases ht with hX | hP | hC
      · exact absurd hX (Finset.disjoint_right.mp hXY hyY)
      · exact ⟨_, hyY, Finset.mem_image.mpr ⟨_, hP, rfl⟩⟩
      · exact ⟨_, hyY, Finset.mem_image.mpr ⟨_, hC, rfl⟩⟩
  | head hstep _hrest ih =>
      rename_i t c
      intro ht htZ hyY
      obtain ⟨⟨hne, htS, hcS, hadj⟩, _htZ', hcZ⟩ := hstep
      -- Produce a trail-state at `c` (then recurse), or escape at an apex.
      -- `Trail X Z c` suffices: feed it to `ih`.
      suffices hTrailc : (G.Trail X Z c) ∨ (∃ w ∈ Y, w ∈ G.bbReachableVertices Z X) by
        rcases hTrailc with hc | hdone
        · exact ih hc hcZ hyY
        · exact hdone
      rcases hadj with hUAdj | ⟨a, haS, hta, hca⟩
      · -- Skeleton edge `t — c`.
        rcases hUAdj with htc | hct
        · -- `t → c`: descend to `c` from a parent.
          exact Or.inl (Or.inr (Or.inl (G.trail_down ht htZ htc)))
        · -- `c → t`: ascend to the parent `c`.
          rcases ht with hX | hP | hC
          · exact Or.inl (Or.inr (Or.inr (G.bbReach_init_parent hX hct)))
          · by_cases hanc : t ∈ G.ancestralSet Z
            · exact Or.inl (Or.inr (Or.inr (G.bbReach_up_collider hP hanc hct)))
            · -- `t` is a non-collider apex `∉ An(Z)`: resolve via `An(X)`/`An(Y)`.
              rcases G.apex_resolve hP htS hanc hct with hcReach | hdone
              · exact Or.inl (Or.inr (Or.inr hcReach))
              · exact Or.inr hdone
          · exact Or.inl (Or.inr (Or.inr (G.bbReach_up_fromChild hC htZ hct)))
      · -- Married edge `t — c` with common child `a`: descend to `a`, then ascend to `c`.
        have ha_reach : (a, BBDir.fromParent) ∈ G.bbReachable Z X := G.trail_down ht htZ hta
        by_cases hanc : a ∈ G.ancestralSet Z
        · exact Or.inl (Or.inr (Or.inr (G.bbReach_up_collider ha_reach hanc hca)))
        · -- `a` is a married apex `∉ An(Z)`: resolve via `An(X)`/`An(Y)`.
          rcases G.apex_resolve ha_reach haS hanc hca with hcReach | hdone
          · exact Or.inl (Or.inr (Or.inr hcReach))
          · exact Or.inr hdone

/-- **Direction 1 (`¬ dSep → ¬ MoralSep`).** If `X` and `Y` are *not* d-separated by `Z`,
then they are not moral-separated: a `G`-active path witnessing d-connection threads a moral
path inside `An(X ∪ Y ∪ Z)` avoiding `Z`. -/
private theorem not_moralSep_of_not_dSep {X Y Z : Finset V}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (h : ¬ G.dSep X Y Z) :
    ¬ G.MoralSep X Y Z := by
  -- Extract a `bbReachable` witness in `Y`, then an active path.
  have hReach : ¬ Disjoint (G.bbReachableVertices Z X) Y := by
    intro hReach
    exact h ⟨hXY, hXZ, hYZ, hReach⟩
  rw [Finset.disjoint_left] at hReach
  push_neg at hReach
  obtain ⟨y, hyReach, hyY⟩ := hReach
  obtain ⟨x, hxX, p, hlen, hact, hhead, hlast⟩ :=
    (G.bbReachableVertices_iff_activePath X Z y).mp hyReach
  -- Every node of `p` is in the ancestral set `S := An(X ∪ Y ∪ Z)`.
  have hnodes := G.activePath_nodes_are_ancestors hxX hyY hact hhead hlast
  -- Endpoints avoid `Z`.
  have hxZ : x ∉ Z := Finset.disjoint_left.mp hXZ hxX
  have hyZ : y ∉ Z := Finset.disjoint_left.mp hYZ hyY
  -- Build the moral connection and contradict separation.
  have hconn : G.MoralConn (G.ancestralSet (X ∪ Y ∪ Z)) Z x y :=
    G.moralConn_of_activePath p.length le_rfl hact hlen hnodes hhead hlast hxZ hyZ
  exact fun hsep => hsep x hxX y hyY hconn

/-- **The moralization criterion.** For pairwise-disjoint `X, Y, Z`, `X` and `Y` are
d-separated by `Z` exactly when they are moral-separated: no moral path inside the ancestral
set `An(X ∪ Y ∪ Z)` connects them while avoiding `Z`. (Lauritzen–Dawid–Larsen–Speed.) -/
theorem dSep_iff_moralSep {X Y Z : Finset V}
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    G.dSep X Y Z ↔ G.MoralSep X Y Z := by
  constructor
  · -- `dSep → MoralSep` via Direction 2: a moral connection would build a d-connection.
    intro hdSep x hxX y hyY hconn
    have hxZ : x ∉ Z := Finset.disjoint_left.mp hXZ hxX
    obtain ⟨w, hwY, hwReach⟩ :=
      G.dconn_of_moralConn hXY hconn (Or.inl hxX) hxZ hyY
    exact (Finset.disjoint_left.mp hdSep.2.2.2 hwReach) hwY
  · -- `MoralSep → dSep` via the contrapositive Direction 1.
    intro hsep
    by_contra hdSep
    exact G.not_moralSep_of_not_dSep hXY hXZ hYZ hdSep hsep

end DAG

/-- **Moral adjacency is a skeleton + v-structure invariant.** Two DAGs with the same
skeleton and the same v-structures induce the same moral adjacency on any ground set: a
shielded pair is moral-adjacent via the shared skeleton edge, and an unshielded married pair
is exactly the apex of a shared immorality. -/
theorem moralAdj_congr {G₁ G₂ : DAG V} (hskel : SameSkeleton G₁ G₂)
    (himm : SameImmoralities G₁ G₂) (S : Finset V) (u v : V) :
    G₁.MoralAdj S u v ↔ G₂.MoralAdj S u v := by
  unfold DAG.MoralAdj
  by_cases hne : u = v
  · simp [hne]
  refine and_congr_right (fun _ => ?_)
  refine and_congr_right (fun hu => ?_)
  refine and_congr_right (fun hv => ?_)
  by_cases hUA : G₁.UAdj u v
  · simp only [hUA, (hskel u v).mp hUA, true_or]
  · have hUA₂ : ¬ G₂.UAdj u v := fun h => hUA ((hskel u v).mpr h)
    simp only [hUA, hUA₂, false_or]
    refine exists_congr (fun c => ?_)
    refine and_congr_right (fun _ => ?_)
    -- common child `u → c ← v` (with `u,v` non-adjacent, distinct) is an immorality.
    constructor
    · rintro ⟨huc, hvc⟩
      have him₁ : G₁.IsImmorality u c v := ⟨huc, hvc, hUA, hne⟩
      have him₂ : G₂.IsImmorality u c v := (himm u c v).mp him₁
      exact ⟨him₂.1, him₂.2.1⟩
    · rintro ⟨huc, hvc⟩
      have him₂ : G₂.IsImmorality u c v := ⟨huc, hvc, hUA₂, hne⟩
      have him₁ : G₁.IsImmorality u c v := (himm u c v).mpr him₂
      exact ⟨him₁.1, him₁.2.1⟩

/-- Moral steps agree across DAGs with the same skeleton and v-structures (same ground set,
same conditioning set). -/
theorem moralStep_congr {G₁ G₂ : DAG V} (hskel : SameSkeleton G₁ G₂)
    (himm : SameImmoralities G₁ G₂) (S Z : Finset V) (u v : V) :
    G₁.MoralStep S Z u v ↔ G₂.MoralStep S Z u v := by
  unfold DAG.MoralStep
  rw [moralAdj_congr hskel himm]

/-- Moral connectivity agrees across DAGs with the same skeleton and v-structures, **for a
fixed ground set** `S`. (The ancestral sets used by `MoralSep` still differ between the
graphs; that reconciliation is `moralSep_congr`.) -/
theorem moralConn_congr {G₁ G₂ : DAG V} (hskel : SameSkeleton G₁ G₂)
    (himm : SameImmoralities G₁ G₂) (S Z : Finset V) (u v : V) :
    G₁.MoralConn S Z u v ↔ G₂.MoralConn S Z u v := by
  unfold DAG.MoralConn
  constructor <;> intro h <;>
    refine Relation.ReflTransGen.mono (fun a b hab => ?_) h
  · exact (moralStep_congr hskel himm S Z a b).mp hab
  · exact (moralStep_congr hskel himm S Z a b).mpr hab

end Causalean
