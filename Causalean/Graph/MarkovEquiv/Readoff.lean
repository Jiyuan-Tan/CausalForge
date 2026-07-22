/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.MarkovEquiv.Defs
import Causalean.Graph.DSep.Ancestral

/-! # Markov equivalence — the easy direction (reading skeleton and v-structures off d-sep)

If two DAGs are Markov equivalent (declare the same d-separations) then they have the same
skeleton and the same v-structures. The point is that both the skeleton and the
v-structures are *determined* by the d-separation relation:

* **Skeleton.** Two distinct vertices are adjacent iff they cannot be d-separated by any set
  (`adjacent_iff_not_dSeparable`): an edge is an always-active path, and conversely two
  non-adjacent vertices are separated by the parents of the topologically later one.
* **V-structures.** For an unshielded triple `a — b — c` (with `a, c` non-adjacent), the
  middle vertex `b` is a collider `a → b ← c` iff `b` lies in *no* separating set of `a`
  and `c` (`immorality_iff_colliderSep`) — the rule the PC algorithm uses to orient
  colliders.

Both characterizations are phrased purely in terms of `dSep`, so Markov equivalence
transports them, giving `sameSkeleton_of_markovEquiv` and `sameImmoralities_of_markovEquiv`,
hence the easy direction `sameSkeleton_sameImmoralities_of_markovEquiv`.
-/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

/-- An edge makes its endpoints inseparable: if `a` and `b` are adjacent then no
conditioning set d-separates them, because the single edge `[a, b]` is an active path
regardless of the conditioning set. -/
theorem not_dSeparable_of_uAdj {a b : V} (h : G.UAdj a b) (Z : Finset V) :
    ¬ G.dSep {a} {b} Z := by
  intro hsep
  have hb : b ∈ G.bbReachableVertices Z {a} := by
    rw [G.bbReachableVertices_iff_activePath]
    refine ⟨a, Finset.mem_singleton_self a, [a, b], ?_, ⟨?_, ?_⟩, rfl, rfl⟩
    · simp
    · intro i hi
      have hi0 : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
      subst hi0
      exact h
    · intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      omega
  simp only [DAG.dSep] at hsep
  exact (Finset.disjoint_left.mp hsep.2.2.2 hb) (Finset.mem_singleton_self b)

/-- **Helper for the skeleton read-off.** If `x` is topologically *before* `y` and the two
are non-adjacent, then conditioning on the parents of `y` d-separates `x` from `y`. Every
active path from `x` to `y` ends with an edge incident to `y`; that edge cannot point *into*
`y` (the second-to-last vertex would then be a conditioned non-collider) nor *out of* `y` (the
second-to-last vertex would be a topological descendant of `y`, contradicting that all path
nodes are ancestors of `{x} ∪ {y} ∪ parents y`, all of which are `≤ y` in topological order). -/
private theorem dSep_parents_of_topoOrder_lt {x y : V}
    (hlt : G.topoOrder x < G.topoOrder y) (hxy : ¬ G.UAdj x y) :
    G.dSep {x} {y} (G.parents y) := by
  have hne : x ≠ y := by
    intro h
    subst h
    exact (Nat.lt_irrefl _) hlt
  -- Suppose not: then `y` is reachable from `{x}` given `parents y`. Subst eliminates the
  -- bound names `x, y`, leaving the source `s₀` and target `t` introduced by the witness.
  rw [DAG.dSep]
  refine ⟨Finset.disjoint_singleton.mpr hne,
    Finset.disjoint_singleton_left.mpr (fun hmem => hxy (Or.inl (G.mem_parents.mp hmem))),
    Finset.disjoint_singleton_left.mpr (fun hmem => G.irrefl y (G.mem_parents.mp hmem)),
    ?_⟩
  rw [Finset.disjoint_left]
  intro t hv hvy
  rw [Finset.mem_singleton] at hvy
  subst hvy
  -- Extract an active path `p` from `s₀` to `t` given `Z := parents t`.
  rw [G.bbReachableVertices_iff_activePath] at hv
  obtain ⟨s₀, hx', p, hlen, hact, hhead, hlast⟩ := hv
  rw [Finset.mem_singleton] at hx'
  subst hx'
  -- The path has length ≥ 3: a length-2 path `[s₀, t]` would force `UAdj s₀ t`.
  have hp_ne : p ≠ [] := by intro hnil; rw [hnil] at hlen; simp at hlen
  have hlast_get : p.get ⟨p.length - 1, by omega⟩ = t := by
    have h := List.getLast?_eq_some_getLast hp_ne
    rw [hlast] at h
    have hy_eq : p.getLast hp_ne = t := Option.some_inj.mp h.symm
    rw [← hy_eq]; exact (List.getLast_eq_getElem hp_ne).symm
  have hhead_get : p.get ⟨0, by omega⟩ = s₀ := by
    have h := List.head?_eq_some_head hp_ne
    rw [hhead] at h
    have hx_eq : p.head hp_ne = s₀ := Option.some_inj.mp h.symm
    rw [← hx_eq]; simp [List.head_eq_getElem hp_ne]
  have hlen3 : p.length ≥ 3 := by
    by_contra hlt2
    -- p.length = 2, so p = [s₀, t]; then UAdj s₀ t from the adjacency at index 0.
    have hp2 : p.length = 2 := by omega
    have hadj0 := hact.1 0 (by omega)
    have h1 : (⟨0 + 1, by omega⟩ : Fin p.length) = ⟨p.length - 1, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [h1] at hadj0
    rw [hlast_get] at hadj0
    rw [hhead_get] at hadj0
    exact hxy hadj0
  -- Name the second-to-last vertex `m` and the triple `(m', m, t)`.
  have hm_idx : p.length - 2 + 1 < p.length := by omega
  have hadj_my := hact.1 (p.length - 2) hm_idx
  have hm1_eq : (⟨p.length - 2 + 1, hm_idx⟩ : Fin p.length) = ⟨p.length - 1, by omega⟩ :=
    Fin.ext (by simp; omega)
  rw [hm1_eq, hlast_get] at hadj_my
  set m := p.get ⟨p.length - 2, by omega⟩ with hm_def
  -- `hadj_my : G.UAdj m t`. Split on the orientation of that last edge.
  rcases hadj_my with hmy | hym
  · -- Case `edge m t`: then `m ∈ parents t = Z`, but the active-path non-collider
    -- condition at the triple `(m', m, t)` forces `m ∉ Z`.
    have htri : p.length - 3 + 2 < p.length := by omega
    have hcoll := hact.2 (p.length - 3) htri
    simp only at hcoll
    have e1 : (⟨p.length - 3 + 1, by omega⟩ : Fin p.length) = ⟨p.length - 2, by omega⟩ :=
      Fin.ext (by simp; omega)
    have e2 : (⟨p.length - 3 + 2, htri⟩ : Fin p.length) = ⟨p.length - 1, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e1, e2, hlast_get] at hcoll
    -- The middle vertex is `m`. It is not a collider: `edge m t` rules out `edge t m`.
    set l := p.get ⟨p.length - 3, by omega⟩ with hl_def
    have hnotColl : ¬ G.IsCollider l m t := by
      rintro ⟨_, hym⟩; exact G.asymm hmy hym
    rw [if_neg hnotColl] at hcoll
    -- But `m ∈ parents t` since `edge m t`.
    exact hcoll (G.mem_parents.mpr hmy)
  · -- Case `edge t m`: then `m` is a child of `t`, hence `topoOrder m > topoOrder t`.
    have htop_m : G.topoOrder t < G.topoOrder m := G.topoOrder_lt t m hym
    -- But `m` lies on the active path, hence in `ancestralSet ({s₀} ∪ {t} ∪ parents t)`.
    have hm_mem : m ∈ p := by rw [hm_def]; exact List.get_mem _ _
    have hm_anc := G.activePath_nodes_are_ancestors
      (Finset.mem_singleton_self s₀) (Finset.mem_singleton_self t) hact hhead hlast m hm_mem
    -- Every member of `{s₀} ∪ {t} ∪ parents t` has `topoOrder ≤ topoOrder t`.
    have hS_le : ∀ s ∈ ({s₀} ∪ {t} ∪ G.parents t : Finset V),
        G.topoOrder s ≤ G.topoOrder t := by
      intro s hs
      simp only [Finset.mem_union, Finset.mem_singleton] at hs
      rcases hs with (hsx | hsy) | hsp
      · subst hsx; exact le_of_lt hlt
      · subst hsy; exact le_refl _
      · exact le_of_lt (G.topoOrder_lt s t (G.mem_parents.mp hsp))
    -- `m ∈ ancestralSet S`: either `m ∈ S` or `m` is a strict ancestor of some `s ∈ S`.
    rcases Finset.mem_union.mp hm_anc with hmS | hmAnc
    · -- `m ∈ S` ⇒ `topoOrder m ≤ topoOrder t`, contradicting `topoOrder t < topoOrder m`.
      have := hS_le m hmS; omega
    · -- `m` strict ancestor of some `s ∈ S` ⇒ `topoOrder m < topoOrder s ≤ topoOrder t`.
      simp only [ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmAnc
      obtain ⟨s, hsS, hms⟩ := hmAnc
      have h1 := G.isAncestor_topoOrder_lt hms
      have h2 := hS_le s hsS
      omega

/-- Two distinct non-adjacent vertices can always be d-separated: conditioning on the
parents of the topologically later vertex blocks every path between them. -/
theorem dSeparable_of_not_uAdj {a b : V} (hne : a ≠ b) (h : ¬ G.UAdj a b) :
    ∃ Z : Finset V, G.dSep {a} {b} Z := by
  -- Pick the topologically later endpoint; condition on its parents. The helper only needs
  -- `topoOrder (earlier) < topoOrder (later)`, so `<` in either direction discharges the case.
  have htop_ne : G.topoOrder a ≠ G.topoOrder b := fun htop => hne (G.topoOrder_injective htop)
  rcases lt_or_gt_of_ne htop_ne with hlt | hlt
  · -- `a` no later than `b`: separate by `parents b`, already in the right orientation.
    exact ⟨G.parents b, G.dSep_parents_of_topoOrder_lt hlt h⟩
  · -- `b` no later than `a`: separate by `parents a`, then flip with `dSep_symm`.
    have hba : ¬ G.UAdj b a := fun h' => h (G.UAdj_symm h')
    exact ⟨G.parents a, G.dSep_symm _ _ _ (G.dSep_parents_of_topoOrder_lt hlt hba)⟩

/-- **Skeleton read-off.** Two distinct vertices are adjacent iff they cannot be d-separated
by any conditioning set. -/
theorem adjacent_iff_not_dSeparable {a b : V} (hne : a ≠ b) :
    G.UAdj a b ↔ ¬ ∃ Z : Finset V, G.dSep {a} {b} Z := by
  constructor
  · intro h ⟨Z, hZ⟩
    exact G.not_dSeparable_of_uAdj h Z hZ
  · intro h
    by_contra hadj
    exact h (G.dSeparable_of_not_uAdj hne hadj)

/-- **Helper for the collider read-off (non-collider case).** On an unshielded triple `x — b
— y` whose ends satisfy `topoOrder x ≤ topoOrder y`, if `b` is *not* a collider then `b` is
a parent of the topologically-later end `y`. Indeed the non-collider has an outgoing edge `b
→ x` or `b → y`; in the former case `b` precedes `x` hence `y`, so the adjacency `b — y`
cannot point into `b` (that would make `b` later than `y`), forcing `b → y`. -/
private theorem edge_to_later_of_nonCollider {x y b : V}
    (hxy_le : G.topoOrder x ≤ G.topoOrder y)
    (hxb : G.UAdj x b) (hyb : G.UAdj y b) (hnc : ¬ G.IsCollider x b y) :
    G.edge b y := by
  have hby : G.UAdj b y := G.UAdj_symm hyb
  rcases G.nonCollider_has_outgoing hxb hby hnc with hbx | hby'
  · -- `edge b x`: then `topoOrder b < topoOrder x ≤ topoOrder y`. The adjacency `y — b`
    -- cannot be `edge y b` (that gives `topoOrder y < topoOrder b`), so it is `edge b y`.
    have htb_x : G.topoOrder b < G.topoOrder x := G.topoOrder_lt b x hbx
    rcases hyb with hyb_e | hby_e
    · exact absurd (G.topoOrder_lt y b hyb_e) (by omega)
    · exact hby_e
  · exact hby'

/-- **Collider read-off.** For an unshielded triple `a — b — c` (with `a, c` non-adjacent
and distinct), the middle vertex `b` is a collider `a → b ← c` — equivalently `a → b ←
c` is a v-structure — iff `b` belongs to no set that d-separates `a` and `c`. -/
theorem immorality_iff_colliderSep {a b c : V}
    (hab : G.UAdj a b) (hcb : G.UAdj c b) (hac : ¬ G.UAdj a c) (hne : a ≠ c) :
    G.IsImmorality a b c ↔ ∀ Z : Finset V, b ∈ Z → ¬ G.dSep {a} {c} Z := by
  constructor
  · -- Forward. From the immorality, `(a, b, c)` is a collider; the length-3 path `[a, b, c]`
    -- is active given any `Z ∋ b` (the collider `b` is activated since `b ∈ Z ⊆ ancestralSet Z`),
    -- so `c` is reachable from `{a}`, contradicting d-separation.
    rintro ⟨heab, hecb, _, _⟩ Z hbZ hsep
    have hcoll : G.IsCollider a b c := ⟨heab, hecb⟩
    have hcReach : c ∈ G.bbReachableVertices Z {a} := by
      rw [G.bbReachableVertices_iff_activePath]
      refine ⟨a, Finset.mem_singleton_self a, [a, b, c], by simp, ⟨?_, ?_⟩, rfl, rfl⟩
      · -- Adjacency along `[a, b, c]`.
        intro i hi
        match i, hi with
        | 0, _ => exact hab
        | 1, _ => exact Or.inr hecb
      · -- The single interior triple `(a, b, c)` is the collider `b`, activated by `b ∈ Z`.
        intro i hi
        have hi0 : i = 0 := by
          simp only [List.length_cons, List.length_nil] at hi; omega
        subst hi0
        simp only [List.get]
        have hbAnc : b ∈ G.bbZAncestors Z := by
          unfold bbZAncestors; exact G.subset_ancestralSet Z hbZ
        rw [if_pos hcoll]
        exact hbAnc
    simp only [DAG.dSep] at hsep
    exact (Finset.disjoint_left.mp hsep.2.2.2 hcReach) (Finset.mem_singleton_self c)
  · -- Backward. Suppose `b` is in no separator of `a, c`. We must show `IsImmorality a b c`,
    -- i.e. `edge a b ∧ edge c b` (the remaining conjuncts are `hac`, `hne`). By contradiction:
    -- if `b` is not the collider `a → b ← c`, then `b` is a non-collider, hence a parent of
    -- the topologically-later of `a, c`; so `parents (later)` separates `a` from `c` *and*
    -- contains `b`, contradicting the hypothesis.
    intro H
    refine ⟨?_, ?_, hac, hne⟩ <;>
    · by_contra hcontra
      -- Reduce both subgoals to: `¬ (edge a b ∧ edge c b)`, i.e. `¬ IsCollider a b c`.
      have hnc : ¬ G.IsCollider a b c := by
        rintro ⟨h1, h2⟩
        first
          | exact hcontra h1
          | exact hcontra h2
      -- Build a separator `Z ∋ b` with `dSep {a} {c} Z`, contradicting `H`.
      have htop_ne : G.topoOrder a ≠ G.topoOrder c :=
        fun htop => hne (G.topoOrder_injective htop)
      rcases lt_or_gt_of_ne htop_ne with hlt | hlt
      · -- `a` no later than `c`: separator `parents c`; `b → c` makes `b ∈ parents c`.
        have heby : G.edge b c := G.edge_to_later_of_nonCollider (le_of_lt hlt) hab hcb hnc
        have hsep : G.dSep {a} {c} (G.parents c) :=
          G.dSep_parents_of_topoOrder_lt hlt hac
        exact H (G.parents c) (G.mem_parents.mpr heby) hsep
      · -- `c` no later than `a`: separator `parents a`; `b → a` makes `b ∈ parents a`.
        have hac' : ¬ G.UAdj c a := fun h' => hac (G.UAdj_symm h')
        have hnc' : ¬ G.IsCollider c b a := by
          rintro ⟨h1, h2⟩; exact hnc ⟨h2, h1⟩
        have heby : G.edge b a := G.edge_to_later_of_nonCollider (le_of_lt hlt) hcb hab hnc'
        have hsep : G.dSep {a} {c} (G.parents a) :=
          G.dSep_symm _ _ _ (G.dSep_parents_of_topoOrder_lt hlt hac')
        exact H (G.parents a) (G.mem_parents.mpr heby) hsep

/-- No self-loops in a DAG. -/
theorem not_edge_self (a : V) : ¬ G.edge a a :=
  fun he => G.isAncestor_irrefl a (DAG.isAncestor.edge he)

/-- No self-adjacency in a DAG. -/
theorem not_uAdj_self (a : V) : ¬ G.UAdj a a :=
  fun h => h.elim (G.not_edge_self a) (G.not_edge_self a)

/-- **Disjoint skeleton read-off witness.** Two distinct non-adjacent vertices are
d-separated by a conditioning set disjoint from both endpoints (the parents of the
topologically later one, which contain neither `a` nor `b`). -/
theorem dSeparable_disjoint_of_not_uAdj {a b : V} (hne : a ≠ b) (h : ¬ G.UAdj a b) :
    ∃ Z : Finset V, a ∉ Z ∧ b ∉ Z ∧ G.dSep {a} {b} Z := by
  have htop_ne : G.topoOrder a ≠ G.topoOrder b := fun htop => hne (G.topoOrder_injective htop)
  rcases lt_or_gt_of_ne htop_ne with hlt | hlt
  · refine ⟨G.parents b, fun hmem => h (Or.inl (G.mem_parents.mp hmem)),
      fun hmem => G.not_edge_self b (G.mem_parents.mp hmem),
      G.dSep_parents_of_topoOrder_lt hlt h⟩
  · have hba : ¬ G.UAdj b a := fun h' => h (G.UAdj_symm h')
    refine ⟨G.parents a, fun hmem => G.not_edge_self a (G.mem_parents.mp hmem),
      fun hmem => h (Or.inr (G.mem_parents.mp hmem)),
      G.dSep_symm _ _ _ (G.dSep_parents_of_topoOrder_lt hlt hba)⟩

/-- **Disjoint collider read-off.** For an unshielded triple `a — b — c`, `b` is the
collider `a → b ← c` iff every separator of `a, c` that contains `b` and excludes `a, c`
fails to d-separate — equivalently, `b` lies in no such separator. (The endpoint-disjoint
form used to transport immoralities across Markov-equivalent graphs.) -/
theorem immorality_iff_colliderSep_disjoint {a b c : V}
    (hab : G.UAdj a b) (hcb : G.UAdj c b) (hac : ¬ G.UAdj a c) (hne : a ≠ c) :
    G.IsImmorality a b c ↔ ∀ Z : Finset V, b ∈ Z → a ∉ Z → c ∉ Z → ¬ G.dSep {a} {c} Z := by
  constructor
  · intro him Z hbZ _ _
    exact (G.immorality_iff_colliderSep hab hcb hac hne).mp him Z hbZ
  · intro H
    refine ⟨?_, ?_, hac, hne⟩ <;>
    · by_contra hcontra
      have hnc : ¬ G.IsCollider a b c := by
        rintro ⟨h1, h2⟩; first | exact hcontra h1 | exact hcontra h2
      have htop_ne : G.topoOrder a ≠ G.topoOrder c :=
        fun htop => hne (G.topoOrder_injective htop)
      rcases lt_or_gt_of_ne htop_ne with hlt | hlt
      · have heby : G.edge b c := G.edge_to_later_of_nonCollider (le_of_lt hlt) hab hcb hnc
        exact H (G.parents c) (G.mem_parents.mpr heby)
          (fun hmem => hac (Or.inl (G.mem_parents.mp hmem)))
          (fun hmem => G.not_edge_self c (G.mem_parents.mp hmem))
          (G.dSep_parents_of_topoOrder_lt hlt hac)
      · have hac' : ¬ G.UAdj c a := fun h' => hac (G.UAdj_symm h')
        have hnc' : ¬ G.IsCollider c b a := by rintro ⟨h1, h2⟩; exact hnc ⟨h2, h1⟩
        have heby : G.edge b a := G.edge_to_later_of_nonCollider (le_of_lt hlt) hcb hab hnc'
        exact H (G.parents a) (G.mem_parents.mpr heby)
          (fun hmem => G.not_edge_self a (G.mem_parents.mp hmem))
          (fun hmem => hac (Or.inr (G.mem_parents.mp hmem)))
          (G.dSep_symm _ _ _ (G.dSep_parents_of_topoOrder_lt hlt hac'))

end DAG

/-- **Markov equivalence ⇒ same skeleton.** -/
theorem sameSkeleton_of_markovEquiv {G₁ G₂ : DAG V} (h : MarkovEquiv G₁ G₂) :
    SameSkeleton G₁ G₂ := by
  -- One-directional transfer: a disjoint separator of a non-adjacent pair transports.
  have key : ∀ {Ga Gb : DAG V}, MarkovEquiv Ga Gb → ∀ a b, a ≠ b →
      ¬ Ga.UAdj a b → ¬ Gb.UAdj a b := by
    intro Ga Gb hab a b hne hna hUAdj
    obtain ⟨Z, haZ, hbZ, hsep⟩ := Ga.dSeparable_disjoint_of_not_uAdj hne hna
    exact Gb.not_dSeparable_of_uAdj hUAdj Z
      ((hab {a} {b} Z (Finset.disjoint_singleton.mpr hne)
        (Finset.disjoint_singleton_left.mpr haZ)
        (Finset.disjoint_singleton_left.mpr hbZ)).mp hsep)
  intro a b
  by_cases hne : a = b
  · subst hne; exact iff_of_false (G₁.not_uAdj_self a) (G₂.not_uAdj_self a)
  · constructor
    · intro h1; by_contra h2; exact key h.symm a b hne h2 h1
    · intro h1; by_contra h2; exact key h a b hne h2 h1

/-- **Markov equivalence ⇒ same v-structures.** -/
theorem sameImmoralities_of_markovEquiv {G₁ G₂ : DAG V} (h : MarkovEquiv G₁ G₂) :
    SameImmoralities G₁ G₂ := by
  have hskel : SameSkeleton G₁ G₂ := sameSkeleton_of_markovEquiv h
  intro a b c
  -- Dispose of the cases where the triple is not unshielded; then use the collider read-off.
  by_cases hne : a = c
  · exact iff_of_false (fun him => him.2.2.2 hne) (fun him => him.2.2.2 hne)
  · by_cases hac : G₁.UAdj a c
    · have hac₂ : G₂.UAdj a c := (hskel a c).mp hac
      exact iff_of_false (fun him => him.2.2.1 hac) (fun him => him.2.2.1 hac₂)
    · have hac₂ : ¬ G₂.UAdj a c := fun h' => hac ((hskel a c).mpr h')
      by_cases hab : G₁.UAdj a b
      · by_cases hcb : G₁.UAdj c b
        · -- the unshielded triple case in both graphs
          have hab₂ : G₂.UAdj a b := (hskel a b).mp hab
          have hcb₂ : G₂.UAdj c b := (hskel c b).mp hcb
          rw [G₁.immorality_iff_colliderSep_disjoint hab hcb hac hne,
              G₂.immorality_iff_colliderSep_disjoint hab₂ hcb₂ hac₂ hne]
          refine forall_congr' (fun Z => ?_)
          refine imp_congr_right (fun _ => ?_)
          refine imp_congr_right (fun haZ => ?_)
          refine imp_congr_right (fun hcZ => ?_)
          exact not_congr (h {a} {c} Z
            (Finset.disjoint_singleton.mpr hne)
            (Finset.disjoint_singleton_left.mpr haZ)
            (Finset.disjoint_singleton_left.mpr hcZ))
        · -- c, b non-adjacent in both: both sides false (needs `edge c b`, hence `UAdj c b`)
          have hcb₂ : ¬ G₂.UAdj c b := fun h' => hcb ((hskel c b).mpr h')
          exact iff_of_false (fun him => hcb (Or.inl him.2.1))
            (fun him => hcb₂ (Or.inl him.2.1))
      · -- a, b non-adjacent in both: both sides false (needs `edge a b`, hence `UAdj a b`)
        have hab₂ : ¬ G₂.UAdj a b := fun h' => hab ((hskel a b).mpr h')
        exact iff_of_false (fun him => hab (Or.inl him.1))
          (fun him => hab₂ (Or.inl him.1))

/-- **Easy direction of Verma–Pearl.** Markov-equivalent DAGs share a skeleton and the same
v-structures. -/
theorem sameSkeleton_sameImmoralities_of_markovEquiv {G₁ G₂ : DAG V}
    (h : MarkovEquiv G₁ G₂) : SameSkeleton G₁ G₂ ∧ SameImmoralities G₁ G₂ :=
  ⟨sameSkeleton_of_markovEquiv h, sameImmoralities_of_markovEquiv h⟩

end Causalean
