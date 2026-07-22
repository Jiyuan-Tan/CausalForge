/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.AcyclicConstruct
import Causalean.Graph.MarkovEquiv.Defs

/-! # Covered-edge reversal (the Andersson–Madigan–Perlman route)

This file develops the **covered-edge reversal** route to the hard direction of Verma–Pearl,
following Andersson, Madigan and Perlman (1997), *A characterization of Markov equivalence
classes for acyclic digraphs*, Appendix B. The route proves the hard direction through
covered-edge reversals rather than through moralization.

A directed edge `a → b` is **covered** when `a` and `b` have the same parents apart from the
edge itself (`pa(a) = pa(b) \ {a}`); equivalently every other vertex is a parent of `a` iff
it is a parent of `b`. The three pillars are:

* **Reversibility** (AMP Lemma 3.1): a covered edge can be reversed and the result is still
  an acyclic digraph with the same skeleton and the same immoralities (`flipEdge_*`).
* **Per-step invariance**: reversing one covered edge preserves all d-separations, hence
  Markov equivalence (`markovEquiv_flipEdge`). This is the analytic core.
* **Decomposition** (AMP Lemma 3.2): two ADGs with the same skeleton and same immoralities
  are connected by a finite sequence of single covered-edge reversals
  (`exists_covered_reversed_edge` + the assembly).

The flipped graph is materialised with `DAG.ofAcyclic` (`AcyclicConstruct.lean`).
-/

namespace Causalean

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : DAG V)

/-- A directed edge `a → b` is **covered** when `a` and `b` share all parents apart from the
edge `a → b` itself: every vertex `c ≠ a` is a parent of `a` iff it is a parent of `b`. Then
`pa(a) = pa(b) \ {a}`. Covered edges are exactly the reversible (unprotected) ones. -/
def IsCoveredEdge (a b : V) : Prop :=
  G.edge a b ∧ ∀ c, c ≠ a → (G.edge c a ↔ G.edge c b)

/-- The edge relation of `G` with the single edge `a → b` deleted. -/
def flipMinus (a b : V) : V → V → Prop :=
  fun u w => G.edge u w ∧ ¬ (u = a ∧ w = b)

/-- The edge relation of `G` with the single edge `a → b` reversed to `b → a`. -/
def flipRel (a b : V) : V → V → Prop :=
  fun u w => G.flipMinus a b u w ∨ (u = b ∧ w = a)

variable {G}

/-- A `flipMinus`-edge is in particular a `G`-edge. -/
theorem flipMinus_le {a b u w : V} (h : G.flipMinus a b u w) : G.edge u w := h.1

/-- A directed `flipMinus`-path strictly increases the topological order. -/
theorem topoOrder_lt_of_flipMinus_transGen {a b u w : V}
    (h : Relation.TransGen (G.flipMinus a b) u w) : G.topoOrder u < G.topoOrder w := by
  induction h with
  | single he => exact G.topoOrder_lt _ _ he.1
  | tail _ he ih => exact lt_trans ih (G.topoOrder_lt _ _ he.1)

/-- A covered edge is genuinely an edge `a → b`, so `a ≠ b`. -/
theorem IsCoveredEdge.ne {a b : V} (h : G.IsCoveredEdge a b) : a ≠ b := by
  rintro rfl; exact G.irrefl _ h.1

/-- **Reversing a covered edge keeps the graph acyclic.** The transitive closure of the
flipped relation is irreflexive. Key step (AMP Lemma 3.1): a directed `G`-path `a ⇝ b` of
length ≥ 2 would end at a parent `c ≠ a` of `b`, hence (covered) a parent of `a`, closing a
`G`-cycle; so no such detour exists and the single reversal introduces no cycle. -/
theorem flipRel_acyclic {a b : V} (hcov : G.IsCoveredEdge a b) :
    ∀ v, ¬ Relation.TransGen (G.flipRel a b) v v := by
  -- last-step destructor for a transitive-closure path
  have transGen_last : ∀ {z : V}, Relation.TransGen (G.flipMinus a b) a z →
      G.flipMinus a b a z ∨
        ∃ c, Relation.TransGen (G.flipMinus a b) a c ∧ G.flipMinus a b c z := by
    intro z h
    induction h with
    | single h => exact Or.inl h
    | tail h1 h2 _ => exact Or.inr ⟨_, h1, h2⟩
  -- No `flipMinus`-detour from `a` to `b`: the last vertex `c` of such a path is a parent of
  -- `b` other than `a`, hence (covered) a parent of `a`, closing a `G`-cycle.
  have hnodetour : ¬ Relation.TransGen (G.flipMinus a b) a b := by
    intro h
    rcases transGen_last h with hab | ⟨c, hac, hcb⟩
    · exact hab.2 ⟨rfl, rfl⟩
    · have hca' : c ≠ a := fun hc => hcb.2 ⟨hc, rfl⟩
      have hca : G.edge c a := (hcov.2 c hca').mpr hcb.1
      have l1 : G.topoOrder a < G.topoOrder c := topoOrder_lt_of_flipMinus_transGen hac
      have l2 : G.topoOrder c < G.topoOrder a := G.topoOrder_lt _ _ hca
      omega
  -- Any flipped-walk either avoids `b → a` (so it is a `flipMinus`-walk) or it splits as
  -- `x ⇝ b` (before the first `b → a`) and `a ⇝ y` (after), both `flipMinus`-reachable.
  have hP : ∀ {x y}, Relation.TransGen (G.flipRel a b) x y →
      Relation.TransGen (G.flipMinus a b) x y ∨
        (Relation.ReflTransGen (G.flipMinus a b) x b ∧
          Relation.ReflTransGen (G.flipMinus a b) a y) := by
    intro x y h
    induction h with
    | single hxy =>
      rcases hxy with h0 | ⟨hxb, hya⟩
      · exact Or.inl (Relation.TransGen.single h0)
      · subst hxb; subst hya
        exact Or.inr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | @tail c y _ hcy ih =>
      rcases hcy with h0 | ⟨hcb, hya⟩
      · rcases ih with hl | ⟨hr1, hr2⟩
        · exact Or.inl (hl.tail h0)
        · exact Or.inr ⟨hr1, hr2.tail h0⟩
      · subst hcb; subst hya
        rcases ih with hl | ⟨hr1, _hr2⟩
        · exact Or.inr ⟨hl.to_reflTransGen, Relation.ReflTransGen.refl⟩
        · exact Or.inr ⟨hr1, Relation.ReflTransGen.refl⟩
  intro v hv
  rcases hP hv with hl | ⟨hr1, hr2⟩
  · exact absurd (topoOrder_lt_of_flipMinus_transGen hl) (lt_irrefl _)
  · have hab : Relation.ReflTransGen (G.flipMinus a b) a b := hr2.trans hr1
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with heq | htr
    · exact hcov.ne heq.symm
    · exact hnodetour htr

/-- The directed acyclic graph obtained from `G` by reversing the covered edge `a → b`. -/
noncomputable def flipEdge {a b : V} (hcov : G.IsCoveredEdge a b) : DAG V :=
  DAG.ofAcyclic (G.flipRel a b) (flipRel_acyclic hcov)

/-- In the graph obtained by reversing a covered edge, the edges are exactly the old edges
except for deleting `a → b` and adding `b → a`. -/
@[simp] theorem flipEdge_edge {a b : V} (hcov : G.IsCoveredEdge a b) (u w : V) :
    (flipEdge hcov).edge u w ↔ (G.edge u w ∧ ¬ (u = a ∧ w = b)) ∨ (u = b ∧ w = a) := by
  rfl

/-- **Reversing a covered edge preserves the skeleton.** The undirected adjacency is
unchanged: only the orientation of the single edge `a — b` flips. -/
theorem flipEdge_sameSkeleton {a b : V} (hcov : G.IsCoveredEdge a b) :
    SameSkeleton G (flipEdge hcov) := by
  intro u w
  simp only [DAG.UAdj, flipEdge_edge]
  constructor
  · rintro (h | h)
    · by_cases hab : u = a ∧ w = b
      · obtain ⟨rfl, rfl⟩ := hab; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inl ⟨h, hab⟩)
    · by_cases hab : w = a ∧ u = b
      · obtain ⟨rfl, rfl⟩ := hab; exact Or.inl (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨h, hab⟩)
  · rintro ((⟨h, _⟩ | ⟨rfl, rfl⟩) | (⟨h, _⟩ | ⟨rfl, rfl⟩))
    · exact Or.inl h
    · exact Or.inr hcov.1
    · exact Or.inr h
    · exact Or.inl hcov.1

/-- **Reversing a covered edge preserves the immoralities.** Because `a` and `b` share all
other parents, no v-structure is created or destroyed by the single reversal. -/
theorem flipEdge_sameImmoralities {a b : V} (hcov : G.IsCoveredEdge a b) :
    SameImmoralities G (flipEdge hcov) := by
  have hU : ∀ x y, G.UAdj x y ↔ (flipEdge hcov).UAdj x y := flipEdge_sameSkeleton hcov
  intro p q r
  constructor
  · rintro ⟨hpq, hrq, hnadj, hpr⟩
    have hpq' : (flipEdge hcov).edge p q := by
      rw [flipEdge_edge]; left; refine ⟨hpq, ?_⟩
      rintro ⟨hpa, hqb⟩
      -- collider `a → b ← r`: covered forces `r → a`, contradicting non-adjacency
      rw [hpa] at hpr hnadj; rw [hqb] at hrq
      exact hnadj (Or.inr ((hcov.2 r (Ne.symm hpr)).mpr hrq))
    have hrq' : (flipEdge hcov).edge r q := by
      rw [flipEdge_edge]; left; refine ⟨hrq, ?_⟩
      rintro ⟨hra, hqb⟩
      -- collider `p → b ← a`: covered forces `p → a`, contradicting non-adjacency
      rw [hra] at hpr hnadj; rw [hqb] at hpq
      exact hnadj (Or.inl ((hcov.2 p hpr).mpr hpq))
    exact ⟨hpq', hrq', fun h => hnadj ((hU p r).mpr h), hpr⟩
  · rintro ⟨hpq, hrq, hnadj, hpr⟩
    rw [flipEdge_edge] at hpq hrq
    have hnadjG : ¬ G.UAdj p r := fun h => hnadj ((hU p r).mp h)
    have hpqG : G.edge p q := by
      rcases hpq with ⟨h, _⟩ | ⟨hpb, hqa⟩
      · exact h
      · exfalso
        rcases hrq with ⟨hra, _⟩ | ⟨hrb, _⟩
        · rw [hqa] at hra
          have hrne : r ≠ a := fun heq => G.irrefl _ (heq ▸ hra)
          apply hnadjG; rw [hpb]; exact Or.inr ((hcov.2 r hrne).mp hra)
        · exact hpr (hpb.trans hrb.symm)
    have hrqG : G.edge r q := by
      rcases hrq with ⟨h, _⟩ | ⟨hrb, hqa⟩
      · exact h
      · exfalso
        rcases hpq with ⟨hpa, _⟩ | ⟨hpb, _⟩
        · rw [hqa] at hpa
          have hpne : p ≠ a := fun heq => G.irrefl _ (heq ▸ hpa)
          apply hnadjG; rw [hrb]; exact Or.inl ((hcov.2 p hpne).mp hpa)
        · exact hpr (hpb.trans hrb.symm)
    exact ⟨hpqG, hrqG, hnadjG, hpr⟩

/-- **Bridge: failure of d-separation is exactly an active path.** For pairwise-disjoint
query sets, `X` and `Y` are *not* d-separated by `Z` iff there is an active path from `X` to
`Y` given `Z`. Assembled from `bbReachableVertices_iff_activePath`. Reduces the covered-flip
invariance to a pure active-path statement. -/
theorem not_dSep_iff_hasActivePath (H : DAG V) (X Y Z : Finset V)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    ¬ H.dSep X Y Z ↔ H.HasActivePath X Y Z := by
  unfold DAG.dSep DAG.HasActivePath
  constructor
  · intro hnot
    have hReach : ¬ Disjoint (H.bbReachableVertices Z X) Y := by
      intro hReach
      exact hnot ⟨hXY, hXZ, hYZ, hReach⟩
    rw [Finset.not_disjoint_iff] at hReach
    obtain ⟨v, hvR, hvY⟩ := hReach
    obtain ⟨x, hxX, p, hlen, hact, hhead, hlast⟩ :=
      (H.bbReachableVertices_iff_activePath X Z v).mp hvR
    exact ⟨p, hlen, hact, by rw [hhead]; exact Finset.mem_image_of_mem _ hxX,
      by rw [hlast]; exact Finset.mem_image_of_mem _ hvY⟩
  · rintro ⟨p, hlen, hact, hhead, hlast⟩ hsep
    obtain ⟨x, hxX, hx⟩ := Finset.mem_image.mp hhead
    obtain ⟨v, hvY, hv⟩ := Finset.mem_image.mp hlast
    have hvReach : v ∈ H.bbReachableVertices Z X := by
      rw [H.bbReachableVertices_iff_activePath]
      exact ⟨x, hxX, p, hlen, hact, by rw [hx], by rw [hv]⟩
    exact (Finset.disjoint_left.mp hsep.2.2.2 hvReach) hvY

/-- Equal directed-edge relations have equal ancestor relations. -/
private theorem isAncestor_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w) {u v : V} :
    G₁.isAncestor u v ↔ G₂.isAncestor u v := by
  constructor
  · intro h
    induction h with
    | edge h => exact isAncestor.edge ((he _ _).mp h)
    | trans _ h ih => exact isAncestor.trans ih ((he _ _).mp h)
  · intro h
    induction h with
    | edge h => exact isAncestor.edge ((he _ _).mpr h)
    | trans _ h ih => exact isAncestor.trans ih ((he _ _).mpr h)

/-- Equal directed-edge relations have equal Bayes-ball ancestor sets. -/
private theorem bbZAncestors_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w) (Z : Finset V) (v : V) :
    v ∈ G₁.bbZAncestors Z ↔ v ∈ G₂.bbZAncestors Z := by
  simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hv | ⟨w, hw, h⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨w, hw, (isAncestor_edge_congr he).mp h⟩
  · rintro (hv | ⟨w, hw, h⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨w, hw, (isAncestor_edge_congr he).mpr h⟩

/-- Equal directed-edge relations have equal undirected adjacencies. -/
private theorem uAdj_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w) {u v : V} :
    G₁.UAdj u v ↔ G₂.UAdj u v := by
  unfold UAdj
  exact or_congr (he u v) (he v u)

/-- Equal directed-edge relations have equal collider predicates. -/
private theorem isCollider_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w) {l m r : V} :
    G₁.IsCollider l m r ↔ G₂.IsCollider l m r := by
  unfold IsCollider
  exact and_congr (he l m) (he r m)

/-- Equal directed-edge relations preserve active paths, including collider activation sets. -/
private theorem isActivePath_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w)
    (Z : Finset V) (p : List V) :
    G₁.IsActivePath Z p ↔ G₂.IsActivePath Z p := by
  constructor
  · intro h
    obtain ⟨hadj, htri⟩ := h
    refine ⟨fun i hi => (uAdj_edge_congr he).mp (hadj i hi), fun i hi => ?_⟩
    let l := p.get ⟨i, by omega⟩
    let m := p.get ⟨i + 1, by omega⟩
    let r := p.get ⟨i + 2, hi⟩
    have hciff : G₁.IsCollider l m r ↔ G₂.IsCollider l m r := isCollider_edge_congr he
    have haiff : m ∈ G₁.bbZAncestors Z ↔ m ∈ G₂.bbZAncestors Z :=
      bbZAncestors_edge_congr he Z m
    have hval := htri i hi
    change (if G₁.IsCollider l m r then m ∈ G₁.bbZAncestors Z else m ∉ Z) at hval
    change (if G₂.IsCollider l m r then m ∈ G₂.bbZAncestors Z else m ∉ Z)
    by_cases hC : G₁.IsCollider l m r
    · rw [if_pos (hciff.mp hC), ← haiff]
      rwa [if_pos hC] at hval
    · have hC₂ : ¬ G₂.IsCollider l m r := fun h => hC (hciff.mpr h)
      rw [if_neg hC₂]
      rwa [if_neg hC] at hval
  · intro h
    obtain ⟨hadj, htri⟩ := h
    refine ⟨fun i hi => (uAdj_edge_congr he).mpr (hadj i hi), fun i hi => ?_⟩
    let l := p.get ⟨i, by omega⟩
    let m := p.get ⟨i + 1, by omega⟩
    let r := p.get ⟨i + 2, hi⟩
    have hciff : G₁.IsCollider l m r ↔ G₂.IsCollider l m r := isCollider_edge_congr he
    have haiff : m ∈ G₁.bbZAncestors Z ↔ m ∈ G₂.bbZAncestors Z :=
      bbZAncestors_edge_congr he Z m
    have hval := htri i hi
    change (if G₂.IsCollider l m r then m ∈ G₂.bbZAncestors Z else m ∉ Z) at hval
    change (if G₁.IsCollider l m r then m ∈ G₁.bbZAncestors Z else m ∉ Z)
    by_cases hC : G₂.IsCollider l m r
    · rw [if_pos (hciff.mpr hC), haiff]
      rwa [if_pos hC] at hval
    · have hC₁ : ¬ G₁.IsCollider l m r := fun h => hC (hciff.mp h)
      rw [if_neg hC₁]
      rwa [if_neg hC] at hval

/-- Equal directed-edge relations preserve existence of active paths. -/
theorem hasActivePath_edge_congr {G₁ G₂ : DAG V}
    (he : ∀ u w : V, G₁.edge u w ↔ G₂.edge u w) (X Y Z : Finset V) :
    G₁.HasActivePath X Y Z ↔ G₂.HasActivePath X Y Z := by
  constructor
  · rintro ⟨p, hlen, hact, hhead, hlast⟩
    exact ⟨p, hlen, (isActivePath_edge_congr he Z p).mp hact, hhead, hlast⟩
  · rintro ⟨p, hlen, hact, hhead, hlast⟩
    exact ⟨p, hlen, (isActivePath_edge_congr he Z p).mpr hact, hhead, hlast⟩

/-- In the flipped graph, the reversed edge `b → a` is covered. -/
theorem flipEdge_isCoveredEdge_back {a b : V} (hcov : G.IsCoveredEdge a b) :
    (flipEdge hcov).IsCoveredEdge b a := by
  constructor
  · rw [flipEdge_edge]
    exact Or.inr ⟨rfl, rfl⟩
  · intro c hcb
    by_cases hca : c = a
    · subst c
      rw [flipEdge_edge, flipEdge_edge]
      constructor
      · rintro (⟨_, hnot⟩ | ⟨hab, _⟩)
        · exact absurd ⟨rfl, rfl⟩ hnot
        · exact absurd hab hcov.ne
      · rintro (⟨haa, _⟩ | ⟨hab, _⟩)
        · exact absurd haa (G.irrefl a)
        · exact absurd hab hcov.ne
    · rw [flipEdge_edge, flipEdge_edge]
      constructor
      · rintro (⟨hcbG, _⟩ | ⟨hcb', _⟩)
        · left
          refine ⟨(hcov.2 c hca).mpr hcbG, ?_⟩
          rintro ⟨hca', _⟩
          exact hca hca'
        · exact absurd hcb' hcb
      · rintro (⟨hcaG, _⟩ | ⟨hcb', _⟩)
        · left
          refine ⟨(hcov.2 c hca).mp hcaG, ?_⟩
          rintro ⟨hca', _⟩
          exact hca hca'
        · exact absurd hcb' hcb

/-- Flipping the reversed covered edge restores the original edge relation. -/
theorem flipEdge_flipEdge_edge {a b : V} (hcov : G.IsCoveredEdge a b) :
    ∀ u w : V, (flipEdge (flipEdge_isCoveredEdge_back hcov)).edge u w ↔ G.edge u w := by
  intro u w
  rw [flipEdge_edge, flipEdge_edge]
  constructor
  · rintro (h | ⟨hub, hwa⟩)
    · rcases h with ⟨h, hnot⟩
      rcases h with ⟨hG, hnot_ab⟩ | ⟨hub, hwa⟩
      · exact hG
      · exact absurd ⟨hub, hwa⟩ hnot
    · subst hub; subst hwa
      exact hcov.1
  · intro hG
    by_cases hab : u = a ∧ w = b
    · obtain ⟨rfl, rfl⟩ := hab
      exact Or.inr ⟨rfl, rfl⟩
    · left
      refine ⟨Or.inl ⟨hG, hab⟩, ?_⟩
      rintro ⟨hub, hwa⟩
      subst hub; subst hwa
      exact G.asymm hcov.1 hG

/-- Last-step decomposition for strict directed ancestry. -/
private theorem isAncestor_last {H : DAG V} {u v : V} (h : H.isAncestor u v) :
    H.edge u v ∨ ∃ w, H.isAncestor u w ∧ H.edge w v := by
  induction h with
  | edge he => exact Or.inl he
  | trans h₁ he _ => exact Or.inr ⟨_, h₁, he⟩

/-- Any flipped ancestor of `a`, except `b` itself, can be rerouted to an ancestor of `b`. -/
private theorem isAncestor_flip_to_b {a b v : V} (hcov : G.IsCoveredEdge a b)
    (hvb : v ≠ b) :
    (flipEdge hcov).isAncestor v a → (flipEdge hcov).isAncestor v b := by
  intro h
  rcases isAncestor_last h with hdir | ⟨q, hvq, hqa⟩
  · rw [flipEdge_edge] at hdir
    rcases hdir with ⟨hvaG, _⟩ | ⟨hvb', _⟩
    · have hva : v ≠ a := fun hv => G.irrefl a (hv ▸ hvaG)
      have hvbG : G.edge v b := (hcov.2 v hva).mp hvaG
      exact isAncestor.edge (by
        rw [flipEdge_edge]
        exact Or.inl ⟨hvbG, fun hab => hva hab.1⟩)
    · exact absurd hvb' hvb
  · rw [flipEdge_edge] at hqa
    rcases hqa with ⟨hqaG, _⟩ | ⟨hqb, _⟩
    · have hqne : q ≠ a := fun hq => G.irrefl a (hq ▸ hqaG)
      have hqbG : G.edge q b := (hcov.2 q hqne).mp hqaG
      exact isAncestor.trans hvq (by
        rw [flipEdge_edge]
        exact Or.inl ⟨hqbG, fun hab => hqne hab.1⟩)
    · subst hqb
      exact hvq

/-- A `G`-edge either survives in the flipped graph or is exactly the deleted edge. -/
private theorem flipEdge_edge_or_deleted {a b u w : V} (hcov : G.IsCoveredEdge a b)
    (he : G.edge u w) : (flipEdge hcov).edge u w ∨ (u = a ∧ w = b) := by
  by_cases hab : u = a ∧ w = b
  · exact Or.inr hab
  · exact Or.inl (by
      rw [flipEdge_edge]
      exact Or.inl ⟨he, hab⟩)

/-- A `G`-ancestor path whose start is not `a` survives the covered flip, rerouting only
the deleted `a → b` step through the shared parents. -/
private theorem isAncestor_flip {a b s z : V} (hcov : G.IsCoveredEdge a b)
    (hsa : s ≠ a) (h : G.isAncestor s z) :
    (flipEdge hcov).isAncestor s z := by
  induction h with
  | edge he =>
      rcases flipEdge_edge_or_deleted hcov he with hF | hdel
      · exact isAncestor.edge hF
      · exact absurd hdel.1 hsa
  | trans h₁ he ih =>
      rcases flipEdge_edge_or_deleted hcov he with hF | hdel
      · exact isAncestor.trans ih hF
      · have hsaAnc : G.isAncestor s a := by
          simpa [hdel.1] using h₁
        have ihA : (flipEdge hcov).isAncestor s a := by
          simpa [hdel.1] using ih
        have hsb : s ≠ b := by
          intro hsb
          have hba : G.topoOrder s < G.topoOrder a := G.isAncestor_topoOrder_lt hsaAnc
          have hab : G.topoOrder a < G.topoOrder b := G.topoOrder_lt _ _ hcov.1
          rw [hsb] at hba
          omega
        simpa [hdel.2] using isAncestor_flip_to_b hcov hsb ihA

/-- Away from `a`, membership in the Bayes-ball ancestor set is preserved by a covered flip. -/
private theorem bbZAncestors_flip_of_ne {a b v : V} (hcov : G.IsCoveredEdge a b)
    (Z : Finset V) (hva : v ≠ a) :
    v ∈ G.bbZAncestors Z → v ∈ (flipEdge hcov).bbZAncestors Z := by
  simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rintro (hvZ | ⟨z, hzZ, hvz⟩)
  · exact Or.inl hvZ
  · exact Or.inr ⟨z, hzZ, isAncestor_flip hcov hva hvz⟩

/-- The vertex `b` keeps its Bayes-ball ancestor-set membership after flipping `a → b`. -/
private theorem bbZAncestors_flip_of_b {a b : V} (hcov : G.IsCoveredEdge a b)
    (Z : Finset V) :
    b ∈ G.bbZAncestors Z → b ∈ (flipEdge hcov).bbZAncestors Z :=
  bbZAncestors_flip_of_ne hcov Z hcov.ne.symm

/-- If `a` reaches `Z` in `G` but not after the flip, that route used `a → b`, so `b` reaches
`Z`; hence `b` is activated in the flipped graph. -/
private theorem bbZAncestors_flip_of_lost {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (h1 : a ∈ G.bbZAncestors Z) (h2 : a ∉ (flipEdge hcov).bbZAncestors Z) :
    b ∈ (flipEdge hcov).bbZAncestors Z := by
  apply bbZAncestors_flip_of_b hcov Z
  simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and] at h1 ⊢
  have hmemflip : ∀ {w : V}, (∃ z ∈ Z, (flipEdge hcov).isAncestor w z) →
      w ∈ (flipEdge hcov).bbZAncestors Z := by
    intro w hw
    simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Or.inr hw
  have haZ : a ∉ Z := fun h => h2 (hmemflip ⟨a, h, isAncestor.edge (by
    rw [flipEdge_edge]; exact Or.inr ⟨rfl, rfl⟩)⟩ |> fun _ => by
    simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]; exact Or.inl h)
  rcases h1 with hZ | ⟨z, hzZ, haz⟩
  · exact absurd hZ haZ
  · rcases G.isAncestor_child haz with hedge | ⟨c, hac, hcz⟩
    · by_cases hzb : z = b
      · exact Or.inl (hzb ▸ hzZ)
      · exact absurd (hmemflip ⟨z, hzZ, isAncestor.edge (by
          rw [flipEdge_edge]; exact Or.inl ⟨hedge, fun h => hzb h.2⟩)⟩) h2
    · by_cases hcb : c = b
      · subst hcb; exact Or.inr ⟨z, hzZ, hcz⟩
      · have hca : c ≠ a := fun h => G.irrefl a (h ▸ hac)
        have hacF : (flipEdge hcov).edge a c := by
          rw [flipEdge_edge]; exact Or.inl ⟨hac, fun h => hcb h.2⟩
        exact absurd (hmemflip ⟨z, hzZ,
          (flipEdge hcov).isAncestor_trans (isAncestor.edge hacF)
            (isAncestor_flip hcov hca hcz)⟩) h2

/-- Away from `b`, Bayes-ball ancestor membership in the flipped graph transports back to `G`. -/
private theorem bbZAncestors_unflip_of_ne {a b v : V} (hcov : G.IsCoveredEdge a b)
    (Z : Finset V) (hvb : v ≠ b) :
    v ∈ (flipEdge hcov).bbZAncestors Z → v ∈ G.bbZAncestors Z := by
  have hback := flipEdge_isCoveredEdge_back hcov
  intro hv
  have hv₂ : v ∈ (flipEdge hback).bbZAncestors Z :=
    bbZAncestors_flip_of_ne (G := flipEdge hcov) hback Z hvb hv
  exact (bbZAncestors_edge_congr (flipEdge_flipEdge_edge hcov) Z v).mp hv₂

/-- Away from `a`, the covered flip leaves directed edges unchanged. -/
private theorem flipEdge_edge_iff_of_ne_a {a b u w : V} (hcov : G.IsCoveredEdge a b)
    (hua : u ≠ a) (hwa : w ≠ a) :
    (flipEdge hcov).edge u w ↔ G.edge u w := by
  rw [flipEdge_edge]
  constructor
  · rintro (⟨he, _⟩ | ⟨_, hwa'⟩)
    · exact he
    · exact absurd hwa' hwa
  · intro he
    exact Or.inl ⟨he, fun hdel => hua hdel.1⟩

/-- Away from `a`, the covered flip leaves collider status unchanged. -/
private theorem flipEdge_isCollider_iff_of_ne_a {a b l m r : V}
    (hcov : G.IsCoveredEdge a b) (hla : l ≠ a) (hma : m ≠ a) (hra : r ≠ a) :
    (flipEdge hcov).IsCollider l m r ↔ G.IsCollider l m r := by
  unfold IsCollider
  exact and_congr (flipEdge_edge_iff_of_ne_a hcov hla hma)
    (flipEdge_edge_iff_of_ne_a hcov hra hma)

/-- If an active path avoids `a`, the same list is active after flipping `a → b`. -/
private theorem isActivePath_flip_of_not_mem {a b : V} (hcov : G.IsCoveredEdge a b)
    {Z : Finset V} {p : List V} (hact : G.IsActivePath Z p) (hna : a ∉ p) :
    (flipEdge hcov).IsActivePath Z p := by
  obtain ⟨hadj, htri⟩ := hact
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · exact (flipEdge_sameSkeleton hcov _ _).mp (hadj i hi)
  · let l := p.get ⟨i, by omega⟩
    let m := p.get ⟨i + 1, by omega⟩
    let r := p.get ⟨i + 2, hi⟩
    have hla : l ≠ a := by
      intro h
      apply hna
      rw [← h]
      exact List.get_mem p ⟨i, by omega⟩
    have hma : m ≠ a := by
      intro h
      apply hna
      rw [← h]
      exact List.get_mem p ⟨i + 1, by omega⟩
    have hra : r ≠ a := by
      intro h
      apply hna
      rw [← h]
      exact List.get_mem p ⟨i + 2, hi⟩
    have hciff : (flipEdge hcov).IsCollider l m r ↔ G.IsCollider l m r :=
      flipEdge_isCollider_iff_of_ne_a hcov hla hma hra
    have hval := htri i hi
    change (if G.IsCollider l m r then m ∈ G.bbZAncestors Z else m ∉ Z) at hval
    change (if (flipEdge hcov).IsCollider l m r
      then m ∈ (flipEdge hcov).bbZAncestors Z else m ∉ Z)
    by_cases hC : G.IsCollider l m r
    · rw [if_pos ((hciff).mpr hC)]
      exact bbZAncestors_flip_of_ne hcov Z hma (by rwa [if_pos hC] at hval)
    · have hCF : ¬ (flipEdge hcov).IsCollider l m r := fun h => hC ((hciff).mp h)
      rw [if_neg hCF]
      rwa [if_neg hC] at hval

/-- Paths with no interior triple transfer across the covered flip by skeleton preservation. -/
private theorem isActivePath_flip_of_length_le_two {a b : V} (hcov : G.IsCoveredEdge a b)
    {Z : Finset V} {p : List V} (hact : G.IsActivePath Z p) (hlen : p.length ≤ 2) :
    (flipEdge hcov).IsActivePath Z p := by
  obtain ⟨hadj, _htri⟩ := hact
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · exact (flipEdge_sameSkeleton hcov _ _).mp (hadj i hi)
  · omega

/-- The path `p` with each interior **collider** occurrence of `a` whose activation is lost in
the flipped graph (`a ∉ (flipEdge).bbZAncestors Z`) replaced by `b`. Same length as `p`;
endpoints are never touched (they are not interior). -/
private noncomputable def swapPath {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (p : List V) : List V :=
  List.ofFn (fun i : Fin p.length =>
    if h : 1 ≤ i.val ∧ i.val + 1 < p.length then
      if p.get i = a ∧ a ∉ (flipEdge hcov).bbZAncestors Z ∧
          G.IsCollider (p.get ⟨i.val - 1, by have := i.isLt; omega⟩) (p.get i)
            (p.get ⟨i.val + 1, h.2⟩)
        then b else p.get i
    else p.get i)

@[simp] private theorem swapPath_length {a b : V} (hcov : G.IsCoveredEdge a b)
    (Z : Finset V) (p : List V) : (swapPath hcov Z p).length = p.length := by
  simp [swapPath]

/-- Each entry of `swapPath` is either the original vertex, or `b` at an interior collider
occurrence of `a` whose activation is lost. -/
private theorem swapPath_get_eq {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (p : List V) (i : ℕ) (hi : i < (swapPath hcov Z p).length) (hi' : i < p.length) :
    (swapPath hcov Z p).get ⟨i, hi⟩ = p.get ⟨i, hi'⟩ ∨
      ((swapPath hcov Z p).get ⟨i, hi⟩ = b ∧ p.get ⟨i, hi'⟩ = a ∧
        1 ≤ i ∧ ∃ (h2 : i + 1 < p.length),
          G.IsCollider (p.get ⟨i - 1, by omega⟩) (p.get ⟨i, hi'⟩) (p.get ⟨i + 1, h2⟩) ∧
          a ∉ (flipEdge hcov).bbZAncestors Z) := by
  simp only [swapPath, List.get_ofFn, Fin.cast_mk]
  split_ifs with h hc
  · exact Or.inr ⟨rfl, hc.1, h.1, h.2, hc.2.2, hc.2.1⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- When the swap predicate holds at `i`, the entry is `b`. -/
private theorem swapPath_get_b_of {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (p : List V) (i : ℕ) (hi : i < (swapPath hcov Z p).length) (hi' : i < p.length)
    (h1 : 1 ≤ i) (h2 : i + 1 < p.length) (ha : p.get ⟨i, hi'⟩ = a)
    (hanc : a ∉ (flipEdge hcov).bbZAncestors Z)
    (hcol : G.IsCollider (p.get ⟨i - 1, by omega⟩) (p.get ⟨i, hi'⟩) (p.get ⟨i + 1, h2⟩)) :
    (swapPath hcov Z p).get ⟨i, hi⟩ = b := by
  simp only [swapPath, List.get_ofFn, Fin.cast_mk]
  rw [dif_pos ⟨h1, h2⟩, if_pos ⟨ha, hanc, hcol⟩]

/-- An edge **into** a vertex `m ∉ {a, b}` is unaffected by the flip. -/
private theorem flipEdge_edge_into_iff {a b m : V} (hcov : G.IsCoveredEdge a b)
    (hma : m ≠ a) (hmb : m ≠ b) (u : V) :
    (flipEdge hcov).edge u m ↔ G.edge u m := by
  rw [flipEdge_edge]
  refine ⟨fun h => h.elim (·.1) (fun hh => absurd hh.2 hma),
    fun h => Or.inl ⟨h, fun hh => hmb hh.2⟩⟩

/-- The `(l, m, r)` configurations that the covered flip turns into an *un-repairable* block.
Each is an `a`/`b` adjacency whose far arrowhead either makes `a` an **inactive** collider after
the flip (clauses 1–2) or destroys the **active** collider at `b` (clauses 3–4). The two
backtracks `b — a — b` and `a — b — a` are special cases (the first via clause 1 with `r = b`,
the second via clause 4 with `l = a`, since `a → b`). `swapPath` cannot repair these locally;
the assembly removes them by dropping/excising one vertex before swapping. -/
private def FlipObstruct (a b l m r : V) : Prop :=
  (m = a ∧ l = b ∧ (G.edge r a ∨ r = b)) ∨
  (m = a ∧ r = b ∧ (G.edge l a ∨ l = b)) ∨
  (m = b ∧ l = a ∧ G.edge r b) ∨
  (m = b ∧ r = a ∧ G.edge l b)

/-- Ancestor-set membership moves backwards along a directed edge. -/
private theorem bbZAncestors_of_edge {Z : Finset V} {u w : V}
    (huw : G.edge u w) (hw : w ∈ G.bbZAncestors Z) :
    u ∈ G.bbZAncestors Z := by
  simp only [bbZAncestors, ancestralSet, ancestorsSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  rcases hw with hwZ | ⟨z, hzZ, hwz⟩
  · exact Or.inr ⟨w, hwZ, isAncestor.edge huw⟩
  · exact Or.inr ⟨z, hzZ, G.isAncestor_trans (isAncestor.edge huw) hwz⟩

/-- The list obtained by skipping one interior index of `p`.  It is defined by `ofFn`
so its indexing equations are definitional after `simp`. -/
private def skipOne (p : List V) (k : ℕ) : List V :=
  List.ofFn (fun i : Fin (p.length - 1) =>
    if h : i.val < k then
      p.get ⟨i.val, by omega⟩
    else
      p.get ⟨i.val + 1, by omega⟩)

omit [DecidableEq V] [Fintype V] in
@[simp] private theorem skipOne_length (p : List V) (k : ℕ) :
    (skipOne p k).length = p.length - 1 := by
  simp [skipOne]

/-- The list obtained by skipping two consecutive interior indices of `p`. -/
private def skipTwo (p : List V) (k : ℕ) : List V :=
  List.ofFn (fun i : Fin (p.length - 2) =>
    if h : i.val < k then
      p.get ⟨i.val, by omega⟩
    else
      p.get ⟨i.val + 2, by omega⟩)

omit [DecidableEq V] [Fintype V] in
@[simp] private theorem skipTwo_length (p : List V) (k : ℕ) :
    (skipTwo p k).length = p.length - 2 := by
  simp [skipTwo]

omit [DecidableEq V] [Fintype V] in
private theorem skipOne_head? {p : List V} {k : ℕ} (hk0 : 0 < k)
    (hk : k < p.length) :
    (skipOne p k).head? = p.head? := by
  rw [List.head?_eq_getElem?, List.head?_eq_getElem?]
  have hp0 : 0 < p.length := by omega
  have hq0 : 0 < (skipOne p k).length := by simp [skipOne_length]; omega
  rw [List.getElem?_eq_getElem hq0, List.getElem?_eq_getElem hp0]
  simp [skipOne, hk0]

omit [DecidableEq V] [Fintype V] in
private theorem skipOne_getLast? {p : List V} {k : ℕ} (hk : k + 1 < p.length) :
    (skipOne p k).getLast? = p.getLast? := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, skipOne_length]
  have hp0 : 0 < p.length := by omega
  rw [List.getElem?_eq_getElem (by rw [skipOne_length]; omega),
    List.getElem?_eq_getElem (by omega)]
  have hnot : ¬ (p.length - 1 - 1 < k) := by omega
  simp [skipOne, hnot, show p.length - 1 - 1 + 1 = p.length - 1 by omega]

omit [DecidableEq V] [Fintype V] in
private theorem skipTwo_head? {p : List V} {k : ℕ} (hk0 : 0 < k)
    (hk : k + 1 < p.length) :
    (skipTwo p k).head? = p.head? := by
  rw [List.head?_eq_getElem?, List.head?_eq_getElem?]
  have hp0 : 0 < p.length := by omega
  have hq0 : 0 < (skipTwo p k).length := by simp [skipTwo_length]; omega
  rw [List.getElem?_eq_getElem hq0, List.getElem?_eq_getElem hp0]
  simp [skipTwo, hk0]

omit [DecidableEq V] [Fintype V] in
private theorem skipTwo_getLast? {p : List V} {k : ℕ} (hk0 : 0 < k)
    (hk : k + 1 < p.length)
    (hsame : p.get ⟨k - 1, by omega⟩ = p.get ⟨k + 1, hk⟩) :
    (skipTwo p k).getLast? = p.getLast? := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, skipTwo_length]
  have hp0 : 0 < p.length := by omega
  rw [List.getElem?_eq_getElem (by rw [skipTwo_length]; omega),
    List.getElem?_eq_getElem (by omega)]
  by_cases htail : k + 2 < p.length
  · have hnot : ¬ (p.length - 2 - 1 < k) := by omega
    simp [skipTwo, hnot, show p.length - 2 - 1 + 2 = p.length - 1 by omega]
  · have hk_last : k + 1 = p.length - 1 := by omega
    have hq_last : p.length - 2 - 1 = k - 1 := by omega
    have htrue : k - 1 < k := by omega
    simpa [skipTwo, hq_last, hk_last, htrue] using hsame

private theorem isActivePath_skipOne {Z : Finset V} {p : List V} {k : ℕ}
    (hact : G.IsActivePath Z p) (hk0 : 0 < k) (hk : k + 1 < p.length)
    (hadj_splice : G.UAdj (p.get ⟨k - 1, by omega⟩) (p.get ⟨k + 1, hk⟩))
    (hleft : ∀ (hk2 : 2 ≤ k),
      if G.IsCollider (p.get ⟨k - 2, by omega⟩) (p.get ⟨k - 1, by omega⟩)
          (p.get ⟨k + 1, hk⟩) then
        p.get ⟨k - 1, by omega⟩ ∈ G.bbZAncestors Z
      else
        p.get ⟨k - 1, by omega⟩ ∉ Z)
    (hright : ∀ (hkR : k + 2 < p.length),
      if G.IsCollider (p.get ⟨k - 1, by omega⟩) (p.get ⟨k + 1, by omega⟩)
          (p.get ⟨k + 2, hkR⟩) then
        p.get ⟨k + 1, by omega⟩ ∈ G.bbZAncestors Z
      else
        p.get ⟨k + 1, by omega⟩ ∉ Z) :
    G.IsActivePath Z (skipOne p k) := by
  obtain ⟨hadj, htri⟩ := hact
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · simp only [skipOne_length] at hi
    simp only [skipOne, List.get_ofFn]
    by_cases hi0 : i < k
    · by_cases hi1 : i + 1 < k
      · have h := hadj i (by omega)
        simpa [hi0, hi1] using h
      · have hik : i = k - 1 := by omega
        subst i
        have h0 : k - 1 < k := by omega
        have h1 : ¬ (k - 1 + 1 < k) := by omega
        simpa [h0, h1, show k - 1 + 1 + 1 = k + 1 by omega] using hadj_splice
    · have hi1 : ¬ (i + 1 < k) := by omega
      have h := hadj (i + 1) (by omega)
      simpa [hi0, hi1, Nat.add_assoc] using h
  · simp only [skipOne_length] at hi
    simp only [skipOne, List.get_ofFn]
    by_cases hi2 : i + 2 < k
    · have hi0 : i < k := by omega
      have hi1 : i + 1 < k := by omega
      have h := htri i (by omega)
      simpa [hi0, hi1, hi2] using h
    · by_cases hi1 : i + 1 < k
      · have hi0 : i < k := by omega
        have hik : i = k - 2 := by omega
        subst i
        have h0 : k - 2 < k := by omega
        have h1 : k - 2 + 1 < k := by omega
        have h2 : ¬ (k - 2 + 2 < k) := by omega
        have hmid : k - 1 < k := by omega
        simpa [h0, h1, h2, show k - 2 + 1 = k - 1 by omega,
          show k - 2 + 2 + 1 = k + 1 by omega, hmid] using hleft (by omega)
      · by_cases hi0 : i < k
        · have hik : i = k - 1 := by omega
          subst i
          have h0 : k - 1 < k := by omega
          have h1 : ¬ (k - 1 + 1 < k) := by omega
          have h2 : ¬ (k - 1 + 2 < k) := by omega
          have hrightNot : ¬ (k + 1 < k) := by omega
          simpa [h0, h1, h2, show k - 1 + 1 + 1 = k + 1 by omega,
            show k - 1 + 2 + 1 = k + 2 by omega, hrightNot] using hright (by omega)
        · have hi1' : ¬ (i + 1 < k) := by omega
          have hi2' : ¬ (i + 2 < k) := by omega
          have h := htri (i + 1) (by omega)
          simpa [hi0, hi1', hi2', Nat.add_assoc] using h

private theorem isActivePath_skipTwo {Z : Finset V} {p : List V} {k : ℕ}
    (hact : G.IsActivePath Z p) (hk0 : 0 < k) (hk : k + 1 < p.length)
    (hsame : p.get ⟨k - 1, by omega⟩ = p.get ⟨k + 1, hk⟩)
    (hsplice : ∀ (hk2 : 2 ≤ k) (hkR : k + 2 < p.length),
      if G.IsCollider (p.get ⟨k - 2, by omega⟩) (p.get ⟨k - 1, by omega⟩)
          (p.get ⟨k + 2, hkR⟩) then
        p.get ⟨k - 1, by omega⟩ ∈ G.bbZAncestors Z
      else
        p.get ⟨k - 1, by omega⟩ ∉ Z) :
    G.IsActivePath Z (skipTwo p k) := by
  obtain ⟨hadj, htri⟩ := hact
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · simp only [skipTwo_length] at hi
    simp only [skipTwo, List.get_ofFn]
    by_cases hi0 : i < k
    · by_cases hi1 : i + 1 < k
      · have h := hadj i (by omega)
        simpa [hi0, hi1] using h
      · have hik : i = k - 1 := by omega
        subst i
        have h0 : k - 1 < k := by omega
        have h1 : ¬ (k - 1 + 1 < k) := by omega
        have h := hadj (k + 1) (by omega)
        rw [← hsame] at h
        simpa [h0, h1, Nat.add_assoc, show k - 1 + 3 = k + 2 by omega] using h
    · have hi1 : ¬ (i + 1 < k) := by omega
      have h := hadj (i + 2) (by omega)
      simpa [hi0, hi1, Nat.add_assoc] using h
  · simp only [skipTwo_length] at hi
    simp only [skipTwo, List.get_ofFn]
    by_cases hi2 : i + 2 < k
    · have hi0 : i < k := by omega
      have hi1 : i + 1 < k := by omega
      have h := htri i (by omega)
      simpa [hi0, hi1, hi2] using h
    · by_cases hi1 : i + 1 < k
      · have hi0 : i < k := by omega
        have hik : i = k - 2 := by omega
        subst i
        have h0 : k - 2 < k := by omega
        have h1 : k - 2 + 1 < k := by omega
        have h2 : ¬ (k - 2 + 2 < k) := by omega
        have hmid : k - 1 < k := by omega
        simpa [h0, h1, h2, show k - 2 + 1 = k - 1 by omega,
          show k - 2 + 2 + 2 = k + 2 by omega, hmid] using hsplice (by omega) (by omega)
      · by_cases hi0 : i < k
        · have hik : i = k - 1 := by omega
          subst i
          have h0 : k - 1 < k := by omega
          have h1 : ¬ (k - 1 + 1 < k) := by omega
          have h2 : ¬ (k - 1 + 2 < k) := by omega
          have h := htri (k + 1) (by omega)
          rw [← hsame] at h
          simpa [h0, h1, h2, Nat.add_assoc, show k - 1 + 3 = k + 2 by omega,
            show k - 1 + 4 = k + 3 by omega] using h
        · have hi1' : ¬ (i + 1 < k) := by omega
          have hi2' : ¬ (i + 2 < k) := by omega
          have h := htri (i + 2) (by omega)
          simpa [hi0, hi1', hi2', Nat.add_assoc] using h

omit [DecidableEq V] [Fintype V] in
private theorem four_le_length_of_backtrack_endpoints_ne {p : List V} {j : ℕ}
    (hne : p.head? ≠ p.getLast?) (hj : j + 2 < p.length)
    (hback : p.get ⟨j, by omega⟩ = p.get ⟨j + 2, hj⟩) :
    4 ≤ p.length := by
  by_contra hlt
  have hlen : p.length = 3 := by omega
  have hj0 : j = 0 := by omega
  apply hne
  rw [List.head?_eq_getElem?, List.getLast?_eq_getElem?]
  rw [List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by omega)]
  congr 1
  simpa [hj0, hlen] using hback

/-- When no interior triple of `p` is flip-obstructing, `swapPath` is `flipEdge`-active. The
swap repairs exactly the collider-`a` positions whose activation is lost; genuine
fork-traversals of the covered edge are kept and stay active because `a` (resp. `b`) remains a
non-collider after the flip. This generalises the no-traversal case: a path with no `a — b`
adjacency at all trivially has no flip-obstructing triple. -/
private theorem isActivePath_swapPath_of_no_obstruct {a b : V} (hcov : G.IsCoveredEdge a b)
    {Z : Finset V} {p : List V} (hact : G.IsActivePath Z p)
    (hfork : ∀ (j : ℕ) (hj : j + 2 < p.length),
      ¬ G.FlipObstruct a b (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
        (p.get ⟨j + 2, hj⟩)) :
    (flipEdge hcov).IsActivePath Z (swapPath hcov Z p) := by
  obtain ⟨hadj, htri⟩ := hact
  constructor
  · -- adjacency
    intro i hi
    have hi1 : i + 1 < p.length := by simpa using hi
    have hi0 : i < p.length := by omega
    have hG : G.UAdj (p.get ⟨i, hi0⟩) (p.get ⟨i + 1, hi1⟩) := hadj i (by simpa using hi)
    rcases swapPath_get_eq hcov Z p i (by omega) hi0 with hvi | ⟨hvi, hai, _, _, hcoli, _⟩
    · rcases swapPath_get_eq hcov Z p (i + 1) (by omega) hi1 with
        hvi1 | ⟨hvi1, hai1, _, _, hcol1, _⟩
      · rw [hvi, hvi1]; exact (flipEdge_sameSkeleton hcov _ _).mp hG
      · -- i+1 swapped: its left collider arm gives `p i → a`, covered ⟹ `p i → b`
        rw [hvi, hvi1]
        have harm : G.edge (p.get ⟨i, hi0⟩) a := by
          have h := hcol1.1
          simp only [Nat.add_sub_cancel] at h
          rw [hai1] at h; exact h
        have hne : p.get ⟨i, hi0⟩ ≠ a := fun h => G.irrefl a (h ▸ harm)
        have hb : G.edge (p.get ⟨i, hi0⟩) b := (hcov.2 _ hne).mp harm
        exact Or.inl ((flipEdge_edge_iff_of_ne_a hcov hne hcov.ne.symm).mpr hb)
    · -- i swapped: its right collider arm gives `p (i+1) → a`, covered ⟹ `p (i+1) → b`
      have harm : G.edge (p.get ⟨i + 1, hi1⟩) a := by
        have h := hcoli.2; rw [hai] at h; exact h
      have hne1 : p.get ⟨i + 1, hi1⟩ ≠ a := fun h => G.irrefl a (h ▸ harm)
      have hb : G.edge (p.get ⟨i + 1, hi1⟩) b := (hcov.2 _ hne1).mp harm
      rcases swapPath_get_eq hcov Z p (i + 1) (by omega) hi1 with hvi1 | ⟨_, hai1, _, _, _⟩
      · rw [hvi, hvi1]
        exact Or.inr ((flipEdge_edge_iff_of_ne_a hcov hne1 hcov.ne.symm).mpr hb)
      · exact absurd hai1 hne1
  · -- collider / activation conditions
    intro j hj
    have hjl : j + 2 < p.length := by simpa using hj
    have hj0 : j < p.length := by omega
    have hj1 : j + 1 < p.length := by omega
    have hjtri := htri j (by simpa using hj)
    have hob := hfork j (by simpa using hj)
    rcases swapPath_get_eq hcov Z p (j + 1) (by omega) hj1 with
      hmid | ⟨hmidb, hmida, _, _, hmcol, hmanc⟩
    · -- middle kept
      by_cases hmida : p.get ⟨j + 1, hj1⟩ = a
      · -- A1: middle = a (kept). Under `hfork`, `a` is a flip-collider iff it is a G-collider,
        -- because a `b` neighbour of `a` would otherwise be a flip-obstructing triple.
        have hjne : p.get ⟨j, hj0⟩ ≠ a := by
          intro h
          have hu := hadj j (by omega); rw [h, hmida] at hu
          rcases hu with he | he <;> exact G.irrefl a he
        have hj2ne : p.get ⟨j + 2, hjl⟩ ≠ a := by
          intro h
          have hu := hadj (j + 1) (by omega); rw [hmida, h] at hu
          rcases hu with he | he <;> exact G.irrefl a he
        rcases swapPath_get_eq hcov Z p j (by omega) hj0 with hvj | ⟨_, haj, _⟩
        on_goal 2 => exact absurd haj hjne
        rcases swapPath_get_eq hcov Z p (j + 2) (by omega) hjl with hvj2 | ⟨_, haj2, _⟩
        on_goal 2 => exact absurd haj2 hj2ne
        have hcoll_iff : (flipEdge hcov).IsCollider (p.get ⟨j, hj0⟩) a (p.get ⟨j + 2, hjl⟩) ↔
            G.IsCollider (p.get ⟨j, hj0⟩) a (p.get ⟨j + 2, hjl⟩) := by
          constructor
          · rintro ⟨hL, hR⟩
            rw [flipEdge_edge] at hL hR
            have hLa : G.edge (p.get ⟨j, hj0⟩) a := by
              rcases hL with ⟨he, _⟩ | ⟨hlb, _⟩
              · exact he
              · exact (hob (Or.inl ⟨hmida, hlb,
                  hR.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩)).elim
            have hRa : G.edge (p.get ⟨j + 2, hjl⟩) a := by
              rcases hR with ⟨he, _⟩ | ⟨hrb, _⟩
              · exact he
              · exact (hob (Or.inr (Or.inl ⟨hmida, hrb, Or.inl hLa⟩))).elim
            exact ⟨hLa, hRa⟩
          · rintro ⟨hL, hR⟩
            exact ⟨by rw [flipEdge_edge]; exact Or.inl ⟨hL, fun h => hjne h.1⟩,
              by rw [flipEdge_edge]; exact Or.inl ⟨hR, fun h => hj2ne h.1⟩⟩
        simp only [hvj, hvj2, hmid, hmida]
        by_cases hC : G.IsCollider (p.get ⟨j, hj0⟩) a (p.get ⟨j + 2, hjl⟩)
        · rw [if_pos (hcoll_iff.mpr hC)]
          by_contra hanc
          have hb : (swapPath hcov Z p).get ⟨j + 1, by simpa using hj1⟩ = b :=
            swapPath_get_b_of hcov Z p (j + 1) (by simpa using hj1) hj1 (by omega) (by omega) hmida
              hanc (by simpa only [Nat.add_sub_cancel, hmida] using hC)
          rw [hmid, hmida] at hb
          exact hcov.ne hb
        · rw [if_neg (fun h => hC (hcoll_iff.mp h))]
          have hcG : ¬ G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) := by
            rw [hmida]; exact hC
          have ht := hjtri; rw [if_neg hcG] at ht; rwa [hmida] at ht
      · -- A2: middle m = p[j+1] ≠ a (kept)
        rw [hmid]
        -- `m ∉ Z` from the original triple, used in every non-collider branch
        have hmnotZ_of : ¬ G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) →
            p.get ⟨j + 1, hj1⟩ ∉ Z := fun hc => by
          have ht := hjtri; rw [if_neg hc] at ht; exact ht
        -- helper: a swapped side gives `m → a`, hence the side has no flip-edge into `m`,
        -- and the original triple is not a collider, so `m ∉ Z`.
        have swapped_side : G.edge (p.get ⟨j + 1, hj1⟩) a →
            ¬ (flipEdge hcov).edge b (p.get ⟨j + 1, hj1⟩) := by
          intro hma hbm
          have hmb : p.get ⟨j + 1, hj1⟩ ≠ b := by
            intro h; rw [h] at hma; exact G.asymm hcov.1 hma
          have hmne : p.get ⟨j + 1, hj1⟩ ≠ a := fun h => G.irrefl a (h ▸ hma)
          exact absurd ((flipEdge_edge_into_iff hcov hmida hmb b).mp hbm)
            (G.asymm ((hcov.2 (p.get ⟨j + 1, hj1⟩) hmne).mp hma))
        rcases swapPath_get_eq hcov Z p j (by omega) hj0 with hvj | ⟨hvjb, hvja, _, _, hvjcol, _⟩
        · rcases swapPath_get_eq hcov Z p (j + 2) (by omega) hjl with
            hvj2 | ⟨hvj2b, hvj2a, _, _, hvj2col, _⟩
          · -- both sides kept: collider status and activation transfer
            by_cases hmb : p.get ⟨j + 1, hj1⟩ = b
            · -- middle is `b`. Under `hfork`, flip-collider ↔ G-collider at `b`: an `a`
              -- neighbour would otherwise destroy the collider (a flip-obstructing triple).
              have hbiff : (flipEdge hcov).IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩)
                  (p.get ⟨j + 2, hjl⟩) ↔
                  G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) := by
                constructor
                · rintro ⟨hL, hR⟩
                  rw [flipEdge_edge, hmb] at hL hR
                  refine ⟨?_, ?_⟩
                  · rcases hL with ⟨he, _⟩ | ⟨_, hba⟩
                    · rw [hmb]; exact he
                    · exact absurd hba.symm hcov.ne
                  · rcases hR with ⟨he, _⟩ | ⟨_, hba⟩
                    · rw [hmb]; exact he
                    · exact absurd hba.symm hcov.ne
                · rintro ⟨hL, hR⟩
                  rw [hmb] at hL hR
                  have hjna : p.get ⟨j, hj0⟩ ≠ a := fun h =>
                    hob (Or.inr (Or.inr (Or.inl ⟨hmb, h, hR⟩)))
                  have hj2na : p.get ⟨j + 2, hjl⟩ ≠ a := fun h =>
                    hob (Or.inr (Or.inr (Or.inr ⟨hmb, h, hL⟩)))
                  exact ⟨by rw [flipEdge_edge, hmb]; exact Or.inl ⟨hL, fun h => hjna h.1⟩,
                    by rw [flipEdge_edge, hmb]; exact Or.inl ⟨hR, fun h => hj2na h.1⟩⟩
              rw [hvj, hvj2]
              by_cases hC : G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩)
              · rw [if_pos (hbiff.mpr hC)]
                have hmG : p.get ⟨j + 1, hj1⟩ ∈ G.bbZAncestors Z := by
                  have ht := hjtri; rwa [if_pos hC] at ht
                rw [hmb]; exact bbZAncestors_flip_of_b hcov Z (by rw [← hmb]; exact hmG)
              · rw [if_neg (fun h => hC (hbiff.mp h))]
                exact hmnotZ_of hC
            · -- middle ∉ {a, b}: edges into it are flip-invariant
              have hiffL := flipEdge_edge_into_iff hcov hmida hmb (p.get ⟨j, hj0⟩)
              have hiffR := flipEdge_edge_into_iff hcov hmida hmb (p.get ⟨j + 2, hjl⟩)
              rw [hvj, hvj2]
              by_cases hC : G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩)
              · rw [if_pos ⟨hiffL.mpr hC.1, hiffR.mpr hC.2⟩]
                have hmG : p.get ⟨j + 1, hj1⟩ ∈ G.bbZAncestors Z := by
                  have ht := hjtri; rwa [if_pos hC] at ht
                exact bbZAncestors_flip_of_ne hcov Z hmida hmG
              · rw [if_neg (fun h => hC ⟨hiffL.mp h.1, hiffR.mp h.2⟩)]
                exact hmnotZ_of hC
          · -- j+2 swapped: p[j+2]=a, collider at j+2 gives m → a
            have hma : G.edge (p.get ⟨j + 1, hj1⟩) a := by
              have h := hvj2col.1; rw [hvj2a] at h; exact h
            have hGc : ¬ G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) :=
              fun h => G.asymm hma (hvj2a ▸ h.2)
            rw [hvj2b, if_neg (fun h => swapped_side hma h.2)]
            exact hmnotZ_of hGc
        · -- j swapped: p[j]=a, collider at j gives m → a
          have hma : G.edge (p.get ⟨j + 1, hj1⟩) a := by
            have h := hvjcol.2; rw [hvja] at h; exact h
          have hGc : ¬ G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) :=
            fun h => G.asymm hma (hvja ▸ h.1)
          rw [hvjb, if_neg (fun h => swapped_side hma h.1)]
          exact hmnotZ_of hGc
    · -- middle swapped to b: p[j+1]=a, G-collider at j+1, a ∉ bbZAncestors_flip
      have harmL : G.edge (p.get ⟨j, hj0⟩) a := by
        have h := hmcol.1; simp only [Nat.add_sub_cancel] at h; rw [hmida] at h; exact h
      have harmR : G.edge (p.get ⟨j + 2, hjl⟩) a := by
        have h := hmcol.2; rw [hmida] at h; exact h
      have hjne : p.get ⟨j, hj0⟩ ≠ a := fun h => G.irrefl a (h ▸ harmL)
      have hj2ne : p.get ⟨j + 2, hjl⟩ ≠ a := fun h => G.irrefl a (h ▸ harmR)
      have hbL : G.edge (p.get ⟨j, hj0⟩) b := (hcov.2 _ hjne).mp harmL
      have hbR : G.edge (p.get ⟨j + 2, hjl⟩) b := (hcov.2 _ hj2ne).mp harmR
      rcases swapPath_get_eq hcov Z p j (by omega) hj0 with hvj | ⟨_, haj, _⟩
      · rcases swapPath_get_eq hcov Z p (j + 2) (by omega) hjl with hvj2 | ⟨_, haj2, _⟩
        · have hcolF : (flipEdge hcov).IsCollider (p.get ⟨j, hj0⟩) b (p.get ⟨j + 2, hjl⟩) :=
            ⟨(flipEdge_edge_iff_of_ne_a hcov hjne hcov.ne.symm).mpr hbL,
              (flipEdge_edge_iff_of_ne_a hcov hj2ne hcov.ne.symm).mpr hbR⟩
          have haG : a ∈ G.bbZAncestors Z := by
            have hc : G.IsCollider (p.get ⟨j, hj0⟩) (p.get ⟨j + 1, hj1⟩) (p.get ⟨j + 2, hjl⟩) := by
              rw [hmida]; exact ⟨harmL, harmR⟩
            have ht := hjtri; rw [if_pos hc] at ht; rwa [hmida] at ht
          simp only [hmidb, hvj, hvj2]
          rw [if_pos hcolF]
          exact bbZAncestors_flip_of_lost hcov Z haG hmanc
        · exact absurd haj2 hj2ne
      · exact absurd haj hjne

/-- `swapPath` never touches the first vertex, so it preserves the head. -/
private theorem swapPath_head? {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (p : List V) : (swapPath hcov Z p).head? = p.head? := by
  rw [List.head?_eq_getElem?, List.head?_eq_getElem?]
  rcases Nat.eq_zero_or_pos p.length with h | h
  · rw [List.getElem?_eq_none (by rw [swapPath_length]; omega), List.getElem?_eq_none (by omega)]
  · rw [List.getElem?_eq_getElem (by rw [swapPath_length]; exact h),
      List.getElem?_eq_getElem h]
    congr 1
    rcases swapPath_get_eq hcov Z p 0 (by rw [swapPath_length]; exact h) h with hh | ⟨_, _, h1, _⟩
    · simpa using hh
    · omega

/-- `swapPath` never touches the last vertex, so it preserves the last element. -/
private theorem swapPath_getLast? {a b : V} (hcov : G.IsCoveredEdge a b) (Z : Finset V)
    (p : List V) : (swapPath hcov Z p).getLast? = p.getLast? := by
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, swapPath_length]
  rcases Nat.eq_zero_or_pos p.length with h | h
  · rw [List.getElem?_eq_none (by rw [swapPath_length]; omega), List.getElem?_eq_none (by omega)]
  · rw [List.getElem?_eq_getElem (by rw [swapPath_length]; omega),
      List.getElem?_eq_getElem (by omega)]
    congr 1
    rcases swapPath_get_eq hcov Z p (p.length - 1) (by rw [swapPath_length]; omega) (by omega)
      with hh | ⟨_, _, _, h2, _⟩
    · simpa using hh
    · omega

/-- **Reduction step.** If some interior triple of an active path is flip-obstructing, then a
strictly shorter active path with the *same endpoints* exists: a covered edge lets us drop the
obstructing middle vertex (reconnecting its neighbours through the shared parent) or, for an
`a — b — a` / `b — a — b` backtrack, excise the loop. The covered structure keeps every
neighbour's arrowhead orientation, so activity is preserved. The distinct-endpoint hypothesis
`hne` rules out the degenerate full-path backtrack `[x, m, x]` (whose only excision `[x]` would
be too short); such a path has equal endpoints and never arises between disjoint `X`, `Y`. -/
private theorem exists_shorter_active_of_obstruct {a b : V} (hcov : G.IsCoveredEdge a b)
    {Z : Finset V} {p : List V} (hact : G.IsActivePath Z p) (hne : p.head? ≠ p.getLast?)
    {j : ℕ} (hj : j + 2 < p.length)
    (hbad : G.FlipObstruct a b (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
      (p.get ⟨j + 2, hj⟩)) :
    ∃ q, G.IsActivePath Z q ∧ q.head? = p.head? ∧ q.getLast? = p.getLast? ∧
      2 ≤ q.length ∧ q.length < p.length := by
  by_cases hlr : p.get ⟨j, by omega⟩ = p.get ⟨j + 2, hj⟩
  · -- EXCISE the backtrack `[x, m, x]`
    have h4 : 4 ≤ p.length := four_le_length_of_backtrack_endpoints_ne hne hj hlr
    refine ⟨skipTwo p (j + 1), ?_, skipTwo_head? (by omega) (by omega),
      skipTwo_getLast? (by omega) (by omega) hlr, by rw [skipTwo_length]; omega,
      by rw [skipTwo_length]; omega⟩
    refine isActivePath_skipTwo hact (by omega) (by omega) hlr (fun hk2 hkR => ?_)
    change
      if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
          (p.get ⟨j + 3, hkR⟩) then
        p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
      else
        p.get ⟨j, by omega⟩ ∉ Z
    have hjm : j - 1 + 1 = j := by omega
    have hjr : j - 1 + 2 = j + 1 := by omega
    by_cases hC :
        G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
          (p.get ⟨j + 3, hkR⟩)
    · rw [if_pos hC]
      rcases hbad with ⟨hm, hl, hr⟩ | ⟨hm, hr, hl⟩ | ⟨hm, hl, hrb⟩ | ⟨hm, hr, hlb⟩
      · have hOld :
            G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 1, by omega⟩) := by
          refine ⟨hC.1, ?_⟩
          rw [hm, hl]
          exact hcov.1
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        rw [if_pos hOld] at ht
        exact ht
      · have hx_b : p.get ⟨j, by omega⟩ = b := by
          calc
            p.get ⟨j, by omega⟩ = p.get ⟨j + 2, hj⟩ := hlr
            _ = b := hr
        have hOld :
            G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 1, by omega⟩) := by
          refine ⟨hC.1, ?_⟩
          rw [hm, hx_b]
          exact hcov.1
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        rw [if_pos hOld] at ht
        exact ht
      · have hcent :
            G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
              (p.get ⟨j + 2, hj⟩) := by
          rw [hl, hm]
          exact ⟨hcov.1, hrb⟩
        have ht :
            if G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                (p.get ⟨j + 2, hj⟩) then
              p.get ⟨j + 1, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 1, by omega⟩ ∉ Z := by
          simpa using hact.2 j (by omega)
        rw [if_pos hcent] at ht
        have hbAnc : b ∈ G.bbZAncestors Z := hm ▸ ht
        have haAnc : a ∈ G.bbZAncestors Z := bbZAncestors_of_edge hcov.1 hbAnc
        exact hl.symm ▸ haAnc
      · have hx_a : p.get ⟨j, by omega⟩ = a := by
          calc
            p.get ⟨j, by omega⟩ = p.get ⟨j + 2, hj⟩ := hlr
            _ = a := hr
        have hcent :
            G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
              (p.get ⟨j + 2, hj⟩) := by
          rw [hm, hr]
          exact ⟨hlb, hcov.1⟩
        have ht :
            if G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                (p.get ⟨j + 2, hj⟩) then
              p.get ⟨j + 1, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 1, by omega⟩ ∉ Z := by
          simpa using hact.2 j (by omega)
        rw [if_pos hcent] at ht
        have hbAnc : b ∈ G.bbZAncestors Z := hm ▸ ht
        have haAnc : a ∈ G.bbZAncestors Z := bbZAncestors_of_edge hcov.1 hbAnc
        exact hx_a.symm ▸ haAnc
    · rw [if_neg hC]
      by_cases hL : G.edge (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
      · have hRmiss : ¬ G.edge (p.get ⟨j + 3, hkR⟩) (p.get ⟨j, by omega⟩) := by
          intro hR
          exact hC ⟨hL, hR⟩
        have hnotOld :
            ¬ G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, hkR⟩) := by
          intro hc
          apply hRmiss
          exact hlr.symm ▸ hc.2
        have ht :
            if G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, hkR⟩) then
              p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 2, hj⟩ ∉ Z := by
          simpa [show j + 1 + 1 = j + 2 by omega,
            show j + 1 + 2 = j + 3 by omega] using hact.2 (j + 1) (by omega)
        rw [if_neg hnotOld] at ht
        intro hxZ
        exact ht (hlr ▸ hxZ)
      · have hnotOld :
            ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 1, by omega⟩) := fun hc => hL hc.1
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        rw [if_neg hnotOld] at ht
        exact ht
  · -- DROP the obstructing middle `m`
    refine ⟨skipOne p (j + 1), ?_, skipOne_head? (by omega) (by omega),
      skipOne_getLast? (by omega), by rw [skipOne_length]; omega,
      by rw [skipOne_length]; omega⟩
    refine isActivePath_skipOne hact (by omega) (by omega) ?adj (fun hk2 => ?left)
      (fun hkR => ?right)
    case adj =>
      rcases hbad with ⟨hm, hl, hr⟩ | ⟨hm, hr, hl⟩ | ⟨hm, hl, hrb⟩ | ⟨hm, hr, hlb⟩
      · have hr_ne_b : p.get ⟨j + 2, hj⟩ ≠ b := by
          intro hr_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := by simpa using hl
              _ = p.get ⟨j + 2, hj⟩ := hr_eq.symm)
        have hra : G.edge (p.get ⟨j + 2, hj⟩) a := by
          rcases hr with hra | hr_eq
          · exact hra
          · exact absurd hr_eq hr_ne_b
        have hr_ne_a : p.get ⟨j + 2, hj⟩ ≠ a := by
          intro hr_eq
          have h := hra
          rw [hr_eq] at h
          exact G.irrefl a h
        have hrb' : G.edge (p.get ⟨j + 2, hj⟩) b :=
          (hcov.2 (p.get ⟨j + 2, hj⟩) hr_ne_a).mp hra
        exact Or.inr (by
          change G.edge (p.get ⟨j + 2, hj⟩) (p.get ⟨j, by omega⟩)
          have hl' : p.get ⟨j, by omega⟩ = b := by simpa using hl
          exact hl'.symm ▸ hrb')
      · have hl_ne_b : p.get ⟨j, by omega⟩ ≠ b := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a := by
          rcases hl with hla | hl_eq
          · exact hla
          · exact absurd hl_eq hl_ne_b
        have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          have h := hla
          rw [hl_eq] at h
          exact G.irrefl a h
        have hlb' : G.edge (p.get ⟨j, by omega⟩) b :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mp hla
        exact Or.inl (by
          change G.edge (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
          exact hr.symm ▸ hlb')
      · have hr_ne_a : p.get ⟨j + 2, hj⟩ ≠ a := by
          intro hr_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = a := by simpa using hl
              _ = p.get ⟨j + 2, hj⟩ := hr_eq.symm)
        have hra : G.edge (p.get ⟨j + 2, hj⟩) a :=
          (hcov.2 (p.get ⟨j + 2, hj⟩) hr_ne_a).mpr hrb
        exact Or.inr (by
          change G.edge (p.get ⟨j + 2, hj⟩) (p.get ⟨j, by omega⟩)
          have hl' : p.get ⟨j, by omega⟩ = a := by simpa using hl
          exact hl'.symm ▸ hra)
      · have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = a := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mpr hlb
        exact Or.inl (by
          change G.edge (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
          exact hr.symm ▸ hla)
    case left =>
      change
        if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
            (p.get ⟨j + 2, hj⟩) then
          p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
        else
          p.get ⟨j, by omega⟩ ∉ Z
      have hjm : j - 1 + 1 = j := by omega
      have hjr : j - 1 + 2 = j + 1 := by omega
      rcases hbad with ⟨hm, hl, hr⟩ | ⟨hm, hr, hl⟩ | ⟨hm, hl, hrb⟩ | ⟨hm, hr, hlb⟩
      · have hr_ne_b : p.get ⟨j + 2, hj⟩ ≠ b := by
          intro hr_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := by simpa using hl
              _ = p.get ⟨j + 2, hj⟩ := hr_eq.symm)
        have hra : G.edge (p.get ⟨j + 2, hj⟩) a := by
          rcases hr with hra | hr_eq
          · exact hra
          · exact absurd hr_eq hr_ne_b
        have hr_ne_a : p.get ⟨j + 2, hj⟩ ≠ a := by
          intro hr_eq
          have h := hra
          rw [hr_eq] at h
          exact G.irrefl a h
        have hrb' : G.edge (p.get ⟨j + 2, hj⟩) b :=
          (hcov.2 (p.get ⟨j + 2, hj⟩) hr_ne_a).mp hra
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        by_cases hL : G.edge (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
        · have hOld :
              G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) := by
            refine ⟨hL, ?_⟩
            rw [hm, hl]
            exact hcov.1
          have hNew :
              G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 2, hj⟩) := by
            refine ⟨hL, ?_⟩
            change G.edge (p.get ⟨j + 2, hj⟩) (p.get ⟨j, by omega⟩)
            have hl' : p.get ⟨j, by omega⟩ = b := by simpa using hl
            exact hl'.symm ▸ hrb'
          rw [if_pos hOld] at ht
          rw [if_pos hNew]
          exact ht
        · have hOld :
              ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) := fun hc => hL hc.1
          have hNew :
              ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 2, hj⟩) := fun hc => hL hc.1
          rw [if_neg hOld] at ht
          rw [if_neg hNew]
          exact ht
      · have hl_ne_b : p.get ⟨j, by omega⟩ ≠ b := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a := by
          rcases hl with hla | hl_eq
          · exact hla
          · exact absurd hl_eq hl_ne_b
        have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          have h := hla
          rw [hl_eq] at h
          exact G.irrefl a h
        have hlb' : G.edge (p.get ⟨j, by omega⟩) b :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mp hla
        have hnotOld :
            ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 1, by omega⟩) := by
          intro hc
          have hal : G.edge a (p.get ⟨j, by omega⟩) := by
            have h := hc.2
            rw [hm] at h
            exact h
          exact G.asymm hla hal
        have hnotNew :
            ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 2, hj⟩) := by
          intro hc
          have hbl : G.edge b (p.get ⟨j, by omega⟩) := by
            have h := hc.2
            rw [hr] at h
            exact h
          exact G.asymm hlb' hbl
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        rw [if_neg hnotOld] at ht
        rw [if_neg hnotNew]
        exact ht
      · by_cases hC :
            G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 2, hj⟩)
        · rw [if_pos hC]
          have hcent :
              G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                (p.get ⟨j + 2, hj⟩) := by
            rw [hl, hm]
            exact ⟨hcov.1, hrb⟩
          have ht :
              if G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                  (p.get ⟨j + 2, hj⟩) then
                p.get ⟨j + 1, by omega⟩ ∈ G.bbZAncestors Z
              else
                p.get ⟨j + 1, by omega⟩ ∉ Z := by
            simpa using hact.2 j (by omega)
          rw [if_pos hcent] at ht
          have hbAnc : b ∈ G.bbZAncestors Z := hm ▸ ht
          have haAnc : a ∈ G.bbZAncestors Z := bbZAncestors_of_edge hcov.1 hbAnc
          exact hl.symm ▸ haAnc
        · rw [if_neg hC]
          have hnotOld :
              ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) := by
            intro hc
            have hba : G.edge b a := by
              have h := hc.2
              rw [hm] at h
              rw [hl] at h
              exact h
            exact G.asymm hcov.1 hba
          have ht :
              if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                  (p.get ⟨j + 1, by omega⟩) then
                p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
              else
                p.get ⟨j, by omega⟩ ∉ Z := by
            simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
          rw [if_neg hnotOld] at ht
          exact ht
      · have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = a := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mpr hlb
        have hnotOld :
            ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 1, by omega⟩) := by
          intro hc
          have hbl : G.edge b (p.get ⟨j, by omega⟩) := by
            have h := hc.2
            rw [hm] at h
            exact h
          exact G.asymm hlb hbl
        have hnotNew :
            ¬ G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
              (p.get ⟨j + 2, hj⟩) := by
          intro hc
          have hal : G.edge a (p.get ⟨j, by omega⟩) := by
            have h := hc.2
            rw [hr] at h
            exact h
          exact G.asymm hla hal
        have ht :
            if G.IsCollider (p.get ⟨j - 1, by omega⟩) (p.get ⟨j, by omega⟩)
                (p.get ⟨j + 1, by omega⟩) then
              p.get ⟨j, by omega⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j, by omega⟩ ∉ Z := by
          simpa [hjm, hjr] using hact.2 (j - 1) (by omega)
        rw [if_neg hnotOld] at ht
        rw [if_neg hnotNew]
        exact ht
    case right =>
      change
        if G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
            (p.get ⟨j + 3, by omega⟩) then
          p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
        else
          p.get ⟨j + 2, hj⟩ ∉ Z
      rcases hbad with ⟨hm, hl, hr⟩ | ⟨hm, hr, hl⟩ | ⟨hm, hl, hrb⟩ | ⟨hm, hr, hlb⟩
      · have hr_ne_b : p.get ⟨j + 2, hj⟩ ≠ b := by
          intro hr_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := by simpa using hl
              _ = p.get ⟨j + 2, hj⟩ := hr_eq.symm)
        have hra : G.edge (p.get ⟨j + 2, hj⟩) a := by
          rcases hr with hra | hr_eq
          · exact hra
          · exact absurd hr_eq hr_ne_b
        have hr_ne_a : p.get ⟨j + 2, hj⟩ ≠ a := by
          intro hr_eq
          have h := hra
          rw [hr_eq] at h
          exact G.irrefl a h
        have hrb' : G.edge (p.get ⟨j + 2, hj⟩) b :=
          (hcov.2 (p.get ⟨j + 2, hj⟩) hr_ne_a).mp hra
        have hnotOld :
            ¬ G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, by omega⟩) := by
          intro hc
          have har : G.edge a (p.get ⟨j + 2, hj⟩) := by
            have h := hc.1
            rw [hm] at h
            exact h
          exact G.asymm har hra
        have hnotNew :
            ¬ G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, by omega⟩) := by
          intro hc
          have hbr : G.edge b (p.get ⟨j + 2, hj⟩) := by
            have h := hc.1
            rw [hl] at h
            exact h
          exact G.asymm hrb' hbr
        have ht :
            if G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) then
              p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 2, hj⟩ ∉ Z := by
          simpa using hact.2 (j + 1) (by omega)
        rw [if_neg hnotOld] at ht
        rw [if_neg hnotNew]
        exact ht
      · have hl_ne_b : p.get ⟨j, by omega⟩ ≠ b := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = b := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a := by
          rcases hl with hla | hl_eq
          · exact hla
          · exact absurd hl_eq hl_ne_b
        have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          have h := hla
          rw [hl_eq] at h
          exact G.irrefl a h
        have hlb' : G.edge (p.get ⟨j, by omega⟩) b :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mp hla
        have ht :
            if G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) then
              p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 2, hj⟩ ∉ Z := by
          simpa using hact.2 (j + 1) (by omega)
        by_cases hR : G.edge (p.get ⟨j + 3, by omega⟩) (p.get ⟨j + 2, hj⟩)
        · have hOld :
              G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) := by
            refine ⟨?_, hR⟩
            rw [hm, hr]
            exact hcov.1
          have hNew :
              G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) := by
            refine ⟨?_, hR⟩
            change G.edge (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
            exact hr.symm ▸ hlb'
          rw [if_pos hOld] at ht
          rw [if_pos hNew]
          exact ht
        · have hOld :
              ¬ G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) := fun hc => hR hc.2
          have hNew :
              ¬ G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) := fun hc => hR hc.2
          rw [if_neg hOld] at ht
          rw [if_neg hNew]
          exact ht
      · have hr_ne_a : p.get ⟨j + 2, hj⟩ ≠ a := by
          intro hr_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = a := by simpa using hl
              _ = p.get ⟨j + 2, hj⟩ := hr_eq.symm)
        have hra : G.edge (p.get ⟨j + 2, hj⟩) a :=
          (hcov.2 (p.get ⟨j + 2, hj⟩) hr_ne_a).mpr hrb
        have hnotOld :
            ¬ G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, by omega⟩) := by
          intro hc
          have hbr : G.edge b (p.get ⟨j + 2, hj⟩) := by
            have h := hc.1
            rw [hm] at h
            exact h
          exact G.asymm hrb hbr
        have hnotNew :
            ¬ G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, by omega⟩) := by
          intro hc
          have har : G.edge a (p.get ⟨j + 2, hj⟩) := by
            have h := hc.1
            rw [hl] at h
            exact h
          exact G.asymm hra har
        have ht :
            if G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) then
              p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
            else
              p.get ⟨j + 2, hj⟩ ∉ Z := by
          simpa using hact.2 (j + 1) (by omega)
        rw [if_neg hnotOld] at ht
        rw [if_neg hnotNew]
        exact ht
      · have hl_ne_a : p.get ⟨j, by omega⟩ ≠ a := by
          intro hl_eq
          exact hlr (by
            calc
              p.get ⟨j, by omega⟩ = a := hl_eq
              _ = p.get ⟨j + 2, hj⟩ := hr.symm)
        have hla : G.edge (p.get ⟨j, by omega⟩) a :=
          (hcov.2 (p.get ⟨j, by omega⟩) hl_ne_a).mpr hlb
        by_cases hC :
            G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 2, hj⟩)
              (p.get ⟨j + 3, by omega⟩)
        · rw [if_pos hC]
          have hcent :
              G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                (p.get ⟨j + 2, hj⟩) := by
            rw [hm, hr]
            exact ⟨hlb, hcov.1⟩
          have ht :
              if G.IsCollider (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩)
                  (p.get ⟨j + 2, hj⟩) then
                p.get ⟨j + 1, by omega⟩ ∈ G.bbZAncestors Z
              else
                p.get ⟨j + 1, by omega⟩ ∉ Z := by
            simpa using hact.2 j (by omega)
          rw [if_pos hcent] at ht
          have hbAnc : b ∈ G.bbZAncestors Z := hm ▸ ht
          have haAnc : a ∈ G.bbZAncestors Z := bbZAncestors_of_edge hcov.1 hbAnc
          exact hr.symm ▸ haAnc
        · rw [if_neg hC]
          have hnotOld :
              ¬ G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                (p.get ⟨j + 3, by omega⟩) := by
            intro hc
            have hba : G.edge b a := by
              have h := hc.1
              rw [hm] at h
              rw [hr] at h
              exact h
            exact G.asymm hcov.1 hba
          have ht :
              if G.IsCollider (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
                  (p.get ⟨j + 3, by omega⟩) then
                p.get ⟨j + 2, hj⟩ ∈ G.bbZAncestors Z
              else
                p.get ⟨j + 2, hj⟩ ∉ Z := by
            simpa using hact.2 (j + 1) (by omega)
          rw [if_neg hnotOld] at ht
          exact ht

/-- **Assembly.** Every active path in `G` yields an active path in `flipEdge` with the same
endpoints. By strong induction on length: if no interior triple is flip-obstructing, the swap
`swapPath` works directly; otherwise the reduction step shortens the path and we recurse. -/
private theorem exists_flip_active_of_active {a b : V} (hcov : G.IsCoveredEdge a b)
    (Z : Finset V) :
    ∀ (p : List V), G.IsActivePath Z p → p.head? ≠ p.getLast? → 2 ≤ p.length →
    ∃ q, (flipEdge hcov).IsActivePath Z q ∧ q.head? = p.head? ∧
      q.getLast? = p.getLast? ∧ 2 ≤ q.length := by
  have H : ∀ (n : ℕ) (p : List V), p.length = n → G.IsActivePath Z p →
      p.head? ≠ p.getLast? → 2 ≤ p.length →
      ∃ q, (flipEdge hcov).IsActivePath Z q ∧ q.head? = p.head? ∧
        q.getLast? = p.getLast? ∧ 2 ≤ q.length := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro p hpn hact hne hlen
      by_cases hbad : ∃ (j : ℕ) (hj : j + 2 < p.length),
          G.FlipObstruct a b (p.get ⟨j, by omega⟩) (p.get ⟨j + 1, by omega⟩) (p.get ⟨j + 2, hj⟩)
      · obtain ⟨j, hj, hb⟩ := hbad
        obtain ⟨q, hqact, hqh, hql, hq2, hqlt⟩ :=
          exists_shorter_active_of_obstruct hcov hact hne hj hb
        obtain ⟨q', hq'a, hq'h, hq'l, hq'2⟩ :=
          IH q.length (by omega) q rfl hqact (by rw [hqh, hql]; exact hne) hq2
        exact ⟨q', hq'a, hq'h.trans hqh, hq'l.trans hql, hq'2⟩
      · push_neg at hbad
        refine ⟨swapPath hcov Z p,
          isActivePath_swapPath_of_no_obstruct hcov hact (fun j hj => hbad j hj),
          swapPath_head? hcov Z p, swapPath_getLast? hcov Z p, ?_⟩
        rw [swapPath_length]; exact hlen
  intro p hact hne hlen
  exact H p.length p rfl hact hne hlen

/-- Active-path connectivity is transported across one covered-edge reversal: the AMP
covered-reversal path-surgery step, assembled from the fork-tolerant swap and the
backtrack/drop reduction. -/
private theorem hasActivePath_flipEdge_of_isCoveredEdge {a b : V}
    (hcov : G.IsCoveredEdge a b) (X Y Z : Finset V)
    (hXY : Disjoint X Y) (_hXZ : Disjoint X Z) (_hYZ : Disjoint Y Z) :
    G.HasActivePath X Y Z → (flipEdge hcov).HasActivePath X Y Z := by
  rintro ⟨p, hlen, hact, hhead, hlast⟩
  -- disjoint `X`, `Y` force distinct endpoints
  have hne : p.head? ≠ p.getLast? := by
    intro h
    rw [Finset.mem_image] at hhead hlast
    obtain ⟨x, hxX, hx⟩ := hhead
    obtain ⟨y, hyY, hy⟩ := hlast
    have hxy : y = x := (Option.some.inj (by rw [hx, h, ← hy] : some x = some y)).symm
    exact Finset.disjoint_left.mp hXY hxX (hxy ▸ hyY)
  obtain ⟨q, hqact, hqh, hql, hq2⟩ := exists_flip_active_of_active hcov Z p hact hne hlen
  refine ⟨q, hq2, hqact, ?_, ?_⟩
  · rw [hqh]; exact hhead
  · rw [hql]; exact hlast

/-- **The analytic core (AMP, per-step invariance).** Reversing one covered edge preserves
every d-separation, hence Markov equivalence. This is the single-edge kernel used by the
covered-reversal proof of the Verma--Pearl hard direction.

By `not_dSep_iff_hasActivePath` this is equivalent to: a covered-edge reversal preserves
active-path connectivity (`HasActivePath`). Since the reversed edge `b → a` is again covered
in `flipEdge` and flipping it back yields `G`, it suffices to transport an active path one way.
The only edge whose orientation changes is `a — b`; a path not traversing it keeps its
collider pattern, and one that does is rerouted through the shared parents of `a` and `b`
(`hcov.2`), whose collider-activation (an `bbZAncestors Z` membership) is preserved because
`a` and `b` reach `Z` through the same ancestors. -/
theorem markovEquiv_flipEdge {a b : V} (hcov : G.IsCoveredEdge a b) :
    MarkovEquiv G (flipEdge hcov) := by
  intro X Y Z hXY hXZ hYZ
  have hAP : G.HasActivePath X Y Z ↔ (flipEdge hcov).HasActivePath X Y Z := by
    constructor
    · exact hasActivePath_flipEdge_of_isCoveredEdge hcov X Y Z hXY hXZ hYZ
    · intro hp
      have hp₂ : (flipEdge (flipEdge_isCoveredEdge_back hcov)).HasActivePath X Y Z :=
        @hasActivePath_flipEdge_of_isCoveredEdge V _ _ (flipEdge hcov) b a
          (flipEdge_isCoveredEdge_back hcov) X Y Z hXY hXZ hYZ hp
      exact (hasActivePath_edge_congr (flipEdge_flipEdge_edge hcov) X Y Z).mp hp₂
  apply not_iff_not.mp
  calc
    ¬ G.dSep X Y Z ↔ G.HasActivePath X Y Z :=
      not_dSep_iff_hasActivePath G X Y Z hXY hXZ hYZ
    _ ↔ (flipEdge hcov).HasActivePath X Y Z := hAP
    _ ↔ ¬ (flipEdge hcov).dSep X Y Z :=
      (not_dSep_iff_hasActivePath (flipEdge hcov) X Y Z hXY hXZ hYZ).symm

end DAG

end Causalean
