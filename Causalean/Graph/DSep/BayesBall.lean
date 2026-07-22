/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bayes Ball Algorithm

This file implements the Bayes Ball BFS algorithm for computing d-separation
reachability in DAGs.

## Main definitions

* `DAG.bbZAncestors` — vertices in Z together with their ancestors
* `DAG.bbReachable` — BFS-reachable (vertex, direction) states from X given Z
* `DAG.bbReachableVertices` — vertices reachable from X given Z

## Main results

* `DAG.bbReachable_mono_source` — BFS reachability monotone in source set
* `DAG.bbReachableVertices_mono_source` — vertex reachability monotone in source set

## References

* Shachter (1998), Bayes Ball algorithm
-/

import Causalean.Graph.DAG
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod

/-! # Bayes Ball Reachability

This file implements the Bayes Ball reachability computation for finite directed
acyclic graphs. Given source and conditioning sets, it tracks directed arrival
states and returns the vertices reachable along paths that remain active under
the conditioning information.

The core definitions are `BBDir`, `BBState`, `bbZAncestors`, one-step transition
`bbStep`, initial frontier `bbInit`, reachable state set `bbReachable`, and
vertex projection `bbReachableVertices`. The exposed invariants include source
monotonicity (`bbReachable_mono_source`,
`bbReachableVertices_mono_source`), minimality of the fixed point, and closure of
reachable states under `bbStep`. -/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

/-- Direction from which a node is visited in the Bayes Ball algorithm: arrival from a
parent (`fromParent`) or arrival from a child (`fromChild`). -/
inductive BBDir
  | fromParent
  | fromChild
  deriving DecidableEq, Repr

/-- The two Bayes Ball arrival directions form a finite type. -/
instance : Fintype BBDir where
  elems := {BBDir.fromParent, BBDir.fromChild}
  complete := fun b => by cases b <;> decide

/-- A Bayes Ball state: a vertex paired with arrival direction. -/
abbrev BBState (V : Type*) := V × BBDir

variable (G : DAG V)

/-- The set of vertices in `Z` together with all ancestors of `Z`.
    A collider is "activated" iff it or a descendant is in `Z`. -/
def bbZAncestors (Z : Finset V) : Finset V := G.ancestralSet Z

/-- One step of the Bayes Ball algorithm from state `(w, dir)`.

    Rules (encoding collider/non-collider blocking):
    - fromChild, w ∉ Z: go to parents (fromChild) and children (fromParent)
    - fromChild, w ∈ Z: stop (conditioned non-collider blocks the path)
    - fromParent, w ∉ Z: go to children (fromParent);
      also go to parents (fromChild) if w or descendant in Z
    - fromParent, w ∈ Z: go to parents (fromChild) -/
def bbStep (Z : Finset V) (s : BBState V) : Finset (BBState V) :=
  let (w, dir) := s
  match dir with
  | BBDir.fromChild =>
    if w ∈ Z then
      ∅
    else
      (G.parents w).map
        ⟨(·, BBDir.fromChild), fun _ _ h => by simpa using h⟩ ∪
      (G.children w).map
        ⟨(·, BBDir.fromParent), fun _ _ h => by simpa using h⟩
  | BBDir.fromParent =>
    if w ∉ Z then
      (G.children w).map
        ⟨(·, BBDir.fromParent), fun _ _ h => by simpa using h⟩ ∪
      if w ∈ G.bbZAncestors Z then
        (G.parents w).map
          ⟨(·, BBDir.fromChild), fun _ _ h => by simpa using h⟩
      else ∅
    else
      (G.parents w).map
        ⟨(·, BBDir.fromChild), fun _ _ h => by simpa using h⟩

/-- Iterative Bayes Ball: compute fixed point of reachable states. -/
private def bbReachAux (Z : Finset V) (frontier visited : Finset (BBState V))
    (fuel : ℕ) : Finset (BBState V) :=
  match fuel with
  | 0 => visited
  | fuel + 1 =>
    let newStates := frontier.biUnion (G.bbStep Z) \ visited
    if newStates = ∅ then visited
    else bbReachAux Z newStates (visited ∪ newStates) fuel

-- ============================================================
-- BFS monotonicity helpers (private, access bbReachAux)
-- ============================================================

/-- The visited set is always a subset of the BFS result. -/
private theorem visited_sub_bbReachAux (Z : Finset V)
    (frontier visited : Finset (BBState V)) (fuel : ℕ) :
    visited ⊆ G.bbReachAux Z frontier visited fuel := by
  induction fuel generalizing frontier visited with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
    simp only [bbReachAux]
    split
    · exact Finset.Subset.refl _
    · exact Finset.subset_union_left.trans (ih _ _)

/-- If two frontiers produce the same new-states set (F₁.biUnion \ V = F₂.biUnion \ V),
    then `bbReachAux` returns the same result. -/
private theorem bbReachAux_sdiff_eq (Z : Finset V)
    {F₁ F₂ visited : Finset (BBState V)} (fuel : ℕ)
    (h : F₁.biUnion (G.bbStep Z) \ visited = F₂.biUnion (G.bbStep Z) \ visited) :
    G.bbReachAux Z F₁ visited fuel = G.bbReachAux Z F₂ visited fuel := by
  induction fuel generalizing F₁ F₂ visited with
  | zero => rfl
  | succ n ih =>
    simp only [bbReachAux, h]

/-- If `F ⊆ C`, `V ⊆ C`, and `C` is closed under `bbStep Z`
    (i.e., `C.biUnion (bbStep Z) ⊆ C`), then the BFS result stays within `C`. -/
private theorem bbReachAux_closed (Z : Finset V)
    {F V' C : Finset (BBState V)} (fuel : ℕ)
    (hF : F ⊆ C) (hV : V' ⊆ C)
    (hC : C.biUnion (G.bbStep Z) ⊆ C) :
    G.bbReachAux Z F V' fuel ⊆ C := by
  induction fuel generalizing F V' with
  | zero => exact hV
  | succ n ih =>
    simp only [bbReachAux]
    split
    · exact hV
    · -- newStates = F.biUnion \ V', newStates ⊆ F.biUnion ⊆ C.biUnion ⊆ C
      have hNewC : F.biUnion (G.bbStep Z) \ V' ⊆ C :=
        Finset.sdiff_subset.trans
          ((Finset.biUnion_subset_biUnion_of_subset_left _ hF).trans hC)
      exact ih hNewC (Finset.union_subset hV hNewC)

/-- **Main BFS monotonicity**: if `F ⊆ V₁ ⊆ V₂`, then the BFS from `(F, V₁)`
    is contained in the BFS from `(V₂, V₂)`. -/
private theorem bbReachAux_mono_combined (Z : Finset V)
    {F V₁ V₂ : Finset (BBState V)}
    (hFV : F ⊆ V₁) (hV : V₁ ⊆ V₂) (fuel : ℕ) :
    G.bbReachAux Z F V₁ fuel ⊆ G.bbReachAux Z V₂ V₂ fuel := by
  induction fuel generalizing F V₁ V₂ with
  | zero => simp only [bbReachAux]; exact hV
  | succ n ih =>
    simp only [bbReachAux]
    split
    · -- newF = ∅: LHS = V₁ ⊆ V₂ ⊆ result
      exact hV.trans (visited_sub_bbReachAux G Z V₂ V₂ (n + 1))
    · next hne =>
      -- newF ≠ ∅: LHS = bbReachAux newF (V₁ ∪ newF) n
      -- Apply IH: need newF ⊆ V₁ ∪ newF ⊆ V₂ ∪ newV₂
      -- where newV₂ = V₂.biUnion \ V₂
      set newF := F.biUnion (G.bbStep Z) \ V₁
      set newV₂ := V₂.biUnion (G.bbStep Z) \ V₂
      -- Key: newF ⊆ V₂ ∪ newV₂
      have h_newF_sub : newF ⊆ V₂ ∪ newV₂ := by
        intro x hx
        have hx_mem := Finset.mem_sdiff.mp hx
        have hx_bU : x ∈ V₂.biUnion (G.bbStep Z) :=
          Finset.mem_biUnion.mpr <| by
            obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hx_mem.1
            exact ⟨s, hV (hFV hs), hxs⟩
        by_cases hxV₂ : x ∈ V₂
        · exact Finset.mem_union_left _ hxV₂
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx_bU, hxV₂⟩)
      -- V₁ ∪ newF ⊆ V₂ ∪ newV₂
      have h_visited_sub : V₁ ∪ newF ⊆ V₂ ∪ newV₂ :=
        Finset.union_subset (hV.trans Finset.subset_union_left) h_newF_sub
      -- Two sub-cases depending on whether newV₂ is empty
      by_cases hneV₂ : newV₂ = ∅
      · -- V₂ is closed under bbStep Z
        have hV₂_closed : V₂.biUnion (G.bbStep Z) ⊆ V₂ := by
          rwa [Finset.sdiff_eq_empty_iff_subset] at hneV₂
        -- V₁ ∪ newF ⊆ V₂ (since newV₂ = ∅)
        have h_sub_V₂ : V₁ ∪ newF ⊆ V₂ := by
          simp only [hneV₂, Finset.union_empty] at h_visited_sub
          exact h_visited_sub
        -- bbReachAux G Z V₂ V₂ (n+1) = V₂ since newV₂ = ∅
        change G.bbReachAux Z newF (V₁ ∪ newF) n ⊆
          if newV₂ = ∅ then V₂ else G.bbReachAux Z newV₂ (V₂ ∪ newV₂) n
        rw [if_pos hneV₂]
        have hNewF_V₂ : newF ⊆ V₂ :=
          Finset.sdiff_subset.trans
            ((Finset.biUnion_subset_biUnion_of_subset_left _ (hFV.trans hV)).trans hV₂_closed)
        exact bbReachAux_closed G Z n hNewF_V₂ h_sub_V₂ hV₂_closed
      · -- newV₂ ≠ ∅
        change G.bbReachAux Z newF (V₁ ∪ newF) n ⊆
          if newV₂ = ∅ then V₂ else G.bbReachAux Z newV₂ (V₂ ∪ newV₂) n
        rw [if_neg hneV₂]
        -- Apply IH to get ⊆ bbReachAux (V₂ ∪ newV₂) (V₂ ∪ newV₂) n
        have step1 := ih (F := newF) Finset.subset_union_right h_visited_sub
        -- Then use sdiff_eq: bbReachAux (V₂ ∪ newV₂) (V₂ ∪ newV₂) n
        --   = bbReachAux newV₂ (V₂ ∪ newV₂) n
        -- because V₂.biUnion ⊆ V₂ ∪ newV₂
        have h_sdiff : (V₂ ∪ newV₂).biUnion (G.bbStep Z) \ (V₂ ∪ newV₂) =
            newV₂.biUnion (G.bbStep Z) \ (V₂ ∪ newV₂) := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_union]
          constructor
          · rintro ⟨⟨s, hs, hxs⟩, hx_not⟩
            refine ⟨?_, hx_not⟩
            rcases hs with hs_V₂ | hs_new
            · -- s ∈ V₂: x ∈ V₂.biUnion ⊆ V₂ ∪ newV₂, contradicts hx_not
              have hxbU : x ∈ V₂.biUnion (G.bbStep Z) := Finset.mem_biUnion.mpr ⟨s, hs_V₂, hxs⟩
              exact absurd (by
                by_cases hxV₂ : x ∈ V₂
                · exact Or.inl hxV₂
                · exact Or.inr (Finset.mem_sdiff.mpr ⟨hxbU, hxV₂⟩)) hx_not
            · exact ⟨s, hs_new, hxs⟩
          · rintro ⟨⟨s, hs, hxs⟩, hx_not⟩
            exact ⟨⟨s, Or.inr hs, hxs⟩, hx_not⟩
        rw [← bbReachAux_sdiff_eq G Z n h_sdiff]
        exact step1

/-- Initial BFS frontier from a source set `X`: for each `x ∈ X`, include all
    children of `x` in direction `fromParent` and all parents of `x` in direction
    `fromChild`. These are the states a "ball" passing through `x` can occupy. -/
def bbInit (X : Finset V) : Finset (BBState V) :=
  X.biUnion (fun x =>
    (G.children x).map
      ⟨(·, BBDir.fromParent), fun _ _ h => by simpa using h⟩ ∪
    (G.parents x).map
      ⟨(·, BBDir.fromChild), fun _ _ h => by simpa using h⟩)

/-- The set of Bayes Ball states reachable from source vertices `X`
    given conditioning set `Z`. -/
def bbReachable (Z X : Finset V) : Finset (BBState V) :=
  bbReachAux G Z (G.bbInit X) (G.bbInit X) (2 * Fintype.card V + 1)

/-- **BFS closure invariant.** If the BFS is invoked in a state where every
    *non-frontier* visited element already has its `bbStep`-image contained in
    `visited`, then the result is closed under `bbStep Z` — provided the fuel
    is large enough to fully saturate. Concretely, the invariant is:

      `(visited \ frontier).biUnion (bbStep Z) ⊆ visited`.

    Combined with sufficient fuel, the BFS will eventually halt with
    `frontier.biUnion (bbStep Z) ⊆ visited`, at which point the entire visited
    set is closed. -/
private theorem bbReachAux_closed_of_invariant (Z : Finset V)
    (frontier visited : Finset (BBState V)) (fuel : ℕ)
    (hF : frontier ⊆ visited)
    (hInv : ∀ s ∈ visited, s ∉ frontier → G.bbStep Z s ⊆ visited)
    (hfuel : fuel + visited.card ≥ 2 * Fintype.card V + 1) :
    ∀ s ∈ G.bbReachAux Z frontier visited fuel,
      G.bbStep Z s ⊆ G.bbReachAux Z frontier visited fuel := by
  induction fuel generalizing frontier visited with
  | zero =>
    -- visited.card ≥ 2 * |V| + 1 > |BBState V|, contradiction with subset_univ.
    exfalso
    have hcard_state : Fintype.card (BBState V) = 2 * Fintype.card V := by
      change Fintype.card (V × BBDir) = _
      rw [Fintype.card_prod]
      have : Fintype.card BBDir = 2 := rfl
      rw [this, Nat.mul_comm]
    have hle : visited.card ≤ 2 * Fintype.card V := by
      have h1 := Finset.card_le_univ visited
      rw [hcard_state] at h1
      exact h1
    omega
  | succ n ih =>
    simp only [bbReachAux]
    split
    · -- Termination: frontier.biUnion (bbStep Z) ⊆ visited
      next hempty =>
        have hclosed : frontier.biUnion (G.bbStep Z) ⊆ visited := by
          rw [← Finset.sdiff_eq_empty_iff_subset]; exact hempty
        intro s hs
        by_cases hsf : s ∈ frontier
        · intro y hy
          exact hclosed (Finset.mem_biUnion.mpr ⟨s, hsf, hy⟩)
        · exact hInv s hs hsf
    · next hne =>
      set newStates := frontier.biUnion (G.bbStep Z) \ visited with hNew_def
      have hnewF : newStates ⊆ visited ∪ newStates := Finset.subset_union_right
      have hInv' : ∀ s ∈ visited ∪ newStates, s ∉ newStates →
          G.bbStep Z s ⊆ visited ∪ newStates := by
        intro s hs hsf
        rcases Finset.mem_union.mp hs with hsv | hsn
        · -- s ∈ visited. Either s ∈ frontier or not.
          by_cases hfr : s ∈ frontier
          · -- s ∈ frontier ⊆ visited. Then bbStep s ⊆ frontier.biUnion ⊆ visited ∪ newStates.
            intro y hy
            have hy_bU : y ∈ frontier.biUnion (G.bbStep Z) :=
              Finset.mem_biUnion.mpr ⟨s, hfr, hy⟩
            by_cases hyv : y ∈ visited
            · exact Finset.mem_union_left _ hyv
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy_bU, hyv⟩)
          · -- s ∈ visited \ frontier: use hInv
            exact (hInv s hsv hfr).trans Finset.subset_union_left
        · exact absurd hsn hsf
      have hpos : newStates.card ≥ 1 :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      have hgrow : (visited ∪ newStates).card ≥ visited.card + 1 := by
        have heq : (visited ∪ newStates).card = visited.card + newStates.card :=
          Finset.card_union_of_disjoint Finset.disjoint_sdiff
        omega
      have hfuel' : n + (visited ∪ newStates).card ≥ 2 * Fintype.card V + 1 := by
        have h1 : (n + 1) + visited.card ≥ 2 * Fintype.card V + 1 := hfuel
        have h2 : (visited ∪ newStates).card ≥ visited.card + 1 := hgrow
        omega
      exact ih newStates (visited ∪ newStates) hnewF hInv' hfuel'

/-- Vertices reachable from `X` via Bayes Ball (ignoring direction). -/
def bbReachableVertices (Z X : Finset V) : Finset V :=
  (G.bbReachable Z X).image Prod.fst

-- ============================================================
-- Monotonicity of reachability in the source set
-- ============================================================

/-- Bayes Ball reachability is monotone in the source set. -/
theorem bbReachable_mono_source {Z : Finset V}
    {X X' : Finset V} (hXX' : X' ⊆ X) :
    G.bbReachable Z X' ⊆ G.bbReachable Z X := by
  simp only [bbReachable]
  exact bbReachAux_mono_combined G Z
    (Finset.Subset.refl _)
    (Finset.biUnion_subset_biUnion_of_subset_left _ hXX')
    _

/-- Bayes Ball reachable vertices are monotone in the source set. -/
theorem bbReachableVertices_mono_source {Z : Finset V}
    {X X' : Finset V} (hXX' : X' ⊆ X) :
    G.bbReachableVertices Z X' ⊆ G.bbReachableVertices Z X :=
  Finset.image_subset_image (G.bbReachable_mono_source hXX')

-- ============================================================
-- Closure properties of `bbReachable` (exposed for ActivePath.lean)
-- ============================================================

/-- The initial BFS frontier `bbInit X` is contained in `bbReachable Z X`. -/
theorem bbReachable_init_subset (Z X : Finset V) :
    G.bbInit X ⊆ G.bbReachable Z X := by
  unfold bbReachable
  exact visited_sub_bbReachAux G Z (G.bbInit X) (G.bbInit X) _

/-- `bbReachable Z X` is the *least* superset of `bbInit X` closed under `bbStep Z`.
    If `S` contains `bbInit X` and is closed under `bbStep Z`, then it contains
    `bbReachable Z X`. -/
theorem bbReachable_minimal (Z X : Finset V) (S : Finset (BBState V))
    (hinit : G.bbInit X ⊆ S)
    (hstep : ∀ s ∈ S, G.bbStep Z s ⊆ S) :
    G.bbReachable Z X ⊆ S := by
  unfold bbReachable
  refine bbReachAux_closed G Z _ hinit hinit ?_
  intro x hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  exact hstep s hs hxs

/-- `bbReachable Z X` is closed under `bbStep Z`. If `s ∈ bbReachable Z X`, then
    every state produced by `bbStep Z s` is also in `bbReachable Z X`. -/
theorem bbReachable_bbStep_subset (Z X : Finset V) {s : BBState V}
    (hs : s ∈ G.bbReachable Z X) :
    G.bbStep Z s ⊆ G.bbReachable Z X := by
  -- Apply `bbReachAux_closed_of_invariant` with the initial setup
  -- `frontier = visited = bbInit X` and the trivial invariant
  -- (no element is outside the frontier). The fuel `2 * Fintype.card V + 1`
  -- is enough since the state space has size `2 * Fintype.card V`.
  unfold bbReachable at hs ⊢
  apply bbReachAux_closed_of_invariant G Z (G.bbInit X) (G.bbInit X)
    (2 * Fintype.card V + 1) (Finset.Subset.refl _)
  · intro s hsv hsf; exact absurd hsv hsf
  · -- fuel + visited.card = 2|V| + 1 + visited.card ≥ 2|V| + 1
    have h := Nat.zero_le (G.bbInit X).card
    omega
  · exact hs

namespace BayesBallRegression

private abbrev ChainNode := Fin 3

private abbrev y : ChainNode := ⟨0, by decide⟩
private abbrev w : ChainNode := ⟨1, by decide⟩
private abbrev x : ChainNode := ⟨2, by decide⟩

private def chainDAG : DAG ChainNode where
  edge u v := (u = y ∧ v = w) ∨ (u = w ∧ v = x)
  decEdge := by infer_instance
  acyclic := DAG.acyclic_of_topoOrder (τ := fun v => v.val)
    (by intro u v h; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)

example : y ∉ chainDAG.bbReachableVertices {w} {x} := by
  decide

end BayesBallRegression

end DAG

end Causalean
