/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.CutsetLatent
import Causalean.SCM.Model.InterventionSet
import Causalean.SCM.Do.GlobalMarkov

/-! # Concatenation d-separation for the latent cutset

This file transfers d-separation from a target set `Y` to the latent cutset that
drives `Y` while avoiding an overridden block.  If `Y` is d-separated from the
randomised do-block `Zr` given the adjustment set `W` together with a block of
fixed nodes `F`, then the same separation holds for the latent cutset
`cutsetLatent Y (Zr ∪ W)`.  The proof concatenates an active path from `Zr` to a
cutset node `c` with the directed cutset arm `c → … → Y`: the join at the latent
node `c` is a fork, so the glued path is active and reaches `Y` from `Zr`,
contradicting the assumed separation.

## Main results

* `SCM.cutsetLatent_dSep_of_dSep` — the concatenation d-separation:
  `dSep Y Zr (W ∪ F) → dSep (cutsetLatent Y (Zr ∪ W)) Zr (W ∪ F)`.
* `SCM.cutsetLatent_dSep_of_fixSet_dSep` — the cross-model variant: separation of
  `Y` from `Zr` in the intervened graph `fixSet Z` (given `W ∪ fixSet.fixed`),
  together with backdoor criterion (i) for `W` (no `w ∈ W` is a base-graph
  descendant of any treatment `random D`, `D ∈ Z`), yields the same latent-cutset
  separation in the base graph `M`.  The base-graph active path is transported
  edge-by-edge into `fixSet Z`; criterion (i) guarantees no treatment out-edge is
  needed.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

/-- **Concatenation d-separation for the latent cutset.**

    Suppose the target set `Y` is d-separated from the randomised do-block `Zr`
    given the adjustment block `W` together with a fixed block `F ⊆ M.fixed`.
    Then the latent cutset `cutsetLatent Y (Zr ∪ W)` is d-separated from `Zr`
    given the same `W ∪ F`.

    The latent cutset records the latent roots reaching `Y` along a directed path
    whose interior avoids `Zr ∪ W`.  An active `Zr → c` path for a cutset node `c`
    extends by this directed arm into an active `Zr → Y` path: the join node `c`
    is a latent fork point not in the conditioning set, and the arm's interior
    avoids `W` (it avoids `Zr ∪ W`) and `F` (interior nodes have parents, so they
    are not fixed roots).  Such a path contradicts `dSep Y Zr (W ∪ F)`. -/
theorem cutsetLatent_dSep_of_dSep (M : Causalean.SCM N Ω)
    (Y Zr W F : Finset (SWIGNode N))
    (hW : W ⊆ M.observed) (hF : F ⊆ M.fixed)
    (hdSep : M.dag.dSep Y Zr (W ∪ F)) :
    M.dag.dSep (M.cutsetLatent Y (Zr ∪ W)) Zr (W ∪ F) := by
  classical
  have hdYZr : Disjoint Y Zr := hdSep.1
  have hdZrWF : Disjoint Zr (W ∪ F) := hdSep.2.2.1
  -- Work with the symmetric form `dSep Zr · (W ∪ F)`.
  refine (M.dag.dSep_symm _ _ _ ?_)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro c hcZr hcCut
    rcases (M.mem_cutsetLatent.mp hcCut) with ⟨_, y, hyY, hcy⟩
    rcases hcy with hcEqy | hcAv
    · exact Finset.disjoint_left.mp hdYZr (by simpa [hcEqy] using hyY) hcZr
    · obtain ⟨q, hq_len, hq_head, hq_last, hq_edge, hq_int⟩ := hcAv.exists_path
      have hq_intWF : ∀ (i : ℕ) (hi : i + 2 < q.length),
          q.get ⟨i + 1, by omega⟩ ∉ W ∪ F := by
        intro i hi hmem
        rcases Finset.mem_union.mp hmem with hmW | hmF
        · exact hq_int i hi (Finset.mem_union_right _ hmW)
        · have hedge : M.dag.edge (q.get ⟨i, by omega⟩) (q.get ⟨i + 1, by omega⟩) :=
            hq_edge i (by omega)
          have hpar : q.get ⟨i, by omega⟩ ∈ M.dag.parents (q.get ⟨i + 1, by omega⟩) :=
            M.dag.mem_parents.mpr hedge
          have hroot : M.dag.parents (q.get ⟨i + 1, by omega⟩) = ∅ :=
            M.fixed_are_roots _ (hF hmF)
          rw [hroot] at hpar
          exact absurd hpar (Finset.notMem_empty _)
      have hq_act : M.dag.IsActivePath (W ∪ F) q :=
        M.dag.isActivePath_of_directed_interior hq_edge hq_intWF
      have hyReachZr : y ∈ M.dag.bbReachableVertices (W ∪ F) Zr := by
        rw [M.dag.bbReachableVertices_iff_activePath]
        exact ⟨c, hcZr, q, hq_len, hq_act, hq_head, hq_last⟩
      have hdSepZr : M.dag.dSep Zr Y (W ∪ F) := M.dag.dSep_symm _ _ _ hdSep
      exact Finset.disjoint_left.mp hdSepZr.2.2.2 hyReachZr hyY
  · exact hdZrWF
  · rw [Finset.disjoint_left]
    intro c hcCut hcWF
    have hc_lat : c ∈ M.unobserved := (M.mem_cutsetLatent.mp hcCut).1
    rcases Finset.mem_union.mp hcWF with hcW | hcF
    · exact M.not_obs_of_unobs hc_lat (hW hcW)
    · obtain ⟨m, hm⟩ := M.fixed_is_fixed c (hF hcF)
      obtain ⟨k, hk⟩ := M.unobserved_is_random c hc_lat
      rw [hm] at hk
      cases hk
  · rw [Finset.disjoint_left]
    intro c hcReach hcCut
    -- `c` is reachable from `Zr` given `W ∪ F`, and lies in the cutset.
    have hdSepZr : M.dag.dSep Zr Y (W ∪ F) := M.dag.dSep_symm _ _ _ hdSep
    -- Unpack the cutset membership: an avoiding arm to some `y ∈ Y`.
    rcases (M.mem_cutsetLatent.mp hcCut) with ⟨hc_lat, y, hyY, hcy⟩
    -- Active `Zr → c` path.
    rw [M.dag.bbReachableVertices_iff_activePath] at hcReach
    obtain ⟨zr, hzrZr, pa, hpa_len, hpa_act, hpa_head, hpa_last⟩ := hcReach
    -- `c ∉ W ∪ F`: latent nodes are neither observed nor fixed.
    have hc_notWF : c ∉ W ∪ F := by
      intro hcWF
      rcases Finset.mem_union.mp hcWF with hcW | hcF
      · exact M.not_obs_of_unobs hc_lat (hW hcW)
      · -- `c ∈ F ⊆ fixed` is `.fixed`-form, but `c ∈ unobserved` is `.random`-form.
        obtain ⟨m, hm⟩ := M.fixed_is_fixed c (hF hcF)
        obtain ⟨k, hk⟩ := M.unobserved_is_random c hc_lat
        rw [hm] at hk
        cases hk
    rcases hcy with hcEqy | hcAv
    · -- Degenerate: `c = y ∈ Y`, but `c` is reachable from `Zr`.
      refine Finset.disjoint_left.mp hdSepZr.2.2.2 ?_ (hcEqy ▸ hyY)
      rw [M.dag.bbReachableVertices_iff_activePath]
      exact ⟨zr, hzrZr, pa, hpa_len, hpa_act, hpa_head, hpa_last⟩
    · -- Build the directed arm `c → … → y` and concatenate.
      obtain ⟨q, hq_len, hq_head, hq_last, hq_edge, hq_int⟩ := hcAv.exists_path
      -- Interior nodes of `q` avoid `W ∪ F`.
      have hq_intWF : ∀ (i : ℕ) (hi : i + 2 < q.length),
          q.get ⟨i + 1, by omega⟩ ∉ W ∪ F := by
        intro i hi hmem
        rcases Finset.mem_union.mp hmem with hmW | hmF
        · -- `q[i+1] ∈ W ⊆ Zr ∪ W`, contradicting interior-avoidance.
          exact hq_int i hi (Finset.mem_union_right _ hmW)
        · -- `q[i+1] ∈ F ⊆ fixed`, but it has an incoming edge, so it is not a root.
          have hedge : M.dag.edge (q.get ⟨i, by omega⟩) (q.get ⟨i + 1, by omega⟩) :=
            hq_edge i (by omega)
          have hpar : q.get ⟨i, by omega⟩ ∈ M.dag.parents (q.get ⟨i + 1, by omega⟩) :=
            M.dag.mem_parents.mpr hedge
          have hroot : M.dag.parents (q.get ⟨i + 1, by omega⟩) = ∅ :=
            M.fixed_are_roots _ (hF hmF)
          rw [hroot] at hpar
          exact absurd hpar (Finset.notMem_empty _)
      -- Concatenate via the public active-path extension lemma.
      have hyReach : y ∈ M.dag.bbReachableVertices (W ∪ F) ({zr} : Finset (SWIGNode N)) :=
        M.dag.bbReachable_extend_directed_arm hpa_len hpa_head hpa_last hpa_act
          hq_len hq_head hq_last hq_edge hq_intWF hc_notWF
      have hyReachZr : y ∈ M.dag.bbReachableVertices (W ∪ F) Zr :=
        M.dag.bbReachableVertices_mono_source
          (Finset.singleton_subset_iff.mpr hzrZr) hyReach
      exact Finset.disjoint_left.mp hdSepZr.2.2.2 hyReachZr hyY

-- ============================================================
-- § 2. Cross-model variant: separation in `fixSet Z` ⟹ cutset separation
-- ============================================================

section CrossModel

variable (M : Causalean.SCM N Ω) (Z : Finset N)
  (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M.observed)
  (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M.fixed)

/-- In `M.fixSet Z _ _`, the node `.random D` (`D ∈ Z`) has no outgoing edges.
    (Local re-derivation, avoiding the heavy kernel imports.) -/
private lemma fixSetRandomNoChildren {D : N} (hD : D ∈ Z) (v : SWIGNode N) :
    ¬ (M.fixSet Z hZ_obs hZ_fixed).dag.edge (SWIGNode.random D) v := by
  intro hEdge
  have h_eqrel :
      (M.fixSet Z hZ_obs hZ_fixed).dag.edge (SWIGNode.random D) v ↔
        SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge Z (SWIGNode.random D) v := by
    simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
  rw [h_eqrel] at hEdge
  simp only [SWIGGraph.splitMonoEdgeRel, if_pos hD] at hEdge

/-- **Edge survival into `fixSet Z`.**  Any base-graph edge `u → v` whose source `u`
    is not a treatment node `.random D` (`D ∈ Z`) survives in `M.fixSet Z _ _`.
    The only edges deleted by `fixSet Z` are the out-edges of the `.random D`
    nodes (`D ∈ Z`); the `.fixed D` (`D ∈ Z`) nodes are isolated roots in `M`, so
    they contribute no base edges. -/
private lemma edge_fixSet_of_edge {u v : SWIGNode N}
    (he : M.dag.edge u v) (hu : ∀ D ∈ Z, u ≠ SWIGNode.random D) :
    (M.fixSet Z hZ_obs hZ_fixed).dag.edge u v := by
  have h_eqrel :
      (M.fixSet Z hZ_obs hZ_fixed).dag.edge u v ↔
        SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge Z u v := by
    simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
  rw [h_eqrel]
  cases u with
  | random u' =>
    by_cases h : u' ∈ Z
    · exact absurd rfl (hu u' h)
    · simpa only [SWIGGraph.splitMonoEdgeRel, if_neg h] using he
  | fixed d =>
    by_cases h : d ∈ Z
    · -- `.fixed d` (`d ∈ Z`) is isolated in `M` (`hZ_fixed`), so `he` is impossible.
      have hfix_notin : SWIGNode.fixed d ∉ M.fixed := hZ_fixed d h
      have hiso := (M.fixed_outside_fixed_isolated d hfix_notin).2
      have hch : v ∈ M.dag.children (SWIGNode.fixed d) := M.dag.mem_children.mpr he
      rw [hiso] at hch
      exact absurd hch (Finset.notMem_empty _)
    · simpa only [SWIGGraph.splitMonoEdgeRel, if_neg h] using he

/-- **Reverse edge transport.**  Any edge `u → v` of `M.fixSet Z _ _` is either a
    base-graph edge `u → v`, or `u = .fixed D` (`D ∈ Z`) with base edge
    `.random D → v` (the redirected out-edge). -/
private lemma edge_of_edge_fixSet {u v : SWIGNode N}
    (he : (M.fixSet Z hZ_obs hZ_fixed).dag.edge u v) :
    M.dag.edge u v ∨
      (∃ D ∈ Z, u = SWIGNode.fixed D ∧ M.dag.edge (SWIGNode.random D) v) := by
  have h_eqrel :
      (M.fixSet Z hZ_obs hZ_fixed).dag.edge u v ↔
        SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge Z u v := by
    simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
  rw [h_eqrel] at he
  cases u with
  | random u' =>
    by_cases h : u' ∈ Z
    · simp only [SWIGGraph.splitMonoEdgeRel, if_pos h] at he
    · exact Or.inl (by simpa only [SWIGGraph.splitMonoEdgeRel, if_neg h] using he)
  | fixed d =>
    by_cases h : d ∈ Z
    · exact Or.inr ⟨d, h, rfl, by simpa only [SWIGGraph.splitMonoEdgeRel, if_pos h] using he⟩
    · exact Or.inl (by simpa only [SWIGGraph.splitMonoEdgeRel, if_neg h] using he)

/-- **Ancestry survival into `fixSet Z`, under a no-treatment hypothesis.**
    A base-graph directed path `u ⤳ v` whose edge sources are all non-treatment
    (`hNoT`: every `s` that is `u` or a proper ancestor of `v` reachable from `u`,
    and itself an ancestor of `v`, is not `.random D` for `D ∈ Z`) is a directed
    path in `M.fixSet Z _ _` as well: `u` is an ancestor of `v` in the split graph. -/
private lemma isAncestor_fixSet_of_isAncestor {u v : SWIGNode N}
    (hanc : M.dag.isAncestor u v)
    (hNoT : ∀ s, (s = u ∨ M.dag.isAncestor u s) → M.dag.isAncestor s v →
      ∀ D ∈ Z, s ≠ SWIGNode.random D) :
    (M.fixSet Z hZ_obs hZ_fixed).dag.isAncestor u v := by
  induction hanc with
  | @edge b he =>
    exact DAG.isAncestor.edge
      (edge_fixSet_of_edge M Z hZ_obs hZ_fixed he
        (hNoT u (Or.inl rfl) (DAG.isAncestor.edge he)))
  | @trans w b hrec he ih =>
    -- `u ⤳ w → b`.  The last edge source `w` is `u` or a proper ancestor of `b`
    -- reachable from `u`, and an ancestor of `b`; so `hNoT` gives `w` non-treatment.
    have hwNoT : ∀ D ∈ Z, w ≠ SWIGNode.random D :=
      hNoT w (Or.inr hrec) (DAG.isAncestor.edge he)
    refine DAG.isAncestor.trans ?_
      (edge_fixSet_of_edge M Z hZ_obs hZ_fixed he hwNoT)
    refine ih ?_
    intro s hs hsw
    exact hNoT s hs (DAG.isAncestor.trans hsw he)

/-- **A treatment node is never a proper ancestor of a conditioning node**, given
    backdoor criterion (i) `hWNonDescM1` and that the fixed block `M.fixed` consists
    of roots.  Here `C = W ∪ M.fixed`. -/
private lemma treatment_not_isAncestor_cond
    (W : Finset (SWIGNode N))
    (hWNonDescM1 : ∀ D ∈ Z, ∀ w ∈ W, ¬ M.dag.isAncestor (SWIGNode.random D) w)
    {D : N} (hD : D ∈ Z) {c : SWIGNode N} (hc : c ∈ W ∪ M.fixed)
    (hanc : M.dag.isAncestor (SWIGNode.random D) c) : False := by
  rcases Finset.mem_union.mp hc with hcW | hcF
  · exact hWNonDescM1 D hD c hcW hanc
  · -- `c ∈ M.fixed` is a root, hence has no incoming edge: but `· ⤳ c` ends with
    -- an edge `· → c`, contradiction.
    have hpar : ∃ p, M.dag.edge p c := by
      cases hanc with
      | edge he => exact ⟨_, he⟩
      | trans _ he => exact ⟨_, he⟩
    obtain ⟨p, hpc⟩ := hpar
    have hpmem : p ∈ M.dag.parents c := M.dag.mem_parents.mpr hpc
    rw [M.fixed_are_roots c hcF] at hpmem
    exact absurd hpmem (Finset.notMem_empty _)

/-- **Collider-activeness transports into `fixSet Z`.**

    If `m` is in the Bayes-Ball ancestral set of `C = W ∪ M.fixed` in the base
    graph (the activation witness for a collider), then `m` is in the ancestral
    set of `C ∪ Z.image .fixed` in `M.fixSet Z _ _`.  Uses backdoor criterion (i):
    no treatment node is a proper ancestor of any `w ∈ W`. -/
private lemma bbZAncestors_fixSet_transport
    (W : Finset (SWIGNode N))
    (hWNonDescM1 : ∀ D ∈ Z, ∀ w ∈ W, ¬ M.dag.isAncestor (SWIGNode.random D) w)
    {m : SWIGNode N}
    (hm : m ∈ M.dag.bbZAncestors (W ∪ M.fixed)) :
    m ∈ (M.fixSet Z hZ_obs hZ_fixed).dag.bbZAncestors
      (W ∪ M.fixed ∪ Z.image SWIGNode.fixed) := by
  simp only [DAG.bbZAncestors, DAG.ancestralSet, DAG.ancestorsSet,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  rcases hm with hmC | ⟨c, hcC, hanc⟩
  · exact Or.inl (Or.inl hmC)
  · -- `m ⤳ c` in `M`; transport the directed path to `M.fixSet Z`.
    refine Or.inr ⟨c, Or.inl hcC, ?_⟩
    have hcC' : c ∈ W ∪ M.fixed := Finset.mem_union.mpr hcC
    refine isAncestor_fixSet_of_isAncestor M Z hZ_obs hZ_fixed hanc ?_
    intro s _ hsc D hD hsEq
    subst hsEq
    exact treatment_not_isAncestor_cond M Z W hWNonDescM1 hD hcC' hsc

/-- A path node `v` carrying any base-graph incident edge cannot be a treatment
    `.fixed D` (`D ∈ Z`): such nodes are isolated in `M`. -/
private lemma not_fixedTreatment_of_uadj
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M.fixed) {a v : SWIGNode N}
    (h : M.dag.UAdj a v) {D : N} (hD : D ∈ Z) : v ≠ SWIGNode.fixed D := by
  intro hveq
  have hiso := M.fixed_outside_fixed_isolated D (hZ_fixed D hD)
  rw [hveq] at h
  rcases h with hav | hva
  · -- `edge a (fixed D)`: `a` is a parent of `fixed D`, but `fixed D` is a root.
    have hmem : a ∈ M.dag.parents (SWIGNode.fixed D) := M.dag.mem_parents.mpr hav
    rw [hiso.1] at hmem; exact absurd hmem (Finset.notMem_empty _)
  · -- `edge (fixed D) a`: `a` is a child of `fixed D`, but `fixed D` is isolated.
    have hmem : a ∈ M.dag.children (SWIGNode.fixed D) := M.dag.mem_children.mpr hva
    rw [hiso.2] at hmem; exact absurd hmem (Finset.notMem_empty _)

/-- **Active-path transport into `fixSet Z`.**

    An `M`-active path `P` given `C = W ∪ M.fixed` whose every step's underlying
    base edge has a non-treatment source (`hInEdge`) is active in `M.fixSet Z _ _`
    given `C ∪ Z.image .fixed`.  The collider activations transport by
    `bbZAncestors_fixSet_transport` (using backdoor criterion (i)); the
    non-collider conditions transport because path nodes are never the treatment
    roots `.fixed D` adjoined to the conditioning set. -/
private lemma path_fixSet_active
    (W : Finset (SWIGNode N))
    (hWNonDescM1 : ∀ D ∈ Z, ∀ w ∈ W, ¬ M.dag.isAncestor (SWIGNode.random D) w)
    {P : List (SWIGNode N)}
    (hact : M.dag.IsActivePath (W ∪ M.fixed) P)
    (hInEdge : ∀ (i : ℕ) (hi : i + 1 < P.length),
      (M.dag.edge (P.get ⟨i, by omega⟩) (P.get ⟨i + 1, hi⟩) →
        ∀ D ∈ Z, P.get ⟨i, by omega⟩ ≠ SWIGNode.random D) ∧
      (M.dag.edge (P.get ⟨i + 1, hi⟩) (P.get ⟨i, by omega⟩) →
        ∀ D ∈ Z, P.get ⟨i + 1, hi⟩ ≠ SWIGNode.random D)) :
    (M.fixSet Z hZ_obs hZ_fixed).dag.IsActivePath
      (W ∪ M.fixed ∪ Z.image SWIGNode.fixed) P := by
  obtain ⟨hadj, hcoll⟩ := hact
  set M2 := M.fixSet Z hZ_obs hZ_fixed with hM2
  -- Adjacency survives.
  have hadj2 : ∀ (i : ℕ) (hi : i + 1 < P.length),
      M2.dag.UAdj (P.get ⟨i, by omega⟩) (P.get ⟨i + 1, hi⟩) := by
    intro i hi
    rcases hadj i hi with he | he
    · exact Or.inl (edge_fixSet_of_edge M Z hZ_obs hZ_fixed he ((hInEdge i hi).1 he))
    · exact Or.inr (edge_fixSet_of_edge M Z hZ_obs hZ_fixed he ((hInEdge i hi).2 he))
  refine ⟨hadj2, fun i hi => ?_⟩
  -- The triple (l, m, r) at index i.
  set l := P.get ⟨i, by omega⟩ with hl
  set m := P.get ⟨i + 1, by omega⟩ with hm
  set r := P.get ⟨i + 2, hi⟩ with hr
  have hc := hcoll i hi
  simp only at hc ⊢
  -- M2-collider ↔ M1-collider on the path triple.
  have hColl_iff : M2.dag.IsCollider l m r ↔ M.dag.IsCollider l m r := by
    constructor
    · rintro ⟨hlm, hrm⟩
      refine ⟨?_, ?_⟩
      · rcases edge_of_edge_fixSet M Z hZ_obs hZ_fixed hlm with h | ⟨D, hD, hlEq, _⟩
        · exact h
        · -- `l = .fixed D` (D ∈ Z) is impossible: `l` is path-adjacent to `m`.
          exact absurd hlEq
            (not_fixedTreatment_of_uadj M Z hZ_fixed (M.dag.UAdj_symm (hadj i (by omega))) hD)
      · rcases edge_of_edge_fixSet M Z hZ_obs hZ_fixed hrm with h | ⟨D, hD, hrEq, _⟩
        · exact h
        · have hadj_mr : M.dag.UAdj m r := hadj (i + 1) (by omega)
          exact absurd hrEq (not_fixedTreatment_of_uadj M Z hZ_fixed hadj_mr hD)
    · rintro ⟨hlm, hrm⟩
      exact ⟨edge_fixSet_of_edge M Z hZ_obs hZ_fixed hlm ((hInEdge i (by omega)).1 hlm),
        edge_fixSet_of_edge M Z hZ_obs hZ_fixed hrm ((hInEdge (i + 1) (by omega)).2 hrm)⟩
  by_cases hC : M.dag.IsCollider l m r
  · rw [if_pos (hColl_iff.mpr hC)]
    rw [if_pos hC] at hc
    exact bbZAncestors_fixSet_transport M Z hZ_obs hZ_fixed W hWNonDescM1 hc
  · rw [if_neg (fun h => hC (hColl_iff.mp h))]
    rw [if_neg hC] at hc
    -- `m ∉ W ∪ M.fixed`; also `m ∉ Z.image .fixed` since `m` is on the path.
    intro hmem
    rcases Finset.mem_union.mp hmem with hm1 | hm2
    · exact hc hm1
    · obtain ⟨D, hD, hDeq⟩ := Finset.mem_image.mp hm2
      exact not_fixedTreatment_of_uadj M Z hZ_fixed (hadj i (by omega)) hD (hm ▸ hDeq.symm)

/-- **No forward run from a non-ancestor source.**

    Pure-graph helper.  Let `prev :: m :: rest` be an active path given `C`, with a
    forward edge `prev → m` entering the run, and assume `s` is an ancestor of `prev`
    (or `s = prev`).  If the run's last node is a root (no incoming edge) and `s` is
    never a proper ancestor of any node of `bbZAncestors C` (`hTreat`), then we reach a
    contradiction: the forward chain out of `s` must either hit the root (impossible —
    roots have no incoming edge) or open a collider apex `m'` with `s ⤳ m' ∈
    bbZAncestors C` (contradicting `hTreat`). -/
private lemma activePath_forwardRun_absurd {V : Type*} [DecidableEq V] [Fintype V]
    (G : DAG V) {C : Finset V} {s : V}
    (hTreat : ∀ k, k ∈ G.bbZAncestors C → ¬ G.isAncestor s k) :
    ∀ (prev m : V) (rest : List V),
      G.IsActivePath C (prev :: m :: rest) →
      G.edge prev m →
      (s = prev ∨ G.isAncestor s prev) →
      (∀ p, ¬ G.edge p ((prev :: m :: rest).getLast (by simp))) →
      False := by
  intro prev m rest
  induction rest generalizing prev m with
  | nil =>
    intro hact hpm _hsprev hroot
    -- The run is `[prev, m]`; `m` is the last node and a root, but `prev → m`.
    exact hroot prev (by simpa using hpm)
  | cons t rest ih =>
    intro hact hpm hsprev hroot
    -- `s ⤳ m` from `s ⤳ prev → m`.
    have hsm : G.isAncestor s m := by
      rcases hsprev with hEq | hanc
      · exact hEq ▸ DAG.isAncestor.edge hpm
      · exact DAG.isAncestor.trans hanc hpm
    obtain ⟨hadj, hcoll⟩ := hact
    -- Adjacency of `m` and `t` (triple index 0 in the path).
    have hmt : G.UAdj m t := by
      have h := hadj 1 (by simp)
      simpa using h
    -- The active-path triple condition at index 0: triple (prev, m, t).
    have htri := hcoll 0 (by simp)
    simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ] at htri
    rcases hmt with hmt | htm
    · -- Forward `m → t`: recurse with `prev := m`, dropping `prev`.
      -- The tail `m :: t :: rest` is active.
      have hact_tail : G.IsActivePath C (m :: t :: rest) := by
        refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · have h := hadj (i + 1) (by simpa [Nat.add_assoc] using Nat.succ_lt_succ hi)
          simpa using h
        · have h := hcoll (i + 1) (by simpa [Nat.add_assoc] using Nat.succ_lt_succ hi)
          simpa [Nat.add_assoc] using h
      have hroot' : ∀ p, ¬ G.edge p ((m :: t :: rest).getLast (by simp)) := by
        simpa using hroot
      exact ih m t hact_tail hmt (Or.inr hsm) hroot'
    · -- Backward `t → m`: `m` is a collider on the triple `(prev, m, t)`.
      have hC : G.IsCollider prev m t := ⟨hpm, htm⟩
      rw [if_pos hC] at htri
      -- `htri : m ∈ bbZAncestors C`; but `s ⤳ m`.
      exact hTreat m htri hsm

/-- A suffix `p.drop j` of an active path is active. -/
private lemma isActivePath_drop {V : Type*} [DecidableEq V] [Fintype V]
    (G : DAG V) {C : Finset V} {p : List V} (j : ℕ)
    (hact : G.IsActivePath C p) : G.IsActivePath C (p.drop j) := by
  obtain ⟨hadj, hcoll⟩ := hact
  have hlen : (p.drop j).length = p.length - j := List.length_drop ..
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hi' : j + i + 1 < p.length := by rw [hlen] at hi; omega
    have e0 : (p.drop j).get ⟨i, by omega⟩ = p.get ⟨j + i, by omega⟩ := by
      simp [List.getElem_drop]
    have e1 : (p.drop j).get ⟨i + 1, hi⟩ = p.get ⟨j + (i + 1), by omega⟩ := by
      simp [List.getElem_drop]
    rw [e0, e1]
    have := hadj (j + i) (by omega)
    convert this using 2
  · have hi' : j + i + 2 < p.length := by rw [hlen] at hi; omega
    have e0 : (p.drop j).get ⟨i, by omega⟩ = p.get ⟨j + i, by omega⟩ := by
      simp [List.getElem_drop]
    have e1 : (p.drop j).get ⟨i + 1, by omega⟩ = p.get ⟨j + (i + 1), by omega⟩ := by
      simp [List.getElem_drop]
    have e2 : (p.drop j).get ⟨i + 2, hi⟩ = p.get ⟨j + (i + 2), by omega⟩ := by
      simp [List.getElem_drop]
    rw [e0, e1, e2]
    have := hcoll (j + i) (by omega)
    convert this using 2
  /- (`convert … using 2` aligns the `Fin` index arithmetic `j + (i+k)` with
      `(j+i)+k`.) -/

/-- Index translation for the join `pa ++ q.tail` (with `q.head = pa.getLast`).
    Left part reads from `pa`; right part reads from `q` shifted by one. -/
private lemma get_appendTail {V : Type*} (pa q : List V)
    (_hpa : pa ≠ []) (hq : q ≠ []) :
    (pa ++ q.tail).length = pa.length + q.length - 1 ∧
    (∀ (j : ℕ) (hj : j < pa.length),
      (pa ++ q.tail).get ⟨j, by
        rw [List.length_append]; have := List.length_tail (l := q); omega⟩ = pa.get ⟨j, hj⟩) ∧
    (∀ (j : ℕ) (hjL : pa.length ≤ j) (hj : j < (pa ++ q.tail).length),
      (pa ++ q.tail).get ⟨j, hj⟩ =
        q.get ⟨j - pa.length + 1, by
          rw [List.length_append, List.length_tail] at hj
          have : 1 ≤ q.length := List.length_pos_iff.mpr hq
          omega⟩) := by
  have htail_len : q.tail.length = q.length - 1 := List.length_tail
  have hqpos : 1 ≤ q.length := List.length_pos_iff.mpr hq
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append, htail_len]; omega
  · intro j hj
    simp only [List.get_eq_getElem, List.getElem_append_left (h := hj)]
  · intro j hjL hj
    have hjr : j - pa.length < q.tail.length := by
      rw [List.length_append] at hj; omega
    have e1 : (pa ++ q.tail).get ⟨j, hj⟩ = q.tail[j - pa.length]'hjr := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
    rw [e1, List.getElem_tail]
    simp [List.get_eq_getElem]

include hZ_obs in
/-- **Existence of an in-edge active path to `Y` from a reachable cutset node.**

    The genuine graph content of `cutsetLatent_dSep_of_fixSet_dSep`.  Assume a latent
    cutset node `c` for `Y` (avoiding `Zr ∪ W`, where `Zr = Z.image .random`) is
    Bayes-Ball reachable from `Zr` given `C = W ∪ M.fixed`.  Then there is an
    `M`-active path from `Zr` to `Y` given `C` along which **no treatment out-edge
    `random D → ·` (`D ∈ Z`) is traversed** (the in-edge property `hInEdge` consumed
    by `path_fixSet_active`).

    Why true: concatenate the active arm `Zr ⤳ c` with the directed cutset arm
    `c → … → y`.  The join node `c` is a *latent root*, hence a fork (both incident path
    edges leave `c`); a treatment out-edge would start a forward directed chain that
    (i) cannot cross the root fork `c`, and (ii) cannot terminate at an opened
    collider — by backdoor criterion (i) that collider would force a treatment node
    to be an ancestor of some `w ∈ W` (or of a fixed root).  Minimising the path
    length pins any residual treatment out-edge to the `Zr`-endpoint, where the same
    chain argument applies.  (The detailed minimal-path/fork bookkeeping is isolated
    here.) -/
private lemma exists_inEdge_activePath_to_Y
    (Y W : Finset (SWIGNode N))
    (hW : W ⊆ M.observed)
    (hWNonDescM1 : ∀ D ∈ Z, ∀ w ∈ W,
      ¬ M.dag.isAncestor (SWIGNode.random D) w)
    {c : SWIGNode N}
    (hc_cut : c ∈ M.cutsetLatent Y (Z.image SWIGNode.random ∪ W))
    (hc_reach : c ∈ M.dag.bbReachableVertices (W ∪ M.fixed)
      (Z.image SWIGNode.random)) :
    ∃ P : List (SWIGNode N),
      P.length ≥ 2 ∧
      M.dag.IsActivePath (W ∪ M.fixed) P ∧
      P.head? ∈ (Z.image SWIGNode.random).image some ∧
      P.getLast? ∈ Y.image some ∧
      (∀ (i : ℕ) (hi : i + 1 < P.length),
        (M.dag.edge (P.get ⟨i, by omega⟩) (P.get ⟨i + 1, hi⟩) →
          ∀ D ∈ Z, P.get ⟨i, by omega⟩ ≠ SWIGNode.random D) ∧
        (M.dag.edge (P.get ⟨i + 1, hi⟩) (P.get ⟨i, by omega⟩) →
          ∀ D ∈ Z, P.get ⟨i + 1, hi⟩ ≠ SWIGNode.random D)) := by
  classical
  set Zr := Z.image SWIGNode.random with hZr
  set C := W ∪ M.fixed with hC
  -- (1) No treatment node is a proper ancestor of any node in `bbZAncestors C`.
  have hTreatAll : ∀ {D : N}, D ∈ Z → ∀ k, k ∈ M.dag.bbZAncestors C →
      ¬ M.dag.isAncestor (SWIGNode.random D) k := by
    intro D hD k hk hanc
    rw [DAG.bbZAncestors, DAG.ancestralSet, Finset.mem_union] at hk
    rcases hk with hkC | hkAnc
    · exact treatment_not_isAncestor_cond M Z W hWNonDescM1 hD hkC hanc
    · rw [DAG.ancestorsSet, Finset.mem_filter] at hkAnc
      obtain ⟨c', hc'C, hkc'⟩ := hkAnc.2
      exact treatment_not_isAncestor_cond M Z W hWNonDescM1 hD hc'C
        (M.dag.isAncestor_trans hanc hkc')
  -- (2) Unpack cutset membership: `c` is latent, and reaches `Y`.
  rcases (M.mem_cutsetLatent.mp hc_cut) with ⟨hc_lat, y, hyY, hcy⟩
  have hc_root : ∀ p, ¬ M.dag.edge p c := by
    intro p hp
    have hmem : p ∈ M.dag.parents c := M.dag.mem_parents.mpr hp
    rw [M.unobs_are_roots c hc_lat] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  have hc_notC : c ∉ C := by
    rw [hC]; intro hcC
    rcases Finset.mem_union.mp hcC with hcW | hcF
    · exact M.not_obs_of_unobs hc_lat (hW hcW)
    · obtain ⟨m, hm⟩ := M.fixed_is_fixed c hcF
      obtain ⟨k, hk⟩ := M.unobserved_is_random c hc_lat
      rw [hm] at hk; cases hk
  have hc_notZr : c ∉ Zr := by
    rw [hZr]; intro hcZr
    obtain ⟨D, hDZ, hDeq⟩ := Finset.mem_image.mp hcZr
    exact M.not_obs_of_unobs hc_lat (hDeq ▸ hZ_obs D hDZ)
  -- (3) Select a MINIMAL-length active `Zr ⤳ c` path given `C`.
  have hExists : ∃ n, ∃ p : List (SWIGNode N), p.length = n ∧ p.length ≥ 2 ∧
      M.dag.IsActivePath C p ∧ (∃ zr ∈ Zr, p.head? = some zr) ∧ p.getLast? = some c := by
    rw [M.dag.bbReachableVertices_iff_activePath] at hc_reach
    obtain ⟨zr, hzrZr, p, hlen, hact, hhead, hlast⟩ := hc_reach
    exact ⟨p.length, p, rfl, hlen, hact, ⟨zr, hzrZr, hhead⟩, hlast⟩
  set n₀ := Nat.find hExists with hn₀
  obtain ⟨pa, hpa_len_eq, hpa_len, hpa_act, ⟨zr, hzrZr, hpa_head⟩, hpa_last⟩ :=
    Nat.find_spec hExists
  -- Minimality: no node `pa[j]` with `j ≥ 1` lies in `Zr`.
  have hZrOnly0 : ∀ (j : ℕ) (hj : j < pa.length), 1 ≤ j → pa.get ⟨j, hj⟩ ∉ Zr := by
    intro j hj hj1 hjZr
    -- `pa.drop j` is a shorter active `Zr ⤳ c` path.
    have hdrop_act : M.dag.IsActivePath C (pa.drop j) := isActivePath_drop M.dag j hpa_act
    have hdrop_len : (pa.drop j).length = pa.length - j := List.length_drop ..
    have hdrop_ge2 : (pa.drop j).length ≥ 2 := by
      rw [hdrop_len]
      -- `c` is the last node and `pa[j] ∈ Zr ≠ c`, so `j < pa.length - 1`.
      by_contra hlt
      push_neg at hlt
      interval_cases h : (pa.length - j)
      · omega
      · -- `pa.drop j = [pa[j]]`, so `pa[j] = c`; but `c ∉ Zr`.
        have hjlast : j = pa.length - 1 := by omega
        have hjc : pa.get ⟨j, hj⟩ = c := by
          have hne : pa ≠ [] := by intro h; rw [h] at hpa_len; simp at hpa_len
          have hgl := List.getLast?_eq_some_getLast hne
          rw [hpa_last] at hgl
          have hgc : pa.getLast hne = c := Option.some_inj.mp hgl.symm
          rw [List.get_eq_getElem]
          rw [List.getLast_eq_getElem hne] at hgc
          rw [← hgc]; congr 1
        rw [hjc] at hjZr; exact hc_notZr hjZr
    have hdrop_head : (pa.drop j).head? = some (pa.get ⟨j, hj⟩) := by
      have hne : (pa.drop j) ≠ [] := by
        rw [← List.length_pos_iff]; omega
      rw [List.head?_eq_some_head hne]
      congr 1
      rw [List.head_drop, List.get_eq_getElem]
    have hdrop_last : (pa.drop j).getLast? = some c := by
      have hne : (pa.drop j) ≠ [] := by rw [← List.length_pos_iff]; omega
      have hpne : pa ≠ [] := by intro h; rw [h] at hpa_len; simp at hpa_len
      rw [List.getLast?_eq_some_getLast hne, List.getLast_drop]
      rw [List.getLast?_eq_some_getLast hpne] at hpa_last
      exact hpa_last
    have hlt_n : (pa.drop j).length < n₀ := by
      rw [hdrop_len, hpa_len_eq]; omega
    exact Nat.find_min hExists hlt_n
      ⟨pa.drop j, rfl, hdrop_ge2, hdrop_act, ⟨_, hjZr, hdrop_head⟩, hdrop_last⟩
  -- Decompose `pa = a :: b :: rest`.
  obtain ⟨a, pa', rfl⟩ := List.exists_cons_of_ne_nil
    (show pa ≠ [] by intro h; rw [h] at hpa_len; simp at hpa_len)
  obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil
    (show pa' ≠ [] by intro h; rw [h] at hpa_len; simp at hpa_len)
  -- `pa[0] = a`, its forward out-edge starts a run to the root `c`: forbidden if `a` treats.
  have ha_notTreat : ∀ D ∈ Z, M.dag.edge a b → a ≠ SWIGNode.random D := by
    intro D hD hab heq
    have hpa_last' : (a :: b :: rest).getLast (by simp) = c := by
      have hne : (a :: b :: rest) ≠ [] := by simp
      have hgl := List.getLast?_eq_some_getLast hne
      rw [hpa_last] at hgl
      exact Option.some_inj.mp hgl.symm
    refine activePath_forwardRun_absurd M.dag (hTreatAll hD) a b rest hpa_act
      hab (Or.inl heq.symm) ?_
    rw [hpa_last']; exact hc_root
  -- In-edge property for `pa` (the whole path), via minimality + the root run.
  have hPaInEdge : ∀ (i : ℕ) (hi : i + 1 < (a :: b :: rest).length),
      (M.dag.edge ((a :: b :: rest).get ⟨i, by omega⟩) ((a :: b :: rest).get ⟨i + 1, hi⟩) →
        ∀ D ∈ Z, (a :: b :: rest).get ⟨i, by omega⟩ ≠ SWIGNode.random D) ∧
      (M.dag.edge ((a :: b :: rest).get ⟨i + 1, hi⟩) ((a :: b :: rest).get ⟨i, by omega⟩) →
        ∀ D ∈ Z, (a :: b :: rest).get ⟨i + 1, hi⟩ ≠ SWIGNode.random D) := by
    intro i hi
    refine ⟨fun hedge D hD heq => ?_, fun hedge D hD heq => ?_⟩
    · -- Forward source `pa[i] = random D`.
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · -- `i = 0`: handled by the root run.
        subst hi0
        simp only [List.get_eq_getElem, List.getElem_cons_zero,
          List.getElem_cons_succ] at hedge heq
        exact ha_notTreat D hD hedge heq
      · -- `i ≥ 1`: `pa[i] ∈ Zr` contradicts minimality.
        exact hZrOnly0 i (by omega) (by omega)
          (by rw [hZr, heq]; exact Finset.mem_image.mpr ⟨D, hD, rfl⟩)
    · -- Backward source `pa[i+1] = random D`, with `i+1 ≥ 1`: contradicts minimality.
      exact hZrOnly0 (i + 1) hi (by omega)
        (by rw [hZr, heq]; exact Finset.mem_image.mpr ⟨D, hD, rfl⟩)
  set pa := a :: b :: rest with hpa_def
  -- Head of `pa` is `zr ∈ Zr`.
  have hpa_head' : pa.head? = some zr := hpa_head
  rcases hcy with hcEqy | hcAv
  · -- DEGENERATE: `c = y ∈ Y`.  Take `P := pa`.
    refine ⟨pa, hpa_len, hpa_act, ?_, ?_, hPaInEdge⟩
    · rw [hpa_head']; exact Finset.mem_image.mpr ⟨zr, hzrZr, rfl⟩
    · rw [hpa_last]; exact Finset.mem_image.mpr ⟨y, hyY, congrArg some hcEqy.symm⟩
  · -- GENERIC: concatenate with the directed cutset arm `c ⤳ y`.
    obtain ⟨q, hq_len, hq_head, hq_last, hq_edge, hq_int⟩ := hcAv.exists_path
    -- Interior nodes of `q` avoid `C = W ∪ M.fixed` and `Zr`.
    have hq_intC : ∀ (i : ℕ) (hi : i + 2 < q.length), q.get ⟨i + 1, by omega⟩ ∉ C := by
      intro i hi hmem
      rw [hC] at hmem
      rcases Finset.mem_union.mp hmem with hmW | hmF
      · exact hq_int i hi (Finset.mem_union_right _ hmW)
      · -- Interior nodes have an incoming edge, so they are not fixed roots.
        have hedge : M.dag.edge (q.get ⟨i, by omega⟩) (q.get ⟨i + 1, by omega⟩) :=
          hq_edge i (by omega)
        have hpar : q.get ⟨i, by omega⟩ ∈ M.dag.parents (q.get ⟨i + 1, by omega⟩) :=
          M.dag.mem_parents.mpr hedge
        rw [M.fixed_are_roots _ hmF] at hpar
        exact absurd hpar (Finset.notMem_empty _)
    have hq_intZr : ∀ (i : ℕ) (hi : i + 2 < q.length), q.get ⟨i + 1, by omega⟩ ∉ Zr := by
      intro i hi hmem
      exact hq_int i hi (Finset.mem_union_left _ hmem)
    -- `q` is active given `C`.
    have hq_act : M.dag.IsActivePath C q :=
      M.dag.isActivePath_of_directed_interior hq_edge hq_intC
    -- The join point: first edge of `q` points out of `c`.
    have hqne : q ≠ [] := by intro h; rw [h] at hq_len; simp at hq_len
    have hq_head_eq : q.get ⟨0, by omega⟩ = c := by
      have h := List.head?_eq_some_head hqne
      rw [hq_head] at h
      rw [List.get_eq_getElem, List.getElem_zero]
      exact Option.some_inj.mp h.symm
    have hseam_out : M.dag.edge c (q.get ⟨1, by omega⟩) := by
      have he := hq_edge 0 (by omega)
      rwa [hq_head_eq] at he
    -- Concatenate.
    obtain ⟨hP_len, hP_head, hP_last, hP_act⟩ :=
      M.dag.chain_join_active hpa_len hpa_head' hpa_last hpa_act hq_len hq_head hq_last
        hq_act hseam_out hc_notC
    refine ⟨pa ++ q.tail, hP_len, hP_act, ?_, ?_, ?_⟩
    · rw [hP_head]; exact Finset.mem_image.mpr ⟨zr, hzrZr, rfl⟩
    · rw [hP_last]; exact Finset.mem_image.mpr ⟨y, hyY, rfl⟩
    · -- In-edge property for `P = pa ++ q.tail`.
      have hpa_ne : pa ≠ [] := by rw [hpa_def]; simp
      obtain ⟨hPlen_eq, hP_L, hP_R⟩ := get_appendTail pa q hpa_ne hqne
      have hqlen2 : 2 ≤ q.length := hq_len
      have hPlen' : (pa ++ q.tail).length = pa.length + q.length - 1 := hPlen_eq
      -- Every strict-interior node of `P` avoids `Zr`.
      have hP_notZr : ∀ (j : ℕ) (hj : j < (pa ++ q.tail).length),
          1 ≤ j → j + 1 < (pa ++ q.tail).length →
          (pa ++ q.tail).get ⟨j, hj⟩ ∉ Zr := by
        intro j hj hj1 hjlast
        by_cases hjR : j < pa.length
        · rw [hP_L j hjR]; exact hZrOnly0 j hjR hj1
        · push_neg at hjR
          rw [hP_R j hjR hj]
          -- `q`-index `idx = j - R + 1`, with `1 ≤ idx ≤ q.length - 2` (interior).
          have hidx_ge : 1 ≤ j - pa.length + 1 := by omega
          have hidx_lt : j - pa.length + 1 + 1 < q.length := by
            rw [hPlen'] at hjlast; omega
          -- Express as `q.get ⟨(j - R) + 1, _⟩` and apply `hq_intZr` at `i = j - R`.
          have := hq_intZr (j - pa.length) (by omega)
          convert this using 2
      -- The last edge of `P` points into `y` (forward), via `q`'s last edge.
      have hP_lastEdge :
          M.dag.edge ((pa ++ q.tail).get ⟨(pa ++ q.tail).length - 2, by omega⟩)
            ((pa ++ q.tail).get ⟨(pa ++ q.tail).length - 1, by omega⟩) := by
        -- The last node `P[last] = q[qlen-1] = y`.
        have hLast1 : (pa ++ q.tail).get ⟨(pa ++ q.tail).length - 1, by omega⟩
            = q.get ⟨q.length - 1, by omega⟩ := by
          rw [hP_R _ (by omega) (by omega)]
          have hidx : (pa ++ q.tail).length - 1 - pa.length + 1 = q.length - 1 := by omega
          exact congrArg _ (Fin.ext hidx)
        -- The penultimate node `P[last-1] = q[qlen-2]`, via the q-part (qlen ≥ 3)
        -- or the join node `c = pa.getLast` (qlen = 2).
        have hLast2 : (pa ++ q.tail).get ⟨(pa ++ q.tail).length - 2, by omega⟩
            = q.get ⟨q.length - 2, by omega⟩ := by
          by_cases hq2 : pa.length ≤ (pa ++ q.tail).length - 2
          · rw [hP_R _ hq2 (by omega)]
            have hidx : (pa ++ q.tail).length - 2 - pa.length + 1 = q.length - 2 := by omega
            exact congrArg _ (Fin.ext hidx)
          · push_neg at hq2
            -- `q.length = 2`, so `P[last-1] = pa.getLast = c = q[0] = q[qlen-2]`.
            rw [hP_L _ hq2]
            have hpa_get_last : pa.get ⟨(pa ++ q.tail).length - 2, hq2⟩ = c := by
              have hgl := List.getLast?_eq_some_getLast hpa_ne
              rw [hpa_last] at hgl
              have hgc : pa.getLast hpa_ne = c := Option.some_inj.mp hgl.symm
              rw [List.get_eq_getElem]
              rw [List.getLast_eq_getElem hpa_ne] at hgc
              rw [← hgc]
              have hidx : ((pa ++ q.tail).length - 2 : ℕ) = pa.length - 1 := by omega
              exact congrArg _ (Fin.ext hidx)
            rw [hpa_get_last]
            have hidx : (0 : ℕ) = q.length - 2 := by omega
            exact hq_head_eq.symm.trans (congrArg _ (Fin.ext hidx))
        rw [hLast1, hLast2]
        have hedge := hq_edge (q.length - 2) (by omega)
        have hidx : (q.length - 2 + 1 : ℕ) = q.length - 1 := by omega
        rw [show (⟨q.length - 2 + 1, by omega⟩ : Fin q.length)
            = ⟨q.length - 1, by omega⟩ from Fin.ext hidx] at hedge
        exact hedge
      -- Assemble.
      intro i hi
      refine ⟨fun hedge D hD heq => ?_, fun hedge D hD heq => ?_⟩
      · -- Forward source `P[i] = random D`.
        rcases Nat.eq_zero_or_pos i with hi0 | hi0
        · -- `i = 0`: `P[0] = a`, `P[1] = b`.
          subst hi0
          rw [hP_L 0 (by omega)] at hedge heq
          rw [hP_L 1 (by omega)] at hedge
          simp only [List.get_eq_getElem] at heq hedge
          exact ha_notTreat D hD hedge heq
        · -- `i ≥ 1`, and `i < P.length - 1` since `i + 1 < P.length`.
          exact hP_notZr i (by omega) (by omega) (by omega)
            (by rw [heq]; exact Finset.mem_image.mpr ⟨D, hD, rfl⟩)
      · -- Backward source `P[i+1] = random D`.
        by_cases hlast : i + 1 + 1 < (pa ++ q.tail).length
        · -- `P[i+1]` is strict interior.
          exact hP_notZr (i + 1) hi (by omega) hlast
            (by rw [heq]; exact Finset.mem_image.mpr ⟨D, hD, rfl⟩)
        · -- `i + 1 = P.length - 1`: the actual last edge is forward into `y`.
          push_neg at hlast
          have hi_eq : i = (pa ++ q.tail).length - 2 := by omega
          have hi1_eq : i + 1 = (pa ++ q.tail).length - 1 := by omega
          -- `hedge : edge P[i+1] P[i]` contradicts the forward last edge `P[i] → P[i+1]`.
          apply M.dag.asymm hedge
          have e0 : (⟨i, by omega⟩ : Fin (pa ++ q.tail).length)
              = ⟨(pa ++ q.tail).length - 2, by omega⟩ := Fin.ext hi_eq
          have e1 : (⟨i + 1, hi⟩ : Fin (pa ++ q.tail).length)
              = ⟨(pa ++ q.tail).length - 1, by omega⟩ := Fin.ext hi1_eq
          rw [e0, e1]; exact hP_lastEdge

/-- **Cross-model concatenation d-separation for the latent cutset.**

    Suppose, in the intervened model `M.fixSet Z _ _`, the target set `Y` is
    d-separated from the randomised do-block `Zr = Z.image .random` given the
    adjustment block `W` together with the post-intervention fixed block.  Assume
    backdoor criterion (i) for `W`: no `w ∈ W` is a descendant of any treatment
    node `.random D` (`D ∈ Z`) in the **base** graph `M.dag`.  Then, in the base
    model `M`, the latent cutset `cutsetLatent Y (Zr ∪ W)` is d-separated from `Zr`
    given `W ∪ M.fixed`.

    The base-model active path `Zr ⤳ Y` produced by a reachable cutset node is
    transported edge-by-edge into `M.fixSet Z _ _` (`path_fixSet_active`); criterion
    (i) guarantees no treatment out-edge is needed, so the path survives and
    contradicts the assumed post-intervention separation. -/
theorem cutsetLatent_dSep_of_fixSet_dSep
    (Y W : Finset (SWIGNode N))
    (hW : W ⊆ M.observed)
    (hWNonDescM1 : ∀ D ∈ Z, ∀ w ∈ W,
      ¬ M.dag.isAncestor (SWIGNode.random D) w)
    (hdSep2 : (M.fixSet Z hZ_obs hZ_fixed).dag.dSep
        Y (Z.image SWIGNode.random)
        (W ∪ (M.fixSet Z hZ_obs hZ_fixed).fixed)) :
    M.dag.dSep (M.cutsetLatent Y (Z.image SWIGNode.random ∪ W))
      (Z.image SWIGNode.random) (W ∪ M.fixed) := by
  classical
  -- The post-intervention conditioning set equals `C2 = W ∪ M.fixed ∪ Zfix`.
  have hCeq : W ∪ (M.fixSet Z hZ_obs hZ_fixed).fixed
      = W ∪ M.fixed ∪ Z.image SWIGNode.fixed := by
    rw [fixSet_fixed, ← Finset.union_assoc]
  -- Symmetric form of the goal: no cutset node is reachable from `Zr`.
  refine (M.dag.dSep_symm _ _ _ ?_)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro zr hzrZr hzrCut
    obtain ⟨D, hD, hzrEq⟩ := Finset.mem_image.mp hzrZr
    have hzrObs : zr ∈ M.observed := by
      rw [← hzrEq]
      exact hZ_obs D hD
    exact M.not_obs_of_unobs ((M.mem_cutsetLatent.mp hzrCut).1) hzrObs
  · refine Disjoint.mono_right ?_ hdSep2.2.2.1
    intro v hv
    rcases Finset.mem_union.mp hv with hvW | hvM
    · exact Finset.mem_union_left _ hvW
    · exact Finset.mem_union_right _ (by
        rw [fixSet_fixed]
        exact Finset.mem_union_left _ hvM)
  · rw [Finset.disjoint_left]
    intro c hcCut hcWF
    have hc_lat : c ∈ M.unobserved := (M.mem_cutsetLatent.mp hcCut).1
    rcases Finset.mem_union.mp hcWF with hcW | hcF
    · exact M.not_obs_of_unobs hc_lat (hW hcW)
    · obtain ⟨m, hm⟩ := M.fixed_is_fixed c hcF
      obtain ⟨k, hk⟩ := M.unobserved_is_random c hc_lat
      rw [hm] at hk
      cases hk
  · rw [Finset.disjoint_left]
    intro c hcReach hcCut
    -- From the reachable cutset node, build an in-edge `M`-active path `Zr ⤳ Y`.
    obtain ⟨P, hPlen, hPact, hPhead, hPlast, hPin⟩ :=
      exists_inEdge_activePath_to_Y M Z hZ_obs Y W hW hWNonDescM1 hcCut hcReach
    -- Transport it to `M.fixSet Z`, given `C2`.
    have hPact2 : (M.fixSet Z hZ_obs hZ_fixed).dag.IsActivePath
        (W ∪ M.fixed ∪ Z.image SWIGNode.fixed) P :=
      path_fixSet_active M Z hZ_obs hZ_fixed W hWNonDescM1 hPact hPin
    -- Recover head/last elements.
    obtain ⟨zr, hzrZr, hzr_head⟩ := Finset.mem_image.mp hPhead
    obtain ⟨y, hyY, hy_last⟩ := Finset.mem_image.mp hPlast
    -- `P` witnesses reachability of `y` from `Zr` in `M.fixSet Z` given `C2`.
    have hyReach2 : y ∈ (M.fixSet Z hZ_obs hZ_fixed).dag.bbReachableVertices
        (W ∪ M.fixed ∪ Z.image SWIGNode.fixed) (Z.image SWIGNode.random) :=
      ((M.fixSet Z hZ_obs hZ_fixed).dag.bbReachableVertices_iff_activePath
          (Z.image SWIGNode.random) (W ∪ M.fixed ∪ Z.image SWIGNode.fixed) y).mpr
        ⟨zr, hzrZr, P, hPlen, hPact2, hzr_head.symm, hy_last.symm⟩
    -- Contradiction with `hdSep2` (symmetrised: no node reachable from `Zr` is in `Y`).
    rw [hCeq] at hdSep2
    have hdSep2' := (M.fixSet Z hZ_obs hZ_fixed).dag.dSep_symm _ _ _ hdSep2
    exact Finset.disjoint_left.mp hdSep2'.2.2.2 hyReach2 hyY

end CrossModel

end SCM

end Causalean
