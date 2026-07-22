/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.ID.Toolkit.Derivation
import Causalean.SCM.Do.Rule2Kernel.Structural.StructPointwise
import Causalean.Graph.DSep.OrderedLocalSG

/-!
# Frontdoor double-intervention graph lemmas

This file contains the graph-only premises needed by the frontdoor
identification derivation after the first intervention has already been applied.

* `frontdoor_fd1_rule3_nonDesc` is the Rule-3 non-ancestry premise: after
  intervening on the mediator block and on the treatment block, no treatment
  intervention copy can still be an ancestor of an outcome node, provided the
  corrected FD1 interception d-separation holds in the `do(X)` graph.
* `frontdoor_fd3_rule2_dSep` is the Rule-2 d-separation premise in the
  double-intervention graph, transported from the FD3 backdoor d-separation.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

section Helpers

variable (M : Causalean.SCM N Ω) (X W : Finset N)
variable (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
variable (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
variable (hW_obs : ∀ D ∈ W, SWIGNode.random D ∈ M.observed)
variable (hW_fixed : ∀ D ∈ W, SWIGNode.fixed D ∉ M.fixed)

private lemma disjoint_base_of_disjoint_random_image
    (hDisj : Disjoint (W.image SWIGNode.random) (X.image SWIGNode.random)) :
    Disjoint W X := by
  rw [Finset.disjoint_left] at hDisj ⊢
  intro d hdW hdX
  exact hDisj (Finset.mem_image.mpr ⟨d, hdW, rfl⟩)
    (Finset.mem_image.mpr ⟨d, hdX, rfl⟩)

private lemma fixSet_fixed_not_mem_of_disjoint
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hDisj : Disjoint W X) :
    ∀ D ∈ X, SWIGNode.fixed D ∉ (M.fixSet W hW_obs hW_fixed).fixed := by
  intro D hD hmem
  rw [SCM.fixSet_fixed] at hmem
  rcases Finset.mem_union.mp hmem with hM | hWF
  · exact hX_fixed D hD hM
  · rcases Finset.mem_image.mp hWF with ⟨D0, hD0W, hEq⟩
    cases hEq
    exact (Finset.disjoint_left.mp hDisj) hD0W hD

private lemma fixSet_fixed_not_mem
    (hW_fixed : ∀ D ∈ W, SWIGNode.fixed D ∉ M.fixed)
    (hDisj : Disjoint X W) :
    ∀ D ∈ W, SWIGNode.fixed D ∉ (M.fixSet X hX_obs hX_fixed).fixed := by
  intro D hD hmem
  rw [SCM.fixSet_fixed] at hmem
  rcases Finset.mem_union.mp hmem with hM | hXF
  · exact hW_fixed D hD hM
  · rcases Finset.mem_image.mp hXF with ⟨D0, hD0X, hEq⟩
    cases hEq
    exact (Finset.disjoint_left.mp hDisj) hD0X hD

private lemma double_edge_to_doX_of_not_fixedW
    (hDisj : Disjoint W X) {u v : SWIGNode N}
    (huW : ∀ D ∈ W, u ≠ SWIGNode.fixed D)
    (he : ((M.fixSet W hW_obs hW_fixed).fixSet X
        (by intro D hD; simpa [SCM.fixSet_observed] using hX_obs D hD)
        (fixSet_fixed_not_mem_of_disjoint M X W hW_obs hW_fixed hX_fixed hDisj)).dag.edge u v) :
    (M.fixSet X hX_obs hX_fixed).dag.edge u v := by
  have hWXedge :
      ((M.fixSet W hW_obs hW_fixed).fixSet X
        (by intro D hD; simpa [SCM.fixSet_observed] using hX_obs D hD)
        (fixSet_fixed_not_mem_of_disjoint M X W hW_obs hW_fixed hX_fixed hDisj)).dag.edge u v ↔
        SWIGGraph.splitMonoEdgeRel
          (SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge W) X u v := by
    simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
  have hXedge :
      (M.fixSet X hX_obs hX_fixed).dag.edge u v ↔
        SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge X u v := by
    simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
  rw [hWXedge] at he
  rw [hXedge]
  cases u with
  | random d =>
      by_cases hdX : d ∈ X
      · simp only [SWIGGraph.splitMonoEdgeRel, if_pos hdX] at he
      · simp only [SWIGGraph.splitMonoEdgeRel, if_neg hdX] at he ⊢
        by_cases hdW : d ∈ W
        · simp only [SWIGGraph.splitMonoEdgeRel, if_pos hdW] at he
        · simpa only [SWIGGraph.splitMonoEdgeRel, if_neg hdW] using he
  | fixed d =>
      by_cases hdX : d ∈ X
      · simp only [SWIGGraph.splitMonoEdgeRel, if_pos hdX] at he ⊢
        have hdW : d ∉ W := by
          intro hdW
          exact (Finset.disjoint_left.mp hDisj) hdW hdX
        simpa only [SWIGGraph.splitMonoEdgeRel, if_neg hdW] using he
      · simp only [SWIGGraph.splitMonoEdgeRel, if_neg hdX] at he ⊢
        by_cases hdW : d ∈ W
        · exact (huW d hdW rfl).elim
        · simpa only [SWIGGraph.splitMonoEdgeRel, if_neg hdW] using he

lemma isAncestorAvoiding_of_sinks {V : Type*} [DecidableEq V] [Fintype V]
    (G : DAG V) (C : Finset V)
    (hSink : ∀ c ∈ C, ∀ v, ¬ G.edge c v)
    {u v : V} (h : G.isAncestor u v) :
    G.isAncestorAvoiding C u v := by
  induction h with
  | edge he => exact DAG.isAncestorAvoiding.edge he
  | @trans w v hprev he ih =>
      exact DAG.isAncestorAvoiding.trans ih
        (by
          intro hwC
          exact hSink w hwC v he)
        he

private lemma not_fixedW_of_incoming_doX
    (hW_fixed : ∀ D ∈ W, SWIGNode.fixed D ∉ M.fixed)
    {u w : SWIGNode N} (he : (M.fixSet X hX_obs hX_fixed).dag.edge u w) :
    ∀ D ∈ W, w ≠ SWIGNode.fixed D := by
  intro D hD hEq
  have hmem : u ∈ (M.fixSet X hX_obs hX_fixed).dag.parents w :=
    (M.fixSet X hX_obs hX_fixed).dag.mem_parents.mpr he
  have hroot : (M.fixSet X hX_obs hX_fixed).dag.parents (SWIGNode.fixed D) = ∅ := by
    by_cases hDX : D ∈ X
    · exact (M.fixSet X hX_obs hX_fixed).fixed_are_roots _
        (SCM.fixed_mem_fixSet M X hX_obs hX_fixed hDX)
    ·
      -- If `D ∉ X`, the fixed node is not a target of `do(X)` and is not fixed in
      -- `M`; its incoming edges remain absent by `fixed_outside_fixed_isolated`.
      ext a
      constructor
      · intro ha
        have haEdge : (M.fixSet X hX_obs hX_fixed).dag.edge a (SWIGNode.fixed D) :=
          (M.fixSet X hX_obs hX_fixed).dag.mem_parents.mp ha
        have h_eqrel :
            (M.fixSet X hX_obs hX_fixed).dag.edge a (SWIGNode.fixed D) ↔
              SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge X a (SWIGNode.fixed D) := by
          simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
        rw [h_eqrel] at haEdge
        have hrootM : M.dag.parents (SWIGNode.fixed D) = ∅ :=
          (M.fixed_outside_fixed_isolated D (hW_fixed D hD)).1
        cases a with
        | random aD =>
            by_cases haX : aD ∈ X
            · simp only [SWIGGraph.splitMonoEdgeRel, if_pos haX] at haEdge
            ·
              simp only [SWIGGraph.splitMonoEdgeRel, if_neg haX] at haEdge
              have hpar : SWIGNode.random aD ∈ M.dag.parents (SWIGNode.fixed D) :=
                M.dag.mem_parents.mpr haEdge
              rw [hrootM] at hpar
              exact False.elim ((Finset.notMem_empty _) hpar)
        | fixed aD =>
            by_cases haX : aD ∈ X
            ·
              simp only [SWIGGraph.splitMonoEdgeRel, if_pos haX] at haEdge
              have hpar : SWIGNode.random aD ∈ M.dag.parents (SWIGNode.fixed D) :=
                M.dag.mem_parents.mpr haEdge
              rw [hrootM] at hpar
              exact False.elim ((Finset.notMem_empty _) hpar)
            ·
              simp only [SWIGGraph.splitMonoEdgeRel, if_neg haX] at haEdge
              have hpar : SWIGNode.fixed aD ∈ M.dag.parents (SWIGNode.fixed D) :=
                M.dag.mem_parents.mpr haEdge
              rw [hrootM] at hpar
              exact False.elim ((Finset.notMem_empty _) hpar)
      · intro ha
        exact False.elim ((Finset.notMem_empty _) ha)
  rw [hEq, hroot] at hmem
  exact (Finset.notMem_empty _) hmem

private lemma double_edge_to_doW_of_not_fixedX
    (hDisj : Disjoint X W) {u v : SWIGNode N}
    (huX : ∀ D ∈ X, u ≠ SWIGNode.fixed D)
    (he : ((M.fixSet X hX_obs hX_fixed).fixSet W
        (by intro D hD; simpa [SCM.fixSet_observed] using hW_obs D hD)
        (fixSet_fixed_not_mem M X W hX_obs hX_fixed hW_fixed hDisj)).dag.edge u v) :
    (M.fixSet W hW_obs hW_fixed).dag.edge u v := by
  have hXWedge :
      ((M.fixSet X hX_obs hX_fixed).fixSet W
        (by intro D hD; simpa [SCM.fixSet_observed] using hW_obs D hD)
        (fixSet_fixed_not_mem M X W hX_obs hX_fixed hW_fixed hDisj)).dag.edge u v ↔
        SWIGGraph.splitMonoEdgeRel
          (SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge X) W u v := by
    simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
  have hWedge :
      (M.fixSet W hW_obs hW_fixed).dag.edge u v ↔
        SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge W u v := by
    simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
  rw [hXWedge] at he
  rw [hWedge]
  cases u with
  | random d =>
      by_cases hdW : d ∈ W
      · simp only [SWIGGraph.splitMonoEdgeRel, if_pos hdW] at he
      · simp only [SWIGGraph.splitMonoEdgeRel, if_neg hdW] at he ⊢
        by_cases hdX : d ∈ X
        · simp only [SWIGGraph.splitMonoEdgeRel, if_pos hdX] at he
        · simpa only [SWIGGraph.splitMonoEdgeRel, if_neg hdX] using he
  | fixed d =>
      by_cases hdW : d ∈ W
      · simp only [SWIGGraph.splitMonoEdgeRel, if_pos hdW] at he ⊢
        have hdX : d ∉ X := by
          intro hdX
          exact (Finset.disjoint_left.mp hDisj) hdX hdW
        simpa only [SWIGGraph.splitMonoEdgeRel, if_neg hdX] using he
      · simp only [SWIGGraph.splitMonoEdgeRel, if_neg hdW] at he ⊢
        by_cases hdX : d ∈ X
        · exact (huX d hdX rfl).elim
        · simpa only [SWIGGraph.splitMonoEdgeRel, if_neg hdX] using he

end Helpers

/-- **G2: corrected-FD1 Rule-3 non-ancestry premise.**

    If the corrected FD1 clause d-separates `Y` from the intervention copies
    `X.image .fixed` in the `do(X)` graph given the mediator random nodes
    `W.image .random`, then after additionally intervening on the mediator block
    no treatment intervention copy is an ancestor of any outcome node. -/
theorem frontdoor_fd1_rule3_nonDesc
    (M : Causalean.SCM N Ω) (X Wbase : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hW_obs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hW_fixed : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hFD1 : (M.fixSet X hX_obs hX_fixed).dag.dSep
      Y (X.image SWIGNode.fixed) (Wbase.image SWIGNode.random))
    (hDisj_WX : Disjoint (Wbase.image SWIGNode.random) (X.image SWIGNode.random)) :
    ∀ v ∈ Y ∪ (∅ : Finset (SWIGNode N)), ∀ d ∈ X,
      ¬ ((M.fixSet Wbase hW_obs hW_fixed).fixSet X
          (by intro D hD; simpa [SCM.fixSet_observed] using hX_obs D hD)
          (fixSet_fixed_not_mem_of_disjoint M X Wbase hW_obs hW_fixed hX_fixed
            (disjoint_base_of_disjoint_random_image X Wbase hDisj_WX))).dag.isAncestor
        (SWIGNode.fixed d) v := by
  classical
  intro v hv d hd hanc
  have hDisjBase : Disjoint Wbase X :=
    disjoint_base_of_disjoint_random_image X Wbase hDisj_WX
  let hX_obs_W : ∀ D ∈ X, SWIGNode.random D ∈ (M.fixSet Wbase hW_obs hW_fixed).observed :=
    by intro D hD; simpa [SCM.fixSet_observed] using hX_obs D hD
  let hX_fixed_W : ∀ D ∈ X, SWIGNode.fixed D ∉ (M.fixSet Wbase hW_obs hW_fixed).fixed :=
    fixSet_fixed_not_mem_of_disjoint M X Wbase hW_obs hW_fixed hX_fixed hDisjBase
  let Gdouble := ((M.fixSet Wbase hW_obs hW_fixed).fixSet X hX_obs_W hX_fixed_W).dag
  have hAvoid : Gdouble.isAncestorAvoiding (Wbase.image SWIGNode.random) (SWIGNode.fixed d) v := by
    refine isAncestorAvoiding_of_sinks Gdouble (Wbase.image SWIGNode.random) ?_ hanc
    intro c hc z he
    rcases Finset.mem_image.mp hc with ⟨D, hD, rfl⟩
    have hDnotX : D ∉ X := by
      intro hDX
      exact (Finset.disjoint_left.mp hDisjBase) hD hDX
    have h_eqrel :
        Gdouble.edge (SWIGNode.random D) z ↔
          SWIGGraph.splitMonoEdgeRel
            (M.fixSet Wbase hW_obs hW_fixed).dag.edge X (SWIGNode.random D) z := by
      simp only [Gdouble, SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
        SWIGGraph.splitMonoDAG]
    rw [h_eqrel] at he
    simp only [SWIGGraph.splitMonoEdgeRel, if_neg hDnotX] at he
    exact SCM.fixSet_random_no_children M Wbase hW_obs hW_fixed hD z he
  obtain ⟨p, hplen, hphead, hplast, hpedge_double, hpintW⟩ := hAvoid.exists_path
  have hpedge_doX :
      ∀ (i : ℕ) (hi : i + 1 < p.length),
        (M.fixSet X hX_obs hX_fixed).dag.edge
          (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, hi⟩) := by
    intro i hi
    refine double_edge_to_doX_of_not_fixedW M X Wbase hX_obs hX_fixed hW_obs hW_fixed
      hDisjBase ?_ (hpedge_double i hi)
    intro D hD hEq
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      have : d = D := by
        have hp0 : p.get ⟨0, by omega⟩ = SWIGNode.fixed d := by
          cases p with
          | nil => simp at hplen
          | cons a t =>
              simp only [List.head?_cons] at hphead
              exact Option.some.inj hphead
        rw [hp0] at hEq
        cases hEq
        rfl
      cases this
      exact (Finset.disjoint_left.mp hDisjBase) hD hd
    ·
      have hprevDouble : Gdouble.edge (p.get ⟨i - 1, by omega⟩) (p.get ⟨i, by omega⟩) := by
        have hprev0 := hpedge_double (i - 1) (by omega)
        have hidx : i - 1 + 1 = i := by omega
        simpa [Gdouble, hidx] using hprev0
      have hmem : p.get ⟨i - 1, by omega⟩ ∈ Gdouble.parents (p.get ⟨i, by omega⟩) :=
        Gdouble.mem_parents.mpr hprevDouble
      have hfixedW_double : SWIGNode.fixed D ∈
          ((M.fixSet Wbase hW_obs hW_fixed).fixSet X hX_obs_W hX_fixed_W).fixed := by
        exact SCM.fixSet_fixed_subset (M.fixSet Wbase hW_obs hW_fixed) X
          hX_obs_W hX_fixed_W (SCM.fixed_mem_fixSet M Wbase hW_obs hW_fixed hD)
      have hroot : Gdouble.parents (SWIGNode.fixed D) = ∅ :=
        ((M.fixSet Wbase hW_obs hW_fixed).fixSet X hX_obs_W hX_fixed_W).fixed_are_roots
          _ hfixedW_double
      rw [hEq, hroot] at hmem
      exact (Finset.notMem_empty _) hmem
  have hpact : (M.fixSet X hX_obs hX_fixed).dag.IsActivePath
      (Wbase.image SWIGNode.random) p :=
    (M.fixSet X hX_obs hX_fixed).dag.isActivePath_of_directed_interior
      hpedge_doX hpintW
  have hvReach : v ∈ (M.fixSet X hX_obs hX_fixed).dag.bbReachableVertices
      (Wbase.image SWIGNode.random) (X.image SWIGNode.fixed) := by
    rw [(M.fixSet X hX_obs hX_fixed).dag.bbReachableVertices_iff_activePath]
    refine ⟨SWIGNode.fixed d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, p, hplen, hpact, ?_, ?_⟩
    · exact hphead
    · exact hplast
  have hSepSymm := (M.fixSet X hX_obs hX_fixed).dag.dSep_symm _ _ _ hFD1
  rw [Finset.union_empty] at hv
  exact (Finset.disjoint_left.mp hSepSymm.2.2.2) hvReach hv

/-- Rule-2 d-separation premise for the frontdoor third condition.

    This is the exact d-separation shape consumed by `do_rule2_kernel` when
    `M' := M.fixSet X`, treatment `:= Wbase`, and adjustment set `:= ∅`. -/
theorem frontdoor_fd3_rule2_dSep
    (M : Causalean.SCM N Ω) (X Wbase : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hW_obs : ∀ D ∈ Wbase, SWIGNode.random D ∈ M.observed)
    (hW_fixed : ∀ D ∈ Wbase, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed)
    (hFD3 : M.toSWIGGraph.backdoorCriterion Wbase hW_obs hW_fixed Y
      (X.image SWIGNode.random))
    (hDisj_WX : Disjoint (Wbase.image SWIGNode.random) (X.image SWIGNode.random)) :
    ((M.fixSet X hX_obs hX_fixed).fixSet Wbase
        (by intro D hD; simpa [SCM.fixSet_observed] using hW_obs D hD)
        (fixSet_fixed_not_mem M X Wbase hX_obs hX_fixed hW_fixed
          ((disjoint_base_of_disjoint_random_image X Wbase hDisj_WX).symm))).dag.dSep
      Y (Wbase.image SWIGNode.random)
      ((∅ : Finset (SWIGNode N)) ∪
        ((M.fixSet X hX_obs hX_fixed).fixSet Wbase
          (by intro D hD; simpa [SCM.fixSet_observed] using hW_obs D hD)
          (fixSet_fixed_not_mem M X Wbase hX_obs hX_fixed hW_fixed
            ((disjoint_base_of_disjoint_random_image X Wbase hDisj_WX).symm))).fixed) := by
  classical
  have hDisjBaseWX : Disjoint Wbase X :=
    disjoint_base_of_disjoint_random_image X Wbase hDisj_WX
  have hDisjBaseXW : Disjoint X Wbase := hDisjBaseWX.symm
  let hW_obs_X : ∀ D ∈ Wbase, SWIGNode.random D ∈
      (M.fixSet X hX_obs hX_fixed).observed :=
    by intro D hD; simpa [SCM.fixSet_observed] using hW_obs D hD
  let hW_fixed_X : ∀ D ∈ Wbase, SWIGNode.fixed D ∉
      (M.fixSet X hX_obs hX_fixed).fixed :=
    fixSet_fixed_not_mem M X Wbase hX_obs hX_fixed hW_fixed hDisjBaseXW
  let Gdouble := ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag
  let Cdouble := (∅ : Finset (SWIGNode N)) ∪
    ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).fixed
  refine ⟨hFD3.2.2.2.2.1, ?_, ?_, ?_⟩
  · have hY_double : Y ⊆
        ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).observed := by
      intro v hv
      simpa [SCM.fixSet_observed] using hY hv
    rw [Finset.disjoint_left]
    intro v hvY hvC
    simp only [Cdouble, Finset.empty_union] at hvC
    exact (((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).not_fixed_of_obs
      (hY_double hvY)) hvC
  · have hW_double : Wbase.image SWIGNode.random ⊆
        ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).observed := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨D, hD, rfl⟩
      simpa [SCM.fixSet_observed] using hW_obs D hD
    rw [Finset.disjoint_left]
    intro v hvW hvC
    simp only [Cdouble, Finset.empty_union] at hvC
    exact (((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).not_fixed_of_obs
      (hW_double hvW)) hvC
  · rw [Finset.disjoint_left]
    intro v hvReach hvW
    rw [((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.bbReachableVertices_iff_activePath] at hvReach
    obtain ⟨y, hyY, p, hlen, hact, hhead, hlast⟩ := hvReach
    have hReach_doW : v ∈ (M.fixSet Wbase hW_obs hW_fixed).dag.bbReachableVertices
        (X.image SWIGNode.random ∪ Wbase.image SWIGNode.fixed) Y := by
      rw [(M.fixSet Wbase hW_obs hW_fixed).dag.bbReachableVertices_iff_activePath]
      refine ⟨y, hyY, p, hlen, ?_, hhead, hlast⟩
      obtain ⟨hadjD, hcollD⟩ := hact
      have hNoFixedInterior : ∀ (i : ℕ) (hi : i + 2 < p.length),
          p.get ⟨i + 1, by omega⟩ ∉
            ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).fixed := by
        intro i hi hmfix
        have hroot :
            ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.parents
              (p.get ⟨i + 1, by omega⟩) = ∅ :=
          ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).fixed_are_roots
            _ hmfix
        have hval := hcollD i hi
        simp only at hval
        set l := p.get ⟨i, by omega⟩
        set m := p.get ⟨i + 1, by omega⟩
        set r := p.get ⟨i + 2, hi⟩
        have hnotColl :
            ¬ ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.IsCollider
                l m r := by
          intro hc
          have hpar : l ∈
              ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.parents m :=
            ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.mem_parents.mpr hc.1
          rw [show m = p.get ⟨i + 1, by omega⟩ from rfl] at hpar
          rw [hroot] at hpar
          exact (Finset.notMem_empty _) hpar
        rw [if_neg hnotColl] at hval
        exact hval (by simpa [Finset.empty_union] using hmfix)
      have hY_not_fixed : ∀ D ∈ X, y ≠ SWIGNode.fixed D := by
        intro D hD hyfix
        have hyObs : y ∈ M.observed := hY hyY
        obtain ⟨n, hn⟩ := M.observed_is_random y hyObs
        rw [hn] at hyfix
        cases hyfix
      have hV_not_fixed : ∀ D ∈ X, v ≠ SWIGNode.fixed D := by
        intro D hD hvfix
        rcases Finset.mem_image.mp hvW with ⟨E, hE, hv⟩
        rw [← hv] at hvfix
        cases hvfix
      have hNotFixedAt : ∀ (k : ℕ) (hk : k < p.length), ∀ D ∈ X,
          p.get ⟨k, hk⟩ ≠ SWIGNode.fixed D := by
        intro k hk D hD hEq
        by_cases hk0 : k = 0
        · subst hk0
          have hp0 : p.get ⟨0, hk⟩ = y := by
            cases p with
            | nil => simp at hlen
            | cons a t =>
                simp only [List.head?_cons] at hhead
                exact Option.some.inj hhead
          rw [hp0] at hEq
          exact hY_not_fixed D hD hEq
        · by_cases hklast : k + 1 = p.length
          · have hpLast : p.get ⟨k, hk⟩ = v := by
              have hp_ne : p ≠ [] := by
                intro hpnil
                rw [hpnil] at hlen
                simp at hlen
              rw [List.getLast?_eq_some_getLast hp_ne] at hlast
              have hgetLast : p.getLast hp_ne = v := Option.some.inj hlast
              rw [← hgetLast]
              rw [List.getLast_eq_getElem]
              congr
              omega
            rw [hpLast] at hEq
            exact hV_not_fixed D hD hEq
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
            have hmid := hNoFixedInterior (k - 1) (by omega)
            have hfixedD : SWIGNode.fixed D ∈
                ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).fixed := by
              exact SCM.fixSet_fixed_subset (M.fixSet X hX_obs hX_fixed) Wbase
                hW_obs_X hW_fixed_X (SCM.fixed_mem_fixSet M X hX_obs hX_fixed hD)
            have hidx : k - 1 + 1 = k := by omega
            rw [show p.get ⟨k - 1 + 1, by omega⟩ = p.get ⟨k, hk⟩ by
                congr 1; exact Fin.ext hidx] at hmid
            exact hmid (by rw [hEq]; exact hfixedD)
      have hNoXrInterior : ∀ (i : ℕ) (hi : i + 2 < p.length),
          p.get ⟨i + 1, by omega⟩ ∉ X.image SWIGNode.random := by
        intro i hi hmX
        rcases Finset.mem_image.mp hmX with ⟨D, hD, hmEq⟩
        set m := p.get ⟨i + 1, by omega⟩
        have hmEq' : m = SWIGNode.random D := by simpa [m] using hmEq.symm
        have hNoOut : ∀ z, ¬ ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.edge
            (SWIGNode.random D) z := by
          intro z he
          have hDnotW : D ∉ Wbase := by
            intro hDW
            exact (Finset.disjoint_left.mp hDisjBaseWX) hDW hD
          have h_eqrel :
              ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.edge
                  (SWIGNode.random D) z ↔
                SWIGGraph.splitMonoEdgeRel
                  (M.fixSet X hX_obs hX_fixed).dag.edge Wbase (SWIGNode.random D) z := by
            simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
          rw [h_eqrel] at he
          simp only [SWIGGraph.splitMonoEdgeRel, if_neg hDnotW] at he
          exact SCM.fixSet_random_no_children M X hX_obs hX_fixed hD z he
        have hadjL := hadjD i (by omega)
        have hadjR := hadjD (i + 1) (by omega)
        have hleft : ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.edge
            (p.get ⟨i, by omega⟩) m := by
          rcases hadjL with h | h
          · simpa [m] using h
          · exfalso
            rw [show p.get ⟨i + 1, by omega⟩ = SWIGNode.random D from by
              simpa [m] using hmEq'] at h
            exact hNoOut (p.get ⟨i, by omega⟩) h
        have hright : ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.edge
            (p.get ⟨i + 2, hi⟩) m := by
          rcases hadjR with h | h
          · exfalso
            rw [show p.get ⟨i + 1, by omega⟩ = SWIGNode.random D from by
              simpa [m] using hmEq'] at h
            exact hNoOut (p.get ⟨i + 2, hi⟩) h
          · simpa [m] using h
        have hCollD :
            ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.IsCollider
              (p.get ⟨i, by omega⟩) m (p.get ⟨i + 2, hi⟩) := ⟨hleft, hright⟩
        have hval := hcollD i hi
        simp only at hval
        rw [show p.get ⟨i + 1, by omega⟩ = m from rfl] at hval
        rw [if_pos hCollD] at hval
        have hm_notC : m ∉ (∅ : Finset (SWIGNode N)) ∪
            ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).fixed := by
          intro hmC
          rw [Finset.empty_union] at hmC
          obtain ⟨n, hn⟩ :=
            ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).fixed_is_fixed m hmC
          rw [hmEq'] at hn
          cases hn
        have hnotAnc : ∀ c,
            ¬ ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.isAncestor
                m c := by
          intro c hanc
          rcases ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.isAncestor_child hanc with hE | ⟨c0, hE, _⟩
          · exact hNoOut c (by simpa [hmEq'] using hE)
          · exact hNoOut c0 (by simpa [hmEq'] using hE)
        simp only [DAG.bbZAncestors, DAG.ancestralSet, DAG.ancestorsSet,
          Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hval
        rcases hval with hmC | ⟨c, hcC, hmc⟩
        · exact hm_notC (Finset.mem_union.mpr hmC)
        · exact hnotAnc c hmc
      refine ⟨?_, ?_⟩
      · intro i hi
        have hdAdj := hadjD i hi
        rcases hdAdj with he | he
        · exact Or.inl (double_edge_to_doW_of_not_fixedX M X Wbase hX_obs hX_fixed
            hW_obs hW_fixed hDisjBaseXW
            (fun D hD => hNotFixedAt i (by omega) D hD) he)
        · exact Or.inr (double_edge_to_doW_of_not_fixedX M X Wbase hX_obs hX_fixed
            hW_obs hW_fixed hDisjBaseXW
            (fun D hD => hNotFixedAt (i + 1) hi D hD) he)
      · intro i hi
        have hvalD := hcollD i hi
        simp only at hvalD
        by_cases hCollW : (M.fixSet Wbase hW_obs hW_fixed).dag.IsCollider
            (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩)
        · rw [if_pos hCollW]
          have hCollD :
              ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.IsCollider
                (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩)
                (p.get ⟨i + 2, hi⟩) := by
            constructor
            · have hadjL := hadjD i (by omega)
              rcases hadjL with h | h
              · exact h
              · exfalso
                have hmw : (M.fixSet Wbase hW_obs hW_fixed).dag.edge
                    (p.get ⟨i + 1, by omega⟩) (p.get ⟨i, by omega⟩) :=
                  double_edge_to_doW_of_not_fixedX M X Wbase hX_obs hX_fixed hW_obs
                    hW_fixed hDisjBaseXW
                    (fun D hD => hNotFixedAt (i + 1) (by omega) D hD) h
                exact (M.fixSet Wbase hW_obs hW_fixed).dag.asymm hmw hCollW.1
            · have hadjR := hadjD (i + 1) (by omega)
              rcases hadjR with h | h
              · exfalso
                have hmw : (M.fixSet Wbase hW_obs hW_fixed).dag.edge
                    (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) :=
                  double_edge_to_doW_of_not_fixedX M X Wbase hX_obs hX_fixed hW_obs
                    hW_fixed hDisjBaseXW
                    (fun D hD => hNotFixedAt (i + 1) (by omega) D hD) h
                exact (M.fixSet Wbase hW_obs hW_fixed).dag.asymm hmw hCollW.2
              · exact h
          rw [if_pos hCollD] at hvalD
          have hnotAncFixed : ∀ c ∈
              ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).fixed,
              ¬ ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.isAncestor
                  (p.get ⟨i + 1, by omega⟩) c := by
            intro c hc hanc
            have hroot :
                ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.parents c = ∅ :=
              ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).fixed_are_roots c hc
            cases hanc with
            | edge he =>
                have hpar : p.get ⟨i + 1, by omega⟩ ∈
                    ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.parents c :=
                  ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.mem_parents.mpr he
                rw [hroot] at hpar
                exact (Finset.notMem_empty _) hpar
            | trans _ he =>
                have hpar :=
                  ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.mem_parents.mpr he
                rw [hroot] at hpar
                exact (Finset.notMem_empty _) hpar
          exfalso
          simp only [DAG.bbZAncestors, DAG.ancestralSet, DAG.ancestorsSet,
            Finset.empty_union, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
            true_and] at hvalD
          rcases hvalD with hmFix | ⟨c, hcFix, hanc⟩
          · exact hNoFixedInterior i hi hmFix
          · exact hnotAncFixed c hcFix hanc
        · rw [if_neg hCollW]
          have hnotCollD :
              ¬ ((M.fixSet X hX_obs hX_fixed).fixSet Wbase hW_obs_X hW_fixed_X).dag.IsCollider
                  (p.get ⟨i, by omega⟩) (p.get ⟨i + 1, by omega⟩) (p.get ⟨i + 2, hi⟩) := by
            intro hcd
            apply hCollW
            constructor
            · exact double_edge_to_doW_of_not_fixedX M X Wbase hX_obs hX_fixed hW_obs
                hW_fixed hDisjBaseXW (fun D hD => hNotFixedAt i (by omega) D hD) hcd.1
            · exact double_edge_to_doW_of_not_fixedX M X Wbase hX_obs hX_fixed hW_obs
                hW_fixed hDisjBaseXW (fun D hD => hNotFixedAt (i + 2) hi D hD) hcd.2
          rw [if_neg hnotCollD] at hvalD
          intro hmCond
          rcases Finset.mem_union.mp hmCond with hmX | hmWfix
          · exact hNoXrInterior i hi hmX
          · apply hvalD
            rw [Finset.empty_union]
            rcases Finset.mem_image.mp hmWfix with ⟨D, hD, hEq⟩
            rw [← hEq]
            exact SCM.fixed_mem_fixSet (M.fixSet X hX_obs hX_fixed) Wbase
              hW_obs_X hW_fixed_X hD
    exact (Finset.disjoint_left.mp (hFD3.2.2.2.2).2.2.2) hReach_doW hvW

end SCM

end Causalean
