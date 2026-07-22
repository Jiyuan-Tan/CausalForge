/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.Kernel
import Causalean.SCM.Model.CounterfactualLemmas
import Causalean.Graph.CComponents

/-! # Latent-block factorization and local consistency

This file provides the local-consistency predicate used by the ID density
factorization and the latent-block decomposition facts that make q-masses split
across c-components.  Local consistency says that an observed assignment agrees
with the structural function at a node when parents are read from fixed values,
the observed assignment, and a latent realization.
-/

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The recursive evaluator can read all earlier observed coordinates from a
full observed assignment. -/
noncomputable def prevFromObservedValues
    (M : Causalean.SCM N Ω) (x : ValuesOn M.observed (swigΩ Ω))
    {n : ℕ} :
    ∀ m : ℕ, m < n → ∀ hm : m < M.observed.card,
      swigΩ Ω (M.observedAt ⟨m, hm⟩).val :=
  fun m _ hm => x (M.observedAt ⟨m, hm⟩)

/-- The latent variables with an edge into a candidate observed c-component. -/
noncomputable def latentBlock
    (M : Causalean.SCM N Ω) (C : Finset (SWIGNode N)) :
    Finset (SWIGNode N) :=
  M.unobserved.filter (fun u => ∃ v ∈ C, M.dag.edge u v)

/-- Distinct full c-components have disjoint latent parent blocks. -/
lemma latentBlock_pairwise_disjoint
    (M : Causalean.SCM N Ω) {C C' : Finset (SWIGNode N)}
    (hC : C ∈ M.toSWIGGraph.cComponentSet)
    (hC' : C' ∈ M.toSWIGGraph.cComponentSet) (hne : C ≠ C') :
    Disjoint (M.latentBlock C) (M.latentBlock C') := by
  rw [Finset.disjoint_left]
  intro u huC huC'
  obtain ⟨hu, v, hvC, huv⟩ := by
    simpa [latentBlock] using (Finset.mem_filter.mp huC)
  obtain ⟨hu', w, hwC', huw⟩ := by
    simpa [latentBlock] using (Finset.mem_filter.mp huC')
  have hdisj := M.toSWIGGraph.cComponentSet_pairwise_disjoint hC hC' hne
  have hwObs : w ∈ M.toSWIGGraph.observed :=
    M.toSWIGGraph.cComponentSet_subset_observed C' hC' hwC'
  have hwNotC : w ∉ C := by
    intro hwC
    exact (Finset.disjoint_left.mp hdisj) hwC hwC'
  exact M.toSWIGGraph.no_shared_unobserved_parent_of_mem_cComponentSet_of_not_mem
    hC hvC hwObs hwNotC hu huv huw

/-- Distinct c-components of an induced SWIG have disjoint latent-parent blocks
in the ambient SCM. -/
lemma latentBlock_pairwise_disjoint_induce_components
    (M : Causalean.SCM N Ω) (R : Finset (SWIGNode N))
    {C C' : Finset (SWIGNode N)}
    (hC : C ∈ (M.toSWIGGraph.induce R).cComponentSet)
    (hC' : C' ∈ (M.toSWIGGraph.induce R).cComponentSet) (hne : C ≠ C') :
    Disjoint (M.latentBlock C) (M.latentBlock C') := by
  classical
  rw [Finset.disjoint_left]
  intro u huC huC'
  obtain ⟨hu, v, hvC, huv⟩ := by
    simpa [latentBlock] using (Finset.mem_filter.mp huC)
  obtain ⟨_hu', w, hwC', huw⟩ := by
    simpa [latentBlock] using (Finset.mem_filter.mp huC')
  have hvIndObs : v ∈ (M.toSWIGGraph.induce R).observed :=
    (M.toSWIGGraph.induce R).cComponentSet_subset_observed C hC hvC
  have hwIndObs : w ∈ (M.toSWIGGraph.induce R).observed :=
    (M.toSWIGGraph.induce R).cComponentSet_subset_observed C' hC' hwC'
  have hvR : v ∈ R := by
    simpa [SWIGGraph.induce] using (Finset.mem_inter.mp hvIndObs).1
  have hvObs : v ∈ M.toSWIGGraph.observed := by
    simpa [SWIGGraph.induce] using (Finset.mem_inter.mp hvIndObs).2
  have hwR : w ∈ R := by
    simpa [SWIGGraph.induce] using (Finset.mem_inter.mp hwIndObs).1
  have hwObs : w ∈ M.toSWIGGraph.observed := by
    simpa [SWIGGraph.induce] using (Finset.mem_inter.mp hwIndObs).2
  have hsame :=
    M.toSWIGGraph.induce_cComponentOf_eq_of_shared_unobserved_parent
      R hu hvR hvObs hwR hwObs huv huw
  have hvComp :
      (M.toSWIGGraph.induce R).cComponentOf v = C :=
    (M.toSWIGGraph.induce R).cComponentOf_eq_of_mem_cComponentSet hC hvC
  have hwComp :
      (M.toSWIGGraph.induce R).cComponentOf w = C' :=
    (M.toSWIGGraph.induce R).cComponentOf_eq_of_mem_cComponentSet hC' hwC'
  exact hne (hvComp ▸ hwComp ▸ hsame)

/-- Do-model specialization of induced-component latent-block disjointness. -/
lemma latentBlock_pairwise_disjoint_fixSet_induce_components
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (R : Finset (SWIGNode N))
    {C C' : Finset (SWIGNode N)}
    (hC : C ∈ ((M.fixSet X hObs hFix).toSWIGGraph.induce R).cComponentSet)
    (hC' : C' ∈ ((M.fixSet X hObs hFix).toSWIGGraph.induce R).cComponentSet)
    (hne : C ≠ C') :
    Disjoint ((M.fixSet X hObs hFix).latentBlock C)
      ((M.fixSet X hObs hFix).latentBlock C') :=
  latentBlock_pairwise_disjoint_induce_components
    (M.fixSet X hObs hFix) R hC hC' hne

/-- `v`'s mechanism, parents read locally from `x`/`s`/`ℓ`, reproduces `x v`. -/
noncomputable def localConsistent
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) (v : SWIGNode N)
    (hv : v ∈ M.observed) (ℓ : M.LatentValues) : Prop :=
  let j := M.observedIndex ⟨v, hv⟩
  (M.observedAt_observedIndex ⟨v, hv⟩) ▸
    M.structFun (M.observedAt j)
      (fun w => M.parentMap s ℓ j.isLt (prevFromObservedValues M x) w)
      = x ⟨v, hv⟩

/-- Local consistency at `v` depends only on the latent block of `v`'s
c-component. -/
lemma localConsistent_depends_only_on_block
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) (v : SWIGNode N)
    (hv : v ∈ M.observed) (ℓ ℓ' : M.LatentValues)
    (hℓ : ∀ u (hu : u ∈ M.latentBlock (M.toSWIGGraph.cComponentOf v)),
      ℓ ⟨u, (Finset.mem_filter.mp hu).1⟩ =
        ℓ' ⟨u, (Finset.mem_filter.mp hu).1⟩) :
    M.localConsistent s x v hv ℓ ↔ M.localConsistent s x v hv ℓ' := by
  unfold localConsistent
  set j : Fin M.observed.card := M.observedIndex ⟨v, hv⟩ with hj
  have hat : (M.observedAt j).val = v := by
    rw [hj]
    exact M.observedAt_observedIndex ⟨v, hv⟩
  have hfun :
      M.structFun (M.observedAt j)
          (fun w => M.parentMap s ℓ j.isLt (prevFromObservedValues M x) w)
        =
      M.structFun (M.observedAt j)
          (fun w => M.parentMap s ℓ' j.isLt (prevFromObservedValues M x) w) := by
    congr 1
    funext w
    by_cases huo : w.val ∈ M.unobserved
    · rw [parentMap_unobserved M s ℓ j.isLt _ w huo,
          parentMap_unobserved M s ℓ' j.isLt _ w huo]
      have hedge_v : M.dag.edge w.val v := by
        have hedge_at : M.dag.edge w.val (M.observedAt j).val :=
          M.dag.mem_parents.mp w.property
        simpa [hat] using hedge_at
      have hvComp : v ∈ M.toSWIGGraph.cComponentOf v :=
        M.toSWIGGraph.mem_cComponentOf_self (by simpa using hv)
      have huBlock : w.val ∈ M.latentBlock (M.toSWIGGraph.cComponentOf v) := by
        rw [latentBlock, Finset.mem_filter]
        exact ⟨huo, ⟨v, hvComp, hedge_v⟩⟩
      exact hℓ w.val huBlock
    · by_cases hfix : w.val ∈ M.fixed
      · rw [parentMap_fixed M s ℓ j.isLt _ w huo hfix,
            parentMap_fixed M s ℓ' j.isLt _ w huo hfix]
      · have hedge : M.dag.edge w.val (M.observedAt j).val :=
          M.dag.mem_parents.mp w.property
        have hobs : w.val ∈ M.observed := by
          rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
          · rcases Finset.mem_union.mp h1 with hfx | hob
            · exact absurd hfx hfix
            · exact hob
          · exact absurd h2 huo
        rw [parentMap_observed M s ℓ j.isLt _ w huo hfix hobs,
            parentMap_observed M s ℓ' j.isLt _ w huo hfix hobs]
  subst j
  change
    ((M.observedAt_observedIndex ⟨v, hv⟩) ▸
        M.structFun (M.observedAt (M.observedIndex ⟨v, hv⟩))
          (fun w => M.parentMap s ℓ (M.observedIndex ⟨v, hv⟩).isLt
            (prevFromObservedValues M x) w)
        = x ⟨v, hv⟩)
      ↔
    ((M.observedAt_observedIndex ⟨v, hv⟩) ▸
        M.structFun (M.observedAt (M.observedIndex ⟨v, hv⟩))
          (fun w => M.parentMap s ℓ' (M.observedIndex ⟨v, hv⟩).isLt
            (prevFromObservedValues M x) w)
        = x ⟨v, hv⟩)
  rw [hfun]

private lemma observedAt_observedIndex_subtype (M : Causalean.SCM N Ω)
    {v : SWIGNode N} (hv : v ∈ M.observed) :
    M.observedAt (M.observedIndex ⟨v, hv⟩) = ⟨v, hv⟩ :=
  Subtype.ext (M.observedAt_observedIndex ⟨v, hv⟩)

lemma prevFromObservedValues_apply_observed
    (M : Causalean.SCM N Ω) (x : ValuesOn M.observed (swigΩ Ω))
    {n : ℕ} {hn : n < M.observed.card}
    {w : {w // w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val}}
    (hobs : w.val ∈ M.observed)
    (hlt : (M.observedIndex ⟨w.val, hobs⟩).val < n) :
    (M.observedAt_observedIndex ⟨w.val, hobs⟩) ▸
        prevFromObservedValues M x
          (M.observedIndex ⟨w.val, hobs⟩).val hlt
          (M.observedIndex ⟨w.val, hobs⟩).isLt
      = x ⟨w.val, hobs⟩ := by
  unfold prevFromObservedValues
  set wobs : {v // v ∈ M.observed} := M.observedAt (M.observedIndex ⟨w.val, hobs⟩)
  have hsub : wobs = ⟨w.val, hobs⟩ := by
    change M.observedAt (M.observedIndex ⟨w.val, hobs⟩) = ⟨w.val, hobs⟩
    exact observedAt_observedIndex_subtype M hobs
  change (Subtype.ext_iff.mp hsub) ▸ x wobs = x ⟨w.val, hobs⟩
  clear_value wobs
  subst hsub
  rfl

lemma parentMap_prevFromObservedValues_eq_dispatch
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) (ℓ : M.LatentValues)
    (j : Fin M.observed.card)
    (w : {w // w ∈ M.dag.parents (M.observedAt j).val}) :
    M.parentMap s ℓ j.isLt (prevFromObservedValues M x) w =
      (if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
       else if hfix : w.val ∈ M.fixed then s ⟨w.val, hfix⟩
       else
        have hedge : M.dag.edge w.val (M.observedAt j).val :=
          M.dag.mem_parents.mp w.property
        have hobs : w.val ∈ M.observed := by
          rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
          · rcases Finset.mem_union.mp h1 with hfx | hob
            · exact absurd hfx hfix
            · exact hob
          · exact absurd h2 huo
        x ⟨w.val, hobs⟩) := by
  by_cases huo : w.val ∈ M.unobserved
  · rw [parentMap_unobserved M s ℓ j.isLt _ w huo, dif_pos huo]
  · rw [dif_neg huo]
    by_cases hfix : w.val ∈ M.fixed
    · rw [parentMap_fixed M s ℓ j.isLt _ w huo hfix, dif_pos hfix]
    · rw [dif_neg hfix]
      have hedge : M.dag.edge w.val (M.observedAt j).val :=
        M.dag.mem_parents.mp w.property
      have hobs : w.val ∈ M.observed := by
        rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
        · rcases Finset.mem_union.mp h1 with hfx | hob
          · exact absurd hfx hfix
          · exact hob
        · exact absurd h2 huo
      rw [parentMap_observed M s ℓ j.isLt _ w huo hfix hobs]
      exact prevFromObservedValues_apply_observed M x hobs
        (M.observed_parent_index_lt j.isLt hedge hobs)

private lemma localConsistent_iff_structFun_dispatch_at_observedAt
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) (ℓ : M.LatentValues)
    (j : Fin M.observed.card) :
    M.localConsistent s x (M.observedAt j).val (M.observedAt j).property ℓ ↔
      M.structFun (M.observedAt j)
        (fun w : {w // w ∈ M.dag.parents (M.observedAt j).val} =>
          if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
          else if hfix : w.val ∈ M.fixed then s ⟨w.val, hfix⟩
          else
            have hedge : M.dag.edge w.val (M.observedAt j).val :=
              M.dag.mem_parents.mp w.property
            have hobs : w.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            x ⟨w.val, hobs⟩)
        = x (M.observedAt j) := by
  unfold localConsistent
  have hsub :
      M.observedAt
          (M.observedIndex ⟨(M.observedAt j).val, (M.observedAt j).property⟩)
        = M.observedAt j :=
    observedAt_observedIndex_subtype M (M.observedAt j).property
  have hj :
      M.observedIndex ⟨(M.observedAt j).val, (M.observedAt j).property⟩ = j := by
    rw [show (⟨(M.observedAt j).val, (M.observedAt j).property⟩ :
        {v // v ∈ M.observed}) = M.observedAt j from Subtype.ext rfl]
    exact M.observedIndex_observedAt j
  have hcast :
      (M.observedAt_observedIndex
          ⟨(M.observedAt j).val, (M.observedAt j).property⟩) ▸
        M.structFun
          (M.observedAt
            (M.observedIndex ⟨(M.observedAt j).val, (M.observedAt j).property⟩))
          (fun w =>
            M.parentMap s ℓ
              (M.observedIndex
                ⟨(M.observedAt j).val, (M.observedAt j).property⟩).isLt
              (prevFromObservedValues M x) w)
      =
        M.structFun (M.observedAt j)
          (fun w : {w // w ∈ M.dag.parents (M.observedAt j).val} =>
            M.parentMap s ℓ j.isLt (prevFromObservedValues M x) w) := by
    suffices h : ∀ (k : Fin M.observed.card) (hkj : k = j)
        (hval : (M.observedAt k).val = (M.observedAt j).val),
        (hval ▸
            M.structFun (M.observedAt k)
              (fun w : {w // w ∈ M.dag.parents (M.observedAt k).val} =>
                M.parentMap s ℓ k.isLt (prevFromObservedValues M x) w))
          =
            M.structFun (M.observedAt j)
              (fun w : {w // w ∈ M.dag.parents (M.observedAt j).val} =>
                M.parentMap s ℓ j.isLt (prevFromObservedValues M x) w) by
      exact h _ hj
        (M.observedAt_observedIndex
          ⟨(M.observedAt j).val, (M.observedAt j).property⟩)
    intro k hkj hval
    subst k
    have hrfl : hval = rfl := Subsingleton.elim _ _
    rw [hrfl]
  change
    ((M.observedAt_observedIndex
          ⟨(M.observedAt j).val, (M.observedAt j).property⟩) ▸
        M.structFun
          (M.observedAt
            (M.observedIndex ⟨(M.observedAt j).val, (M.observedAt j).property⟩))
          (fun w =>
            M.parentMap s ℓ
              (M.observedIndex
                ⟨(M.observedAt j).val, (M.observedAt j).property⟩).isLt
              (prevFromObservedValues M x) w)
      = x (M.observedAt j))
      ↔
    (M.structFun (M.observedAt j)
        (fun w : {w // w ∈ M.dag.parents (M.observedAt j).val} =>
          if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
          else if hfix : w.val ∈ M.fixed then s ⟨w.val, hfix⟩
          else
            have hedge : M.dag.edge w.val (M.observedAt j).val :=
              M.dag.mem_parents.mp w.property
            have hobs : w.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            x ⟨w.val, hobs⟩)
        = x (M.observedAt j))
  rw [hcast]
  have hfun :
      M.structFun (M.observedAt j)
          (fun w : {w // w ∈ M.dag.parents (M.observedAt j).val} =>
            M.parentMap s ℓ j.isLt (prevFromObservedValues M x) w)
        =
      M.structFun (M.observedAt j)
          (fun w : {w // w ∈ M.dag.parents (M.observedAt j).val} =>
            if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
            else if hfix : w.val ∈ M.fixed then s ⟨w.val, hfix⟩
            else
              have hedge : M.dag.edge w.val (M.observedAt j).val :=
                M.dag.mem_parents.mp w.property
              have hobs : w.val ∈ M.observed := by
                rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
                · rcases Finset.mem_union.mp h1 with hfx | hob
                  · exact absurd hfx hfix
                  · exact hob
                · exact absurd h2 huo
              x ⟨w.val, hobs⟩) := by
    congr 1
    funext w
    exact parentMap_prevFromObservedValues_eq_dispatch M s x ℓ j w
  rw [hfun]

lemma localConsistent_iff_structFun_dispatch
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) (v : SWIGNode N)
    (hv : v ∈ M.observed) (ℓ : M.LatentValues) :
    M.localConsistent s x v hv ℓ ↔
      M.structFun ⟨v, hv⟩
        (fun w : {w // w ∈ M.dag.parents v} =>
          if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
          else if hfix : w.val ∈ M.fixed then s ⟨w.val, hfix⟩
          else
            have hedge : M.dag.edge w.val v :=
              M.dag.mem_parents.mp w.property
            have hobs : w.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            x ⟨w.val, hobs⟩)
        = x ⟨v, hv⟩ := by
  set j : Fin M.observed.card := M.observedIndex ⟨v, hv⟩ with hj
  set vobs : {v // v ∈ M.observed} := M.observedAt j with hvobs
  have hsub : vobs = ⟨v, hv⟩ := by
    rw [hvobs]
    rw [hj]
    exact observedAt_observedIndex_subtype M hv
  have hiff := localConsistent_iff_structFun_dispatch_at_observedAt M s x ℓ j
  change
    M.localConsistent s x vobs.val vobs.property ℓ ↔
      M.structFun vobs
        (fun w : {w // w ∈ M.dag.parents vobs.val} =>
          if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
          else if hfix : w.val ∈ M.fixed then s ⟨w.val, hfix⟩
          else
            have hedge : M.dag.edge w.val vobs.val :=
              M.dag.mem_parents.mp w.property
            have hobs : w.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            x ⟨w.val, hobs⟩)
        = x vobs at hiff
  clear_value vobs
  subst hsub
  exact hiff

private lemma evalMap_eq_iff_localConsistent_of_observed_parent_agree
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) (ℓ : M.LatentValues)
    (v : SWIGNode N) (hv : v ∈ M.observed)
    (hprev : ∀ w (hw : w ∈ M.observed), M.dag.edge w v →
      M.evalMap s ℓ ⟨w, Finset.mem_union_left _ hw⟩ = x ⟨w, hw⟩) :
    M.evalMap s ℓ ⟨v, Finset.mem_union_left _ hv⟩ = x ⟨v, hv⟩
      ↔ M.localConsistent s x v hv ℓ := by
  rw [evalMap_observed_unfold M s ℓ ⟨v, hv⟩,
      localConsistent_iff_structFun_dispatch M s x v hv ℓ]
  have hfun :
      M.structFun ⟨v, hv⟩
          (fun w : {w // w ∈ M.dag.parents v} =>
            if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
            else if hfix : w.val ∈ M.fixed then s ⟨w.val, hfix⟩
            else
              have hedge : M.dag.edge w.val v := M.dag.mem_parents.mp w.property
              have hobs : w.val ∈ M.observed := by
                rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
                · rcases Finset.mem_union.mp h1 with hfx | hob
                  · exact absurd hfx hfix
                  · exact hob
                · exact absurd h2 huo
              M.evalMap s ℓ ⟨w.val, Finset.mem_union_left _ hobs⟩)
        =
      M.structFun ⟨v, hv⟩
          (fun w : {w // w ∈ M.dag.parents v} =>
            if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
            else if hfix : w.val ∈ M.fixed then s ⟨w.val, hfix⟩
            else
              have hedge : M.dag.edge w.val v := M.dag.mem_parents.mp w.property
              have hobs : w.val ∈ M.observed := by
                rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
                · rcases Finset.mem_union.mp h1 with hfx | hob
                  · exact absurd hfx hfix
                  · exact hob
                · exact absurd h2 huo
              x ⟨w.val, hobs⟩) := by
    congr 1
    funext w
    by_cases huo : w.val ∈ M.unobserved
    · rw [dif_pos huo, dif_pos huo]
    · rw [dif_neg huo, dif_neg huo]
      by_cases hfix : w.val ∈ M.fixed
      · rw [dif_pos hfix, dif_pos hfix]
      · rw [dif_neg hfix, dif_neg hfix]
        have hedge : M.dag.edge w.val v := M.dag.mem_parents.mp w.property
        have hobs : w.val ∈ M.observed := by
          rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
          · rcases Finset.mem_union.mp h1 with hfx | hob
            · exact absurd hfx hfix
            · exact hob
          · exact absurd h2 huo
        exact hprev w.val hobs hedge
  rw [hfun]

private lemma evalMap_eq_x_of_observedAt_eq
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) (ℓ : M.LatentValues)
    (j : Fin M.observed.card) {v : SWIGNode N} (hv : v ∈ M.observed)
    (hval : (M.observedAt j).val = v)
    (h : M.evalMap s ℓ
          ⟨(M.observedAt j).val,
            Finset.mem_union_left M.unobserved (M.observedAt j).property⟩
        = x (M.observedAt j)) :
    M.evalMap s ℓ ⟨v, Finset.mem_union_left _ hv⟩ = x ⟨v, hv⟩ := by
  set vobs : {v // v ∈ M.observed} := M.observedAt j with hvobs
  have hsub : vobs = ⟨v, hv⟩ := by
    rw [hvobs]
    exact Subtype.ext hval
  change
    M.evalMap s ℓ
        ⟨vobs.val, Finset.mem_union_left M.unobserved vobs.property⟩
      = x vobs at h
  clear_value vobs
  subst hsub
  exact h
/-- Local consistency is transported across a `fixSet` intervention when the
fixed intervention coordinates are pinned to the corresponding random
coordinates. -/
lemma localConsistent_fixSet_iff
    (M : Causalean.SCM N Ω) (W : Finset N)
    (hObs : ∀ D ∈ W, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ W, SWIGNode.fixed D ∉ M.fixed)
    (sW : (M.fixSet W hObs hFix).FixedValues) (s : M.FixedValues)
    (x' : ValuesOn (M.fixSet W hObs hFix).observed (swigΩ Ω))
    (x : ValuesOn M.observed (swigΩ Ω))
    (v : SWIGNode N) (hv' : v ∈ (M.fixSet W hObs hFix).observed)
    (hv : v ∈ M.observed)
    (hnot : v ∉ W.image SWIGNode.random)
    (hobsAgree : ∀ w (hw : w ∈ M.observed),
      x' ⟨w, by simpa [fixSet_observed] using hw⟩ = x ⟨w, hw⟩)
    (hpin : ∀ D (hD : D ∈ W),
      x ⟨SWIGNode.random D, hObs D hD⟩ =
        sW ⟨SWIGNode.fixed D,
          Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩)
    (hproj : M.fixSetProj W hObs hFix sW = s)
    (ℓ : M.LatentValues) :
    (M.fixSet W hObs hFix).localConsistent sW x' v hv' ℓ
      ↔ M.localConsistent s x v hv ℓ := by
  rw [localConsistent_iff_structFun_dispatch (M.fixSet W hObs hFix) sW x' v hv' ℓ,
      localConsistent_iff_structFun_dispatch M s x v hv ℓ]
  rw [fixSet_structFun_apply]
  have _ : v ∉ W.image SWIGNode.random := hnot
  have hxv : x' ⟨v, hv'⟩ = x ⟨v, hv⟩ := by
    simpa [fixSet_observed] using hobsAgree v hv
  have hsf :
      M.structFun ⟨v, hv⟩
        (fixMonoParentMap M.toSWIGGraph W hObs hFix v
          (fun w : {w // w ∈ (M.fixSet W hObs hFix).dag.parents v} =>
            if huo : w.val ∈ (M.fixSet W hObs hFix).unobserved then ℓ ⟨w.val, huo⟩
            else if hfix : w.val ∈ (M.fixSet W hObs hFix).fixed then sW ⟨w.val, hfix⟩
            else
              have hedge : (M.fixSet W hObs hFix).dag.edge w.val v :=
                (M.fixSet W hObs hFix).dag.mem_parents.mp w.property
              have hobs : w.val ∈ (M.fixSet W hObs hFix).observed := by
                rcases Finset.mem_union.mp
                    ((M.fixSet W hObs hFix).dag_edges_classified _ _ hedge).1 with h1 | h2
                · rcases Finset.mem_union.mp h1 with hfx | hob
                  · exact absurd hfx hfix
                  · exact hob
                · exact absurd h2 huo
              x' ⟨w.val, hobs⟩))
        =
      M.structFun ⟨v, hv⟩
        (fun w : {w // w ∈ M.dag.parents v} =>
          if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
          else if hfix : w.val ∈ M.fixed then s ⟨w.val, hfix⟩
          else
            have hedge : M.dag.edge w.val v :=
              M.dag.mem_parents.mp w.property
            have hobs : w.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            x ⟨w.val, hobs⟩) := by
    congr 1
    funext w
    have hedgeM : M.dag.edge w.val v := M.dag.mem_parents.mp w.property
    obtain ⟨wVal, hwMem⟩ := w
    simp only at *
    cases wVal with
    | fixed d =>
      have hdfix : SWIGNode.fixed d ∈ M.fixed := by
        by_contra hdf
        have hiso := M.fixed_outside_fixed_isolated d hdf
        have : v ∈ M.dag.children (SWIGNode.fixed d) :=
          M.dag.mem_children.mpr hedgeM
        rw [hiso.2] at this
        exact (Finset.notMem_empty _) this
      have hdfix' : SWIGNode.fixed d ∈ (M.fixSet W hObs hFix).fixed :=
        Finset.mem_union_left _ hdfix
      have hdnuo : SWIGNode.fixed d ∉ M.unobserved := by
        intro h
        obtain ⟨m, hm⟩ := M.unobserved_is_random _ h
        exact absurd hm (by simp)
      have hdnuo' : SWIGNode.fixed d ∉ (M.fixSet W hObs hFix).unobserved := by
        simpa [fixSet_unobserved] using hdnuo
      rw [fixMonoParentMap_apply_fixed M.toSWIGGraph W hObs hFix v _ d hwMem]
      simp only [Subtype.coe_mk]
      rw [dif_neg hdnuo', dif_pos hdfix', dif_neg hdnuo, dif_pos hdfix]
      simpa [fixSetProj, valuesProjection] using
        congrFun hproj (⟨SWIGNode.fixed d, hdfix⟩ : {w // w ∈ M.fixed})
    | random u =>
      by_cases hu : u ∈ W
      · have hru_obs : SWIGNode.random u ∈ M.observed := hObs u hu
        have hru_nuo : SWIGNode.random u ∉ M.unobserved := fun h =>
          (Finset.disjoint_left.mp M.obs_unobs_disjoint hru_obs) h
        have hru_nfix : SWIGNode.random u ∉ M.fixed := by
          intro h
          obtain ⟨m, hm⟩ := M.fixed_is_fixed _ h
          exact absurd hm (by simp)
        have hfu : SWIGNode.fixed u ∈ (M.fixSet W hObs hFix).fixed :=
          fixed_mem_fixSet M W hObs hFix hu
        have hfu_nuo : SWIGNode.fixed u ∉ (M.fixSet W hObs hFix).unobserved := by
          intro h
          obtain ⟨m, hm⟩ := (M.fixSet W hObs hFix).unobserved_is_random _ h
          exact absurd hm (by simp)
        rw [fixMonoParentMap_apply_random M.toSWIGGraph W hObs hFix v u hu _ hwMem]
        simp only [Subtype.coe_mk]
        rw [dif_neg hfu_nuo, dif_pos hfu, dif_neg hru_nuo, dif_neg hru_nfix]
        simpa using (hpin u hu).symm
      · have hru_nfix : SWIGNode.random u ∉ M.fixed := by
          intro h
          obtain ⟨m, hm⟩ := M.fixed_is_fixed _ h
          exact absurd hm (by simp)
        have hru_ndfix : SWIGNode.random u ∉ (M.fixSet W hObs hFix).fixed := by
          intro h
          obtain ⟨m, hm⟩ := (M.fixSet W hObs hFix).fixed_is_fixed _ h
          exact absurd hm (by simp)
        rw [fixMonoParentMap_apply_random_notMem M.toSWIGGraph W hObs hFix v _ u hu hwMem]
        simp only [Subtype.coe_mk]
        by_cases huo : SWIGNode.random u ∈ M.unobserved
        · have huo' : SWIGNode.random u ∈ (M.fixSet W hObs hFix).unobserved := by
            simpa [fixSet_unobserved] using huo
          rw [dif_pos huo', dif_pos huo]
        · have huo' : SWIGNode.random u ∉ (M.fixSet W hObs hFix).unobserved := by
            simpa [fixSet_unobserved] using huo
          rw [dif_neg huo', dif_neg huo, dif_neg hru_ndfix, dif_neg hru_nfix]
          have hru_obs : SWIGNode.random u ∈ M.observed := by
            rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedgeM).1 with h1 | h2
            · rcases Finset.mem_union.mp h1 with hfx | hob
              · exact absurd hfx hru_nfix
              · exact hob
            · exact absurd h2 huo
          simpa [fixSet_observed] using hobsAgree (SWIGNode.random u) hru_obs
  change
    (M.structFun ⟨v, hv⟩
        (fixMonoParentMap M.toSWIGGraph W hObs hFix v
          (fun w : {w // w ∈ (M.fixSet W hObs hFix).dag.parents v} =>
            if huo : w.val ∈ (M.fixSet W hObs hFix).unobserved then ℓ ⟨w.val, huo⟩
            else if hfix : w.val ∈ (M.fixSet W hObs hFix).fixed then sW ⟨w.val, hfix⟩
            else
              have hedge : (M.fixSet W hObs hFix).dag.edge w.val v :=
                (M.fixSet W hObs hFix).dag.mem_parents.mp w.property
              have hobs : w.val ∈ (M.fixSet W hObs hFix).observed := by
                rcases Finset.mem_union.mp
                    ((M.fixSet W hObs hFix).dag_edges_classified _ _ hedge).1 with h1 | h2
                · rcases Finset.mem_union.mp h1 with hfx | hob
                  · exact absurd hfx hfix
                  · exact hob
                · exact absurd h2 huo
              x' ⟨w.val, hobs⟩))
      = x' ⟨v, hv'⟩)
      ↔
    (M.structFun ⟨v, hv⟩
        (fun w : {w // w ∈ M.dag.parents v} =>
          if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
          else if hfix : w.val ∈ M.fixed then s ⟨w.val, hfix⟩
          else
            have hedge : M.dag.edge w.val v :=
              M.dag.mem_parents.mp w.property
            have hobs : w.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            x ⟨w.val, hobs⟩)
      = x ⟨v, hv⟩)
  rw [hsf, hxv]

/-- A finite set of observed nodes is closed under observed parents. -/
def ObsParentClosed
    (M : Causalean.SCM N Ω) (P : Finset (SWIGNode N)) : Prop :=
  P ⊆ M.observed ∧ ∀ v ∈ P, ∀ w ∈ M.observed, M.dag.edge w v → w ∈ P

/-- Agreement of evaluation on an observed-parent-closed set is equivalent to
pointwise local consistency on that set. -/
theorem evalMap_agree_iff_localConsistent
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω)) (ℓ : M.LatentValues) :
    (∀ v (hv : v ∈ P), M.evalMap s ℓ ⟨v, Finset.mem_union_left _ (hP.1 hv)⟩
        = x ⟨v, hP.1 hv⟩)
      ↔ ∀ v (hv : v ∈ P), M.localConsistent s x v (hP.1 hv) ℓ := by
  constructor
  · intro hEval v hv
    exact (evalMap_eq_iff_localConsistent_of_observed_parent_agree
      M s x ℓ v (hP.1 hv) (by
        intro w hwObs hedge
        exact hEval w (hP.2 v hv w hwObs hedge))).mp (hEval v hv)
  · intro hLocal
    suffices hstr : ∀ (n : ℕ) (hn : n < M.observed.card),
        (M.observedAt ⟨n, hn⟩).val ∈ P →
          M.evalMap s ℓ
              ⟨(M.observedAt ⟨n, hn⟩).val,
                Finset.mem_union_left _ (M.observedAt ⟨n, hn⟩).property⟩
            =
          x (M.observedAt ⟨n, hn⟩) by
      intro v hv
      have hidx := hstr (M.observedIndex ⟨v, hP.1 hv⟩).val
        (M.observedIndex ⟨v, hP.1 hv⟩).isLt (by
          have hsub := observedAt_observedIndex_subtype M (hP.1 hv)
          simpa [hsub] using hv)
      have hval :
          (M.observedAt (M.observedIndex ⟨v, hP.1 hv⟩)).val = v :=
        M.observedAt_observedIndex ⟨v, hP.1 hv⟩
      exact evalMap_eq_x_of_observedAt_eq M s x ℓ
        (M.observedIndex ⟨v, hP.1 hv⟩) (hP.1 hv) hval hidx
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro hn hvP
      let vobs : {v // v ∈ M.observed} := M.observedAt ⟨n, hn⟩
      have hiff := evalMap_eq_iff_localConsistent_of_observed_parent_agree
        M s x ℓ vobs.val vobs.property (by
          intro w hwObs hedge
          have hwP : w ∈ P := hP.2 vobs.val hvP w hwObs hedge
          set j : Fin M.observed.card := M.observedIndex ⟨w, hwObs⟩ with hj
          have hlt : j.val < n := by
            rw [hj]
            exact M.observed_parent_index_lt hn hedge hwObs
          have hih := ih j.val hlt j.isLt (by
            have hsub : M.observedAt j = ⟨w, hwObs⟩ := by
              rw [hj]
              exact observedAt_observedIndex_subtype M hwObs
            simpa [hsub] using hwP)
          have hval : (M.observedAt j).val = w := by
            rw [hj]
            exact M.observedAt_observedIndex ⟨w, hwObs⟩
          exact evalMap_eq_x_of_observedAt_eq M s x ℓ j hwObs hval hih)
      exact hiff.mpr (hLocal vobs.val hvP)

end Causalean.SCM
