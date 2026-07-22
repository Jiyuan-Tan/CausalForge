/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.SCM
import Causalean.Graph.SWIGSplitMono

/-! # Monolithic Multi-Target Intervention

This file defines the one-shot version of a multi-target intervention on a
structural causal model. It reroutes all affected outgoing edges in a single
graph transformation, which gives later comparison lemmas direct access to the
unchanged structural functions at unaffected vertices.

The graph layer is the monolithic SWIG split; latent distributions are inherited
unchanged, and structural functions use one parent reindexing map rather than
iterated single-target interventions.

## Main definitions and results

* `SCM.fixMonoParentMap` reindexes split-graph parent tuples back to the parent
  tuple expected by the original structural function.
* `SCM.fixMono` builds the monolithic multi-target intervention SCM, inheriting
  latent laws and reusing structural functions through `fixMonoParentMap`.
* `SCM.fixMono_observed`, `SCM.fixMono_unobserved`, `SCM.fixMono_fixed`, and
  `SCM.fixMono_latentDist` expose the preserved or enlarged primitive fields.
* `SCM.fixMono_parents_eq_of_no_fixed_parent` gives parent-set coincidence at
  vertices whose post-intervention parents contain no targeted fixed copy.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

-- ============================================================
-- Monolithic parent reindex
-- ============================================================

/-- The monolithic parent reindexer converts split-graph parent values into the parent values expected by the original structural function.

    Parent reindexing used by `fixMono`: takes a parent-value tuple over the
    monolithically-split graph `G.splitMono X …` at vertex `v` and produces
    the corresponding tuple over the original `G.dag.parents v`.

    For each `D ∈ X`, the `.random D` coordinate of the original parent set is
    read from the `.fixed D` position of the split-graph tuple (since
    `.random D` is no longer a parent there, but `.fixed D` is, whenever
    `.random D` was an original parent).  All other coordinates are copied. -/
noncomputable def fixMonoParentMap
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (v : SWIGNode N)
    (ξ : ∀ w' : {w' // w' ∈ (G.splitMono X hObs hFix).dag.parents v},
            swigΩ Ω w'.val) :
    ∀ w : {w // w ∈ G.dag.parents v}, swigΩ Ω w.val
  | ⟨SWIGNode.random u, hwVal⟩ =>
      if hu : u ∈ X then
        ξ ⟨SWIGNode.fixed u,
          (SWIGGraph.splitMono_parents_char G X hObs hFix v (SWIGNode.fixed u)).2
            (Or.inr ⟨u, hu, rfl, hwVal⟩)⟩
      else
        ξ ⟨SWIGNode.random u,
          (SWIGGraph.splitMono_parents_char G X hObs hFix v (SWIGNode.random u)).2
            (Or.inl ⟨hwVal,
              fun D hD heq => hu (SWIGNode.random.inj heq ▸ hD)⟩)⟩
  | ⟨SWIGNode.fixed d, hwVal⟩ =>
      ξ ⟨SWIGNode.fixed d,
        (SWIGGraph.splitMono_parents_char G X hObs hFix v (SWIGNode.fixed d)).2
          (Or.inl ⟨hwVal, fun _ _ heq => by cases heq⟩)⟩

/-- At a fixed-coordinate parent, the monolithic parent reindexer reads the same fixed coordinate from the split graph.

    Pointwise evaluation of `fixMonoParentMap` at a `.fixed d` coordinate:
    the input tuple is read directly at `.fixed d`. -/
lemma fixMonoParentMap_apply_fixed
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (v : SWIGNode N)
    (ξ : ∀ w' : {w' // w' ∈ (G.splitMono X hObs hFix).dag.parents v},
            swigΩ Ω w'.val)
    (d : N) (hwVal : SWIGNode.fixed d ∈ G.dag.parents v) :
    fixMonoParentMap (Ω := Ω) G X hObs hFix v ξ
        (⟨SWIGNode.fixed d, hwVal⟩ : {w // w ∈ G.dag.parents v})
      = ξ ⟨SWIGNode.fixed d,
          (SWIGGraph.splitMono_parents_char G X hObs hFix v
              (SWIGNode.fixed d)).2
            (Or.inl ⟨hwVal, fun _ _ heq => by cases heq⟩)⟩ := rfl

/-- At an untreated random-coordinate parent, the monolithic parent reindexer reads the same random coordinate from the split graph.

    Pointwise evaluation of `fixMonoParentMap` at a `.random u` coordinate
    with `u ∉ X`: the input tuple is read directly at `.random u`. -/
lemma fixMonoParentMap_apply_random_notMem
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (v : SWIGNode N)
    (ξ : ∀ w' : {w' // w' ∈ (G.splitMono X hObs hFix).dag.parents v},
            swigΩ Ω w'.val)
    (u : N) (hu : u ∉ X) (hwVal : SWIGNode.random u ∈ G.dag.parents v) :
    fixMonoParentMap (Ω := Ω) G X hObs hFix v ξ
        (⟨SWIGNode.random u, hwVal⟩ : {w // w ∈ G.dag.parents v})
      = ξ ⟨SWIGNode.random u,
          (SWIGGraph.splitMono_parents_char G X hObs hFix v
              (SWIGNode.random u)).2
            (Or.inl ⟨hwVal,
              fun D hD heq => hu (SWIGNode.random.inj heq ▸ hD)⟩)⟩ := by
  unfold fixMonoParentMap
  simp only [dif_neg hu]

/-- At a treated random-coordinate parent, the monolithic parent reindexer reads the corresponding fixed coordinate from the split graph.

    Pointwise evaluation of `fixMonoParentMap` at a `.random D` coordinate
    (D ∈ X): value is read from the `.fixed D` position of the split-graph
    tuple. -/
lemma fixMonoParentMap_apply_random
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (v : SWIGNode N) (D : N) (hD : D ∈ X)
    (ξ : ∀ w' : {w' // w' ∈ (G.splitMono X hObs hFix).dag.parents v},
            swigΩ Ω w'.val)
    (hD_parent : SWIGNode.random D ∈ G.dag.parents v) :
    fixMonoParentMap (Ω := Ω) G X hObs hFix v ξ
        (⟨SWIGNode.random D, hD_parent⟩ : {w // w ∈ G.dag.parents v})
      = ξ ⟨SWIGNode.fixed D,
          (SWIGGraph.splitMono_parents_char G X hObs hFix v
              (SWIGNode.fixed D)).2
            (Or.inr ⟨D, hD, rfl, hD_parent⟩)⟩ := by
  unfold fixMonoParentMap
  simp only [dif_pos hD]

/-- Measurability of `fixMonoParentMap` at a fixed vertex, as a function of
    the input parent tuple. -/
private lemma measurable_fixMonoParentMap
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (v : SWIGNode N) :
    Measurable (fixMonoParentMap (Ω := Ω) G X hObs hFix v) := by
  classical
  refine measurable_pi_iff.mpr ?_
  rintro ⟨wVal, hwVal⟩
  match wVal, hwVal with
  | SWIGNode.random u, hwVal =>
    by_cases hu : u ∈ X
    · have h_eq : (fun ξ : ∀ w' : {w' // w' ∈ (G.splitMono X hObs hFix).dag.parents v},
              swigΩ Ω w'.val =>
          fixMonoParentMap G X hObs hFix v ξ
            (⟨SWIGNode.random u, hwVal⟩ : {w // w ∈ G.dag.parents v}))
        = (fun ξ => ξ ⟨SWIGNode.fixed u,
            (SWIGGraph.splitMono_parents_char G X hObs hFix v
                (SWIGNode.fixed u)).2 (Or.inr ⟨u, hu, rfl, hwVal⟩)⟩) := by
        funext ξ
        exact fixMonoParentMap_apply_random (Ω := Ω) G X hObs hFix v u hu ξ hwVal
      rw [h_eq]
      exact measurable_pi_apply _
    · have h_eq : (fun ξ : ∀ w' : {w' // w' ∈ (G.splitMono X hObs hFix).dag.parents v},
              swigΩ Ω w'.val =>
          fixMonoParentMap G X hObs hFix v ξ
            (⟨SWIGNode.random u, hwVal⟩ : {w // w ∈ G.dag.parents v}))
        = (fun ξ => ξ ⟨SWIGNode.random u,
            (SWIGGraph.splitMono_parents_char G X hObs hFix v
                (SWIGNode.random u)).2 (Or.inl ⟨hwVal,
                  fun D hD heq => hu (SWIGNode.random.inj heq ▸ hD)⟩)⟩) := by
        funext ξ
        exact fixMonoParentMap_apply_random_notMem (Ω := Ω) G X hObs hFix v ξ u hu hwVal
      rw [h_eq]
      exact measurable_pi_apply _
  | SWIGNode.fixed d, hwVal =>
    have h_eq : (fun ξ : ∀ w' : {w' // w' ∈ (G.splitMono X hObs hFix).dag.parents v},
            swigΩ Ω w'.val =>
        fixMonoParentMap G X hObs hFix v ξ
          (⟨SWIGNode.fixed d, hwVal⟩ : {w // w ∈ G.dag.parents v}))
      = (fun ξ => ξ ⟨SWIGNode.fixed d,
          (SWIGGraph.splitMono_parents_char G X hObs hFix v
              (SWIGNode.fixed d)).2
            (Or.inl ⟨hwVal, fun _ _ heq => by cases heq⟩)⟩) := by
      funext ξ
      exact fixMonoParentMap_apply_fixed (Ω := Ω) G X hObs hFix v ξ d hwVal
    rw [h_eq]
    exact measurable_pi_apply _

-- ============================================================
-- The monolithic do operation
-- ============================================================

/-- The monolithic generalized intervention applies all target splits at once while inheriting latent laws and reindexing structural parents.

    **Monolithic multi-target generalized do.** (Definition 8, one-shot form.)

    Graph layer is `SWIGGraph.splitMono`; latents and structural functions
    are inherited from `M` with parent tuples reindexed through
    `fixMonoParentMap`. -/
noncomputable def fixMono (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    Causalean.SCM N Ω := by
  classical
  let G' : SWIGGraph N := M.toSWIGGraph.splitMono X hObs hFix
  -- Edge-type assignment on the split graph: edges out of `.fixed D` (D ∈ X)
  -- inherit the types of the corresponding `.random D`-outgoing edges.
  let edgeTypes' : EdgeTypeAssignment G'.dag :=
    { edgeType :=
        fun u v =>
          if h : ∃ D ∈ X, u = SWIGNode.fixed D then
            M.edgeTypes.edgeType (SWIGNode.random (Classical.choose h)) v
          else
            M.edgeTypes.edgeType u v }
  -- Observed set is unchanged by `splitMono`, so every observed node of the
  -- split graph is observed in the original model.
  have observed_in_original :
      ∀ v' : {v // v ∈ G'.observed}, v'.val ∈ M.observed := by
    intro v'
    exact v'.property
  refine
    { dag        := G'.dag
      fixed      := G'.fixed
      observed   := G'.observed
      unobserved := G'.unobserved
      fixed_is_fixed        := G'.fixed_is_fixed
      observed_is_random    := G'.observed_is_random
      unobserved_is_random  := G'.unobserved_is_random
      obs_unobs_disjoint    := G'.obs_unobs_disjoint
      dag_edges_classified  := G'.dag_edges_classified
      fixed_image_in_observed := G'.fixed_image_in_observed
      fixed_are_roots       := G'.fixed_are_roots
      unobs_are_roots       := G'.unobs_are_roots
      fixed_outside_fixed_isolated := G'.fixed_outside_fixed_isolated
      all_children_in_observed := G'.all_children_in_observed
      edgeTypes := edgeTypes'
      iota_valueSpace := ?_
      structFun := ?_
      structFun_measurable := ?_
      latentDist := M.latentDist
      isProbability_latent := M.isProbability_latent }
  · -- `iota_valueSpace`
    intro s
    rcases s with ⟨sVal, hs⟩
    rcases G'.fixed_is_fixed sVal hs with ⟨n, rfl⟩
    simp [iotaMap]
  · -- `structFun`
    intro v' ξ
    have hv_obs : v'.val ∈ M.observed := observed_in_original v'
    exact M.structFun ⟨v'.val, hv_obs⟩
      (fixMonoParentMap M.toSWIGGraph X hObs hFix v'.val ξ)
  · -- `structFun_measurable`
    intro v'
    have hv_obs : v'.val ∈ M.observed := observed_in_original v'
    exact (M.structFun_measurable ⟨v'.val, hv_obs⟩).comp
      (measurable_fixMonoParentMap M.toSWIGGraph X hObs hFix v'.val)

-- ============================================================
-- Interface lemmas
-- ============================================================

/-- The monolithic intervention preserves the observed node set. -/
@[simp] lemma fixMono_observed (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    (M.fixMono X hObs hFix).observed = M.observed := rfl

/-- The monolithic intervention preserves the unobserved node set. -/
@[simp] lemma fixMono_unobserved (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    (M.fixMono X hObs hFix).unobserved = M.unobserved := rfl

/-- The monolithic intervention's fixed node set is the old fixed set plus the fixed copies of the targets. -/
@[simp] lemma fixMono_fixed (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    (M.fixMono X hObs hFix).fixed = M.fixed ∪ X.image SWIGNode.fixed := rfl

/-- The monolithic intervention leaves every latent-root distribution unchanged. -/
@[simp] lemma fixMono_latentDist (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (u : {u // u ∈ (M.fixMono X hObs hFix).unobserved}) :
    (M.fixMono X hObs hFix).latentDist u = M.latentDist u := rfl

/-- The original fixed node set is contained in the fixed node set after the monolithic intervention. -/
lemma fixMono_fixed_subset (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    M.fixed ⊆ (M.fixMono X hObs hFix).fixed := by
  intro x hx
  rw [fixMono_fixed]
  exact Finset.mem_union_left _ hx

/-- The fixed copies of the intervention targets are contained in the fixed node set after the monolithic intervention. -/
lemma fixMono_image_fixed_subset (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    X.image SWIGNode.fixed ⊆ (M.fixMono X hObs hFix).fixed := by
  intro x hx
  rw [fixMono_fixed]
  exact Finset.mem_union_right _ hx

/-- If no fixed copy of a target is a parent of a vertex after intervention, that vertex has the same parents as before.

    **Parent-set coincidence at non-`.fixed`-targeted vertices (SCM level).**

    If no `.fixed D` (D ∈ X) is a parent of `v` in the monolithic-do SCM,
    then `v`'s parent set coincides with `v`'s parent set in the base SCM.
    Delegates to `SWIGGraph.splitMono_parents_eq_of_no_fixed_parent`. -/
lemma fixMono_parents_eq_of_no_fixed_parent
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    {v : SWIGNode N}
    (hNoFP : ∀ D ∈ X,
      SWIGNode.fixed D ∉ (M.fixMono X hObs hFix).dag.parents v) :
    (M.fixMono X hObs hFix).dag.parents v = M.dag.parents v := by
  -- `(M.fixMono X).dag = (M.toSWIGGraph.splitMono X …).dag` by definition.
  exact SWIGGraph.splitMono_parents_eq_of_no_fixed_parent
    M.toSWIGGraph X hObs hFix v hNoFP

end SCM

end Causalean
