/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.InterventionSet
import Causalean.Graph.DSep.BackdoorBridges

/-! # Intervention Ancestry

This file relates ancestry in the graph after a set intervention to ancestry in the
original structural causal model. It supplies the graph bridge used to turn a
non-descendant condition in a back-door criterion into the non-ancestry hypothesis
needed for Rule 3 of do-calculus.

The main theorem, `SCM.fixSet_isAncestor_fixed_forward`, lifts a directed ancestry
path starting at an intervened fixed copy in `(M.fixSet X).dag` to an ancestry
path starting at the corresponding random node in the base graph. The auxiliary
`DAG.not_isAncestor_of_root'` records that a root has no proper ancestors.
-/

namespace Causalean

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V] (G : DAG V)

/-- A vertex with no incoming edges has no proper ancestors. -/
lemma not_isAncestor_of_root' {r : V}
    (hr : ∀ u, ¬ G.edge u r) (u : V) : ¬ G.isAncestor u r := by
  intro h
  cases h with
  | edge he => exact hr _ he
  | trans _ he => exact hr _ he

end DAG

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

/-- Helper: edges in `(M.fixSet X).dag` reduce to `splitMonoEdgeRel` of the
    base DAG.  Used to destructure an intervention-graph edge into its
    base-graph source. -/
private lemma fixSet_edge_iff
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (u v : SWIGNode N) :
    (M.fixSet X hX_obs hX_fixed).dag.edge u v ↔
      SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge X u v := by
  simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
             SWIGGraph.splitMonoDAG]

/-- **Forward direction: `.fixed D`-ancestry in `fixSet X` lifts to
    `.random D`-ancestry in the base graph.**

    In `(M.fixSet X).dag`, the split node `.fixed D` (`D ∈ X`) has no
    incoming edges and its outgoing edges are exactly `.random D`'s
    original outgoing edges (rerouted). Interior vertices of a directed
    `.fixed D → v` path cannot be `.random d` with `d ∈ X` (which has no
    outgoing edges in `fixSet X`), nor `.fixed d` with `d ∈ X` (which is
    isolated in `M.dag`, making the IH vacuous). Consequently each step
    lifts to a corresponding base edge. -/
theorem fixSet_isAncestor_fixed_forward
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    {D : N} (hD : D ∈ X) {v : SWIGNode N}
    (h : (M.fixSet X hX_obs hX_fixed).dag.isAncestor (SWIGNode.fixed D) v) :
    M.toSWIGGraph.dag.isAncestor (SWIGNode.random D) v := by
  induction h with
  | edge he =>
    -- Direct edge `.fixed D → v` in `fixSet X`.
    rw [fixSet_edge_iff] at he
    simp only [SWIGGraph.splitMonoEdgeRel, if_pos hD] at he
    exact DAG.isAncestor.edge he
  | @trans w _ _ he ih =>
    -- Case split on the intermediate vertex `w`.
    rw [fixSet_edge_iff] at he
    cases w with
    | random u =>
      simp only [SWIGGraph.splitMonoEdgeRel] at he
      by_cases hu : u ∈ X
      · -- `.random u` (u ∈ X) has no outgoing edges in split; `he` is False.
        simp only [if_pos hu] at he
      · rw [if_neg hu] at he
        exact DAG.isAncestor.trans ih he
    | fixed d =>
      simp only [SWIGGraph.splitMonoEdgeRel] at he
      by_cases hd : d ∈ X
      · -- IH claims `isAncestor_M (.random D) (.fixed d)`, but `.fixed d`
        -- (d ∈ X) is isolated in the base graph, so has no ancestors.
        exfalso
        have hiso := M.toSWIGGraph.fixed_outside_fixed_isolated d (hX_fixed d hd)
        have hNoInc : ∀ x, ¬ M.toSWIGGraph.dag.edge x (SWIGNode.fixed d) := by
          intro x hx
          have : x ∈ M.toSWIGGraph.dag.parents (SWIGNode.fixed d) :=
            M.toSWIGGraph.dag.mem_parents.mpr hx
          rw [hiso.1] at this
          exact (Finset.notMem_empty _) this
        exact M.toSWIGGraph.dag.not_isAncestor_of_root' hNoInc _ ih
      · rw [if_neg hd] at he
        exact DAG.isAncestor.trans ih he

end SCM

end Causalean
