/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.DAG
import Causalean.Graph.SWIG
import Causalean.Graph.SWIGSplitMono
import Causalean.Graph.CComponents
import Causalean.SCM.ID.GraphicalThms.DoGFormulaRec
import Causalean.SCM.ID.DiscreteID.Checker

/-! # Frontdoor Example

This file constructs the canonical frontdoor graph with one latent confounder
between treatment and outcome, an observed mediator, and no intervention fixed
at the initial graph. The declarations `FDNode`, `fdEdge`, `fdDAG`, and `fdSWIG`
define the graph and standard SWIG representation. The examples verify the
c-components, show that the recursive ID certificate `idSucceedsRec` succeeds
for `P(Y | do(X))`, show that the simpler no-fixing reachability certificate
does not apply to the same outcome district, and check that the executable
`idAlgorithm` returns `true` on the concrete graph.
-/

set_option linter.style.nativeDecide false

namespace Causalean.SCM.Examples.Frontdoor

-- ============================================================
-- Vertex type
-- ============================================================

/-- The frontdoor example has latent confounder, treatment, mediator, and outcome vertices. -/
inductive FDNode
  | fdU  -- latent confounder of X and Y
  | fdX  -- treatment
  | fdM  -- mediator
  | fdY  -- outcome
  deriving DecidableEq, Repr

open FDNode

/-- The frontdoor-example vertex set is finite, with four named vertices. -/
instance : Fintype FDNode where
  elems := {fdU, fdX, fdM, fdY}
  complete := by intro x; cases x <;> simp

-- ============================================================
-- Edge relation
-- ============================================================

/-- The frontdoor graph has latent confounding of X and Y, and the directed path X → M → Y. -/
def fdEdge : FDNode → FDNode → Prop
  | fdU, fdX => True
  | fdU, fdY => True
  | fdX, fdM => True
  | fdM, fdY => True
  | _,   _   => False

/-- Whether a proposed frontdoor-example edge is present is decidable by endpoint cases. -/
instance : DecidableRel fdEdge := by
  intro a b; cases a <;> cases b <;> simp [fdEdge] <;> infer_instance

-- ============================================================
-- Topological order
-- ============================================================

/-- The frontdoor graph orders latent confounder, treatment, mediator, then outcome. -/
def fdTopo : FDNode → ℕ
  | fdU => 0
  | fdX => 1
  | fdM => 2
  | fdY => 3

/-- Every frontdoor edge points from an earlier to a later node in the chosen order. -/
theorem fdTopo_lt : ∀ u v, fdEdge u v → fdTopo u < fdTopo v := by
  intro u v h; cases u <;> cases v <;> simp_all [fdEdge, fdTopo]

-- ============================================================
-- The DAG
-- ============================================================

/-- This directed acyclic graph formalizes the canonical frontdoor example. -/
def fdDAG : DAG FDNode where
  edge := fdEdge
  decEdge := inferInstance
  acyclic := DAG.acyclic_of_topoOrder fdTopo_lt

-- ============================================================
-- SWIG graph (standard model, no intervention)
-- ============================================================

/-- This SWIG graph represents the frontdoor example before any intervention. -/
def fdSWIG : SWIGGraph FDNode where
  dag := initialSWIG fdDAG
  fixed := ∅
  observed := {SWIGNode.random fdX, SWIGNode.random fdM, SWIGNode.random fdY}
  unobserved := {SWIGNode.random fdU}
  fixed_is_fixed := by intro s hs; simp at hs
  observed_is_random := by
    intro v hv; simp at hv
    rcases hv with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  unobserved_is_random := by
    intro u hu; simp at hu
    subst hu
    exact ⟨_, rfl⟩
  obs_unobs_disjoint := by native_decide
  dag_edges_classified := by native_decide
  fixed_image_in_observed := by intro s hs; simp at hs
  fixed_are_roots := by intro s hs; simp at hs
  unobs_are_roots := by
    intro u hu; simp at hu
    subst hu
    simpa [initialSWIG] using
      swig_random_root_of_root fdDAG ∅ fdU (by native_decide : fdDAG.parents fdU = ∅)
  fixed_outside_fixed_isolated := by
    intro n _
    cases n <;> exact ⟨by native_decide, by native_decide⟩
  all_children_in_observed := by native_decide

-- ============================================================
-- C-components and recursive ID witness
-- ============================================================

example : fdSWIG.cComponentOf (SWIGNode.random fdX) =
    {SWIGNode.random fdX, SWIGNode.random fdY} := by native_decide

example : fdSWIG.cComponentOf (SWIGNode.random fdM) =
    {SWIGNode.random fdM} := by native_decide

example : fdSWIG.cComponentOf (SWIGNode.random fdY) =
    {SWIGNode.random fdX, SWIGNode.random fdY} := by native_decide

example : Causalean.SCM.ID.inducedAncestral fdSWIG
    ({SWIGNode.random fdX, SWIGNode.random fdY} : Finset (SWIGNode FDNode))
    ({SWIGNode.random fdY} : Finset (SWIGNode FDNode)) =
    {SWIGNode.random fdY} := by
  unfold Causalean.SCM.ID.inducedAncestral
  simp [SWIGGraph.induce]
  native_decide

example : Causalean.SCM.ID.containingCComponent fdSWIG
    ({SWIGNode.random fdY} : Finset (SWIGNode FDNode)) =
    {SWIGNode.random fdX, SWIGNode.random fdY} := by
  unfold Causalean.SCM.ID.containingCComponent
  split
  · rename_i hne
    have hchoose :
        Exists.choose hne = SWIGNode.random fdY := by
      have hmem := Exists.choose_spec hne
      simpa using hmem
    rw [hchoose]
    native_decide
  · rename_i hne
    exact False.elim (hne (by simp))

example : Causalean.SCM.ID.idSucceedsRec ({fdX} : Finset FDNode)
    ({SWIGNode.random fdY} : Finset (SWIGNode FDNode)) fdSWIG := by
  let hX : Causalean.SCM.ID.interventionValid {fdX} fdSWIG := by
    refine ⟨?_, ?_⟩
    · intro D hD
      simp at hD
      subst hD
      native_decide
    · intro D hD
      simp at hD
      subst hD
      native_decide
  refine ⟨hX, ?_, ?_, ?_⟩
  · native_decide
  · decide
  · intro S hS
    have hSet :
        ((fdSWIG.splitMono {fdX} hX.1 hX.2).induce
          ((fdSWIG.splitMono {fdX} hX.1 hX.2).dag.ancestralSet
            ({SWIGNode.random fdY} : Finset (SWIGNode FDNode)))).cComponentSet =
        ({ {SWIGNode.random fdM}, {SWIGNode.random fdY} } :
          Finset (Finset (SWIGNode FDNode))) := by
      rw [SWIGGraph.cComponentSet]
      simp [SWIGGraph.splitMono, SWIGGraph.induce]
      native_decide
    rw [hSet] at hS
    simp at hS
    rcases hS with hS | hS
    · subst hS
      have hMmem :
          ({SWIGNode.random fdM} : Finset (SWIGNode FDNode)) ∈ fdSWIG.cComponentSet := by
        rw [SWIGGraph.cComponentSet]
        refine Finset.mem_image.mpr ⟨SWIGNode.random fdM, by native_decide, ?_⟩
        native_decide
      rw [Causalean.SCM.ID.containingCComponent_of_mem_cComponentSet fdSWIG _ hMmem]
      exact Causalean.SCM.ID.CFactorReachableRec.base (by simp) (by simp)
        (Causalean.SCM.ID.inducedAncestral_self_of_mem_cComponentSet fdSWIG _ hMmem)
    · subst hS
      have hContaining :
          Causalean.SCM.ID.containingCComponent fdSWIG
            ({SWIGNode.random fdY} : Finset (SWIGNode FDNode)) =
          {SWIGNode.random fdX, SWIGNode.random fdY} := by
        unfold Causalean.SCM.ID.containingCComponent
        split
        · rename_i hne
          have hchoose :
              Exists.choose hne = SWIGNode.random fdY := by
            have hmem := Exists.choose_spec hne
            simpa using hmem
          rw [hchoose]
          native_decide
        · rename_i hne
          exact False.elim (hne (by simp))
      rw [hContaining]
      exact Causalean.SCM.ID.CFactorReachableRec.base (by simp) (by simp) (by
        unfold Causalean.SCM.ID.inducedAncestral
        simp [SWIGGraph.induce]
        native_decide)

example : ¬ Causalean.SCM.ID.cFactorReachable fdSWIG
    (Causalean.SCM.ID.containingCComponent fdSWIG
      ({SWIGNode.random fdY} : Finset (SWIGNode FDNode)))
    ({SWIGNode.random fdY} : Finset (SWIGNode FDNode)) := by
  rintro ⟨_, _, hmem⟩
  have hnot :
      ({SWIGNode.random fdY} : Finset (SWIGNode FDNode)) ∉ fdSWIG.cComponentSet := by
    rw [SWIGGraph.cComponentSet]
    native_decide
  exact hnot hmem

/-! ### Running the executable checker

The `idAlgorithm` decision procedure *computes* on the concrete frontdoor graph and
returns `true` — a verified "P(Y ∣ do(X)) is identifiable", with the fixing step the
no-fixing fragment cannot handle. -/

/-- `#eval` runs the checker; it prints `true`. -/
example :
    Causalean.SCM.ID.idAlgorithm 10 fdSWIG ({fdX} : Finset FDNode)
      ({SWIGNode.random fdY} : Finset (SWIGNode FDNode)) = true := by
  native_decide

end Causalean.SCM.Examples.Frontdoor
