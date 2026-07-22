/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Example: Backdoor Adjustment DAG

This file constructs the canonical backdoor-adjustment DAG and exercises the
DAG, d-separation, and SWIG/splitMono APIs.

## The DAG

```
    Z
   ↙ ↘
  D → Y
```

- Observed: D (treatment, binary), Y (outcome, continuous), Z (confounder)
- Unobserved confounders: none (Z is observed here, unlike the IV setting)
- Latent root noise sources: U₁ (root for Z), U₂ (root for D), and U₃
  (root for Y), included as independent exogenous roots satisfying
  `SWIGGraph.unobs_are_roots`.
- The backdoor criterion: Z satisfies the backdoor criterion for (D, Y)
  because (i) no element of Z is a descendant of D, and (ii) Z blocks all
  backdoor paths from D to Y (the only such path D ← Z → Y is blocked by
  conditioning on Z).

## Backdoor criterion (informal)

Z satisfies the backdoor criterion for (D → Y) in a DAG G if:
  (i)  No node in Z is a descendant of D.
  (ii) Z d-separates Y from D in the lower-bar graph G_{D̄}
       (i.e., the SWIG after splitting D = the graph where D's incoming
       edges are cut, operationally `bdSWIG.splitMono {bdD}`).

We demonstrate (ii) directly via `splitMono`.
-/

import Causalean.Graph.DAG
import Causalean.Graph.DSep.Separation
import Causalean.Graph.SWIG
import Causalean.Graph.SWIGSplitMono
import Causalean.Graph.CComponents
import Causalean.SCM.Model.EdgeType
import Causalean.SCM.Model.SCM
import Causalean.SCM.ID.BackdoorCriterion
import Causalean.SCM.ID.GraphicalThms.DoGFormula

/-! # Backdoor Adjustment Example

This file constructs the canonical directed acyclic graph for backdoor
adjustment, with a treatment, an outcome, an observed confounder, and latent root
noise variables. The declarations `BDNode`, `bdEdge`, `bdDAG`, and `bdSWIG`
define the graph and its standard SWIG representation. The examples check
parents, roots, c-components, ID reachability, and the split-graph
d-separation condition behind the graphical backdoor criterion; the final
backdoor-criterion example verifies that the observed confounder is a valid
adjustment set for the treatment-outcome effect.
-/

set_option linter.style.nativeDecide false

namespace Causalean.SCM.Examples.BackDoor

-- ============================================================
-- Vertex type
-- ============================================================

/-- The backdoor example has treatment, outcome, observed-confounder, and three latent-root vertices. -/
inductive BDNode
  | bdD  -- treatment
  | bdY  -- outcome
  | bdZ  -- observed confounder
  | bdU1 -- latent root for Z
  | bdU2 -- latent root for D
  | bdU3 -- latent root for Y
  deriving DecidableEq

open BDNode

namespace instReprBDNode

/--
For each vertex of the backdoor-adjustment DAG and each natural-number precedence level, this
method returns a formatted textual rendering of that vertex. There are no additional hypotheses
or side conditions.

This helper is the explicit form of the representation method that `deriving Repr` would generate.
-/
protected def repr : BDNode → Nat → Std.Format
  | bdD, _ => "Causalean.SCM.Examples.BackDoor.BDNode.bdD"
  | bdY, _ => "Causalean.SCM.Examples.BackDoor.BDNode.bdY"
  | bdZ, _ => "Causalean.SCM.Examples.BackDoor.BDNode.bdZ"
  | bdU1, _ => "Causalean.SCM.Examples.BackDoor.BDNode.bdU1"
  | bdU2, _ => "Causalean.SCM.Examples.BackDoor.BDNode.bdU2"
  | bdU3, _ => "Causalean.SCM.Examples.BackDoor.BDNode.bdU3"

end instReprBDNode

/-- Backdoor-example vertices can be rendered as their fully qualified constructor names. -/
instance instReprBDNode : Repr BDNode where
  reprPrec := instReprBDNode.repr

/-- The backdoor-example vertex set is finite, with six named vertices. -/
instance : Fintype BDNode where
  elems := {bdD, bdY, bdZ, bdU1, bdU2, bdU3}
  complete := by intro x; cases x <;> simp

-- ============================================================
-- Edge relation
-- ============================================================

/-- The backdoor graph has confounding paths through the observed confounder, a direct treatment-outcome edge, and one latent root for each observed node. -/
def bdEdge : BDNode → BDNode → Prop
  | bdZ,  bdD  => True
  | bdZ,  bdY  => True
  | bdD,  bdY  => True
  | bdU1, bdZ  => True
  | bdU2, bdD  => True
  | bdU3, bdY  => True
  | _,    _    => False

/-- Whether a proposed backdoor-example edge is present is decidable by case analysis on the endpoints. -/
instance : DecidableRel bdEdge := by
  intro a b; cases a <;> cases b <;> simp [bdEdge] <;> infer_instance

-- ============================================================
-- Topological order
-- ============================================================

/-- The backdoor graph orders latent roots first, then confounder, treatment, and outcome. -/
def bdTopo : BDNode → ℕ
  | bdU1 => 0
  | bdU2 => 1
  | bdU3 => 2
  | bdZ  => 3
  | bdD  => 4
  | bdY  => 5

/-- Every edge in the backdoor graph points from an earlier to a later node in the chosen topological order. -/
theorem bdTopo_lt : ∀ u v, bdEdge u v → bdTopo u < bdTopo v := by
  intro u v h; cases u <;> cases v <;> simp_all [bdEdge, bdTopo]

-- ============================================================
-- The DAG
-- ============================================================

/-- This directed acyclic graph formalizes the canonical backdoor-adjustment example. -/
def bdDAG : DAG BDNode where
  edge := bdEdge
  decEdge := inferInstance
  acyclic := DAG.acyclic_of_topoOrder bdTopo_lt

-- ============================================================
-- Testing DAG.lean: parents and roots
-- ============================================================

-- Z and U₂ are parents of D
example : bdZ  ∈ bdDAG.parents bdD := by decide
example : bdU2 ∈ bdDAG.parents bdD := by decide

-- Z, D, U₃ are parents of Y
example : bdZ  ∈ bdDAG.parents bdY := by decide
example : bdD  ∈ bdDAG.parents bdY := by decide
example : bdU3 ∈ bdDAG.parents bdY := by decide

-- Latent roots have no parents
example : bdDAG.parents bdU1 = ∅ := by native_decide
example : bdDAG.parents bdU2 = ∅ := by native_decide
example : bdDAG.parents bdU3 = ∅ := by native_decide

-- U₁, U₂, U₃ are roots; D, Y, Z are not
example : bdDAG.isRoot bdU1 := by native_decide
example : bdDAG.isRoot bdU2 := by native_decide
example : bdDAG.isRoot bdU3 := by native_decide
example : ¬bdDAG.isRoot bdD := by native_decide
example : ¬bdDAG.isRoot bdY := by native_decide
example : ¬bdDAG.isRoot bdZ := by native_decide

-- ============================================================
-- Testing DSep.lean: d-separation in the full DAG
-- ============================================================

-- Y and D are NOT d-separated by ∅ (direct edge D → Y)
example : ¬bdDAG.dSep {bdY} {bdD} ∅ := by decide

-- Y and D ARE d-separated by {Z} (Z blocks D ← Z → Y AND direct path is not a backdoor)
-- Actually: {D → Y} is still open. The backdoor path D ← Z → Y is blocked by Z.
-- But {D → Y} alone means dSep {D} {Y} {Z} is False.
example : ¬bdDAG.dSep {bdD} {bdY} {bdZ} := by native_decide

-- Z d-separates Y from D in the *interventional* graph (see splitMono below)

-- Instrument: Z and U₂ are NOT d-separated by ∅ (path Z → D ← U₂ is blocked by D;
-- but Z → D is direct, so Z and D are not d-sep by ∅)
example : ¬bdDAG.dSep {bdZ} {bdD} ∅ := by decide

-- U₁ and U₂ are d-separated by ∅ (no path between them)
example : bdDAG.dSep {bdU1} {bdU2} ∅ := by decide

-- ============================================================
-- SWIG graph (standard model, no intervention)
-- ============================================================

/-- This SWIG graph represents the backdoor example before any intervention.

The treatment, outcome, and confounder are observed random nodes, while the three
latent roots are unobserved random nodes. -/
def bdSWIG : SWIGGraph BDNode where
  dag := initialSWIG bdDAG
  fixed := ∅
  observed := {SWIGNode.random bdD, SWIGNode.random bdY, SWIGNode.random bdZ}
  unobserved := {SWIGNode.random bdU1, SWIGNode.random bdU2, SWIGNode.random bdU3}
  fixed_is_fixed := by intro s hs; simp at hs
  observed_is_random := by
    intro v hv; simp at hv
    rcases hv with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  unobserved_is_random := by
    intro u hu; simp at hu
    rcases hu with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  obs_unobs_disjoint := by native_decide
  dag_edges_classified := by native_decide
  fixed_image_in_observed := by intro s hs; simp at hs
  fixed_are_roots := by intro s hs; simp at hs
  unobs_are_roots := by
    intro u hu; simp at hu
    rcases hu with rfl | rfl | rfl
    · simpa [initialSWIG] using
        swig_random_root_of_root bdDAG ∅ bdU1 (by native_decide : bdDAG.parents bdU1 = ∅)
    · simpa [initialSWIG] using
        swig_random_root_of_root bdDAG ∅ bdU2 (by native_decide : bdDAG.parents bdU2 = ∅)
    · simpa [initialSWIG] using
        swig_random_root_of_root bdDAG ∅ bdU3 (by native_decide : bdDAG.parents bdU3 = ∅)
  fixed_outside_fixed_isolated := by
    intro n _
    cases n <;> exact ⟨by native_decide, by native_decide⟩
  all_children_in_observed := by native_decide

-- ============================================================
-- C-components
-- ============================================================

-- D and Y share no unobserved parent in this DAG (their unobserved parents are distinct)
example : ¬bdSWIG.directlyConfounded (SWIGNode.random bdD) (SWIGNode.random bdY) := by decide

-- D and Z share no unobserved parent
example : ¬bdSWIG.directlyConfounded (SWIGNode.random bdD) (SWIGNode.random bdZ) := by decide

-- Each observed node is its own singleton C-component
example : bdSWIG.cComponentOf (SWIGNode.random bdD) = {SWIGNode.random bdD} := by native_decide
example : bdSWIG.cComponentOf (SWIGNode.random bdY) = {SWIGNode.random bdY} := by native_decide
example : bdSWIG.cComponentOf (SWIGNode.random bdZ) = {SWIGNode.random bdZ} := by native_decide

example : Causalean.SCM.ID.idSucceeds ({bdD} : Finset BDNode)
    ({SWIGNode.random bdY} : Finset (SWIGNode BDNode)) bdSWIG := by
  let hX : Causalean.SCM.ID.interventionValid {bdD} bdSWIG := by
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
    rw [SWIGGraph.cComponentSet] at hS
    rcases Finset.mem_image.mp hS with ⟨a, haObs, rfl⟩
    simp [SWIGGraph.induce] at haObs
    rcases haObs with ⟨haAnc, haObsOrig⟩
    simp [bdSWIG] at haObsOrig
    rcases haObsOrig with rfl | rfl | rfl
    · have hnot :
          SWIGNode.random bdD ∉
            (bdSWIG.splitMono {bdD} hX.1 hX.2).dag.ancestralSet {SWIGNode.random bdY} := by
        simp [SWIGGraph.splitMono]
        native_decide
      exact False.elim (hnot haAnc)
    · have hComp :
          ((bdSWIG.splitMono {bdD} hX.1 hX.2).induce
              ((bdSWIG.splitMono {bdD} hX.1 hX.2).dag.ancestralSet
                {SWIGNode.random bdY})).cComponentOf (SWIGNode.random bdY) =
            {SWIGNode.random bdY} := by
        simp [SWIGGraph.splitMono, SWIGGraph.induce]
        native_decide
      rw [hComp]
      unfold Causalean.SCM.ID.cFactorReachable Causalean.SCM.ID.containingCComponent
      refine ⟨by simp, ?_, ?_⟩
      · intro v hv
        simp at hv
        have hOrigComp :
            bdSWIG.cComponentOf (SWIGNode.random bdY) = {SWIGNode.random bdY} := by
          native_decide
        subst v
        split
        · rename_i hne
          have hchoose :
              Exists.choose hne = SWIGNode.random bdY := by
            have hmem := Exists.choose_spec hne
            simpa using hmem
          rw [hchoose, hOrigComp]
          simp
        · rename_i hne
          exact False.elim (hne (by simp))
      · rw [SWIGGraph.cComponentSet]
        refine Finset.mem_image.mpr ⟨SWIGNode.random bdY, by native_decide, ?_⟩
        native_decide
    · have hComp :
          ((bdSWIG.splitMono {bdD} hX.1 hX.2).induce
              ((bdSWIG.splitMono {bdD} hX.1 hX.2).dag.ancestralSet
                {SWIGNode.random bdY})).cComponentOf (SWIGNode.random bdZ) =
            {SWIGNode.random bdZ} := by
        simp [SWIGGraph.splitMono, SWIGGraph.induce]
        native_decide
      rw [hComp]
      unfold Causalean.SCM.ID.cFactorReachable Causalean.SCM.ID.containingCComponent
      refine ⟨by simp, ?_, ?_⟩
      · intro v hv
        simp at hv
        have hOrigComp :
            bdSWIG.cComponentOf (SWIGNode.random bdZ) = {SWIGNode.random bdZ} := by
          native_decide
        subst v
        split
        · rename_i hne
          have hchoose :
              Exists.choose hne = SWIGNode.random bdZ := by
            have hmem := Exists.choose_spec hne
            simpa using hmem
          rw [hchoose, hOrigComp]
          simp
        · rename_i hne
          exact False.elim (hne (by simp))
      · rw [SWIGGraph.cComponentSet]
        refine Finset.mem_image.mpr ⟨SWIGNode.random bdZ, by native_decide, ?_⟩
        native_decide

-- ============================================================
-- Backdoor criterion: condition (ii) via splitMono
--
-- The backdoor criterion for (D → Y) w.r.t. adjustment set Z requires:
--   (ii) Z d-separates Y from D in the lower-bar graph G_{D̄},
--        i.e., the graph where all edges INTO D are removed.
-- In SWIG terms this is `bdSWIG.splitMono {bdD}`:
--   the split reroutes D's incoming edges so that `.random bdD` has no parents,
--   while `.fixed bdD` carries D's outgoing edges.
-- We demonstrate (ii) directly:
-- ============================================================

-- Demonstrates condition (ii) of the backdoor criterion directly:
-- Z d-seps Y from D in the lower-bar graph (= bdSWIG.splitMono {bdD}).
-- We use the underlying computable DAG `splitMonoDAG` directly (since `splitMono`
-- is noncomputable due to its SWIGGraph fields, but the DAG is fully computable).
example : (bdSWIG.splitMonoDAG {bdD}
    (by intro D hD; simp at hD; subst hD; native_decide)).dSep
    {SWIGNode.random bdY} {SWIGNode.random bdD} {SWIGNode.random bdZ} := by native_decide

-- Condition (i): Z contains no descendant of D
-- (bdZ is not a descendant of bdD in bdDAG)
example : ¬bdDAG.isAncestor bdD bdZ := by native_decide

-- awaits `SWIGGraph.backdoorCriterion` from `SCM/ID/Backdoor.lean`

-- ============================================================
-- Edge type assignment
-- ============================================================

/-- The backdoor example treats every graph edge as nonparametric. -/
def bdEdgeTypes : EdgeTypeAssignment bdDAG :=
  EdgeTypeAssignment.allNonparametric bdDAG

example : bdEdgeTypes.isFullyNonparametric := by
  intro u v _; rfl

-- ============================================================
-- Backdoor criterion (graph-level): (D, Y) with adjustment set {Z}
-- ============================================================

/-- The observed confounder satisfies the graphical backdoor criterion for the treatment-outcome effect in this example. -/
example :
    bdSWIG.backdoorCriterion {bdD}
      (by intro D hD; simp at hD; subst hD; native_decide)
      (by intro D hD; simp at hD; subst hD; native_decide)
      {SWIGNode.random bdY}
      {SWIGNode.random bdZ} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Guard: {Z} is observed.
    intro z hz
    simp at hz
    subst hz
    native_decide
  · -- Guard: {Z} is disjoint from {Y}.
    native_decide
  · -- Guard: {Z} is disjoint from {D}.
    native_decide
  · -- Condition (i): {Z} contains no descendant of any random D
    intro z hz D hD
    simp at hz hD
    subst hz; subst hD
    native_decide
  · -- Condition (ii): Z d-separates Y from X in splitMono.
    -- `splitMono` is noncomputable, but `splitMono.dag = splitMonoDAG`
    -- definitionally, so we discharge via the computable `splitMonoDAG`
    -- decided natively (inlined to keep the goal free of free variables
    -- that would trip up `native_decide`).
    exact (by native_decide :
      (bdSWIG.splitMonoDAG {bdD} (by native_decide)).dSep
        {SWIGNode.random bdY} (Finset.image SWIGNode.random {bdD})
        ({SWIGNode.random bdZ} ∪ Finset.image SWIGNode.fixed {bdD}))

end Causalean.SCM.Examples.BackDoor
