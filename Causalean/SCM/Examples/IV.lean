/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Example: Instrumental Variable DAG

This file constructs the standard IV DAG and uses it to exercise
the DAG, d-separation, C-component, edge type, and SWIG graph APIs.

## The DAG

```
    U
   ↙ ↘
  Z → D → Y
```

- Observed: Z (instrument, binary), D (treatment, binary), Y (outcome, continuous)
- Unobserved: U (confounder)
- Edges: Z → D (monotonic increasing), D → Y, U → D, U → Y
- Z is a valid instrument: it affects Y only through D, and is independent of U.
-/

import Causalean.Graph.DAG
import Causalean.Graph.DSep.Separation
import Causalean.Graph.SWIG
import Causalean.Graph.CComponents
import Causalean.SCM.Model.EdgeType
import Causalean.SCM.Model.SCM

/-! # Instrumental Variable Example

This file constructs the standard instrumental-variable graph with an instrument, a treatment, an
outcome, and an unobserved confounder of the treatment-outcome relationship. It exercises the
graphical, component, edge-type, and structural-model interfaces used by instrumental-variable
examples elsewhere in the library. -/

set_option linter.style.nativeDecide false

namespace Causalean.SCM.Examples.IV

-- ============================================================
-- Vertex type
-- ============================================================

/-- The instrumental-variable example has instrument, treatment, outcome, and unobserved-confounder vertices. -/
inductive IVNode
  | Z  -- instrument (binary)
  | D  -- treatment (binary)
  | Y  -- outcome (continuous)
  | U  -- unobserved confounder
  deriving DecidableEq

open IVNode

namespace instReprIVNode

/--
For each vertex of the instrumental-variable DAG and each natural-number precedence level, this
method returns a formatted textual rendering of that vertex. There are no additional hypotheses
or side conditions.

This helper is the explicit form of the representation method that `deriving Repr` would generate.
-/
protected def repr : IVNode → Nat → Std.Format
  | Z, _ => "Causalean.SCM.Examples.IV.IVNode.Z"
  | D, _ => "Causalean.SCM.Examples.IV.IVNode.D"
  | Y, _ => "Causalean.SCM.Examples.IV.IVNode.Y"
  | U, _ => "Causalean.SCM.Examples.IV.IVNode.U"

end instReprIVNode

/-- Instrumental-variable vertices can be rendered as their fully qualified constructor names. -/
instance instReprIVNode : Repr IVNode where
  reprPrec := instReprIVNode.repr

/-- The instrumental-variable vertex set is finite, with four named vertices. -/
instance : Fintype IVNode where
  elems := {Z, D, Y, U}
  complete := by intro x; cases x <;> simp

-- ============================================================
-- Edge relation
-- ============================================================

/-- The instrumental-variable graph has instrument-to-treatment, treatment-to-outcome, and latent-confounder-to-treatment/outcome edges. -/
def ivEdge : IVNode → IVNode → Prop
  | Z, D => True
  | D, Y => True
  | U, D => True
  | U, Y => True
  | _, _ => False

/-- Whether a proposed instrumental-variable edge is present is decidable by case analysis on the endpoints. -/
instance : DecidableRel ivEdge := by
  intro a b; cases a <;> cases b <;> simp [ivEdge] <;> infer_instance

-- ============================================================
-- Topological order
-- ============================================================

/-- The instrumental-variable graph orders the unobserved confounder and instrument before treatment and outcome. -/
def ivTopo : IVNode → ℕ
  | U => 0
  | Z => 1
  | D => 2
  | Y => 3

/-- Every edge in the instrumental-variable graph points from an earlier to a later node in the chosen topological order. -/
theorem ivTopo_lt : ∀ u v, ivEdge u v → ivTopo u < ivTopo v := by
  intro u v h; cases u <;> cases v <;> simp_all [ivEdge, ivTopo]

-- ============================================================
-- The DAG
-- ============================================================

/-- This directed acyclic graph formalizes the standard instrumental-variable example. -/
def ivDAG : DAG IVNode where
  edge := ivEdge
  decEdge := inferInstance
  acyclic := DAG.acyclic_of_topoOrder ivTopo_lt

-- ============================================================
-- Testing DAG.lean: parents, children
-- ============================================================

-- Parents: Z and U are parents of D
example : Z ∈ ivDAG.parents D := by decide
example : U ∈ ivDAG.parents D := by decide

-- Parents: D and U are parents of Y
example : D ∈ ivDAG.parents Y := by decide
example : U ∈ ivDAG.parents Y := by decide

-- Z is a root (no parents)
example : ivDAG.parents Z = ∅ := by native_decide

-- U is a root (no parents)
example : ivDAG.parents U = ∅ := by native_decide

-- Children: Z has child D
example : D ∈ ivDAG.children Z := by decide

-- Children: D has child Y
example : Y ∈ ivDAG.children D := by decide

-- Children: U has children D and Y
example : D ∈ ivDAG.children U := by decide
example : Y ∈ ivDAG.children U := by decide

-- Y is a leaf (no children)
example : ivDAG.children Y = ∅ := by native_decide

-- ============================================================
-- Testing DAG.lean: roots
-- ============================================================

-- Z and U are roots
example : ivDAG.isRoot Z := by native_decide
example : ivDAG.isRoot U := by native_decide

-- D is not a root (it has parents)
example : ¬ivDAG.isRoot D := by native_decide

-- Y is not a root
example : ¬ivDAG.isRoot Y := by native_decide

-- ============================================================
-- Testing DAG.lean: ancestors, descendants (inductive)
-- ============================================================

-- Z is an ancestor of D (one edge)
example : ivDAG.isAncestor Z D :=
  DAG.isAncestor.edge (show ivDAG.edge Z D from trivial)

-- Z is an ancestor of Y (transitively: Z → D → Y)
example : ivDAG.isAncestor Z Y :=
  DAG.isAncestor.trans
    (DAG.isAncestor.edge (show ivDAG.edge Z D from trivial))
    (show ivDAG.edge D Y from trivial)

-- U is an ancestor of Y (directly)
example : ivDAG.isAncestor U Y :=
  DAG.isAncestor.edge (show ivDAG.edge U Y from trivial)

-- U is an ancestor of D (directly)
example : ivDAG.isAncestor U D :=
  DAG.isAncestor.edge (show ivDAG.edge U D from trivial)

-- Irreflexivity: no vertex is its own ancestor
example : ¬ivDAG.isAncestor Z Z := ivDAG.isAncestor_irrefl Z
example : ¬ivDAG.isAncestor Y Y := ivDAG.isAncestor_irrefl Y

-- Asymmetry: if Z is ancestor of D, D is not ancestor of Z
example (h : ivDAG.isAncestor Z D) : ¬ivDAG.isAncestor D Z := by
  intro h'
  exact absurd (ivDAG.isAncestor_trans h h') (ivDAG.isAncestor_irrefl Z)

-- ============================================================
-- Testing DSep.lean: d-separation
-- ============================================================

-- Z and Y are NOT d-separated by ∅ (active path Z → D → Y)
example : ¬ivDAG.dSep {Z} {Y} ∅ := by decide

-- Z and Y are NOT d-separated by {D} either
-- (conditioning on D opens the collider path Z → D ← U → Y)
example : ¬ivDAG.dSep {Z} {Y} {D} := by native_decide

-- Z and Y ARE d-separated by {D, U}
example : ivDAG.dSep {Z} {Y} {D, U} := by decide

-- Instrument validity: Z ⊥ U | ∅ (no path between Z and U)
example : ivDAG.dSep {Z} {U} ∅ := by decide

-- D and U are NOT d-separated by ∅ (direct edge U → D)
example : ¬ivDAG.dSep {D} {U} ∅ := by decide

-- ============================================================
-- Testing Graph/SWIG.lean and Graph/CComponents.lean: C-components
-- ============================================================

/-- This SWIG graph represents the instrumental-variable example before any intervention.

The instrument, treatment, and outcome are observed random nodes, while the
unobserved confounder is the sole unobserved random node. -/
def ivSWIGGraph : SWIGGraph IVNode where
  dag := initialSWIG ivDAG
  fixed := ∅
  observed := {SWIGNode.random Z, SWIGNode.random D, SWIGNode.random Y}
  unobserved := {SWIGNode.random U}
  fixed_is_fixed := by intro s hs; simp at hs
  observed_is_random := by
    intro v hv; simp at hv
    rcases hv with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  unobserved_is_random := by
    intro u hu; simp at hu; subst hu; exact ⟨U, rfl⟩
  obs_unobs_disjoint := by native_decide
  dag_edges_classified := by native_decide
  fixed_image_in_observed := by intro s hs; simp at hs
  fixed_are_roots := by intro s hs; simp at hs
  unobs_are_roots := by
    intro u hu; simp at hu; subst hu
    simpa [initialSWIG] using
      (swig_random_root_of_root ivDAG ∅ U (by native_decide : ivDAG.parents U = ∅))
  fixed_outside_fixed_isolated := by
    intro n _
    cases n <;> exact ⟨by native_decide, by native_decide⟩
  all_children_in_observed := by native_decide

-- D and Y are directly confounded (they share unobserved parent U)
example : ivSWIGGraph.directlyConfounded (SWIGNode.random D) (SWIGNode.random Y) := by decide

-- Z and D are NOT directly confounded (no shared unobserved parent)
example : ¬ivSWIGGraph.directlyConfounded (SWIGNode.random Z) (SWIGNode.random D) := by decide

-- Z and Y are NOT directly confounded
example : ¬ivSWIGGraph.directlyConfounded (SWIGNode.random Z) (SWIGNode.random Y) := by decide

-- C-component of D includes Y (via shared confounder U)
example : SWIGNode.random Y ∈ ivSWIGGraph.cComponentOf (SWIGNode.random D) := by native_decide

-- C-component of Z is just {Z} (no bidirected edges to Z)
example : ivSWIGGraph.cComponentOf (SWIGNode.random Z) = {SWIGNode.random Z} := by native_decide

-- ============================================================
-- Testing EdgeType.lean: edge type assignment
-- ============================================================

/-- The instrumental-variable edge assignment makes the instrument's effect on treatment strictly increasing and leaves all other edges nonparametric. -/
def ivEdgeTypes : EdgeTypeAssignment ivDAG where
  edgeType
    | Z, D => .monotonic .strictlyIncreasing
    | _, _ => .nonparametric

-- The Z → D edge is monotonic
example : ivEdgeTypes.edgeType Z D = .monotonic .strictlyIncreasing := rfl

-- The D → Y edge is nonparametric
example : ivEdgeTypes.edgeType D Y = .nonparametric := rfl

-- The U → D edge is nonparametric
example : ivEdgeTypes.edgeType U D = .nonparametric := rfl

-- The U → Y edge is nonparametric
example : ivEdgeTypes.edgeType U Y = .nonparametric := rfl

-- The assignment is NOT fully nonparametric (Z → D is monotonic)
example : ¬ivEdgeTypes.isFullyNonparametric := by
  intro h
  have := h Z D (show ivEdge Z D from trivial)
  simp [ivEdgeTypes] at this

-- The default all-nonparametric assignment IS fully nonparametric
example : (EdgeTypeAssignment.allNonparametric ivDAG).isFullyNonparametric := by
  intro u v _
  rfl

-- The monotonic Z → D edge refines nonparametric (weaker assumption)
example : (EdgeType.monotonic .strictlyIncreasing).refines .nonparametric :=
  EdgeType.refines_nonparametric _

-- ============================================================
-- Testing SCM.lean: explicit SCM construction (trivial Unit model)
-- ============================================================

section ExplicitModel

/-- This toy instrumental-variable model uses a one-point value space for every node.

In a substantive application, the instrument and treatment could be Boolean and
the outcome real-valued. -/
def ivΩ : IVNode → Type := fun _ => Unit

/-- Every one-point value space in the toy instrumental-variable model carries the trivial measurable structure. -/
instance ivΩ_measurable : ∀ n, MeasurableSpace (ivΩ n) := fun _ => ⊤

/-- This concrete instrumental-variable structural model realizes the example with one-point value spaces.

It demonstrates the full construction pattern: provide the SWIG graph, structural
functions for observed nodes, and a probability law for the latent root. With
one-point value spaces these data are constant functions and a point mass. -/
noncomputable def ivSCM : Causalean.SCM IVNode ivΩ where
  dag := initialSWIG ivDAG
  fixed := ∅
  observed := {SWIGNode.random Z, SWIGNode.random D, SWIGNode.random Y}
  unobserved := {SWIGNode.random U}
  fixed_is_fixed := by intro s hs; simp at hs
  observed_is_random := by
    intro v hv; simp at hv
    rcases hv with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  unobserved_is_random := by
    intro u hu; simp at hu; subst hu; exact ⟨U, rfl⟩
  obs_unobs_disjoint := by native_decide
  dag_edges_classified := by native_decide
  fixed_image_in_observed := by intro s hs; simp at hs
  fixed_are_roots := by intro s hs; simp at hs
  unobs_are_roots := by
    intro u hu; simp at hu; subst hu
    simpa [initialSWIG] using
      (swig_random_root_of_root ivDAG ∅ U (by native_decide : ivDAG.parents U = ∅))
  fixed_outside_fixed_isolated := by
    intro n _
    cases n <;> exact ⟨by native_decide, by native_decide⟩
  all_children_in_observed := by native_decide
  edgeTypes := EdgeTypeAssignment.allNonparametric (initialSWIG ivDAG)
  iota_valueSpace := by
    intro s
    exact (Finset.notMem_empty s.val s.property).elim
  structFun := fun v => by
    -- `swigΩ ivΩ v.val = Unit` for any constructor of `SWIGNode`, since `ivΩ _ = Unit`.
    rcases v with ⟨n, _⟩
    cases n <;> exact fun _ => ()
  structFun_measurable := by
    intro v
    rcases v with ⟨n, _⟩
    cases n <;> exact measurable_const
  latentDist := fun u => by
    rcases u with ⟨n, _⟩
    cases n <;> exact MeasureTheory.Measure.dirac ()
  isProbability_latent := by
    intro u
    rcases u with ⟨n, _⟩
    cases n <;> exact inferInstance

-- The model has no fixed nodes (standard model).
example : ivSCM.isStandard := by
  rfl

end ExplicitModel

-- ============================================================
-- Testing SWIG intervention graph (pure DAG content, unchanged)
-- ============================================================

section InterventionGraph

/-- This graph is the SWIG obtained by intervening on the treatment in the instrumental-variable DAG. -/
def ivDoDGraph : DAG (SWIGNode IVNode) :=
  swigDAG ivDAG {D}

-- The fixed intervention node `d` is a root in the SWIG.
example : ivDoDGraph.parents (.fixed D) = ∅ := by
  simpa [ivDoDGraph] using swig_fixed_are_roots ivDAG {D} D

-- The intervened value `d` inherits the outgoing edge to Y.
example : ivDoDGraph.edge (.fixed D) (.random Y) := by
  decide

-- The random copy of D keeps its incoming edges.
example : ivDoDGraph.edge (.random Z) (.random D) := by
  decide

example : ivDoDGraph.edge (.random U) (.random D) := by
  decide

-- The random copy of D no longer has the outgoing edge to Y.
example : ¬ivDoDGraph.edge (.random D) (.random Y) := by
  decide

end InterventionGraph

end Causalean.SCM.Examples.IV
