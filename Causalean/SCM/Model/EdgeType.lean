/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.DAG

/-! # Edge Type Hierarchy

This file records functional restrictions that may be attached to directed edges in
a causal graph, including nonparametric, monotone, linear, and parametric cases.
The hierarchy is separate from the probabilistic semantics of structural causal
models and is used to track functional assumptions.

## Main definitions

* `MonotonicityKind` records the four monotonicity directions.
* `EdgeType` classifies an edge as nonparametric, monotone, linear, or
  parametrically restricted.
* `EdgeType.refinesBool` and `EdgeType.refines` encode the assumption-refinement
  order in which every edge type refines the nonparametric top element.
* `EdgeTypeAssignment` attaches an `EdgeType` label to each ordered edge slot of
  a directed acyclic graph, with `EdgeTypeAssignment.allNonparametric` as the
  default assignment.
-/

namespace Causalean

/-- A monotonicity kind records whether an edge is nondecreasing, nonincreasing, strictly increasing, or strictly decreasing.

    For every monotonicity classification and every natural-number pretty-printing
precedence, the derived representation function returns a standard formatted
description of that classification.

    From the tex: "Monotonic: non-increasing, non-decreasing,
    strictly increasing, or strictly decreasing." -/
inductive MonotonicityKind
  | nonDecreasing
  | nonIncreasing
  | strictlyIncreasing
  | strictlyDecreasing
  deriving DecidableEq, Repr

/-- An edge type records whether an edge is nonparametric, monotonic, linear, or parametric.

    For any two edge-type classifications, the derived equality procedure decides
whether the first classification is equal to the second; for every edge-type
classification and every natural-number pretty-printing precedence, the derived
representation function returns a standard formatted description of that
classification.

    From the tex (Section 2):
    1. Nonparametric: no assumption on the structural equation.
    2. Monotonic: with a specified monotonicity kind.
    3. Parametric: linear, or another named parametric family.

    `Parametric` is an opaque tag in this layer; downstream developments can
    refine it with a concrete family when they need one. -/
inductive EdgeType
  | nonparametric
  | monotonic (kind : MonotonicityKind)
  | linear
  | parametric
  deriving DecidableEq, Repr

namespace EdgeType

/-- The Boolean refinement check decides whether one edge-type assumption is at least as specific as another.

    Nonparametric is the weakest assumption: every edge type refines it. A
    linear edge refines the linear and nonparametric classes, but it is not
    automatically monotone: without a sign restriction on its coefficient, the
    linear structural function need not be strictly increasing. Returns `Bool`
    for decidability; use `refines` for the `Prop` version. -/
def refinesBool : EdgeType → EdgeType → Bool
  | _, .nonparametric => true
  | .monotonic k₁, .monotonic k₂ => k₁ == k₂
  | .linear, .linear => true
  | .parametric, .parametric => true
  | _, _ => false

/-- The refinement relation says that one edge-type assumption is at least as specific as another.

    Nonparametric is the weakest assumption: every edge type refines it. -/
def refines (e₁ e₂ : EdgeType) : Prop := e₁.refinesBool e₂ = true

/-- Refinement between two edge-type assumptions is decidable. -/
instance decRefines (e₁ e₂ : EdgeType) : Decidable (e₁.refines e₂) :=
  inferInstanceAs (Decidable (_ = true))

/-- Every edge-type assumption refines itself. -/
theorem refines_refl : (e : EdgeType) → e.refines e
  | .nonparametric => rfl
  | .monotonic k => by cases k <;> rfl
  | .linear => rfl
  | .parametric => rfl

/-- Nonparametric is the top of the refinement order: everything refines it. -/
theorem refines_nonparametric (e : EdgeType) : e.refines .nonparametric := by
  cases e <;> simp [refines, refinesBool]

end EdgeType

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- An edge type assignment attaches a functional-assumption label to each directed edge of a graph.

    An edge type assignment for a DAG: a function that assigns an `EdgeType`
    to each directed edge.

    From the tex remark: "Edge types (nonparametric, monotonic, linear) can be
    encoded via a function edgeType : E → EdgeType that assigns a type to each
    edge." -/
structure EdgeTypeAssignment (G : DAG V) where
  /-- The edge type of each directed edge `(u, v)`.
      Only meaningful when `G.edge u v` holds. -/
  edgeType : V → V → EdgeType

namespace EdgeTypeAssignment

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : DAG V}

/-- The default edge-type assignment labels every edge as nonparametric. -/
def allNonparametric (G : DAG V) : EdgeTypeAssignment G where
  edgeType := fun _ _ => .nonparametric

/-- The incoming edge-type set collects the labels on all edges pointing into a vertex. -/
def incomingTypes (a : EdgeTypeAssignment G) (v : V) : Finset EdgeType :=
  (G.parents v).image (fun u => a.edgeType u v)

/-- A graph is fully nonparametric under an assignment when every directed edge is labeled nonparametric. -/
def isFullyNonparametric (a : EdgeTypeAssignment G) : Prop :=
  ∀ u v, G.edge u v → a.edgeType u v = .nonparametric

/-- Full nonparametricity of an edge-type assignment is decidable. -/
instance decIsFullyNonparametric (a : EdgeTypeAssignment G) :
    Decidable a.isFullyNonparametric :=
  inferInstanceAs (Decidable (∀ u v, G.edge u v → _))

end EdgeTypeAssignment

end Causalean
