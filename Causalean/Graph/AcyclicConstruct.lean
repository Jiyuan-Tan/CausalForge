/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.DAG

/-! # Constructing a DAG from a raw acyclic edge relation

Since `DAG` stores acyclicity directly (`acyclic : ∀ v, ¬ Relation.TransGen edge v v`),
building one only requires exhibiting the edge relation, its decidability, and a
proof that it has no directed cycle. This file provides:

* `DAG.ofAcyclic e hac` — from an edge relation `e` whose transitive closure is
  irreflexive (`hac`). Materialises the graph directly. (Used e.g. for the
  Verma–Pearl covered-edge reversal, where acyclicity of the modified relation is
  known before any topological numbering.)

For constructions that already carry a topological numbering, build the `DAG`
structure directly and discharge its `acyclic` field with
`DAG.acyclic_of_topoOrder` (in `Causalean.Graph.DAG`), which keeps the edge
relation definitionally transparent.
-/

namespace Causalean

namespace DAG

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Build a DAG from an acyclic edge relation.** Given `e : V → V → Prop` whose
transitive closure is irreflexive (`hac`, i.e. `e` has no directed cycle), this is
the directed acyclic graph with edge relation `e`. -/
noncomputable def ofAcyclic (e : V → V → Prop)
    (hac : ∀ v, ¬ Relation.TransGen e v v) : DAG V where
  edge := e
  decEdge := Classical.decRel e
  acyclic := hac

/-- The graph built from an acyclic edge relation has exactly that edge relation. -/
@[simp] theorem ofAcyclic_edge (e : V → V → Prop)
    (hac : ∀ v, ¬ Relation.TransGen e v v) :
    (ofAcyclic e hac).edge = e := rfl

end DAG

end Causalean
