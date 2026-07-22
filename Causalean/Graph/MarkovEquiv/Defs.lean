/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.DSep.Separation

/-! # Markov equivalence of DAGs — basic definitions

This file introduces the combinatorial vocabulary for the Verma–Pearl characterization of
Markov equivalence. Two directed acyclic graphs on the same vertices are **Markov
equivalent** when they encode exactly the same d-separation statements, i.e. the same
conditional-independence constraints. The Verma–Pearl theorem (proved in the umbrella
file) says this happens precisely when the graphs share a *skeleton* and the same
*v-structures* (immoralities).

The definitions here are:

* `DAG.IsImmorality G a b c` — there is a v-structure (immorality) `a → b ← c` whose two
  parents `a, c` are non-adjacent and distinct;
* `SameSkeleton G₁ G₂` — the two graphs have the same undirected adjacency;
* `SameImmoralities G₁ G₂` — the two graphs have the same v-structures;
* `MarkovEquiv G₁ G₂` — the two graphs declare the same d-separations.

All of these are decidable on a finite vertex type. The underlying undirected adjacency is
the existing `DAG.UAdj` (`a` and `b` joined by an edge in either direction) and a collider
`a → b ← c` is `DAG.IsCollider`.
-/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

/-- A **v-structure (immorality)** at `b`: directed edges `a → b` and `c → b` whose tails
`a` and `c` are distinct and not joined by any edge. Immoralities are the colliders whose
parents are non-adjacent; they are exactly the part of the collider structure that is
visible to conditional independence. -/
def IsImmorality (a b c : V) : Prop :=
  G.edge a b ∧ G.edge c b ∧ ¬ G.UAdj a c ∧ a ≠ c

/-- Whether a proposed v-structure in a finite DAG is decidable. -/
instance (a b c : V) : Decidable (G.IsImmorality a b c) := by
  unfold IsImmorality; infer_instance

end DAG

/-- Two DAGs have the **same skeleton** when their undirected adjacency relations agree:
for every pair `a, b`, there is an edge (in either direction) between them in `G₁` iff there
is one in `G₂`. -/
def SameSkeleton (G₁ G₂ : DAG V) : Prop := ∀ a b, G₁.UAdj a b ↔ G₂.UAdj a b

/-- Two DAGs have the **same v-structures** when their immorality relations agree. -/
def SameImmoralities (G₁ G₂ : DAG V) : Prop :=
  ∀ a b c, G₁.IsImmorality a b c ↔ G₂.IsImmorality a b c

/-- Two DAGs are **Markov equivalent** when they entail exactly the same d-separations:
for every triple of vertex sets `X, Y, Z`, `X` and `Y` are d-separated by `Z` in `G₁` iff
they are in `G₂`. Equivalently (via the global Markov property) the two graphs impose the
same conditional-independence constraints on every distribution. The quantification ranges
over pairwise-disjoint triples `X, Y, Z` — the standard setting for conditional
independence — matching the global Markov property and the moralization criterion. -/
def MarkovEquiv (G₁ G₂ : DAG V) : Prop :=
  ∀ X Y Z : Finset V, Disjoint X Y → Disjoint X Z → Disjoint Y Z →
    (G₁.dSep X Y Z ↔ G₂.dSep X Y Z)

/-- Whether two finite DAGs have the same skeleton is decidable. -/
instance (G₁ G₂ : DAG V) : Decidable (SameSkeleton G₁ G₂) := by
  unfold SameSkeleton; infer_instance

/-- Whether two finite DAGs have the same v-structures is decidable. -/
instance (G₁ G₂ : DAG V) : Decidable (SameImmoralities G₁ G₂) := by
  unfold SameImmoralities; infer_instance

/-- Markov equivalence is reflexive. -/
@[refl] theorem MarkovEquiv.refl (G : DAG V) : MarkovEquiv G G :=
  fun _ _ _ _ _ _ => Iff.rfl

/-- Markov equivalence is symmetric. -/
theorem MarkovEquiv.symm {G₁ G₂ : DAG V} (h : MarkovEquiv G₁ G₂) : MarkovEquiv G₂ G₁ :=
  fun X Y Z hXY hXZ hYZ => (h X Y Z hXY hXZ hYZ).symm

/-- Markov equivalence is transitive. -/
theorem MarkovEquiv.trans {G₁ G₂ G₃ : DAG V}
    (h₁ : MarkovEquiv G₁ G₂) (h₂ : MarkovEquiv G₂ G₃) : MarkovEquiv G₁ G₃ :=
  fun X Y Z hXY hXZ hYZ => (h₁ X Y Z hXY hXZ hYZ).trans (h₂ X Y Z hXY hXZ hYZ)

end Causalean
