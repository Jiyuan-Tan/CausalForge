/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# SWIG Graph: Node Type, Graph Construction, and Split Operation

This file defines the SWIG (Single World Intervention Graph) graph structure
following Richardson and Robins.

## Main definitions

* `SWIGNode` — node type: each original node has a `random` and `fixed` version
* `swigΩ` — value-space family: both versions share the same value space
* `swigEdge` — the edge relation in a SWIG DAG
* `swigDAG` — the SWIG as a `DAG (SWIGNode N)` given an original `DAG N` and targets
* `iotaMap` — the injection mapping fixed → random counterpart
* `SWIGGraph` — graph-level causal packaging:
  `(S, V, U, E, ι)` with root constraints

The multi-target split operation (`SWIGGraph.splitMono`, Definition 8) is in
the sibling file `Graph/SWIGSplitMono.lean`.

## Design note

This file provides the pure graph-level SWIG construction. The probabilistic
side lives in `SCM` (see `Causalean/SCM/Model/SCM.lean`).

The `SCM` structure extends `SWIGGraph N`, so every structural causal model
already lives in the SWIG node space. A standard model (no interventions) has
`fixed = ∅`; non-listed fixed-form nodes are isolated dummies outside
`unobserved`, whose members are random-form latent nodes.

## References

* Basic Concepts.tex, Definitions 4 and 7 (SWIG Graph, Split)
-/

import Causalean.Graph.DAG
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Fintype.Sum
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Single World Intervention Graphs

This file defines the graph-theoretic structure of a Single World Intervention
Graph (SWIG). A base variable `n : N` has two SWIG nodes: `.random n`, used for
the natural random variable, and `.fixed n`, used for intervention values. The
shared value-space family `swigΩ` gives both copies the same measurable value
space as the base variable.

The core construction is `swigDAG G targets`. It keeps incoming edges into
targeted random nodes, reroutes outgoing edges from each targeted random node to
the corresponding fixed node, and leaves fixed nodes for non-targets isolated.
The interleaved order `swigTopo` proves that this edge relation is acyclic, and
the basic lemmas describe roots, target parents, and the initial no-intervention
SWIG.

The structure `SWIGGraph` packages a DAG on SWIG nodes together with the fixed,
observed, and unobserved node sets, the link map `ι` from fixed nodes to their
random counterparts, and root/classification invariants used by structural
causal models. The namespace also provides graph equivalence up to edge and
partition equality, plus parent/child classification lemmas. The monolithic
multi-target split operation is defined in `Causalean.Graph.SWIGSplitMono`. -/

namespace Causalean

-- ============================================================
-- SWIG Node Type
-- ============================================================

/-- A node of a SWIG (Single World Intervention Graph) is either the *random* version of a
base variable or its *fixed* intervention version, so the SWIG node set is the disjoint
union of two copies of the base variable set.

    Each original node n has a random version `random n` and a fixed version
    `fixed n`. In a SWIG with intervention targets T:
    - `random n` exists for all n (the natural/random version)
    - `fixed d` is meaningful only for d ∈ T (the intervention value)
    - For d ∉ T, `fixed d` is an isolated dummy node

    In the SWIG split, a targeted variable keeps its random copy for incoming edges while
    its fixed copy carries the outgoing edges. -/
inductive SWIGNode (N : Type*)
  | random : N → SWIGNode N
  | fixed : N → SWIGNode N
  deriving DecidableEq, Repr

namespace SWIGNode

variable {N : Type*}

/-- The random-node constructor is injective: equal random SWIG nodes come from the same
base variable. -/
theorem random_injective : Function.Injective (@SWIGNode.random N) := by
  intro a b h; cases h; rfl

/-- The fixed-node constructor is injective: equal fixed SWIG nodes come from the same base
variable. -/
theorem fixed_injective : Function.Injective (@SWIGNode.fixed N) := by
  intro a b h; cases h; rfl

/-- Equivalence between SWIGNode N and N ⊕ N. -/
def equiv : SWIGNode N ≃ N ⊕ N where
  toFun
    | .random n => Sum.inl n
    | .fixed n => Sum.inr n
  invFun
    | .inl n => .random n
    | .inr n => .fixed n
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

/-- If the base variables are finite, then the split SWIG node set is finite. -/
instance [Fintype N] : Fintype (SWIGNode N) :=
  Fintype.ofEquiv (N ⊕ N) equiv.symm

end SWIGNode

-- ============================================================
-- SWIG Value-Space Family
-- ============================================================

/-- Value-space family for the SWIG model.
    Both random and fixed versions of a node share the same value space
    as the original node: swigΩ(.random n) = Ω n and swigΩ(.fixed n) = Ω n.
    This matches the tex requirement X_d = X_{ι(d)}.
    Declared as `abbrev` so that `swigΩ Ω (.random n)` reduces to `Ω n`
    during type class synthesis. -/
abbrev swigΩ {N : Type*} (Ω : N → Type*) : SWIGNode N → Type _
  | .random n => Ω n
  | .fixed n => Ω n

/-- The shared SWIG value-space family inherits measurable spaces from the base variables. -/
instance instMeasurableSpaceSwigΩ {N : Type*} (Ω : N → Type*)
    [∀ n, MeasurableSpace (Ω n)] : ∀ sn, MeasurableSpace (swigΩ Ω sn)
  | .random _ => inferInstance
  | .fixed _ => inferInstance

/-- The shared SWIG value-space family inherits standard Borel spaces from the base variables. -/
instance instStandardBorelSpaceSwigΩ {N : Type*} (Ω : N → Type*)
    [∀ n, MeasurableSpace (Ω n)] [∀ n, StandardBorelSpace (Ω n)] :
    ∀ sn, StandardBorelSpace (swigΩ Ω sn)
  | .random _ => inferInstance
  | .fixed _ => inferInstance

/-- The shared SWIG value-space family is nonempty whenever each base value space is nonempty. -/
instance instNonemptySwigΩ {N : Type*} (Ω : N → Type*) [∀ n, Nonempty (Ω n)] :
    ∀ sn, Nonempty (swigΩ Ω sn)
  | .random _ => inferInstance
  | .fixed _ => inferInstance

-- ============================================================
-- SWIG Edge Relation
-- ============================================================

variable {N : Type*} [DecidableEq N] [Fintype N]

/-- The edge relation in a SWIG.

    Given an original DAG G and intervention targets T:
    - (random u → random v): edge iff G.edge u v AND u ∉ T
      (if u is a target, its outgoing edges go from fixed u instead)
    - (fixed d → random v): edge iff d ∈ T AND G.edge d v
      (fixed d inherits the outgoing edges of d)
    - All other pairs: no edge (fixed nodes have no parents in the SWIG)

    Equivalently, the SWIG edge set is obtained by replacing each outgoing edge from a
    target `d` with an edge from `.fixed d`, while retaining incoming edges to `.random d`. -/
def swigEdge (G : DAG N) (targets : Finset N) : SWIGNode N → SWIGNode N → Prop
  | .random u, .random v => G.edge u v ∧ u ∉ targets
  | .fixed d, .random v => d ∈ targets ∧ G.edge d v
  | _, _ => False

/-- The SWIG edge relation is decidable whenever the base variables and target set are finite. -/
instance swigEdge_decidable (G : DAG N) (targets : Finset N) :
    DecidableRel (swigEdge G targets) := by
  intro a b
  cases a <;> cases b <;> simp only [swigEdge] <;> infer_instance

-- ============================================================
-- SWIG Topological Order
-- ============================================================

/-- Topological order for the SWIG.

    We double the original topological order and interleave:
    - fixed n  ↦ 2 * topoOrder n
    - random n ↦ 2 * topoOrder n + 1

    This ensures fixed d has smaller order than random v whenever G.edge d v
    (since topoOrder d < topoOrder v in the original DAG). -/
noncomputable def swigTopo (G : DAG N) : SWIGNode N → ℕ
  | .random n => 2 * G.topoOrder n + 1
  | .fixed n => 2 * G.topoOrder n

/-- Every SWIG edge points from a lower to a higher position in the interleaved topological
order. -/
theorem swigTopo_lt (G : DAG N) (targets : Finset N) :
    ∀ u v, swigEdge G targets u v → swigTopo G u < swigTopo G v := by
  intro u v h
  cases u with
  | random u =>
    cases v with
    | random v =>
      simp only [swigEdge] at h
      simp only [swigTopo]
      have := G.topoOrder_lt u v h.1
      omega
    | fixed _ => exact absurd h (by simp [swigEdge])
  | fixed d =>
    cases v with
    | random v =>
      simp only [swigEdge] at h
      simp only [swigTopo]
      have := G.topoOrder_lt d v h.2
      omega
    | fixed _ => exact absurd h (by simp [swigEdge])

-- ============================================================
-- SWIG DAG
-- ============================================================

/-- The SWIG DAG: the DAG on SWIGNode N constructed by node-splitting.

    Given an original DAG G and intervention targets T ⊆ V, the SWIG G(T) has:
    - For each target D ∈ T: random D keeps incoming edges, fixed D gets outgoing edges
    - For non-targets: random n keeps all original edges
    - Fixed nodes for non-targets are isolated (no edges) -/
def swigDAG (G : DAG N) (targets : Finset N) : DAG (SWIGNode N) where
  edge := swigEdge G targets
  decEdge := swigEdge_decidable G targets
  acyclic := DAG.acyclic_of_topoOrder (swigTopo_lt G targets)

-- ============================================================
-- The ι map (linking fixed to random counterparts)
-- ============================================================

/-- The injection ι mapping each fixed intervention parameter to its
    random counterpart. In the SWIG, ι(fixed d) = random d.

    At the graph level this realizes the link `ι : S → V` from intervention parameters
    to their random counterparts. -/
def iotaMap : SWIGNode N → SWIGNode N
  | .fixed n => .random n
  | .random n => .random n

omit [DecidableEq N] [Fintype N] in
/-- The link map sends the fixed copy of a base variable to its random copy. -/
theorem iotaMap_fixed (n : N) : iotaMap (.fixed n : SWIGNode N) = .random n := rfl

-- ============================================================
-- Properties of the SWIG construction
-- ============================================================

/-- Fixed nodes in the SWIG are roots (no parents). -/
theorem swig_fixed_are_roots (G : DAG N) (targets : Finset N) (n : N) :
    (swigDAG G targets).parents (.fixed n) = ∅ := by
  simp only [DAG.parents, swigDAG, Finset.filter_eq_empty_iff]
  intro x _
  cases x <;> simp [swigEdge]

/-- In the SWIG, random nodes of intervention targets have the same incoming edges
    as in the original DAG (mapped to random versions). Specifically, the parents
    of random D in the SWIG are exactly the random versions of D's parents in G. -/
theorem swig_target_parents (G : DAG N) (targets : Finset N) (d : N) (_hd : d ∈ targets) :
    ∀ x : SWIGNode N, x ∈ (swigDAG G targets).parents (.random d) ↔
      ∃ p, G.edge p d ∧ x = .random p ∧ p ∉ targets ∨
           G.edge p d ∧ x = .fixed p ∧ p ∈ targets := by
  intro x
  simp only [DAG.parents, swigDAG, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hedge
    cases x with
    | random u =>
      simp only [swigEdge] at hedge
      exact ⟨u, Or.inl ⟨hedge.1, rfl, hedge.2⟩⟩
    | fixed f =>
      simp only [swigEdge] at hedge
      exact ⟨f, Or.inr ⟨hedge.2, rfl, hedge.1⟩⟩
  · intro ⟨p, hp⟩
    rcases hp with ⟨hedge, rfl, hnt⟩ | ⟨hedge, rfl, ht⟩
    · simp only [swigEdge]; exact ⟨hedge, hnt⟩
    · simp only [swigEdge]; exact ⟨ht, hedge⟩

/-- If n is a root in G, then random n is a root in the SWIG. -/
theorem swig_random_root_of_root (G : DAG N) (targets : Finset N) (n : N)
    (hroot : G.parents n = ∅) :
    (swigDAG G targets).parents (.random n) = ∅ := by
  simp only [DAG.parents, swigDAG, Finset.filter_eq_empty_iff]
  intro x _
  cases x with
  | random u =>
    simp only [swigEdge]
    intro ⟨hedge, _⟩
    have : u ∈ G.parents n := G.mem_parents.mpr hedge
    simp [hroot] at this
  | fixed d =>
    simp only [swigEdge]
    intro ⟨_, hedge⟩
    have : d ∈ G.parents n := G.mem_parents.mpr hedge
    simp [hroot] at this

-- ============================================================
-- Lifting a DAG to its initial SWIG (no interventions)
-- ============================================================

/-- The initial SWIG DAG with no intervention targets.
    All edges stay between random nodes; all fixed nodes are isolated.
    This is the DAG used by a standard causal model. -/
def initialSWIG (G : DAG N) : DAG (SWIGNode N) := swigDAG G ∅

/-- In the initial SWIG (no targets), edges between random nodes match
    the original edges exactly. -/
theorem initialSWIG_random_edge (G : DAG N) (u v : N) :
    (initialSWIG G).edge (.random u) (.random v) ↔ G.edge u v := by
  simp [initialSWIG, swigDAG, swigEdge]

/-- All fixed nodes are isolated in the initial SWIG. -/
theorem initialSWIG_fixed_isolated (G : DAG N) (n : N) :
    (initialSWIG G).parents (.fixed n) = ∅ :=
  swig_fixed_are_roots G ∅ n

-- ============================================================
-- SWIGGraph structure
-- ============================================================

/-- A SWIG Graph `G = (S, V, U, E, ι)` (Definition 4 from Basic Concepts.tex).

    Consists of a DAG on `SWIGNode N` together with a three-way partition
    `(fixed S, observed V, unobserved U)`, an injective mapping `ι : S → V`,
    and root constraints on S and U.

    When `S = ∅`, the SWIG reduces to the standard DAG `(V ∪ U, E)`. -/
structure SWIGGraph (N : Type*) [DecidableEq N] [Fintype N] where
  /-- The underlying DAG on SWIG nodes. -/
  dag : DAG (SWIGNode N)
  /-- Fixed (intervention) nodes `S` as fixed SWIG nodes. -/
  fixed : Finset (SWIGNode N)
  /-- Observed/endogenous random nodes `V` as random SWIG nodes. -/
  observed : Finset (SWIGNode N)
  /-- Unobserved/exogenous random nodes `U` as random SWIG nodes. -/
  unobserved : Finset (SWIGNode N)
  /-- All elements of `fixed` are of the form `.fixed n`. -/
  fixed_is_fixed :
    ∀ s ∈ fixed, ∃ n : N, s = SWIGNode.fixed n
  /-- All elements of `observed` are of the form `.random n`. -/
  observed_is_random :
    ∀ v ∈ observed, ∃ n : N, v = SWIGNode.random n
  /-- All elements of `unobserved` are of the form `.random n`. -/
  unobserved_is_random :
    ∀ u ∈ unobserved, ∃ n : N, u = SWIGNode.random n
  /-- `observed` and `unobserved` are disjoint. -/
  obs_unobs_disjoint : Disjoint observed unobserved
  /-- Every vertex participating in any edge of `dag` is classified as
      fixed, observed, or unobserved. Trivially preserved under edge
      removal, which is why it replaces the older `obs_unobs_cover_random`
      that did not survive the `induce` operation. -/
  dag_edges_classified :
    ∀ u v, dag.edge u v →
      u ∈ fixed ∪ observed ∪ unobserved ∧
      v ∈ fixed ∪ observed ∪ unobserved
  /-- The image of `fixed` under `iotaMap` lies in `observed`. -/
  fixed_image_in_observed :
    ∀ s ∈ fixed, iotaMap s ∈ observed
  /-- Fixed nodes are roots in `dag`. -/
  fixed_are_roots : ∀ s ∈ fixed, dag.parents s = ∅
  /-- Unobserved nodes are roots in `dag`. -/
  unobs_are_roots : ∀ u ∈ unobserved, dag.parents u = ∅
  /-- Any fixed-form node not listed in `fixed` is isolated in `dag`. -/
  fixed_outside_fixed_isolated :
    ∀ n : N, SWIGNode.fixed n ∉ fixed →
      dag.parents (SWIGNode.fixed n) = ∅ ∧ dag.children (SWIGNode.fixed n) = ∅
  /-- Every child of any classified node is observed. This global
      child-classification invariant is used to rule out outgoing edges into
      fixed or latent-root nodes. -/
  all_children_in_observed :
    ∀ u ∈ unobserved ∪ fixed ∪ observed, dag.children u ⊆ observed

namespace SWIGGraph

variable {N : Type*} [DecidableEq N] [Fintype N]

/-- The canonical map `ι : S → V` sending each fixed intervention parameter
    to its random counterpart in `observed`, via `iotaMap`. -/
def iota (G : SWIGGraph N) (s : {s // s ∈ G.fixed}) :
    {v // v ∈ G.observed} :=
⟨iotaMap s, G.fixed_image_in_observed s s.property⟩

/-- Evaluate `ι` as a `SWIGNode` (forgetting membership). -/
def iotaNode (G : SWIGGraph N) (s : {s // s ∈ G.fixed}) : SWIGNode N :=
  (G.iota s).1

/-- Forgetting the membership proof in the graph-level link map gives the node-level link map. -/
@[simp] theorem iotaNode_eq_iotaMap (G : SWIGGraph N) (s : {s // s ∈ G.fixed}) :
    G.iotaNode s = iotaMap s := rfl

/-- `ι` at the level of original nodes `N`, using the fact that
    every `s ∈ fixed` is of the form `.fixed n`. -/
def iotaN (G : SWIGGraph N) (d : {n : N // SWIGNode.fixed n ∈ G.fixed}) :
    {n : N // SWIGNode.random n ∈ G.observed} :=
by
  refine ⟨d, ?_⟩
  have := G.fixed_image_in_observed (SWIGNode.fixed d) d.property
  -- `iotaMap (.fixed d)` is `.random d`
  simpa [iotaMap] using this

/-- A standard SWIG graph has no fixed (intervention) variables: S = ∅. -/
def isStandard (G : SWIGGraph N) : Prop := G.fixed = ∅

-- ============================================================
-- Equivalence of SWIG graphs (up to topological order)
-- ============================================================

/-- Equivalence of SWIG graphs, ignoring the particular topological order.

Two `SWIGGraph`s are considered equivalent if:
- They have the same edge relation on `SWIGNode N`
- Their `fixed`, `observed`, and `unobserved` node sets coincide.

Everything else (edge decidability, the acyclicity proof, and the derived
topological order `dag.topoOrder`) is determined by the edge relation, so we treat
it as irrelevant for equivalence. -/
def Equivalent (G H : SWIGGraph N) : Prop :=
  (∀ u v, G.dag.edge u v ↔ H.dag.edge u v) ∧
  G.fixed = H.fixed ∧
  G.observed = H.observed ∧
  G.unobserved = H.unobserved

/-- SWIG graph equivalence is reflexive. -/
@[refl] theorem Equivalent.refl (G : SWIGGraph N) : Equivalent G G := by
  unfold Equivalent
  refine And.intro ?hedge ?hfix
  · intro u v; exact Iff.rfl
  · exact And.intro rfl (And.intro rfl rfl)

/-- SWIG graph equivalence is symmetric. -/
@[symm] theorem Equivalent.symm {G H : SWIGGraph N} :
    Equivalent G H → Equivalent H G := by
  intro h
  rcases h with ⟨hedge, hfix, hobs, hunobs⟩
  refine And.intro ?hedge' ?rest
  · intro u v
    have := hedge u v
    exact this.symm
  · refine And.intro ?hfix' ?hobs_unobs'
    · simp [hfix]
    · refine And.intro ?hobs' ?hunobs'
      · simp [hobs]
      · simp [hunobs]

/-- SWIG graph equivalence is transitive. -/
@[trans] theorem Equivalent.trans {G H K : SWIGGraph N} :
    Equivalent G H → Equivalent H K → Equivalent G K := by
  intro hGH hHK
  rcases hGH with ⟨hedgeGH, hfixGH, hobsGH, hunobsGH⟩
  rcases hHK with ⟨hedgeHK, hfixHK, hobsHK, hunobsHK⟩
  refine And.intro ?hedge ?rest
  · intro u v
    exact Iff.trans (hedgeGH u v) (hedgeHK u v)
  · refine And.intro ?hfix ?hobs_unobs
    · -- fixed sets
      simp [hfixGH, hfixHK]
    · refine And.intro ?hobs ?hunobs
      · -- observed sets
        simp [hobsGH, hobsHK]
      · -- unobserved sets
        simp [hunobsGH, hunobsHK]

/-- Equivalent SWIGGraphs have the same `parents` Finset at every node.

    Consequence of `Equivalent`'s edge-iff clause and the fact that
    `DAG.parents` is `Finset.univ.filter (edge · v)`. -/
theorem Equivalent.parents_eq {G H : SWIGGraph N}
    (h : G.Equivalent H) (v : SWIGNode N) :
    G.dag.parents v = H.dag.parents v := by
  ext u
  rw [G.dag.mem_parents, H.dag.mem_parents]
  exact h.1 u v

/-- If `u` is a parent of `v` in `G`, then `u` is classified
    (fixed, observed, or unobserved). -/
theorem parent_classified (G : SWIGGraph N) {u v : SWIGNode N}
    (h : u ∈ G.dag.parents v) :
    u ∈ G.fixed ∪ G.observed ∪ G.unobserved :=
  (G.dag_edges_classified u v (G.dag.mem_parents.mp h)).1

/-- If `w` is a child of `u` in `G`, then `w` is classified
    (fixed, observed, or unobserved). -/
theorem child_classified (G : SWIGGraph N) {u w : SWIGNode N}
    (h : w ∈ G.dag.children u) :
    w ∈ G.fixed ∪ G.observed ∪ G.unobserved :=
  (G.dag_edges_classified u w (G.dag.mem_children.mp h)).2

end SWIGGraph

end Causalean
