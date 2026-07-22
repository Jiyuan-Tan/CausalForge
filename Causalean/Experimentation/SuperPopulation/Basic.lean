/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Probability.SteinMethod.DepGraphCLT

/-!
# Super-population locally-dependent network field

The design-based experimentation substrate (`Experimentation/DesignBased/`) fixes the potential
outcomes and puts all randomness in the assignment, so its probability space is a finite product
measure over the treatment vector.  The **super-population / model-based** route is the opposite:
the units (and their outcomes) are themselves drawn from a population, the randomness is the
*sampling / population draw*, and the dependence between units is governed by a network rather
than by an assignment mechanism.  This file provides the base object for that route.

A `NetworkDependence` is the model-based sibling of `Causalean.Stat.IIDSample`: instead of mutual
independence (`iIndepFun`) it carries a **bounded-range / m-dependent** network — node-level
random summands `X i : Ω → ℝ` on a common ambient space `(Ω, μ)`, together with a reflexive,
symmetric adjacency relation such that index sets with no edge between them carry independent
summand tuples.  This is exactly the data of a dependency graph
(`Causalean.SteinMethod.DepGraph`), so `toDepGraph` exposes the field to the proved Stein
dependency-graph CLT (`stein_cdf_clt_of_depGraph`), which the `CLT` file specializes.

This is the m-dependent (exact-independence-beyond-the-network) layer.  Decaying-dependence
(ψ- or mixing) models, where far-apart nodes are only approximately independent, are a
different super-population abstraction and are not part of this module.
-/

open MeasureTheory ProbabilityTheory

namespace Causalean.Experimentation.SuperPopulation

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- A **super-population locally-dependent network field**: node-level random summands
`X i : Ω → ℝ` on a common ambient measure space `(Ω, μ)`, with a reflexive, symmetric network
relation `adj` such that any two index sets with no edge between them carry independent summand
tuples (exact `m`-dependence beyond the network).  This is the model-based counterpart of the
finite design — the randomness is the population draw, not the assignment — and the m-dependence
sibling of an i.i.d. sample. -/
structure NetworkDependence (V Ω : Type*) [Fintype V] [DecidableEq V]
    [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- The node-level random summand (one real-valued contribution per unit). -/
  X : V → Ω → ℝ
  /-- The network / dependency relation between units. -/
  adj : V → V → Prop
  /-- Decidability of adjacency (for the neighborhood `Finset`). -/
  decAdj : DecidableRel adj
  /-- Each unit is adjacent to itself. -/
  refl : ∀ i, adj i i
  /-- The network is symmetric. -/
  symm : ∀ i j, adj i j → adj j i
  /-- Each node summand is measurable. -/
  meas : ∀ i, Measurable (X i)
  /-- Non-adjacent index sets carry independent summand tuples (exact `m`-dependence). -/
  indep : ∀ A B : Finset V, (∀ a ∈ A, ∀ b ∈ B, ¬ adj a b) →
    IndepFun (fun ω => fun k : A => X k ω) (fun ω => fun k : B => X k ω) μ

namespace NetworkDependence

variable (F : NetworkDependence V Ω μ)

/-- The network field, viewed as a Stein dependency graph for its summands — a pure field rename,
so the proved dependency-graph CLT applies verbatim. -/
def toDepGraph : Causalean.SteinMethod.DepGraph F.X μ where
  G := F.adj
  decG := F.decAdj
  refl := F.refl
  symm := F.symm
  meas := F.meas
  indep := F.indep

/-- The closed network neighborhood `N i = {j | adj i j}` of a unit. -/
noncomputable def nbhd (i : V) : Finset V := F.toDepGraph.nbhd i

/-- Membership in the neighborhood is exactly adjacency. -/
theorem mem_nbhd_iff {i j : V} : j ∈ F.nbhd i ↔ F.adj i j := F.toDepGraph.mem_nbhd_iff

/-- Each unit lies in its own neighborhood. -/
theorem self_mem_nbhd (i : V) : i ∈ F.nbhd i := F.toDepGraph.self_mem_nbhd i

end NetworkDependence

end Causalean.Experimentation.SuperPopulation
