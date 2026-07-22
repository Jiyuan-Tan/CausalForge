/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.SWIG
import Causalean.SCM.Model.EdgeType
import Causalean.Mathlib.MeasureTheory.FinsetValues
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Notation

/-! # Structural causal models

This file defines the core measure-theoretic structural causal model object used by the
single-world intervention graph framework. It provides the `SCM` structure itself,
aliases for fixed, observed, latent, and random value assignments, the latent product
measure, canonical topological-order indexing of observed nodes, and structural equivalence
of models. The underlying value-space bookkeeping (`ValuesOn`, `valuesProjection`, and the
coordinate-restriction measurability lemmas) lives in
`Causalean.Mathlib.MeasureTheory.FinsetValues`.

An `SCM` consists of a SWIG graph, value spaces, deterministic measurable structural
functions for observed variables, edge labels, and one probability measure for each latent
root. Later evaluation and kernel files build the joint and observational laws from these
primitive ingredients.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. SCM structure
-- ============================================================

/-- A generalized structural causal model consists of a SWIG graph, deterministic measurable
structural functions, and independent latent-root laws.

    Extends `SWIGGraph N` with deterministic measurable structural functions for each
    observed node and one probability measure per latent root.  Randomness lives only
    in the latent roots; the joint / observational kernels are derived via the
    evaluation map in `Causalean.SCM.Model.Evaluation`.

    Fields:
    1. `edgeTypes` — `EdgeTypeAssignment`, orthogonal to semantics, unchanged from the
       kernel-primitive model.
    2. `iota_valueSpace` — matching value spaces for SWIG pairs: `X_d = X_{ι(d)}`.
       Kept as a field because `s.val ∈ fixed` is not a refinement type that forces
       `s.val = .fixed n`, so the equality is not always `rfl` without case analysis.
    3. `structFun v` — for each observed `v`, the deterministic structural map from the
       product of parent value spaces to `Ω v`.
    4. `structFun_measurable` — `structFun v` is measurable.
    5. `latentDist u` — for each latent root `u`, a probability measure on `Ω u`.
    6. `isProbability_latent` — each `latentDist u` is a probability measure.

    The latent product measure `⊗_{u} latentDist u` is a derived quantity; see
    `SCM.latentProduct` below.  Mutual independence of the latent family is automatic
    from the product measure construction. -/
structure SCM (N : Type*) [DecidableEq N] [Fintype N]
    (Ω : N → Type*) [∀ n, MeasurableSpace (Ω n)] extends SWIGGraph N where
  /-- Edge type assignment for the DAG. -/
  edgeTypes : EdgeTypeAssignment dag
  /-- Fixed parameter and its random counterpart share the same value space:
      `X_d = X_{ι(d)}` for each `d ∈ S`. -/
  iota_valueSpace :
    ∀ s : {s // s ∈ fixed}, swigΩ Ω s.val = swigΩ Ω (iotaMap s.val)
  /-- Deterministic measurable structural function for each observed node `v ∈ V`:
      takes parent values (from `S ∪ V ∪ U`) to a value in `Ω v`.
      In paper notation this is `f_v : ∏_{w ∈ Pa(v)} X_w → X_v`. -/
  structFun : ∀ v : {v // v ∈ observed},
    (∀ w : {w // w ∈ dag.parents v.val}, swigΩ Ω w.val) → swigΩ Ω v.val
  /-- Each structural function is measurable. -/
  structFun_measurable : ∀ v : {v // v ∈ observed}, Measurable (structFun v)
  /-- Probability measure on each latent root.  In paper notation this is `ℙ(L)` for
      `L ∈ 𝐋`; in the Lean code we keep the `unobserved` set name from `SWIGGraph`. -/
  latentDist : ∀ u : {u // u ∈ unobserved},
    MeasureTheory.Measure (swigΩ Ω u.val)
  /-- Each `latentDist u` is a probability measure. -/
  isProbability_latent :
    ∀ u : {u // u ∈ unobserved}, MeasureTheory.IsProbabilityMeasure (latentDist u)

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

-- ============================================================
-- § 2. Type aliases and basic definitions
-- ============================================================

/-- Fixed values assign intervention or fixed-node values in a structural causal model. -/
abbrev FixedValues (M : Causalean.SCM N Ω) :=
  ValuesOn M.fixed (swigΩ Ω)

/-- Observed values assign values to the observed nodes of a structural causal model. -/
abbrev ObservedValues (M : Causalean.SCM N Ω) :=
  ValuesOn M.observed (swigΩ Ω)

/-- Latent values assign values to the unobserved root nodes of a structural causal model. -/
abbrev LatentValues (M : Causalean.SCM N Ω) :=
  ValuesOn M.unobserved (swigΩ Ω)

/-- Unobserved values are the same object as latent values and are kept as a compatibility alias.

    Deprecated alias preserving the old `UnobservedValues` name; identical to
    `LatentValues`. -/
abbrev UnobservedValues (M : Causalean.SCM N Ω) := LatentValues M

/-- A standard structural causal model has no fixed intervention variables. -/
def isStandard (M : Causalean.SCM N Ω) : Prop := M.fixed = ∅

/-- The random variables of a structural causal model are its observed and latent nodes. -/
def randomVars (M : Causalean.SCM N Ω) : Finset (SWIGNode N) :=
  M.observed ∪ M.unobserved

/-- Random values assign values to every observed or latent node in a structural causal model. -/
abbrev RandomValues (M : Causalean.SCM N Ω) :=
  ValuesOn M.randomVars (swigΩ Ω)

/-- An observed node cannot also be an unobserved node. -/
theorem not_unobs_of_obs (M : Causalean.SCM N Ω) {n : SWIGNode N} (h : n ∈ M.observed) :
    n ∉ M.unobserved :=
  Finset.disjoint_left.mp M.obs_unobs_disjoint h

/-- An unobserved node cannot also be an observed node. -/
theorem not_obs_of_unobs (M : Causalean.SCM N Ω) {n : SWIGNode N} (h : n ∈ M.unobserved) :
    n ∉ M.observed :=
  Finset.disjoint_right.mp M.obs_unobs_disjoint h

/-- An observed node cannot also be a fixed node.

    A node in `observed` is not in `fixed`: `observed` elements are of the form
    `.random _` while `fixed` elements are of the form `.fixed _`. -/
theorem not_fixed_of_obs (M : Causalean.SCM N Ω) {n : SWIGNode N} (h : n ∈ M.observed) :
    n ∉ M.fixed := by
  intro hfix
  obtain ⟨m, hm⟩ := M.fixed_is_fixed n hfix
  obtain ⟨k, hk⟩ := M.observed_is_random n h
  rw [hm] at hk
  cases hk

-- ============================================================
-- § 3. Latent product measure (derived)
-- ============================================================

/-- The latent product is the joint distribution over all latent roots formed from their
individual laws.

    The joint distribution over all latent roots, built as the product of the per-latent
    measures.  Mutual independence of the family `{L}_{L ∈ 𝐋}` is automatic from the
    `Measure.pi` construction.

    In paper notation this is `ℙ(𝐋) = ⊗_{L ∈ 𝐋} ℙ(L)`. -/
noncomputable def latentProduct (M : Causalean.SCM N Ω) :
    MeasureTheory.Measure (LatentValues M) :=
  letI := M.isProbability_latent
  MeasureTheory.Measure.pi (fun u => M.latentDist u)

/-- The latent product measure has total mass one. -/
instance instProbabilityLatentProduct (M : Causalean.SCM N Ω) :
    MeasureTheory.IsProbabilityMeasure (M.latentProduct) := by
  letI := M.isProbability_latent
  change MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.pi (fun u => M.latentDist u))
  infer_instance

-- ============================================================
-- § 4. Topological ordering of observed nodes
-- ============================================================

/-- The graph's topological order gives a canonical linear order on SWIG nodes. -/
noncomputable def topoLinearOrder (M : Causalean.SCM N Ω) : LinearOrder (SWIGNode N) :=
  LinearOrder.lift' M.dag.topoOrder M.dag.topoOrder_injective

/-- The observed-node enumeration returns the node at a given position in canonical topological
order. -/
noncomputable def observedAt (M : Causalean.SCM N Ω) (i : Fin M.observed.card) :
    {v // v ∈ M.observed} := by
  classical
  letI := M.topoLinearOrder
  exact M.observed.orderIsoOfFin rfl i

/-- The observed-node index returns the canonical topological position of an observed node. -/
noncomputable def observedIndex (M : Causalean.SCM N Ω) (v : {v // v ∈ M.observed}) :
    Fin M.observed.card := by
  classical
  letI := M.topoLinearOrder
  exact (M.observed.orderIsoOfFin rfl).symm v

/-- Looking up an observed node by its canonical index recovers the same node. -/
theorem observedAt_observedIndex (M : Causalean.SCM N Ω) (v : {v // v ∈ M.observed}) :
    (M.observedAt (M.observedIndex v)).val = v.val := by
  classical
  letI := M.topoLinearOrder
  simp [SCM.observedAt, SCM.observedIndex]

/-- Looking up the canonical index of the observed node at a position recovers that position.

    Round-trip the other way: looking up the index of the node at position `k`
    recovers `k`. -/
theorem observedIndex_observedAt (M : Causalean.SCM N Ω) (k : Fin M.observed.card) :
    M.observedIndex (M.observedAt k) = k := by
  classical
  letI := M.topoLinearOrder
  simp [SCM.observedAt, SCM.observedIndex]

/-- An observed parent of a node must appear earlier in the canonical observed topological order.

    An observed parent of the `n`-th observed node must already appear in the
    canonical observed prefix of length `n`. -/
theorem observed_parent_index_lt (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n < M.observed.card) {p : SWIGNode N}
    (hparent : M.dag.edge p (M.observedAt ⟨n, hn⟩).val)
    (hobs : p ∈ M.observed) :
    M.observedIndex ⟨p, hobs⟩ < ⟨n, hn⟩ := by
  classical
  letI := M.topoLinearOrder
  have hp_lt : (⟨p, hobs⟩ : {v // v ∈ M.observed}) < M.observedAt ⟨n, hn⟩ := by
    change p < (M.observedAt ⟨n, hn⟩).val
    simpa [SCM.topoLinearOrder] using M.dag.topoOrder_lt p _ hparent
  have hidx :
      (M.observed.orderIsoOfFin rfl).symm ⟨p, hobs⟩ <
        (M.observed.orderIsoOfFin rfl).symm (M.observedAt ⟨n, hn⟩) :=
    (M.observed.orderIsoOfFin rfl).symm.strictMono hp_lt
  simpa [SCM.observedIndex, SCM.observedAt] using hidx

-- ============================================================
-- § 5. Structural equivalence of structural causal models
-- ============================================================

/-- Two structural causal models are structurally equivalent when their graph, edge labels,
structural functions, and latent laws agree.

    Two structural causal models are structurally equivalent if they share the same SWIG graph
    (in the `SWIGGraph.Equivalent` sense), agree on edge types for corresponding edges, and have
    the same primitive structural data (`structFun` and `latentDist`).  Proof fields
    (`structFun_measurable`, `isProbability_latent`) are ignored. -/
def Equiv (M₁ M₂ : Causalean.SCM N Ω) : Prop :=
  Causalean.SWIGGraph.Equivalent M₁.toSWIGGraph M₂.toSWIGGraph ∧
  (∀ u v, M₁.dag.edge u v → M₂.dag.edge u v →
    M₁.edgeTypes.edgeType u v = M₂.edgeTypes.edgeType u v) ∧
  HEq M₁.structFun M₂.structFun ∧
  HEq M₁.latentDist M₂.latentDist

/-- Structural equivalence is reflexive. -/
lemma Equiv.refl (M : Causalean.SCM N Ω) : Equiv M M := by
  refine And.intro (Causalean.SWIGGraph.Equivalent.refl _) ?_
  refine And.intro ?_ ?_
  · intro u v _ _
    rfl
  · exact And.intro HEq.rfl HEq.rfl

/-- Structural equivalence is symmetric. -/
lemma Equiv.symm {M₁ M₂ : Causalean.SCM N Ω} (h : Equiv M₁ M₂) :
    Equiv M₂ M₁ := by
  rcases h with ⟨hG, hE, hF, hL⟩
  refine And.intro hG.symm ?_
  refine And.intro ?_ ?_
  · intro u v hu hv
    exact (hE u v ((hG.1 u v).2 hu) ((hG.1 u v).1 hv)).symm
  · exact And.intro hF.symm hL.symm

/-- Structural equivalence is transitive. -/
lemma Equiv.trans {M₁ M₂ M₃ : Causalean.SCM N Ω}
    (h₁ : Equiv M₁ M₂) (h₂ : Equiv M₂ M₃) : Equiv M₁ M₃ := by
  rcases h₁ with ⟨hG₁, hE₁, hF₁, hL₁⟩
  rcases h₂ with ⟨hG₂, hE₂, hF₂, hL₂⟩
  refine And.intro (Causalean.SWIGGraph.Equivalent.trans hG₁ hG₂) ?_
  refine And.intro ?_ ?_
  · intro u v hu hv
    have hM₂_edge : M₂.dag.edge u v := (hG₁.1 u v).1 hu
    exact (hE₁ u v hu hM₂_edge).trans (hE₂ u v hM₂_edge hv)
  · exact And.intro (hF₁.trans hF₂) (hL₁.trans hL₂)

/-- Structural causal models form a setoid under structural equivalence. -/
instance instSetoidSCM :
    Setoid (Causalean.SCM N Ω) where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

end SCM

end Causalean
