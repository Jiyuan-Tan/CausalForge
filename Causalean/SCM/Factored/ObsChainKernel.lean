/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Do.Rule2Kernel.Helpers
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-! # Observational Chain-Rule Kernel

The observational kernel factors along the topological order of observed nodes
as the iterated product of one-node conditional kernels given the full observed
history. This is the ordinary chain rule for kernels, formulated with
Mathlib's continuous-safe `condKernel`.

This file builds the prefix node sets, the one-step observational conditional
kernel, the recursive chain kernel, and the full-length product kernel
`qFactorProduct`. The final equality with `obsKernel` is stated as the real
kernel equality and proved by the standard disintegration induction.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SWIGGraph

variable (G : SWIGGraph N)

/-- **Observed predecessors `Pa⁺_G(v)`.** The observed nodes appearing strictly
before `v` in the topological order of `G.dag`.

This is Tian's full-history convention: it is not the direct-parent set. -/
noncomputable def observedPredecessors (v : SWIGNode N) : Finset (SWIGNode N) :=
  G.observed.filter (fun w => G.dag.topoOrder w < G.dag.topoOrder v)

/-- Observed predecessors are observed by construction. -/
lemma observedPredecessors_subset_observed (v : SWIGNode N) :
    G.observedPredecessors v ⊆ G.observed := by
  intro w hw
  exact (Finset.mem_filter.mp hw).1

end SWIGGraph

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Prefix node sets
-- ============================================================

/-- The first `n` observed nodes in the canonical topological order. If
`n ≥ M.observed.card`, this is all observed nodes. -/
noncomputable def prefixNodes (M : Causalean.SCM N Ω) (n : ℕ) :
    Finset (SWIGNode N) :=
  M.observed.filter
    (fun v => if h : v ∈ M.observed then (M.observedIndex ⟨v, h⟩).val < n else False)

/-- Membership in `prefixNodes` is exactly having observed index below `n`. -/
lemma mem_prefixNodes_iff (M : Causalean.SCM N Ω) (n : ℕ) (v : SWIGNode N) :
    v ∈ M.prefixNodes n ↔
      ∃ h : v ∈ M.observed, (M.observedIndex ⟨v, h⟩).val < n := by
  unfold prefixNodes
  constructor
  · intro hv
    rcases Finset.mem_filter.mp hv with ⟨hobs, hltif⟩
    exact ⟨hobs, by simpa [hobs] using hltif⟩
  · rintro ⟨hobs, hlt⟩
    exact Finset.mem_filter.mpr ⟨hobs, by simpa [hobs] using hlt⟩

/-- Prefix nodes are observed nodes. -/
lemma prefixNodes_subset_observed (M : Causalean.SCM N Ω) (n : ℕ) :
    M.prefixNodes n ⊆ M.observed := by
  intro v hv
  exact (M.mem_prefixNodes_iff n v).mp hv |>.1

/-- The empty prefix has no nodes. -/
lemma prefixNodes_zero (M : Causalean.SCM N Ω) :
    M.prefixNodes 0 = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (M.mem_prefixNodes_iff 0 v).mp hv with ⟨_, hlt⟩
    omega
  · simp

/-- An observed node at index `i` belongs to the first `n` nodes iff `i < n`. -/
lemma observedAt_mem_prefixNodes_iff (M : Causalean.SCM N Ω)
    (n : ℕ) (i : Fin M.observed.card) :
    (M.observedAt i).val ∈ M.prefixNodes n ↔ i.val < n := by
  rw [M.mem_prefixNodes_iff]
  constructor
  · rintro ⟨hobs, hlt⟩
    have hidx : M.observedIndex ⟨(M.observedAt i).val, hobs⟩ = i := by
      have hsub :
          (⟨(M.observedAt i).val, hobs⟩ : {v // v ∈ M.observed}) = M.observedAt i :=
        Subtype.ext rfl
      rw [hsub]
      exact M.observedIndex_observedAt i
    rwa [hidx] at hlt
  · intro hlt
    exact ⟨(M.observedAt i).property,
      by simpa [M.observedIndex_observedAt i] using hlt⟩

/-- The full prefix is the full observed node set. -/
lemma prefixNodes_card (M : Causalean.SCM N Ω) :
    M.prefixNodes M.observed.card = M.observed := by
  ext v
  constructor
  · exact fun hv => M.prefixNodes_subset_observed _ hv
  · intro hv
    exact (M.mem_prefixNodes_iff M.observed.card v).mpr
      ⟨hv, (M.observedIndex ⟨v, hv⟩).isLt⟩

/-- The next observed node is not in the previous prefix. -/
lemma observedAt_not_mem_prefixNodes (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n < M.observed.card) :
    (M.observedAt ⟨n, hn⟩).val ∉ M.prefixNodes n := by
  rw [M.observedAt_mem_prefixNodes_iff n ⟨n, hn⟩]
  exact Nat.lt_irrefl n

/-- The prefix successor is obtained by adjoining the next observed node. -/
lemma prefixNodes_succ (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n < M.observed.card) :
    M.prefixNodes (n + 1) =
      M.prefixNodes n ∪ {(M.observedAt ⟨n, hn⟩).val} := by
  ext v
  constructor
  · intro hv
    rcases (M.mem_prefixNodes_iff (n + 1) v).mp hv with ⟨hobs, hlt⟩
    by_cases hlt_n : (M.observedIndex ⟨v, hobs⟩).val < n
    · exact Finset.mem_union_left _ ((M.mem_prefixNodes_iff n v).mpr ⟨hobs, hlt_n⟩)
    · have hidx_val : (M.observedIndex ⟨v, hobs⟩).val = n := by omega
      have hidx : M.observedIndex ⟨v, hobs⟩ = ⟨n, hn⟩ := Fin.ext hidx_val
      have hv_eq : v = (M.observedAt ⟨n, hn⟩).val := by
        have hround := M.observedAt_observedIndex ⟨v, hobs⟩
        rw [hidx] at hround
        exact hround.symm
      exact Finset.mem_union_right _ (by simp [hv_eq])
  · intro hv
    rcases Finset.mem_union.mp hv with hvpre | hvlast
    · rcases (M.mem_prefixNodes_iff n v).mp hvpre with ⟨hobs, hlt⟩
      exact (M.mem_prefixNodes_iff (n + 1) v).mpr ⟨hobs, by omega⟩
    · have hv_eq : v = (M.observedAt ⟨n, hn⟩).val := by simpa using hvlast
      subst hv_eq
      rw [M.observedAt_mem_prefixNodes_iff (n + 1) ⟨n, hn⟩]
      exact Nat.lt_succ_self n

/-- The previous prefix is disjoint from the singleton next node. -/
lemma prefixNodes_disjoint_singleton_next (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n < M.observed.card) :
    Disjoint (M.prefixNodes n) ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) := by
  rw [Finset.disjoint_singleton_right]
  exact M.observedAt_not_mem_prefixNodes hn

/-- For the node at index `n`, Tian's full-history predecessor set is exactly
the first `n` observed nodes. -/
lemma observedPredecessors_observedAt (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n < M.observed.card) :
    M.toSWIGGraph.observedPredecessors (M.observedAt ⟨n, hn⟩).val =
      M.prefixNodes n := by
  classical
  letI := M.topoLinearOrder
  ext w
  constructor
  · intro hw
    rcases Finset.mem_filter.mp hw with ⟨hwobs, htopo⟩
    have hw_lt :
        (⟨w, hwobs⟩ : {v // v ∈ M.observed}) < M.observedAt ⟨n, hn⟩ := by
      change w < (M.observedAt ⟨n, hn⟩).val
      simpa [SCM.topoLinearOrder] using htopo
    have hidx :
        (M.observed.orderIsoOfFin rfl).symm ⟨w, hwobs⟩ <
          (M.observed.orderIsoOfFin rfl).symm (M.observedAt ⟨n, hn⟩) :=
      (M.observed.orderIsoOfFin rfl).symm.strictMono hw_lt
    exact (M.mem_prefixNodes_iff n w).mpr
      ⟨hwobs, by simpa [SCM.observedIndex, SCM.observedAt] using hidx⟩
  · intro hw
    rcases (M.mem_prefixNodes_iff n w).mp hw with ⟨hwobs, hidx_lt⟩
    refine Finset.mem_filter.mpr ⟨hwobs, ?_⟩
    have hfin :
        M.observedIndex ⟨w, hwobs⟩ < ⟨n, hn⟩ := by
      exact Fin.mk_lt_mk.mpr hidx_lt
    have hw_lt :
        (⟨w, hwobs⟩ : {v // v ∈ M.observed}) < M.observedAt ⟨n, hn⟩ := by
      have hmono :=
        (M.observed.orderIsoOfFin rfl).strictMono
          (by simpa [SCM.observedIndex, SCM.observedAt] using hfin)
      simpa [SCM.observedAt_observedIndex] using hmono
    change w < (M.observedAt ⟨n, hn⟩).val at hw_lt
    simpa [SCM.topoLinearOrder] using hw_lt

-- ============================================================
-- § 2. Single-node conditional step kernels
-- ============================================================

/-- Read the only coordinate of a singleton `ValuesOn` tuple. -/
noncomputable def singletonValue {v : SWIGNode N}
    (x : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω)) :
    swigΩ Ω v :=
  x ⟨v, by simp⟩

/-- Build a singleton `ValuesOn` tuple from a value. -/
noncomputable def singletonValues {v : SWIGNode N} (x : swigΩ Ω v) :
    ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) :=
  fun ⟨w, hw⟩ => by
    have h : w = v := by simpa using hw
    exact h ▸ x

/-- Reading a singleton value is measurable. -/
lemma measurable_singletonValue {v : SWIGNode N} :
    Measurable (singletonValue (Ω := Ω) (v := v)) := by
  unfold singletonValue
  exact measurable_pi_apply (⟨v, by simp⟩ :
    {w // w ∈ ({v} : Finset (SWIGNode N))})

/-- Building a singleton tuple is measurable. -/
lemma measurable_singletonValues {v : SWIGNode N} :
    Measurable (singletonValues (Ω := Ω) (v := v)) := by
  refine measurable_pi_iff.mpr ?_
  rintro ⟨w, hw⟩
  have h : w = v := by simpa using hw
  subst w
  change Measurable (id : swigΩ Ω v → swigΩ Ω v)
  exact measurable_id

/-- Reading the tuple built from a singleton value returns that value. -/
@[simp] lemma singletonValue_singletonValues {v : SWIGNode N}
    (x : swigΩ Ω v) :
    singletonValue (Ω := Ω) (v := v)
      (singletonValues (Ω := Ω) (v := v) x) = x := by
  rfl

/-- Building a singleton tuple from its only coordinate returns the tuple. -/
@[simp] lemma singletonValues_singletonValue {v : SWIGNode N}
    (x : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω)) :
    singletonValues (Ω := Ω) (v := v)
      (singletonValue (Ω := Ω) (v := v) x) = x := by
  ext ⟨w, hw⟩
  have hwv : w = v := by simpa using hw
  subst w
  rfl

/-- The single-node observational conditional kernel for the `n`-th observed
node given the first `n` observed nodes. -/
noncomputable def obsStepCondKernel
    (M : Causalean.SCM N Ω) {n : ℕ} (hn : n < M.observed.card)
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M.FixedValues) (ValuesOn (M.prefixNodes n) (swigΩ Ω))] :
    ProbabilityTheory.Kernel
      (M.FixedValues × ValuesOn (M.prefixNodes n) (swigΩ Ω))
      (swigΩ Ω (M.observedAt ⟨n, hn⟩).val) :=
  (M.obsCondKernel ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N))
      (M.prefixNodes n)
      (by
        intro v hv
        have hv_eq : v = (M.observedAt ⟨n, hn⟩).val := by simpa using hv
        simp [hv_eq, (M.observedAt ⟨n, hn⟩).property])
      (M.prefixNodes_subset_observed n)).map
    (singletonValue (Ω := Ω) (v := (M.observedAt ⟨n, hn⟩).val))

/-- The one-node observational conditional kernel is Markov. -/
instance isMarkov_obsStepCondKernel
    (M : Causalean.SCM N Ω) {n : ℕ} (hn : n < M.observed.card)
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M.FixedValues) (ValuesOn (M.prefixNodes n) (swigΩ Ω))] :
    ProbabilityTheory.IsMarkovKernel (M.obsStepCondKernel hn) := by
  have hY :
      ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) ⊆ M.observed := by
    intro v hv
    have hv_eq : v = (M.observedAt ⟨n, hn⟩).val := by simpa using hv
    simp [hv_eq, (M.observedAt ⟨n, hn⟩).property]
  have hCC : M.prefixNodes n ⊆ M.observed := M.prefixNodes_subset_observed n
  haveI : ProbabilityTheory.IsMarkovKernel
      (M.obsCondPairKernel ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N))
        (M.prefixNodes n) hY hCC) := by
    unfold SCM.obsCondPairKernel
    exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
      (Measurable.prodMk
        (measurable_valuesProjection hCC)
        (measurable_valuesProjection hY))
  haveI : ProbabilityTheory.IsFiniteKernel
      (M.obsCondPairKernel ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N))
        (M.prefixNodes n) hY hCC) := by
    infer_instance
  unfold obsStepCondKernel SCM.obsCondKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    (measurable_singletonValue (Ω := Ω))

/-- The one-node observational conditional kernel is finite. -/
instance isFinite_obsStepCondKernel
    (M : Causalean.SCM N Ω) {n : ℕ} (hn : n < M.observed.card)
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M.FixedValues) (ValuesOn (M.prefixNodes n) (swigΩ Ω))] :
    ProbabilityTheory.IsFiniteKernel (M.obsStepCondKernel hn) := by
  infer_instance

/-- Mapping the scalar step kernel back to the singleton tuple recovers the
conditional kernel it was built from. -/
lemma obsStepCondKernel_map_singletonValues
    (M : Causalean.SCM N Ω) {n : ℕ} (hn : n < M.observed.card)
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M.FixedValues) (ValuesOn (M.prefixNodes n) (swigΩ Ω))] :
    (M.obsStepCondKernel hn).map
        (singletonValues (Ω := Ω) (v := (M.observedAt ⟨n, hn⟩).val))
      =
    M.obsCondKernel ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N))
      (M.prefixNodes n)
      (by
        intro v hv
        have hv_eq : v = (M.observedAt ⟨n, hn⟩).val := by simpa using hv
        simp [hv_eq, (M.observedAt ⟨n, hn⟩).property])
      (M.prefixNodes_subset_observed n) := by
  refine ProbabilityTheory.Kernel.ext fun sc => ?_
  unfold obsStepCondKernel
  rw [ProbabilityTheory.Kernel.map_apply _ (measurable_singletonValues (Ω := Ω))]
  rw [ProbabilityTheory.Kernel.map_apply _ (measurable_singletonValue (Ω := Ω))]
  rw [MeasureTheory.Measure.map_map
      (measurable_singletonValues (Ω := Ω))
      (measurable_singletonValue (Ω := Ω))]
  have hcomp :
      (singletonValues (Ω := Ω) (v := (M.observedAt ⟨n, hn⟩).val) ∘
        singletonValue (Ω := Ω) (v := (M.observedAt ⟨n, hn⟩).val))
        =
      (id :
        ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω) →
          ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω)) := by
    funext x
    exact singletonValues_singletonValue (Ω := Ω) x
  rw [hcomp, MeasureTheory.Measure.map_id]

/-- Slice form of `obsStepCondKernel_map_singletonValues`. -/
lemma obsStepCondKernel_sectR_map_singletonValues
    (M : Causalean.SCM N Ω) {n : ℕ} (hn : n < M.observed.card)
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M.FixedValues) (ValuesOn (M.prefixNodes n) (swigΩ Ω))]
    (s : M.FixedValues) :
    ((M.obsStepCondKernel hn).sectR s).map
        (singletonValues (Ω := Ω) (v := (M.observedAt ⟨n, hn⟩).val))
      =
    (M.obsCondKernel ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N))
      (M.prefixNodes n)
      (by
        intro v hv
        have hv_eq : v = (M.observedAt ⟨n, hn⟩).val := by simpa using hv
        simp [hv_eq, (M.observedAt ⟨n, hn⟩).property])
      (M.prefixNodes_subset_observed n)).sectR s := by
  refine ProbabilityTheory.Kernel.ext fun c => ?_
  unfold ProbabilityTheory.Kernel.sectR
  rw [ProbabilityTheory.Kernel.map_apply _ (measurable_singletonValues (Ω := Ω))]
  rw [ProbabilityTheory.Kernel.comap_apply]
  rw [ProbabilityTheory.Kernel.comap_apply]
  have h := congrArg (fun k => k (s, c)) (M.obsStepCondKernel_map_singletonValues hn)
  change ((M.obsStepCondKernel hn).map
        (singletonValues (Ω := Ω) (v := (M.observedAt ⟨n, hn⟩).val))) (s, c)
      =
    M.obsCondKernel ({(M.observedAt ⟨n, hn⟩).val} : Finset (SWIGNode N))
      (M.prefixNodes n)
      (by
        intro v hv
        have hv_eq : v = (M.observedAt ⟨n, hn⟩).val := by simpa using hv
        simp [hv_eq, (M.observedAt ⟨n, hn⟩).property])
      (M.prefixNodes_subset_observed n) (s, c) at h
  rw [ProbabilityTheory.Kernel.map_apply _ (measurable_singletonValues (Ω := Ω))] at h
  exact h

-- ============================================================
-- § 3. Recursive observational chain kernel
-- ============================================================

/-- The unique value on the empty prefix. -/
noncomputable def emptyPrefixValues (M : Causalean.SCM N Ω) :
    ValuesOn (M.prefixNodes 0) (swigΩ Ω) :=
  fun ⟨v, hv⟩ => by
    have : v ∈ (∅ : Finset (SWIGNode N)) := by
      simp [M.prefixNodes_zero] at hv
    simp at this

/-- The base observational chain kernel: a Dirac mass on the empty prefix. -/
noncomputable def obsChainKernelZero (M : Causalean.SCM N Ω) :
    ProbabilityTheory.Kernel M.FixedValues (ValuesOn (M.prefixNodes 0) (swigΩ Ω)) :=
  ProbabilityTheory.Kernel.const _ (MeasureTheory.Measure.dirac M.emptyPrefixValues)

/-- The base observational chain kernel is Markov. -/
instance isMarkov_obsChainKernelZero (M : Causalean.SCM N Ω) :
    ProbabilityTheory.IsMarkovKernel M.obsChainKernelZero := by
  unfold obsChainKernelZero
  infer_instance

/-- Extend a prefix assignment by the next observed value. -/
noncomputable def extendObsPrefix (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n < M.observed.card) :
    ValuesOn (M.prefixNodes n) (swigΩ Ω) ×
        swigΩ Ω (M.observedAt ⟨n, hn⟩).val →
      ValuesOn (M.prefixNodes (n + 1)) (swigΩ Ω) :=
  fun p =>
    (valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hn).symm)
      (valuesUnionMk p.1
        (singletonValues (Ω := Ω) (v := (M.observedAt ⟨n, hn⟩).val) p.2))

/-- Prefix extension is measurable. -/
lemma measurable_extendObsPrefix (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n < M.observed.card) :
    Measurable (M.extendObsPrefix hn) := by
    unfold extendObsPrefix
    exact (valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hn).symm).measurable.comp
      ((measurable_valuesUnionMk (Ω := swigΩ Ω)).comp
        (Measurable.prodMk measurable_fst
          ((measurable_singletonValues (Ω := Ω)).comp measurable_snd)))

/-- Projecting the successor prefix through the union equivalence gives the
previous-prefix block and the singleton next-node block. -/
lemma prefixSucc_projection_pair (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n < M.observed.card) :
    (fun ω : M.ObservedValues =>
        valuesUnionEquiv (Ω := Ω) (M.prefixNodes_disjoint_singleton_next hn)
          ((valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hn))
            (valuesProjection (M.prefixNodes_subset_observed (n + 1)) ω)))
      =
    (fun ω : M.ObservedValues =>
        (valuesProjection (M.prefixNodes_subset_observed n) ω,
          valuesProjection
            (by
              intro w hw
              have hw_eq :
                  w = (M.observedAt ⟨n, hn⟩).val := by simpa using hw
              simp [hw_eq, (M.observedAt ⟨n, hn⟩).property])
            ω)) := by
  funext ω
  ext i
  · rfl
  · rfl

/-- The successor-prefix extension is inverse to the union-equivalence view of
the successor prefix. -/
lemma valuesUnionEquiv_extendObsPrefix (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n < M.observed.card)
    (p : ValuesOn (M.prefixNodes n) (swigΩ Ω) ×
        swigΩ Ω (M.observedAt ⟨n, hn⟩).val) :
    valuesUnionEquiv (Ω := Ω) (M.prefixNodes_disjoint_singleton_next hn)
        ((valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hn))
          (M.extendObsPrefix hn p))
      =
    (p.1,
      singletonValues (Ω := Ω) (v := (M.observedAt ⟨n, hn⟩).val) p.2) := by
  change valuesUnionEquiv (Ω := Ω) (M.prefixNodes_disjoint_singleton_next hn)
      ((valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hn))
        ((valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hn)).symm
          (valuesUnionMk p.1 (singletonValues p.2)))) = _
  have hcast :
      (valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hn))
        ((valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hn)).symm
          (valuesUnionMk p.1 (singletonValues p.2)))
        =
      valuesUnionMk p.1 (singletonValues p.2) :=
    by
      change (valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hn)).toFun
          ((valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hn)).invFun
            (valuesUnionMk p.1 (singletonValues p.2)))
        = valuesUnionMk p.1 (singletonValues p.2)
      exact (valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hn)).right_inv _
  rw [hcast]
  change (valuesUnionEquiv (Ω := Ω) (M.prefixNodes_disjoint_singleton_next hn)).toFun
      ((valuesUnionEquiv (Ω := Ω) (M.prefixNodes_disjoint_singleton_next hn)).invFun
        (p.1, singletonValues p.2))
    = (p.1, singletonValues p.2)
  exact (valuesUnionEquiv (Ω := Ω) (M.prefixNodes_disjoint_singleton_next hn)).right_inv _

/-- Slice-level disintegration for the pair kernel defining `obsCondKernel`. -/
lemma obsCondPairKernel_apply_eq_compProd
    (M : Causalean.SCM N Ω) (Y CC : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed) (hCC : CC ⊆ M.observed)
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn CC (swigΩ Ω))]
    (s : M.FixedValues) :
    M.obsCondPairKernel Y CC hY hCC s =
      ((M.obsKernel s).map (valuesProjection hCC)) ⊗ₘ
        (M.obsCondKernel Y CC hY hCC).sectR s := by
  classical
  have hπCC : Measurable (valuesProjection (Ω := swigΩ Ω) hCC) :=
    measurable_valuesProjection _
  have hπY : Measurable (valuesProjection (Ω := swigΩ Ω) hY) :=
    measurable_valuesProjection _
  set κ : ProbabilityTheory.Kernel M.FixedValues
        (ValuesOn CC (swigΩ Ω) × ValuesOn Y (swigΩ Ω)) :=
    M.obsCondPairKernel Y CC hY hCC with hκ_def
  haveI : ProbabilityTheory.IsMarkovKernel κ := by
    rw [hκ_def]
    unfold obsCondPairKernel
    exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ (hπCC.prodMk hπY)
  have hDisint :
      κ.fst ⊗ₖ M.obsCondKernel Y CC hY hCC = κ := by
    change κ.fst ⊗ₖ κ.condKernel = κ
    exact ProbabilityTheory.Kernel.disintegrate _ _
  haveI : ProbabilityTheory.IsMarkovKernel (M.obsCondKernel Y CC hY hCC) := by
    unfold obsCondKernel
    infer_instance
  have hAt :
      (κ.fst s) ⊗ₘ (M.obsCondKernel Y CC hY hCC).sectR s = κ s := by
    have h := congrArg (fun k => k s) hDisint
    change (κ.fst ⊗ₖ M.obsCondKernel Y CC hY hCC) s = κ s at h
    rw [ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR] at h
    exact h
  have hFst :
      κ.fst s = (M.obsKernel s).map (valuesProjection hCC) := by
    rw [hκ_def]
    unfold obsCondPairKernel
    rw [ProbabilityTheory.Kernel.fst_map_prod _ hπY,
        ProbabilityTheory.Kernel.map_apply _ hπCC]
  rw [hκ_def, ← hAt, hFst]

/-- The recursive observational chain-rule kernel through the first `n`
observed nodes. -/
noncomputable def obsChainKernel (M : Causalean.SCM N Ω)
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        (M.FixedValues) (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    (n : ℕ) → (hn : n ≤ M.observed.card) →
      ProbabilityTheory.Kernel M.FixedValues (ValuesOn (M.prefixNodes n) (swigΩ Ω))
  | 0, _ => M.obsChainKernelZero
  | k + 1, hn => by
      have hk : k < M.observed.card := Nat.lt_of_succ_le hn
      letI : StandardBorelSpace
          (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω)) :=
        inferInstance
      letI : Nonempty
          (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω)) :=
        inferInstance
      letI : MeasurableSpace.CountableOrCountablyGenerated
          (M.FixedValues) (ValuesOn (M.prefixNodes k) (swigΩ Ω)) :=
        inferInstance
      exact ((M.obsChainKernel k (Nat.le_of_succ_le hn)) ⊗ₖ
        (M.obsStepCondKernel hk)).map (M.extendObsPrefix hk)

/-- The recursive observational chain kernel is Markov. -/
instance isMarkov_obsChainKernel (M : Causalean.SCM N Ω)
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        (M.FixedValues) (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    ∀ (n : ℕ) (hn : n ≤ M.observed.card),
      ProbabilityTheory.IsMarkovKernel (M.obsChainKernel n hn)
  | 0, _ => M.isMarkov_obsChainKernelZero
  | k + 1, hn => by
      have hk : k < M.observed.card := Nat.lt_of_succ_le hn
      letI := M.isMarkov_obsChainKernel k (Nat.le_of_succ_le hn)
      letI : StandardBorelSpace
          (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω)) :=
        inferInstance
      letI : Nonempty
          (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω)) :=
        inferInstance
      letI : MeasurableSpace.CountableOrCountablyGenerated
          (M.FixedValues) (ValuesOn (M.prefixNodes k) (swigΩ Ω)) :=
        inferInstance
      change ProbabilityTheory.IsMarkovKernel
        (((M.obsChainKernel k (Nat.le_of_succ_le hn)) ⊗ₖ
          (M.obsStepCondKernel hk)).map (M.extendObsPrefix hk))
      exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
        (M.measurable_extendObsPrefix hk)

-- ============================================================
-- § 4. Full-length product and chain-rule theorem
-- ============================================================

/-- Pushforward along a measurable equivalence is injective on measures. -/
lemma measure_eq_of_map_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) {μ ν : MeasureTheory.Measure α}
    (h : μ.map e = ν.map e) : μ = ν := by
  calc
    μ = (μ.map e).map e.symm := by
      rw [MeasureTheory.Measure.map_map e.symm.measurable e.measurable]
      have hcomp : e.symm ∘ (e : α → β) = id := by
        funext x
        exact e.left_inv x
      rw [hcomp, MeasureTheory.Measure.map_id]
    _ = (ν.map e).map e.symm := by rw [h]
    _ = ν := by
      rw [MeasureTheory.Measure.map_map e.symm.measurable e.measurable]
      have hcomp : e.symm ∘ (e : α → β) = id := by
        funext x
        exact e.left_inv x
      rw [hcomp, MeasureTheory.Measure.map_id]

/-- The full observational chain-rule product as a kernel on observed values. -/
noncomputable def qFactorProduct (M : Causalean.SCM N Ω)
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        (M.FixedValues) (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    ProbabilityTheory.Kernel M.FixedValues M.ObservedValues :=
    (M.obsChainKernel M.observed.card (le_refl _)).map
      (valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card)

/-- Prefix form of the observational chain rule. -/
theorem obsKernel_map_prefixNodes (M : Causalean.SCM N Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        (M.FixedValues) (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    ∀ (n : ℕ) (hn : n ≤ M.observed.card),
      (M.obsKernel s).map (valuesProjection (M.prefixNodes_subset_observed n))
        = M.obsChainKernel n hn s := by
  intro n
  induction n with
  | zero =>
      intro hn
      change (M.obsKernel s).map (valuesProjection (M.prefixNodes_subset_observed 0))
        = M.obsChainKernelZero s
      unfold obsChainKernelZero
      rw [ProbabilityTheory.Kernel.const_apply]
      refine MeasureTheory.Measure.ext fun A hA => ?_
      have hsub : Subsingleton (ValuesOn (M.prefixNodes 0) (swigΩ Ω)) := by
        refine ⟨fun f g => ?_⟩
        funext ⟨w, hw⟩
        have : w ∈ (∅ : Finset (SWIGNode N)) := by
          rw [M.prefixNodes_zero] at hw
          exact hw
        exact absurd this (Finset.notMem_empty _)
      by_cases hmem : M.emptyPrefixValues ∈ A
      · have hAuniv : A = Set.univ := by
          ext x
          constructor
          · intro _; trivial
          · intro _
            have hx : x = M.emptyPrefixValues := Subsingleton.elim _ _
            simpa [hx] using hmem
        rw [hAuniv]
        rw [MeasureTheory.Measure.map_apply
          (measurable_valuesProjection (M.prefixNodes_subset_observed 0))
          MeasurableSet.univ]
        simp [M.obsKernel_apply_univ s]
      · have hAempty : A = ∅ := by
          ext x
          constructor
          · intro hx
            have hx0 : x = M.emptyPrefixValues := Subsingleton.elim _ _
            exact (hmem (by simpa [hx0] using hx)).elim
          · intro hx
            exact False.elim hx
        rw [hAempty]
        simp
  | succ n ih =>
      intro hn
      classical
      have hk : n < M.observed.card := Nat.lt_of_succ_le hn
      let Y : Finset (SWIGNode N) := {(M.observedAt ⟨n, hk⟩).val}
      let hY : Y ⊆ M.observed := by
        intro v hv
        have hv_eq : v = (M.observedAt ⟨n, hk⟩).val := by simpa [Y] using hv
        simp [hv_eq, (M.observedAt ⟨n, hk⟩).property]
      let hCC : M.prefixNodes n ⊆ M.observed := M.prefixNodes_subset_observed n
      let e : ValuesOn (M.prefixNodes (n + 1)) (swigΩ Ω) ≃ᵐ
          ValuesOn (M.prefixNodes n) (swigΩ Ω) × ValuesOn Y (swigΩ Ω) :=
        (valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hk)).trans
          (valuesUnionEquiv (Ω := Ω) (M.prefixNodes_disjoint_singleton_next hk))
      refine measure_eq_of_map_measurableEquiv e ?_
      have hIH := ih (Nat.le_of_succ_le hn)
      change MeasureTheory.Measure.map e
          (MeasureTheory.Measure.map
            (valuesProjection (M.prefixNodes_subset_observed (n + 1))) (M.obsKernel s))
        =
        MeasureTheory.Measure.map e
          ((((M.obsChainKernel n (Nat.le_of_succ_le hn)) ⊗ₖ
            (M.obsStepCondKernel hk)).map (M.extendObsPrefix hk)) s)
      rw [ProbabilityTheory.Kernel.map_apply _ (M.measurable_extendObsPrefix hk)]
      rw [ProbabilityTheory.Kernel.compProd_apply_eq_compProd_sectR]
      rw [← hIH]
      rw [MeasureTheory.Measure.map_map e.measurable
          (measurable_valuesProjection (M.prefixNodes_subset_observed (n + 1)))]
      rw [MeasureTheory.Measure.map_map e.measurable (M.measurable_extendObsPrefix hk)]
      have hleft_fun :
          e ∘ valuesProjection (M.prefixNodes_subset_observed (n + 1))
            =
          (fun ω : M.ObservedValues =>
            (valuesProjection (M.prefixNodes_subset_observed n) ω,
              valuesProjection hY ω)) := by
        change
          (fun ω : M.ObservedValues =>
              valuesUnionEquiv (Ω := Ω) (M.prefixNodes_disjoint_singleton_next hk)
                ((valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hk))
                  (valuesProjection (M.prefixNodes_subset_observed (n + 1)) ω)))
            =
          (fun ω : M.ObservedValues =>
            (valuesProjection (M.prefixNodes_subset_observed n) ω,
              valuesProjection hY ω))
        exact M.prefixSucc_projection_pair hk
      rw [hleft_fun]
      have hright_fun :
          e ∘ M.extendObsPrefix hk =
          (fun p : ValuesOn (M.prefixNodes n) (swigΩ Ω) ×
              swigΩ Ω (M.observedAt ⟨n, hk⟩).val =>
            (p.1,
              singletonValues (Ω := Ω)
                (v := (M.observedAt ⟨n, hk⟩).val) p.2)) := by
        funext p
        exact M.valuesUnionEquiv_extendObsPrefix hk p
      rw [hright_fun]
      change MeasureTheory.Measure.map
          (fun ω : M.ObservedValues =>
            (valuesProjection hCC ω, valuesProjection hY ω)) (M.obsKernel s)
        =
        MeasureTheory.Measure.map
          (Prod.map id
            (singletonValues (Ω := Ω) (v := (M.observedAt ⟨n, hk⟩).val)))
          (((M.obsKernel s).map (valuesProjection hCC)) ⊗ₘ
            (M.obsStepCondKernel hk).sectR s)
      rw [← MeasureTheory.Measure.compProd_map
        (μ := (M.obsKernel s).map (valuesProjection hCC))
        (κ := (M.obsStepCondKernel hk).sectR s)
        (f := singletonValues (Ω := Ω) (v := (M.observedAt ⟨n, hk⟩).val))
        (measurable_singletonValues (Ω := Ω))]
      rw [M.obsStepCondKernel_sectR_map_singletonValues hk s]
      rw [← M.obsCondPairKernel_apply_eq_compProd Y (M.prefixNodes n) hY hCC s]
      unfold obsCondPairKernel
      rw [ProbabilityTheory.Kernel.map_apply _ ((measurable_valuesProjection hCC).prodMk
        (measurable_valuesProjection hY))]

/-- The observational kernel is the full chain-rule product of one-node
conditionals along the observed topological order. -/
theorem obsKernel_eq_qFactorProduct (M : Causalean.SCM N Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        (M.FixedValues) (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    M.obsKernel s = M.qFactorProduct s := by
  unfold qFactorProduct
  rw [ProbabilityTheory.Kernel.map_apply _
    (valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card).measurable]
  have hprefix := M.obsKernel_map_prefixNodes s M.observed.card (le_refl _)
  rw [← hprefix]
  rw [MeasureTheory.Measure.map_map
    (valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card).measurable
    (measurable_valuesProjection (M.prefixNodes_subset_observed M.observed.card))]
  have hcomp :
      (valuesEquivOfEq (Ω := swigΩ Ω) M.prefixNodes_card) ∘
        valuesProjection (M.prefixNodes_subset_observed M.observed.card)
        =
      (id : M.ObservedValues → M.ObservedValues) := by
    funext ω
    rfl
  rw [hcomp, MeasureTheory.Measure.map_id]

end SCM

end Causalean
