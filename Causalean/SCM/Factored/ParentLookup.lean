/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Parent-value lookup from a prefix state

For the factored construction of `jointKernel`, at step `n` we need to feed the
structural function `M.structFun v_n` (where `v_n = M.observedAt ⟨n, hn⟩`) with
its parent tuple.  Each parent `p ∈ M.dag.parents v_n.val` falls into exactly
one of three classes — `fixed`, `unobserved`, or `observed` — by
`SWIGGraph.dag_edges_classified`, and its value is read from the corresponding
component of the input state `(s : FixedValues M, ℓ : LatentValues M,
ξ : ObservedPrefixValues M n _)`:

* fixed parent → `s ⟨p.val, _⟩`
* unobserved parent → `ℓ ⟨p.val, _⟩`
* observed parent → `observedPrefixValue` at `observedIndex p`, which is
  `< n` by `SCM.observed_parent_index_lt` — then `cast` through the
  `observedAt_observedIndex` equality.

## Main definitions

* `SCM.parentValuesFromPrefix hn` — the parent-lookup map.
* `SCM.measurable_parentValuesFromPrefix` — joint measurability.

The observed-parent branch mirrors the evaluator's indexing convention: read
the stored prefix coordinate at `observedIndex p` and transport it across
`observedAt_observedIndex`.
-/

import Causalean.SCM.Factored.PrefixState

/-! # Parent Lookup from Prefix States

This file builds the map that reads the parent values of the next observed node
from a fixed assignment, a latent assignment, and an observed prefix. The lookup
classifies each parent as fixed, observed, or unobserved, then proves the joint
measurability needed by the deterministic step kernels in the factored
construction of the joint kernel. -/

namespace Causalean

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Parent classification for an observed target
-- ============================================================

/-- A parent that is neither fixed nor observed must be an unobserved node.
    This lets an evaluator classify a parent's value source without depending on
    where the target appears in an observation order. -/
theorem parent_unobserved_of_not_fixed_not_observed
    (G : SWIGGraph N) {u v : SWIGNode N}
    (hedge : G.dag.edge u v)
    (hfix : u ∉ G.fixed) (hobs : u ∉ G.observed) :
    u ∈ G.unobserved := by
  have hclass : u ∈ G.fixed ∪ G.observed ∪ G.unobserved :=
    (G.dag_edges_classified _ _ hedge).1
  rcases Finset.mem_union.mp hclass with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact (hfix h).elim
    · exact (hobs h).elim
  · exact h

-- ============================================================
-- § 3. Parent-value lookup
-- ============================================================

/-- Assemble the full parent tuple of the next observed node
    `v_n = M.observedAt ⟨n, hn⟩` from fixed values `s`, latent values `ℓ`,
    and the already-generated observed prefix `ξ`. -/
noncomputable def parentValuesFromPrefix (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    (M.FixedValues × M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn)) →
      (∀ w : {w // w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val},
        swigΩ Ω w.val) :=
  fun sℓξ w =>
    by
      by_cases hfix : w.val ∈ M.fixed
      · -- Fixed parent: read from `s = sℓξ.1`.
        exact sℓξ.1 ⟨w.val, hfix⟩
      · by_cases hobs : w.val ∈ M.observed
        · -- Observed parent: read from the prefix `ξ = sℓξ.2.2` at index
          -- `observedIndex w < n`, then cast to `swigΩ Ω w.val`.
          have hlt : M.observedIndex ⟨w.val, hobs⟩ < ⟨n, hn⟩ :=
            M.observed_parent_index_lt hn
              (M.dag.mem_parents.mp w.property) hobs
          let iobs : Fin n :=
            ⟨(M.observedIndex ⟨w.val, hobs⟩ : ℕ), hlt⟩
          have hEq :
              swigΩ Ω (M.observedAt (M.observedIndex ⟨w.val, hobs⟩)).val =
                swigΩ Ω w.val := by
            simpa using
              congrArg (swigΩ Ω) (M.observedAt_observedIndex ⟨w.val, hobs⟩)
          exact cast hEq <| by
            simpa [iobs] using
              M.observedPrefixValue (Nat.le_of_succ_le hn) sℓξ.2.2 iobs
        · -- Unobserved parent: read from `ℓ = sℓξ.2.1`.
          have hunobs : w.val ∈ M.unobserved :=
            parent_unobserved_of_not_fixed_not_observed M.toSWIGGraph
              (M.dag.mem_parents.mp w.property) hfix hobs
          exact sℓξ.2.1 ⟨w.val, hunobs⟩

-- ============================================================
-- § 4. Measurability of the parent-lookup map
-- ============================================================

/-- Fix a structural causal model `M` and a step index `n` such that [there are
    at least `n + 1` observed nodes, so `n` names a valid position in the
    canonical topological order of observed nodes](hyp:hn). Then [the map
    `parentValuesFromPrefix` that reads off the parent values of the `n`-th
    observed node from a fixed-value assignment, a latent assignment, and the
    already-generated length-`n` prefix of observed values is jointly
    measurable in these three arguments](goal). -/
@[fun_prop]
theorem measurable_parentValuesFromPrefix (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    Measurable (M.parentValuesFromPrefix hn) := by
  classical
  refine measurable_pi_lambda _ ?_
  intro w
  by_cases hfix : w.val ∈ M.fixed
  · -- Fixed case: projection `sℓξ ↦ sℓξ.1 ⟨w.val, hfix⟩`.
    have h0 : Measurable fun x : M.FixedValues =>
        x (⟨w.val, hfix⟩ : {x // x ∈ M.fixed}) := measurable_pi_apply _
    have h : Measurable fun c : M.FixedValues ×
        M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn) =>
        c.1 (⟨w.val, hfix⟩ : {x // x ∈ M.fixed}) :=
      h0.comp measurable_fst
    simpa [SCM.parentValuesFromPrefix, hfix] using h
  · by_cases hobs : w.val ∈ M.observed
    · -- Observed case: `cast ∘ observedPrefixValue ∘ snd ∘ snd`.
      have hlt : M.observedIndex ⟨w.val, hobs⟩ < ⟨n, hn⟩ :=
        M.observed_parent_index_lt hn
          (M.dag.mem_parents.mp w.property) hobs
      let iobs : Fin n :=
        ⟨(M.observedIndex ⟨w.val, hobs⟩ : ℕ), hlt⟩
      have hNode :
          (M.observedAt (M.observedIndex ⟨w.val, hobs⟩)).val = w.val := by
        simpa using M.observedAt_observedIndex ⟨w.val, hobs⟩
      have hEq :
          swigΩ Ω (M.observedAt (M.observedIndex ⟨w.val, hobs⟩)).val =
            swigΩ Ω w.val := by
        simpa using congrArg (swigΩ Ω) hNode
      -- Measurability of reading slot `iobs` from the prefix, as a function
      -- of the full product input.
      have hmeas :
          Measurable fun c : M.FixedValues ×
              M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn) =>
            M.observedPrefixValue (Nat.le_of_succ_le hn) c.2.2 iobs :=
        (M.measurable_observedPrefixValue
            (Nat.le_of_succ_le hn) iobs).comp
          ((measurable_snd : Measurable Prod.snd).comp
            (measurable_snd : Measurable Prod.snd))
      have hcast :
          Measurable (fun y :
              swigΩ Ω (M.observedAt (M.observedIndex ⟨w.val, hobs⟩)).val =>
            cast hEq y) :=
        measurable_cast_family hNode
      have hmeasCast :
          Measurable fun c : M.FixedValues ×
              M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn) =>
            cast hEq
              (M.observedPrefixValue (Nat.le_of_succ_le hn) c.2.2 iobs) :=
        hcast.comp hmeas
      simpa [SCM.parentValuesFromPrefix, hfix, hobs, iobs] using hmeasCast
    · -- Unobserved case: projection `sℓξ ↦ sℓξ.2.1 ⟨w.val, hunobs⟩`.
      have hunobs : w.val ∈ M.unobserved :=
        parent_unobserved_of_not_fixed_not_observed M.toSWIGGraph
          (M.dag.mem_parents.mp w.property) hfix hobs
      have h0 : Measurable fun x : M.LatentValues =>
          x (⟨w.val, hunobs⟩ : {x // x ∈ M.unobserved}) := measurable_pi_apply _
      have h : Measurable fun c : M.FixedValues ×
          M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn) =>
          c.2.1 (⟨w.val, hunobs⟩ : {x // x ∈ M.unobserved}) :=
        h0.comp (measurable_fst.comp measurable_snd)
      simpa [SCM.parentValuesFromPrefix, hfix, hobs, hunobs] using h

end SCM

end Causalean
