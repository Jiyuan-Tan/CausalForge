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

/-- If `w` is a parent of the `(n+1)`-st observed node and is neither fixed nor
    observed, then `w` must be unobserved.  Direct consequence of
    `SWIGGraph.dag_edges_classified`. -/
private theorem parent_unobserved_of_not_fixed_not_observed
    (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card)
    (w : {w // w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val})
    (hfix : w.val ∉ M.fixed) (hobs : w.val ∉ M.observed) :
    w.val ∈ M.unobserved := by
  have hedge : M.dag.edge w.val (M.observedAt ⟨n, hn⟩).val :=
    M.dag.mem_parents.mp w.property
  have hclass : w.val ∈ M.fixed ∪ M.observed ∪ M.unobserved :=
    (M.dag_edges_classified _ _ hedge).1
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
            ⟨(M.observedIndex ⟨w.val, hobs⟩ : ℕ), by simpa using hlt⟩
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
            parent_unobserved_of_not_fixed_not_observed (M := M) hn w hfix hobs
          exact sℓξ.2.1 ⟨w.val, hunobs⟩

-- ============================================================
-- § 4. Measurability of the parent-lookup map
-- ============================================================

/-- The parent-lookup map `parentValuesFromPrefix` is jointly measurable in
    `(s, ℓ, ξ)`. -/
theorem measurable_parentValuesFromPrefix (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    Measurable (M.parentValuesFromPrefix hn) := by
  classical
  refine measurable_pi_lambda _ ?_
  intro w
  by_cases hfix : w.val ∈ M.fixed
  · -- Fixed case: projection `sℓξ ↦ sℓξ.1 ⟨w.val, hfix⟩`.
    let wf : {x // x ∈ M.fixed} := ⟨w.val, hfix⟩
    simpa [SCM.parentValuesFromPrefix, hfix, wf] using
      ((measurable_pi_apply (a := wf)) :
          Measurable fun x : M.FixedValues => x wf).comp
        (measurable_fst : Measurable Prod.fst)
  · by_cases hobs : w.val ∈ M.observed
    · -- Observed case: `cast ∘ observedPrefixValue ∘ snd ∘ snd`.
      have hlt : M.observedIndex ⟨w.val, hobs⟩ < ⟨n, hn⟩ :=
        M.observed_parent_index_lt hn
          (M.dag.mem_parents.mp w.property) hobs
      let iobs : Fin n :=
        ⟨(M.observedIndex ⟨w.val, hobs⟩ : ℕ), by simpa using hlt⟩
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
        measurable_cast_swigΩ hNode
      have hmeasCast :
          Measurable fun c : M.FixedValues ×
              M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn) =>
            cast hEq
              (M.observedPrefixValue (Nat.le_of_succ_le hn) c.2.2 iobs) :=
        hcast.comp hmeas
      simpa [SCM.parentValuesFromPrefix, hfix, hobs, iobs] using hmeasCast
    · -- Unobserved case: projection `sℓξ ↦ sℓξ.2.1 ⟨w.val, hunobs⟩`.
      have hunobs : w.val ∈ M.unobserved :=
        parent_unobserved_of_not_fixed_not_observed (M := M) hn w hfix hobs
      let wu : {x // x ∈ M.unobserved} := ⟨w.val, hunobs⟩
      simpa [SCM.parentValuesFromPrefix, hfix, hobs, hunobs, wu] using
        ((measurable_pi_apply (a := wu)) :
            Measurable fun x : M.LatentValues => x wu).comp
          ((measurable_fst : Measurable Prod.fst).comp
            (measurable_snd : Measurable Prod.snd))

end SCM

end Causalean
