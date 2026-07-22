/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Final factorization theorem for `jointKernel`

Combines the prefix-kernel correspondence with the pointwise form of
`jointKernel` from `Causalean.SCM.Model.Kernel` to exhibit `jointKernel` as the
pushforward of the sequential prefix kernel at full length through a reindexing
map that identifies the full prefix state with `RandomValues M`.

## Main declarations

* `SCM.orderedLatentPrefixFullToRandom` — reindex the length-`observed.card`
  prefix state `(LatentValues × ObservedPrefixValues)` to `RandomValues M`.
* `SCM.measurable_orderedLatentPrefixFullToRandom` — the reindex is measurable.
* `SCM.partialEvalMap_full_eq` — `orderedLatentPrefixFullToRandom ∘ partialEvalMap
  observed.card _ s = evalMap s`, the deterministic bridge.
* `SCM.jointKernel_factored` — pointwise form: `M.jointKernel s = (jointKernelPrefix
  observed.card _ s).map orderedLatentPrefixFullToRandom`.
* `SCM.jointKernel_eq_factored_kernel` — kernel-level restatement.
-/

import Causalean.SCM.Factored.EvalMapCorrespond
import Causalean.SCM.Model.Kernel

/-! # Factorization of the Joint Kernel

This file assembles the prefix-kernel correspondence into the final
factorization theorem for the joint kernel of a structural causal model. It
identifies the full prefix state with all random coordinates, proves the
reindexing map is measurable, relates the full deterministic prefix map to
`evalMap`, and states both pointwise and kernel-level factorization theorems. -/

namespace Causalean

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Full-prefix to `RandomValues` reindex
-- ============================================================

/-- Reindex the full prefix state (all observed nodes generated, plus the latent
    tuple) to `RandomValues M = ValuesOn (observed ∪ unobserved) (swigΩ Ω)`.

    * If `v.val ∈ M.observed`, read from the observed prefix via
      `observedPrefixValue` at `observedIndex v`, then `cast` through the index
      identity `(observedAt (observedIndex v)).val = v.val`.
    * If `v.val ∈ M.unobserved`, read from the `LatentValues` component. -/
noncomputable def orderedLatentPrefixFullToRandom (M : Causalean.SCM N Ω) :
    M.OrderedLatentPrefixValues M.observed.card (le_refl _) → M.RandomValues :=
  fun p v =>
    by
      by_cases hobs : v.val ∈ M.observed
      · have hEq : swigΩ Ω (M.observedAt (M.observedIndex ⟨v.val, hobs⟩)).val =
            swigΩ Ω v.val := by
          simpa using congrArg (swigΩ Ω) (M.observedAt_observedIndex ⟨v.val, hobs⟩)
        exact cast hEq (M.observedPrefixValue (le_refl _) p.2
          (M.observedIndex ⟨v.val, hobs⟩))
      · have hunobs : v.val ∈ M.unobserved := by
          rcases Finset.mem_union.mp v.property with hobs' | hunobs
          · exact False.elim (hobs hobs')
          · exact hunobs
        exact p.1 ⟨v.val, hunobs⟩

-- ============================================================
-- § 2. Measurability of the reindex
-- ============================================================

/-- `orderedLatentPrefixFullToRandom` is measurable.  Case-split mirrors the
    definition; the observed branch composes `observedPrefixValue` with a
    `cast`. -/
theorem measurable_orderedLatentPrefixFullToRandom (M : Causalean.SCM N Ω) :
    Measurable M.orderedLatentPrefixFullToRandom := by
  classical
  refine measurable_pi_lambda _ ?_
  intro ⟨n, hn⟩
  simp only [orderedLatentPrefixFullToRandom]
  by_cases hobs : n ∈ M.observed
  · simp [hobs]
    have hNode : (M.observedAt (M.observedIndex ⟨n, hobs⟩)).val = n :=
      M.observedAt_observedIndex ⟨n, hobs⟩
    have hmeas :
        Measurable fun p : M.OrderedLatentPrefixValues M.observed.card (le_refl _) =>
          M.observedPrefixValue (le_refl _) p.2 (M.observedIndex ⟨n, hobs⟩) :=
      (M.measurable_observedPrefixValue (le_refl _) (M.observedIndex ⟨n, hobs⟩)).comp
        (measurable_snd : Measurable Prod.snd)
    exact (measurable_cast_swigΩ hNode).comp hmeas
  · have hunobs : n ∈ M.unobserved := by
      rcases Finset.mem_union.mp hn with hobs' | hunobs
      · exact False.elim (hobs hobs')
      · exact hunobs
    simp [hobs]
    exact ((measurable_pi_apply (⟨n, hunobs⟩ : {x // x ∈ M.unobserved})).comp
      (measurable_fst : Measurable Prod.fst))

-- ============================================================
-- § 3. Bridge: reindex ∘ partialEvalMap full = evalMap
-- ============================================================

/-- Bridge lemma: reindexing the deterministic full-prefix value built from
    `partialEvalMap` at length `observed.card` yields exactly `evalMap s ℓ`.

    * On observed coordinates: `partialEvalMap_observedPrefixValue` reduces the
      observed-prefix reader to `evalObservedAux`, matching `evalMap`'s observed
      branch up to the `observedAt_observedIndex` cast.
    * On unobserved coordinates: `partialEvalMap_latent` makes `.1 = ℓ`, matching
      `evalMap`'s unobserved branch. -/
theorem partialEvalMap_full_eq (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M) :
    M.orderedLatentPrefixFullToRandom
        (M.partialEvalMap M.observed.card (le_refl _) s ℓ) =
      M.evalMap s ℓ := by
  funext v
  unfold orderedLatentPrefixFullToRandom
  by_cases hobs : v.val ∈ M.observed
  · -- Observed branch: both sides are (cast) of `evalObservedAux` at
    -- `observedIndex v`.
    simp only [hobs, dif_pos]
    -- LHS: cast hEq (observedPrefixValue ((partialEvalMap ...).2) (observedIndex v))
    rw [M.partialEvalMap_observedPrefixValue s ℓ M.observed.card (le_refl _)
        (M.observedIndex ⟨v.val, hobs⟩)]
    -- RHS: evalMap_observed form
    rw [M.evalMap_observed s ℓ v hobs]
    -- Both sides transport the same `evalObservedAux` along the identity
    -- `(M.observedAt (observedIndex v)).val = v.val`.  LHS uses `cast
    -- (congrArg (swigΩ Ω) h)`, RHS uses `h ▸ _`; they agree by the generic
    -- identity `cast (congrArg f h) x = h ▸ x` (both `Eq.mpr`/`Eq.mp` when
    -- `h` is used as a motive transport). -/
    have hNode : (M.observedAt (M.observedIndex ⟨v.val, hobs⟩)).val = v.val :=
      M.observedAt_observedIndex ⟨v.val, hobs⟩
    -- Abstract the transported value as `aux` with the exact shape expected
    -- on the RHS: the `▸` motive transports along `hNode : (observedAt idx).val = v.val`,
    -- so `aux` must have type `swigΩ Ω (observedAt (observedIndex v)).val`.
    let aux0 : swigΩ Ω (M.observedAt (M.observedIndex ⟨v.val, hobs⟩)).val :=
      M.evalObservedAux s ℓ (M.observedIndex ⟨v.val, hobs⟩).val
        (Nat.lt_of_lt_of_le (M.observedIndex ⟨v.val, hobs⟩).isLt (le_refl _))
    -- Goal: cast hEq aux0 = hNode ▸ aux0; both transports use the same node
    -- equality, so they're equal via `eqRec_eq_cast`.
    change cast _ aux0 = hNode ▸ aux0
    exact (eqRec_eq_cast (motive := fun x _ => swigΩ Ω x) aux0 hNode).symm
  · -- Unobserved branch: LHS reads `p.1 ⟨v.val, huo⟩ = ℓ ⟨v.val, huo⟩` by
    -- `partialEvalMap_latent`; RHS is `ℓ ⟨v.val, huo⟩` by `evalMap_unobserved`.
    simp only [hobs, dif_neg, not_false_eq_true]
    have hunobs : v.val ∈ M.unobserved := by
      rcases Finset.mem_union.mp v.property with hobs' | hunobs
      · exact False.elim (hobs hobs')
      · exact hunobs
    rw [M.evalMap_unobserved s ℓ v hunobs]
    -- LHS: `(partialEvalMap M.observed.card _ s ℓ).1 ⟨v.val, hunobs⟩`
    -- By `partialEvalMap_latent`, `.1 = ℓ`.
    have := M.partialEvalMap_latent s ℓ M.observed.card (le_refl _)
    rw [this]

-- ============================================================
-- § 4. Main factorization theorem (pointwise)
-- ============================================================

/-- **Main factorization theorem (pointwise).**  At each fixed assignment `s`,
    the joint kernel equals the pushforward of the full-length prefix kernel
    through the reindex `orderedLatentPrefixFullToRandom`.

    Proof chain:
    1. `jointKernel s = latentProduct.map (evalMap s)` by `jointKernel_apply_eq`.
    2. `evalMap s = orderedLatentPrefixFullToRandom ∘ partialEvalMap _ _ s`
       by `partialEvalMap_full_eq`.
    3. `Measure.map_map` (or equivalent) commutes the outer `.map` with the
       composition.
    4. `latentProduct.map (partialEvalMap _ _ s) = jointKernelPrefix _ _ s`
       by `jointKernelPrefix_apply_eq`. -/
theorem jointKernel_factored (M : Causalean.SCM N Ω) (s : FixedValues M) :
    M.jointKernel s =
      ((M.jointKernelPrefix M.observed.card (le_refl _)) s).map
        M.orderedLatentPrefixFullToRandom := by
  -- Step 1: unfold `jointKernel` at `s`.
  rw [M.jointKernel_apply_eq s]
  -- Step 2: rewrite `evalMap s` as `orderedLatentPrefixFullToRandom ∘ partialEvalMap _ _ s`.
  have hfun :
      (fun ℓ => M.evalMap s ℓ) =
        M.orderedLatentPrefixFullToRandom ∘
          (fun ℓ => M.partialEvalMap M.observed.card (le_refl _) s ℓ) := by
    funext ℓ
    exact (M.partialEvalMap_full_eq s ℓ).symm
  rw [hfun]
  -- Step 3: use `Measure.map_map` to commute `.map` with composition.
  have hmeas_reindex := M.measurable_orderedLatentPrefixFullToRandom
  have hmeas_partial :
      Measurable (fun ℓ : LatentValues M =>
        M.partialEvalMap M.observed.card (le_refl _) s ℓ) := by
    have := M.measurable_partialEvalMap M.observed.card (le_refl _)
    exact this.comp (Measurable.prodMk measurable_const measurable_id)
  rw [← MeasureTheory.Measure.map_map hmeas_reindex hmeas_partial]
  -- Step 4: rewrite the inner `.map` using `jointKernelPrefix_apply_eq`.
  rw [← M.jointKernelPrefix_apply_eq s M.observed.card (le_refl _)]

-- ============================================================
-- § 5. Kernel-level restatement
-- ============================================================

/-- **Kernel-level factorization.**  The joint kernel equals the prefix kernel at
    full length, pushed through `orderedLatentPrefixFullToRandom`.  Follows from
    the pointwise form via kernel extensionality. -/
theorem jointKernel_eq_factored_kernel (M : Causalean.SCM N Ω) :
    M.jointKernel =
      (M.jointKernelPrefix M.observed.card (le_refl _)).map
        M.orderedLatentPrefixFullToRandom := by
  refine ProbabilityTheory.Kernel.ext fun s => ?_
  rw [ProbabilityTheory.Kernel.map_apply _ M.measurable_orderedLatentPrefixFullToRandom]
  exact M.jointKernel_factored s

end SCM

end Causalean
