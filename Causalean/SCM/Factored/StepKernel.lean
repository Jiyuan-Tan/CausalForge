/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Deterministic step kernel

For the factored construction of `jointKernel`, at step `n` the value of the
next observed node `v_n = M.observedAt ⟨n, hn⟩` is produced **deterministically**
from its parent tuple by the structural function `M.structFun v_n`.  We package
this as a `Kernel.deterministic` kernel whose source is the prefix state
`FixedValues M × OrderedLatentPrefixValues M n _` and whose target is
`swigΩ Ω v_n.val`.

## Main definitions

* `SCM.stepFun hn` — the deterministic assignment
  `structFun v_n ∘ parentValuesFromPrefix hn`.
* `SCM.measurable_stepFun hn` — its measurability.
* `SCM.stepKernel hn` — `Kernel.deterministic (stepFun hn) _`.
* `SCM.isMarkov_stepKernel hn` — the `IsMarkovKernel` instance.
-/

import Causalean.SCM.Factored.ParentLookup
import Mathlib.Probability.Kernel.Basic

/-! # Step Kernels for Observed Nodes

This file constructs the deterministic kernel that generates the next observed
coordinate from its fixed, latent, and previously generated observed parents.
The step kernels are the local transition pieces in the sequential
factorization of the joint kernel, and their measurability follows from the
parent-lookup map and the SCM structural-function measurability field. -/

namespace Causalean

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. The deterministic step function and its measurability
-- ============================================================

/-- The deterministic assignment producing the value of the `n`-th observed node
    `v_n = M.observedAt ⟨n, hn⟩` from the current prefix state `(s, ℓ, ξ)`:
    assemble the parent tuple via `parentValuesFromPrefix`, then apply the
    structural function `M.structFun v_n`. -/
noncomputable def stepFun (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    (M.FixedValues × M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn)) →
      swigΩ Ω (M.observedAt ⟨n, hn⟩).val :=
  fun sℓξ => M.structFun (M.observedAt ⟨n, hn⟩) (M.parentValuesFromPrefix hn sℓξ)

/-- `stepFun` is measurable. -/
theorem measurable_stepFun (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    Measurable (M.stepFun hn) :=
  (M.structFun_measurable (M.observedAt ⟨n, hn⟩)).comp
    (M.measurable_parentValuesFromPrefix hn)

-- ============================================================
-- § 2. The step kernel
-- ============================================================

/-- The step kernel for the `n`-th observed node.  Since `structFun v_n` is a
    deterministic measurable map, the kernel is `Kernel.deterministic (stepFun hn)`:
    on input `(s, ℓ, ξ)` it returns `Dirac (structFun v_n (Pa(v_n)))`. -/
noncomputable def stepKernel (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    ProbabilityTheory.Kernel
      (M.FixedValues × M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn))
      (swigΩ Ω (M.observedAt ⟨n, hn⟩).val) :=
  ProbabilityTheory.Kernel.deterministic (M.stepFun hn) (M.measurable_stepFun hn)

/-- The step kernel is Markov (inherits from `Kernel.deterministic`). -/
instance isMarkov_stepKernel (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    ProbabilityTheory.IsMarkovKernel (M.stepKernel hn) := by
  unfold stepKernel; infer_instance

end SCM

end Causalean
