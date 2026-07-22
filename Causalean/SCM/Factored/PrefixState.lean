/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.SCM

/-! # Prefix States for Factored Kernels

This file builds the finite prefix state spaces used to construct a structural
causal model's joint kernel sequentially along a topological ordering. The
definitions package latent values together with already generated observed values,
with measurability facts for the downstream factored-kernel construction.
-/

namespace Causalean

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

omit [DecidableEq N] [Fintype N] in
/-- `cast` along `congrArg (swigΩ Ω) h` is measurable: changing a node index by
    an equality preserves the underlying σ-algebra. -/
theorem measurable_cast_swigΩ {a b : SWIGNode N} (hab : a = b) :
    Measurable (cast (congrArg (swigΩ Ω) hab) : swigΩ Ω a → swigΩ Ω b) := by
  subst hab
  exact measurable_id

-- ============================================================
-- § 1. Observed prefix values
-- ============================================================

/-- Values for the first `n` observed nodes in canonical topological order. -/
def ObservedPrefixValues (M : Causalean.SCM N Ω) :
    (n : ℕ) → n ≤ M.observed.card → Type _ :=
  fun n hn =>
    match n with
    | 0 => PUnit.{uΩ + 1}
    | k + 1 => ObservedPrefixValues M k (Nat.le_of_succ_le hn) ×
        swigΩ Ω (M.observedAt ⟨k, hn⟩).val

/-- Measurable-space structure on `ObservedPrefixValues`, by the same recursion
    as the type itself. -/
noncomputable instance instMeasurableSpaceObservedPrefixValues (M : Causalean.SCM N Ω) :
    ∀ {n : ℕ} (hn : n ≤ M.observed.card), MeasurableSpace (M.ObservedPrefixValues n hn)
  | 0, _ => by
      dsimp [ObservedPrefixValues]
      infer_instance
  | k + 1, hn => by
      dsimp [ObservedPrefixValues]
      letI := instMeasurableSpaceObservedPrefixValues (M := M) (hn := Nat.le_of_succ_le hn)
      infer_instance

/-- Random values consisting of the latent tuple paired with an observed prefix.
    This is the state-space of the kernel at step `n` in the factored construction. -/
abbrev OrderedLatentPrefixValues (M : Causalean.SCM N Ω) (n : ℕ)
    (hn : n ≤ M.observed.card) :=
  LatentValues M × ObservedPrefixValues M n hn

-- ============================================================
-- § 2. Coordinate reader on an observed prefix
-- ============================================================

/-- Read the value of an observed node at position `i < n` from a prefix state
    of length `n`. -/
noncomputable def observedPrefixValue (M : Causalean.SCM N Ω) :
    ∀ {n : ℕ} (hn : n ≤ M.observed.card),
      M.ObservedPrefixValues n hn →
      (i : Fin n) →
        swigΩ Ω (M.observedAt ⟨i.1, Nat.lt_of_lt_of_le i.2 hn⟩).val
  | 0, _, _, i => Fin.elim0 i
  | k + 1, hn, ξ, i =>
      Fin.lastCases
        (by simpa using ξ.2)
        (fun j => by
          simpa using M.observedPrefixValue (Nat.le_of_succ_le hn) ξ.1 j)
        i

/-- `observedPrefixValue` is measurable in its prefix-state argument. -/
theorem measurable_observedPrefixValue (M : Causalean.SCM N Ω) :
    ∀ {n : ℕ} (hn : n ≤ M.observed.card) (i : Fin n),
      Measurable (fun ξ : M.ObservedPrefixValues n hn => M.observedPrefixValue hn ξ i)
  | 0, _, i => Fin.elim0 i
  | k + 1, hn, i =>
      Fin.lastCases
        (by simpa [SCM.observedPrefixValue] using (measurable_snd : Measurable Prod.snd))
        (fun j => by
          simpa [SCM.observedPrefixValue] using
            (M.measurable_observedPrefixValue (Nat.le_of_succ_le hn) j).comp
              (measurable_fst : Measurable Prod.fst))
        i

-- ============================================================
-- § 3. Extending a prefix state by one position
-- ============================================================

/-- Append the next observed value to an ordered-latent prefix state.  This is the
    state-space normalization map used after one `compProd` step in the factored
    construction: `((ℓ, ξ), y) ↦ (ℓ, (ξ, y))`. -/
def extendOrderedLatentPrefix (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    (M.OrderedLatentPrefixValues n (Nat.le_of_succ_le hn) ×
      swigΩ Ω (M.observedAt ⟨n, hn⟩).val) →
      M.OrderedLatentPrefixValues (n + 1) hn
  | ((ℓ, ξ), y) => (ℓ, (ξ, y))

/-- The prefix-extension map is measurable. -/
theorem measurable_extendOrderedLatentPrefix (M : Causalean.SCM N Ω) {n : ℕ}
    (hn : n + 1 ≤ M.observed.card) :
    Measurable (M.extendOrderedLatentPrefix hn) :=
  Measurable.prodMk (measurable_fst.comp measurable_fst)
    (Measurable.prodMk (measurable_snd.comp measurable_fst) measurable_snd)

end SCM

end Causalean
