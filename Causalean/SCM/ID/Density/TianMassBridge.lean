/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Density.MassBridge
import Causalean.SCM.ID.GraphicalThms.DoGFormulaTian

/-!
# Tian density point-mass bridges

This file connects the Tian prefix-density construction to finite point-mass
ratios.  Its public bridge theorem
`tianPrefixStepDensityInPrefix_eq_mass_ratio` says that, on a measurable
singleton with nonzero finite reference mass, a Tian one-step Radon--Nikodym
density is exactly the conditional singleton mass divided by the corresponding
singleton mass of the product reference.

The result is used by the discrete ID soundness lane to translate the
measure-theoretic density factorization into the point-mass formulas consumed by
finite conditional-mass proofs.
-/

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators
open MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace ID

/-- A Tian prefix-step density is the prefix conditional singleton mass divided
by the corresponding singleton mass of the product reference. -/
theorem tianPrefixStepDensityInPrefix_eq_mass_ratio
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : Measure (ValuesOn D (swigΩ Ω))) (ref : ReferenceMeasures Ω)
    [IsFiniteMeasure μ]
    [∀ (j : ℕ) (hj : j < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨j, hj⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (j : ℕ) (hj : j < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨j, hj⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (k i : ℕ) (hi : i < k) (hcard : i < D.card)
    [MeasurableSingletonClass
      (ValuesOn ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (z : ValuesOn (H.prefixIn D k) (swigΩ Ω))
    (hac :
      (condDistrib
          (valuesProjection
            (show ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D ⟨i, hcard⟩).property))
          (valuesProjection (H.prefixIn_subset D i))
          μ)
          (valuesProjection (prefixIn_mono H D (Nat.le_of_lt hi)) z) ≪
        jointRef ref ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)))
    (href0 :
      jointRef ref ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N))
        ({valuesProjection
          (show ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)) ⊆
              H.prefixIn D k from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            subst hv
            rw [nodesAt_mem_prefixIn_iff H D k ⟨i, hcard⟩]
            exact hi) z} :
          Set (ValuesOn ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N))
            (swigΩ Ω))) ≠ 0)
    (hreftop :
      jointRef ref ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N))
        ({valuesProjection
          (show ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)) ⊆
              H.prefixIn D k from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            subst hv
            rw [nodesAt_mem_prefixIn_iff H D k ⟨i, hcard⟩]
            exact hi) z} :
          Set (ValuesOn ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N))
            (swigΩ Ω))) ≠ ∞) :
    tianPrefixStepDensityInPrefix H D μ ref k z i =
      (condDistrib
          (valuesProjection
            (show ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D ⟨i, hcard⟩).property))
          (valuesProjection (H.prefixIn_subset D i))
          μ)
          (valuesProjection (prefixIn_mono H D (Nat.le_of_lt hi)) z)
          ({valuesProjection
            (show ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)) ⊆
                H.prefixIn D k from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              subst hv
              rw [nodesAt_mem_prefixIn_iff H D k ⟨i, hcard⟩]
              exact hi) z} :
            Set (ValuesOn ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N))
              (swigΩ Ω))) /
        jointRef ref ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)) ⊆
                H.prefixIn D k from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              subst hv
              rw [nodesAt_mem_prefixIn_iff H D k ⟨i, hcard⟩]
              exact hi) z} :
            Set (ValuesOn ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N))
              (swigΩ Ω))) := by
  unfold tianPrefixStepDensityInPrefix
  simp [hi, hcard, rnDeriv_singleton_eq_div _ _ hac _ href0 hreftop]

end ID

end Causalean.SCM
