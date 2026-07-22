/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Stratified randomization

**Stratified randomization** partitions the population into strata `k : K` and independently runs a
complete randomization within each stratum, treating exactly `n₁ k` of the `N k` units there.  It is
the product `prodDesign` of the per-stratum complete-randomization designs, so assignments in
different strata are independent.  This file records the design and its **inclusion probabilities**:
a unit in stratum `k` is treated with first-order probability `n₁ k / N k` (its own stratum's rate),
and two units in *distinct* strata are jointly treated with probability the product of their stratum
rates.
-/

import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization
import Causalean.Experimentation.DesignBased.ProductVariance

/-!
# Stratified randomization designs

This file builds `stratifiedDesign`, the product of stratum-level complete-randomization designs.
It proves the first-order inclusion probability `stratifiedDesign_incl`, the within-stratum
second-order inclusion probability `stratifiedDesign_incl_pair_within`, and the across-strata
factorization `stratifiedDesign_incl_pair_across`. These lemmas expose the design facts needed by
estimators whose bias or variance depends on stratified treatment inclusion probabilities.
-/

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {V : K → Type*} [∀ k, Fintype (V k)] [∀ k, DecidableEq (V k)]

/-- The **stratified randomization design**: an independent complete randomization within each
stratum `k`, treating exactly `n₁ k` of that stratum's units. Built as the product of the
per-stratum complete-randomization designs. -/
noncomputable def stratifiedDesign (n₁ : K → ℕ) (hn : ∀ k, n₁ k ≤ Fintype.card (V k)) :
    FiniteDesign (∀ k, {S : Finset (V k) // S.card = n₁ k}) :=
  prodDesign (fun k => completeRandomization (n₁ k) (hn k))

/-- **First-order inclusion probability.** A unit `i` in stratum `k` is treated with probability
`n₁ k / N k`, the complete-randomization rate of its own stratum. -/
lemma stratifiedDesign_incl (n₁ : K → ℕ) (hn : ∀ k, n₁ k ≤ Fintype.card (V k))
    (k : K) (i : V k) :
    (stratifiedDesign n₁ hn).Pr (fun z => i ∈ (z k).val)
      = (n₁ k : ℝ) / (Fintype.card (V k) : ℝ) := by
  unfold FiniteDesign.Pr FiniteDesign.ind
  simp only [stratifiedDesign]
  change (prodDesign (fun k => completeRandomization (n₁ k) (hn k))).E
      (fun z => (fun S => if i ∈ S.val then (1 : ℝ) else 0) (z k))
    = (n₁ k : ℝ) / (Fintype.card (V k) : ℝ)
  rw [FiniteDesign.E_prod_apply
    (fun k => completeRandomization (n₁ k) (hn k)) k
    (fun S => if i ∈ S.val then (1 : ℝ) else 0)]
  change (completeRandomization (n₁ k) (hn k)).Pr (fun S => i ∈ S.val)
    = (n₁ k : ℝ) / (Fintype.card (V k) : ℝ)
  exact completeRandomization_incl (n₁ k) (hn k) i

/-- **Second-order inclusion probability within one stratum.** Two distinct units in the same
stratum `k` are jointly treated with the complete-randomization second-order inclusion
probability for that stratum. -/
lemma stratifiedDesign_incl_pair_within (n₁ : K → ℕ) (hn : ∀ k, n₁ k ≤ Fintype.card (V k))
    (k : K) {i j : V k} (hij : i ≠ j) :
    (stratifiedDesign n₁ hn).Pr (fun z => i ∈ (z k).val ∧ j ∈ (z k).val)
      = ((n₁ k : ℝ) * ((n₁ k : ℝ) - 1)) /
        ((Fintype.card (V k) : ℝ) * ((Fintype.card (V k) : ℝ) - 1)) := by
  unfold FiniteDesign.Pr FiniteDesign.ind
  simp only [stratifiedDesign]
  change (prodDesign (fun k => completeRandomization (n₁ k) (hn k))).E
      (fun z => (fun S => if i ∈ S.val ∧ j ∈ S.val then (1 : ℝ) else 0) (z k))
    = ((n₁ k : ℝ) * ((n₁ k : ℝ) - 1)) /
        ((Fintype.card (V k) : ℝ) * ((Fintype.card (V k) : ℝ) - 1))
  rw [FiniteDesign.E_prod_apply
    (fun k => completeRandomization (n₁ k) (hn k)) k
    (fun S => if i ∈ S.val ∧ j ∈ S.val then (1 : ℝ) else 0)]
  change (completeRandomization (n₁ k) (hn k)).Pr (fun S => i ∈ S.val ∧ j ∈ S.val)
    = ((n₁ k : ℝ) * ((n₁ k : ℝ) - 1)) /
        ((Fintype.card (V k) : ℝ) * ((Fintype.card (V k) : ℝ) - 1))
  exact completeRandomization_incl_pair (n₁ k) (hn k) hij

/-- **Second-order inclusion probability across strata.** Two units in distinct strata `k ≠ k'` are
jointly treated with probability the product of their stratum treatment rates — the strata are
randomized independently. -/
lemma stratifiedDesign_incl_pair_across (n₁ : K → ℕ) (hn : ∀ k, n₁ k ≤ Fintype.card (V k))
    {k k' : K} (hk : k ≠ k') (i : V k) (i' : V k') :
    (stratifiedDesign n₁ hn).Pr (fun z => i ∈ (z k).val ∧ i' ∈ (z k').val)
      = ((n₁ k : ℝ) / (Fintype.card (V k) : ℝ)) * ((n₁ k' : ℝ) / (Fintype.card (V k') : ℝ)) := by
  unfold FiniteDesign.Pr FiniteDesign.ind
  simp only [stratifiedDesign]
  have hpoint : (fun z : ∀ k, {S : Finset (V k) // S.card = n₁ k} =>
      if i ∈ (z k).val ∧ i' ∈ (z k').val then (1 : ℝ) else 0)
      =
      (fun z =>
        (fun S => if i ∈ S.val then (1 : ℝ) else 0) (z k) *
        (fun S => if i' ∈ S.val then (1 : ℝ) else 0) (z k')) := by
    funext z
    by_cases hi : i ∈ (z k).val
    · by_cases hi' : i' ∈ (z k').val
      · simp [hi, hi']
      · simp [hi, hi']
    · simp [hi]
  rw [hpoint]
  rw [FiniteDesign.E_prod_apply₂
    (fun k => completeRandomization (n₁ k) (hn k)) hk
    (fun S => if i ∈ S.val then (1 : ℝ) else 0)
    (fun S => if i' ∈ S.val then (1 : ℝ) else 0)]
  rw [show (completeRandomization (n₁ k) (hn k)).E
      (fun S => if i ∈ S.val then (1 : ℝ) else 0)
      = (n₁ k : ℝ) / (Fintype.card (V k) : ℝ) from by
        change (completeRandomization (n₁ k) (hn k)).Pr (fun S => i ∈ S.val)
          = (n₁ k : ℝ) / (Fintype.card (V k) : ℝ)
        exact completeRandomization_incl (n₁ k) (hn k) i]
  rw [show (completeRandomization (n₁ k') (hn k')).E
      (fun S => if i' ∈ S.val then (1 : ℝ) else 0)
      = (n₁ k' : ℝ) / (Fintype.card (V k') : ℝ) from by
        change (completeRandomization (n₁ k') (hn k')).Pr (fun S => i' ∈ S.val)
          = (n₁ k' : ℝ) / (Fintype.card (V k') : ℝ)
        exact completeRandomization_incl (n₁ k') (hn k') i']

end DesignBased
end Experimentation
end Causalean
