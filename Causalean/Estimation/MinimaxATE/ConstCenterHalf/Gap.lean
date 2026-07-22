/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the exact ATE gap of the construction

The explicit Case-1 construction of `Construction.lean` perturbs the treated
arm by `gλ(1,·) = (1/2 + α·Δ)/(1 − 2β·Δ)`, leaving the control arm and the null
estimate `ĝ ≡ 1/2` untouched.  The key fact behind the lower bound is that the
**average treatment effect of the construction is exactly**

  `ate gλ = 2β(α+β)/(1 − 4β²)`,

**independent of the Rademacher sign vector `λ`**.  This is the bias that any
estimator faces against the indistinguishable family: within each pair `j` the
two positions contribute `(1/2 + α s)/(1 − 2β s) − 1/2` and
`(1/2 − α s)/(1 + 2β s) − 1/2` with `s = signOf (λ j) ∈ {±1}`, and these two
asymmetric contributions sum to `4β(α+β)/(1 − 4β²)` regardless of `s`.  The null
estimate `ĝ ≡ 1/2` has zero ATE, so the gap equals the same quantity.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Construction
import Mathlib.Tactic.LinearCombination

/-! # Base ATE Gap

This file computes the exact average treatment effect gap for the base paired-cell
perturbation family. The theorem `ate_ghat` records that the centered null estimate has zero
ATE. The private calculation `perPair` collapses the two positions in a paired cell, and
`ate_gPerturbed` sums those contributions to show that every sign-indexed perturbation has the
same ATE `2β(α+β)/(1−4β²)`.

The public theorem `ate_gap` packages the separation between the perturbed construction and the
null estimate; this is the ATE separation used in the finite two-point lower bound.
-/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

variable {K : ℕ} {α β : ℝ}

/-- The null estimate `ĝ ≡ 1/2` has zero ATE: every cell contributes
`1/2 − 1/2 = 0`. -/
theorem ate_ghat : ate (ghat : Bool → (Fin K × Bool) → ℝ) = 0 := by
  simp [ate, ghat]

/-- **Per-pair contribution.**  For a fixed pair index, the two positions
(`Δ = s` and `Δ = −s` with `s = signOf (λ j) ∈ {±1}`) contribute the same total
`4β(α+β)/(1 − 4β²)` to the ATE numerator, regardless of the sign `s`. -/
private theorem perPair (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (lam : Fin K → Bool) (j : Fin K) :
    ((gPerturbed α β lam true (j, true) - gPerturbed α β lam false (j, true))
      + (gPerturbed α β lam true (j, false) - gPerturbed α β lam false (j, false)))
      = 4 * β * (α + β) / (1 - 4 * β ^ 2) := by
  have hβ4 : β ≤ 1 / 4 := by linarith
  have h1 : (1 : ℝ) - 2 * β > 0 := by linarith
  have h2 : (1 : ℝ) + 2 * β > 0 := by linarith
  have h3 : (1 : ℝ) - 4 * β ^ 2 > 0 := by nlinarith
  -- Δ at the two positions of pair j: `signOf true * s = s`, `signOf false * s = -s`.
  have hΔt : Δ lam (j, true) = signOf (lam j) := by
    simp [Δ]
  have hΔf : Δ lam (j, false) = - signOf (lam j) := by
    simp [Δ]
  -- Work with the abstract sign `s = signOf (λ j) ∈ {±1}`, using `s² = 1`.
  set s := signOf (lam j) with hsdef
  have hs2 : s ^ 2 = 1 := signOf_sq (lam j)
  have hsle : s ≤ 1 := by
    rcases signOf_mem (lam j) with h | h <;> rw [← hsdef] at h <;> rw [h]; norm_num
  have hsge : -1 ≤ s := by
    rcases signOf_mem (lam j) with h | h <;> rw [← hsdef] at h <;> rw [h]; norm_num
  simp only [gPerturbed, Bool.false_eq_true, if_false, if_true, hΔt, hΔf]
  -- The two denominators `1 − 2sβ` and `1 + 2sβ` multiply to `1 − 4β²s² = 1 − 4β²`.
  have d1 : (1 : ℝ) - 2 * s * β ≠ 0 := by nlinarith
  have d2 : (1 : ℝ) - -(2 * s * β) ≠ 0 := by nlinarith
  have d3 : (1 : ℝ) - β ^ 2 * 4 ≠ 0 := by nlinarith
  field_simp
  linear_combination (8 * α * β + 8 * β ^ 2) * hs2

/-- **Exact ATE of the perturbed construction.**  Summing the per-pair
contributions (`perPair`, each `4β(α+β)/(1−4β²)`, independent of the signs `λ`)
over the `K` pairs and dividing by `card (Fin K × Bool) = 2K` gives
`ate gλ = 2β(α+β)/(1−4β²)`, independent of `λ`. -/
theorem ate_gPerturbed [NeZero K] (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (lam : Fin K → Bool) :
    ate (gPerturbed α β lam) = 2 * β * (α + β) / (1 - 4 * β ^ 2) := by
  have hβ4 : β ≤ 1 / 4 := by linarith
  have h3 : (1 : ℝ) - 4 * β ^ 2 > 0 := by nlinarith
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  rw [ate]
  -- Split the sum over `Fin K × Bool` into pairs, collapse each pair via `perPair`.
  rw [Fintype.sum_prod_type]
  have hpair : ∀ j : Fin K,
      (∑ b : Bool, (gPerturbed α β lam true (j, b) - gPerturbed α β lam false (j, b)))
        = 4 * β * (α + β) / (1 - 4 * β ^ 2) := by
    intro j
    rw [Fintype.sum_bool]
    have := perPair hα hβ hαβ lam j
    linarith [this]
  rw [Finset.sum_congr rfl (fun j _ => hpair j)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  push_cast
  field_simp
  ring

/-- The ATE gap between the construction and the null estimate `ĝ ≡ 1/2`. -/
theorem ate_gap [NeZero K] (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (lam : Fin K → Bool) :
    ate (gPerturbed α β lam) - ate (ghat : Bool → (Fin K × Bool) → ℝ)
      = 2 * β * (α + β) / (1 - 4 * β ^ 2) := by
  rw [ate_ghat, sub_zero]
  exact ate_gPerturbed hα hβ hαβ lam

end Causalean.Estimation.MinimaxATE
