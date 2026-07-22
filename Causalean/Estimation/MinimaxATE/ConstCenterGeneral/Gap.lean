/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the exact ATE gap (general constant center)

For the general-constant-center construction in `ConstCenterGeneral/Construction.lean`, the average
treatment effect of the perturbed family is **exactly**

  `ate gλ = (g₁ − g₀) + g₁·β(α+β)/(g₁² − β²)`,

**independent of the Rademacher sign vector `λ`**.  The null estimate has
`ate ĝ = g₁ − g₀`, so the gap any estimator must straddle is

  `ate gλ − ate ĝ = g₁·β(α+β)/(g₁² − β²)`,

which collapses to `2β(α+β)/(1 − 4β²)` of `Gap.lean` at `g₁ = 1/2`.  Within a pair
`j` the two positions (`Δ = s` and `Δ = −s`, `s = signOf (λ j) ∈ {±1}`) contribute
`(g₁²+αg₁s)/(g₁−βs)` and `(g₁²−αg₁s)/(g₁+βs)`, which sum to `2g₁(g₁²+αβ)/(g₁²−β²)`
regardless of `s`.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.Construction
import Mathlib.Tactic.LinearCombination

/-! # General-Center ATE Gap

This file computes the exact average-treatment-effect gap for the general constant-center
Rademacher construction.  The calculation shows that every sign vector produces the same ATE
shift from the null center, giving the separation used by the general-center lower bound.

The main public results are `ate_ghatG`, the null-center ATE calculation;
`gPertG_true_eq`, which clears the treated-arm denominator for algebraic use;
`ate_gPertG`, the exact perturbed ATE formula; and `ate_gapG`, the resulting
constant ATE separation between the perturbation and the null. -/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

namespace GenConstr

variable {K : ℕ} (P : GenConstr)

/-- `g₁² − β² > 0` since `0 ≤ β < g₁`. -/
theorem g1sq_sub_betasq_pos : 0 < P.g₁ ^ 2 - P.β ^ 2 := by
  have := P.hβg₁; have := P.hβ; have := P.hg₁0; nlinarith

/-- **Cleared treated arm.**  Multiplying numerator and denominator by `g₁` turns the
inner fraction `β/g₁` into the polynomial denominator `g₁ − β·Δ`:
`gλ(1,x) = (g₁² + α·g₁·Δ)/(g₁ − β·Δ)`. -/
theorem gPertG_true_eq (lam : Fin K → Bool) (x : Fin K × Bool) :
    P.gPertG lam true x = (P.g₁ ^ 2 + P.α * P.g₁ * Δ lam x) / (P.g₁ - P.β * Δ lam x) := by
  have hg₁ne : P.g₁ ≠ 0 := ne_of_gt P.hg₁0
  have hden0 := P.denomG_pos lam x
  have hden : P.g₁ - P.β * Δ lam x ≠ 0 := by
    rcases Δ_mem lam x with h | h <;> rw [h] <;>
      · have := P.hβg₁; have := P.hβ; intro hc; nlinarith
  simp only [gPertG, if_true]
  rw [div_eq_div_iff hden0.ne' hden]
  field_simp

/-- The null estimate `ĝ` has ATE `g₁ − g₀`: every cell contributes `g₁ − g₀`. -/
theorem ate_ghatG [NeZero K] : ate (P.ghatG (K := K)) = P.g₁ - P.g₀ := by
  rw [ate]
  have : ∀ x : Fin K × Bool, P.ghatG true x - P.ghatG false x = P.g₁ - P.g₀ := by
    intro x; simp [ghatG]
  rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hcard : (Fintype.card (Fin K × Bool) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- **Per-pair contribution.**  For a fixed pair index, the two positions
(`Δ = s` and `Δ = −s`) contribute the same total
`2g₁(g₁²+αβ)/(g₁²−β²) − 2g₀` to the ATE numerator, regardless of the sign `s`. -/
private theorem perPairG (lam : Fin K → Bool) (j : Fin K) :
    ((P.gPertG lam true (j, true) - P.gPertG lam false (j, true))
      + (P.gPertG lam true (j, false) - P.gPertG lam false (j, false)))
      = 2 * P.g₁ * (P.g₁ ^ 2 + P.α * P.β) / (P.g₁ ^ 2 - P.β ^ 2) - 2 * P.g₀ := by
  have hg₁0 := P.hg₁0
  have hg₁ne : P.g₁ ≠ 0 := ne_of_gt hg₁0
  have d3 : P.g₁ ^ 2 - P.β ^ 2 ≠ 0 := ne_of_gt P.g1sq_sub_betasq_pos
  have hΔt : Δ lam (j, true) = signOf (lam j) := by simp [Δ]
  have hΔf : Δ lam (j, false) = - signOf (lam j) := by simp [Δ]
  have hfalse : ∀ b, P.gPertG lam false (j, b) = P.g₀ := fun b => by simp [gPertG]
  simp only [P.gPertG_true_eq, hfalse, hΔt, hΔf]
  -- the cleared denominators `g₁ ∓ β` are nonzero in either sign case
  have hβ := P.hβ
  have hβg₁ := P.hβg₁
  have e1 : P.g₁ - P.β ≠ 0 := by intro hc; nlinarith
  have e2 : P.g₁ + P.β ≠ 0 := by intro hc; nlinarith
  -- evaluate at the two concrete signs `signOf (λ j) ∈ {±1}`; each is a rational identity
  rcases signOf_mem (lam j) with h | h <;> rw [h] <;>
    simp only [mul_one, mul_neg, neg_neg, sub_neg_eq_add] <;>
    · field_simp
      ring

/-- **Exact ATE of the perturbed construction.**  Summing the per-pair contributions
(each `2g₁(g₁²+αβ)/(g₁²−β²) − 2g₀`, independent of `λ`) over the `K` pairs and dividing
by `card (Fin K × Bool) = 2K` gives `ate gλ = (g₁ − g₀) + g₁β(α+β)/(g₁²−β²)`. -/
theorem ate_gPertG [NeZero K] (lam : Fin K → Bool) :
    ate (P.gPertG lam) = (P.g₁ - P.g₀) + P.g₁ * P.β * (P.α + P.β) / (P.g₁ ^ 2 - P.β ^ 2) := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have d3 : P.g₁ ^ 2 - P.β ^ 2 ≠ 0 := ne_of_gt P.g1sq_sub_betasq_pos
  rw [ate, Fintype.sum_prod_type]
  have hpair : ∀ j : Fin K,
      (∑ b : Bool, (P.gPertG lam true (j, b) - P.gPertG lam false (j, b)))
        = 2 * P.g₁ * (P.g₁ ^ 2 + P.α * P.β) / (P.g₁ ^ 2 - P.β ^ 2) - 2 * P.g₀ := by
    intro j
    rw [Fintype.sum_bool]
    have := P.perPairG lam j
    linarith [this]
  rw [Finset.sum_congr rfl (fun j _ => hpair j)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  push_cast
  field_simp
  ring

/-- The ATE gap between the construction and the null estimate. -/
theorem ate_gapG [NeZero K] (lam : Fin K → Bool) :
    ate (P.gPertG lam) - ate (P.ghatG (K := K))
      = P.g₁ * P.β * (P.α + P.β) / (P.g₁ ^ 2 - P.β ^ 2) := by
  rw [ate_gPertG, ate_ghatG]; ring

end GenConstr

end Causalean.Estimation.MinimaxATE
