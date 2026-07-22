/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: class membership (cell-varying center)

The cell-varying-center analogue of `ConstCenterGeneral/Membership.lean`. Because the bump
magnitude now varies with the pair index, the squared `L²` errors are *averages* of
per-pair quantities rather than a single exact value, so we control them by the
per-pair (sup-type) budgets

* `(m₀ⱼ·(β/g₁ⱼ))² ≤ εm` for the propensity, and
* `g₁ⱼ²(α+β)²/(g₁ⱼ − β)² ≤ εg` for the treated arm,

each holding for every pair `j`.  An average of terms each `≤ ε` is `≤ ε`, so the
construction lands in `ℱ(εg, εm)`.  (These per-pair bounds are *sufficient*: they
imply the paper's `L²`-average budgets, giving a valid — if slightly conservative —
in-class perturbation, which is all a lower bound needs.)  The capstone `inClassV`
collapses to `ConstCenterGeneral.inClassG` when the center is constant.
-/

import Causalean.Estimation.MinimaxATE.Reduction.Bump
import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.Gap

/-! # Cell-Varying Class Membership

This file proves that the cell-varying perturbation family for the structure-agnostic
average treatment effect lower bound belongs to the finite nuisance class whenever
the per-cell propensity and outcome-regression error budgets hold.  It supplies the
membership estimates used to assemble the first cell-varying minimax lower bound.

The lemmas `l2sq_mPertV_le`, `l2sq_gPertV_false`, `gPertV_true_sub`, and
`l2sq_gPertV_true_le` bound the propensity and outcome-arm `L²(P_X)` errors.  The capstone
`inClassV` combines those estimates with `validDGP_pertV` to show every perturbed sign vector lies
in `InClass` around the cell-varying center. -/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

namespace VarConstr

variable {K : ℕ} (P : VarConstr K)

/-- The propensity perturbation's squared `L²` error is `≤ εm` whenever every pair's
bump magnitude `(m₀ⱼ·(β/g₁ⱼ))²` is `≤ εm`. -/
theorem l2sq_mPertV_le [NeZero K] {εm : ℝ}
    (hm : ∀ j, (P.m₀ j * (P.β / P.g₁ j)) ^ 2 ≤ εm) (lam : Fin K → Bool) :
    l2sq (P.mPertV lam) (P.mhatV (K := K)) ≤ εm := by
  set C := Fin K × Bool
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm : ∀ x : C, (P.mPertV lam x - P.mhatV x) ^ 2 ≤ εm := by
    intro x
    have hdiff : P.mPertV lam x - P.mhatV x = -(P.m₀ x.1 * (P.β / P.g₁ x.1)) * Δ lam x := by
      simp only [mPertV, mhatV]; ring
    rw [hdiff, mul_pow, neg_sq, Δ_sq lam x, mul_one]
    exact hm x.1
  rw [l2sq]
  have hsum : ∑ x : C, (P.mPertV lam x - P.mhatV x) ^ 2 ≤ ∑ _x : C, εm :=
    Finset.sum_le_sum (fun x _ => hterm x)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc (Fintype.card C : ℝ)⁻¹ * ∑ x : C, (P.mPertV lam x - P.mhatV x) ^ 2
      ≤ (Fintype.card C : ℝ)⁻¹ * ((Fintype.card C : ℝ) * εm) := by
        apply mul_le_mul_of_nonneg_left hsum; positivity
    _ = εm := by field_simp

/-- The control outcome arm is unchanged, so its `L²` error is `0`. -/
theorem l2sq_gPertV_false (lam : Fin K → Bool) :
    l2sq (P.gPertV lam false) (P.ghatV false) = 0 := by
  have h : P.gPertV lam false = P.ghatV false := by
    funext x; simp only [gPertV, ghatV, Bool.false_eq_true, if_false]
  rw [h, l2sq_self]

/-- The treated arm's pointwise deviation from `ĝ(1,x) = g₁ x.1` is
`g₁ x.1·(α+β)·Δ/(g₁ x.1 − β·Δ)`. -/
theorem gPertV_true_sub (lam : Fin K → Bool) (x : Fin K × Bool) :
    P.gPertV lam true x - P.g₁ x.1
      = P.g₁ x.1 * (P.α + P.β) * Δ lam x / (P.g₁ x.1 - P.β * Δ lam x) := by
  have hden : P.g₁ x.1 - P.β * Δ lam x ≠ 0 := by
    rcases Δ_mem lam x with h | h <;> rw [h] <;>
      · have := P.hβg₁ x.1; have := P.hβ; intro hc; nlinarith
  rw [gPertV_true_eq, eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
  ring

/-- The treated arm's squared `L²` error is `≤ εg` whenever every pair's bound
`g₁ⱼ²(α+β)²/(g₁ⱼ − β)²` is `≤ εg`. -/
theorem l2sq_gPertV_true_le [NeZero K] {εg : ℝ}
    (hg : ∀ j, P.g₁ j ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ j - P.β) ^ 2 ≤ εg) (lam : Fin K → Bool) :
    l2sq (P.gPertV lam true) (P.ghatV true) ≤ εg := by
  set C := Fin K × Bool
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm : ∀ x : C, (P.gPertV lam true x - P.ghatV true x) ^ 2 ≤ εg := by
    intro x
    have hghat : P.ghatV true x = P.g₁ x.1 := by simp [ghatV]
    have hden : (0 : ℝ) < P.g₁ x.1 - P.β := by have := P.hβg₁ x.1; linarith
    have hden2 : (0 : ℝ) < (P.g₁ x.1 - P.β) ^ 2 := by positivity
    have hdenΔ : (0 : ℝ) < (P.g₁ x.1 - P.β * Δ lam x) ^ 2 := by
      have hdne : P.g₁ x.1 - P.β * Δ lam x ≠ 0 := by
        rcases Δ_mem lam x with h | h <;> rw [h] <;>
          · have := P.hβg₁ x.1; have := P.hβ; intro hc; nlinarith
      positivity
    rw [hghat, P.gPertV_true_sub lam x]
    have hsq : (P.g₁ x.1 * (P.α + P.β) * Δ lam x / (P.g₁ x.1 - P.β * Δ lam x)) ^ 2
        = P.g₁ x.1 ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ x.1 - P.β * Δ lam x) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Δ_sq, mul_one]
    rw [hsq]
    have hcmp : (P.g₁ x.1 - P.β) ^ 2 ≤ (P.g₁ x.1 - P.β * Δ lam x) ^ 2 := by
      have hβ := P.hβ
      have hβg₁ := P.hβg₁ x.1
      have hg₁0 := P.hg₁0 x.1
      rcases Δ_mem lam x with h | h
      · rw [h]; nlinarith
      · rw [h]; nlinarith
    refine le_trans ?_ (hg x.1)
    apply div_le_div_of_nonneg_left (by positivity) hden2 hcmp
  rw [l2sq]
  have hsum : ∑ x : C, (P.gPertV lam true x - P.ghatV true x) ^ 2 ≤ ∑ _x : C, εg :=
    Finset.sum_le_sum (fun x _ => hterm x)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc (Fintype.card C : ℝ)⁻¹ * ∑ x : C, (P.gPertV lam true x - P.ghatV true x) ^ 2
      ≤ (Fintype.card C : ℝ)⁻¹ * ((Fintype.card C : ℝ) * εg) := by
        apply mul_le_mul_of_nonneg_left hsum; positivity
    _ = εg := by field_simp

/-- **Class membership.**  With the per-pair budgets satisfied, the perturbed DGP
`(mλ, gλ)` lies in the structure-agnostic class `ℱ(εg, εm)` around the cell-varying
center `(m̂, ĝ)`. -/
theorem inClassV [NeZero K] {εg εm : ℝ}
    (hm : ∀ j, (P.m₀ j * (P.β / P.g₁ j)) ^ 2 ≤ εm)
    (hg : ∀ j, P.g₁ j ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ j - P.β) ^ 2 ≤ εg)
    (hεg : 0 ≤ εg) (lam : Fin K → Bool) :
    InClass (P.mhatV (K := K)) P.ghatV εg εm (P.mPertV lam) (P.gPertV lam) := by
  refine ⟨P.validDGP_pertV lam, ?_, ?_⟩
  · intro d
    cases d with
    | false => rw [P.l2sq_gPertV_false lam]; exact hεg
    | true => exact P.l2sq_gPertV_true_le hg lam
  · exact P.l2sq_mPertV_le hm lam

end VarConstr

end Causalean.Estimation.MinimaxATE
