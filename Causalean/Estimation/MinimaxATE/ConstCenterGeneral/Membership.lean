/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: class membership (general constant center)

This is the general-constant-center analogue of `Membership.lean`. For the
construction in `ConstCenterGeneral/Construction.lean` — centered at an arbitrary constant nuisance
estimate `(m₀, g₀, g₁) ∈ (0,1)³` — we prove the perturbed DGP `(mλ, gλ)` lands inside
the structure-agnostic nuisance class `ℱ(εg, εm)` of `Model.lean`, once the bump
scalars `α, β` respect the error budgets.  Concretely:

* the propensity perturbation `mλ = m₀·(1 − (β/g₁)·Δ)` has **exact** squared `L²`
  size `(m₀·(β/g₁))²` (a Rademacher bump of magnitude `m₀·(β/g₁)`, via `l2sq_bump`);
* the control arm `gλ(0,·) = g₀ = ĝ(0,·)` is unchanged, so its `L²` error is `0`;
* the treated arm `gλ(1,·)` deviates from `ĝ(1) = g₁` by `g₁(α+β)·Δ/(g₁ − β·Δ)`,
  whose squared `L²` error is bounded uniformly by `g₁²(α+β)²/(g₁ − β)²`.

The capstone `inClassG` packages these into `InClass m̂ ĝ εg εm mλ gλ` whenever
`(m₀·(β/g₁))² ≤ εm` and `g₁²(α+β)²/(g₁ − β)² ≤ εg`.  This collapses to
`inClass_perturbed` of `Membership.lean` at `m₀ = g₁ = 1/2`.
-/

import Causalean.Estimation.MinimaxATE.Reduction.Bump
import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.Gap

/-! # General-Center Membership

This file proves that the general constant-center Rademacher perturbations belong to the
structure-agnostic nuisance class when the propensity and outcome error budgets are large enough.
The supporting estimates are `l2sq_mPertG` for the exact propensity error,
`l2sq_gPertG_false` for the unchanged control arm, `gPertG_true_sub` for the treated-arm
pointwise deviation, and `l2sq_gPertG_true_le` for the uniform treated-arm error bound.

The capstone `inClassG` packages these estimates into the realizability input required by the
general-center minimax lower bound. -/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

namespace GenConstr

variable {K : ℕ} (P : GenConstr)

/-- The propensity perturbation has exact squared `L²` size `(m₀·(β/g₁))²`: it is a
Rademacher bump of magnitude `m₀·(β/g₁)` on `Δ`. -/
theorem l2sq_mPertG [NeZero K] (lam : Fin K → Bool) :
    l2sq (P.mPertG lam) (P.mhatG (K := K)) = (P.m₀ * (P.β / P.g₁)) ^ 2 := by
  have hbump : (P.mPertG lam)
      = (fun x => P.mhatG x + (-(P.m₀ * (P.β / P.g₁))) * Δ lam x) := by
    funext x
    simp only [mPertG, mhatG]
    ring
  rw [hbump]
  have hb := l2sq_bump (P.mhatG (K := K)) (-(P.m₀ * (P.β / P.g₁))) (fun x => Δ lam x)
    (fun x => Δ_sq lam x)
  rw [hb]
  ring

/-- The control outcome arm is unchanged (`gλ(0,·) = g₀ = ĝ(0,·)`), so its `L²`
error is `0`. -/
theorem l2sq_gPertG_false (lam : Fin K → Bool) :
    l2sq (P.gPertG lam false) (P.ghatG false) = 0 := by
  have h : P.gPertG lam false = P.ghatG false := by
    funext x
    simp only [gPertG, ghatG, Bool.false_eq_true, if_false]
  rw [h, l2sq_self]

/-- The treated outcome arm: its pointwise deviation from `ĝ(1) = g₁` is
`g₁(α+β)·Δ/(g₁ − β·Δ)`. -/
theorem gPertG_true_sub (lam : Fin K → Bool) (x : Fin K × Bool) :
    P.gPertG lam true x - P.g₁ = P.g₁ * (P.α + P.β) * Δ lam x / (P.g₁ - P.β * Δ lam x) := by
  have hden : P.g₁ - P.β * Δ lam x ≠ 0 := by
    rcases Δ_mem lam x with h | h <;> rw [h] <;>
      · have := P.hβg₁; have := P.hβ; intro hc; nlinarith
  rw [gPertG_true_eq, eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
  ring

/-- Uniform bound on the treated arm's squared `L²` error: every pointwise term is
`≤ g₁²(α+β)²/(g₁ − β)²`, so the average is too. -/
theorem l2sq_gPertG_true_le [NeZero K] (lam : Fin K → Bool) :
    l2sq (P.gPertG lam true) (P.ghatG true) ≤ P.g₁ ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ - P.β) ^ 2 := by
  set C := Fin K × Bool
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- denominator `g₁ − β` is positive
  have hden : (0 : ℝ) < P.g₁ - P.β := by have := P.hβg₁; linarith
  have hden2 : (0 : ℝ) < (P.g₁ - P.β) ^ 2 := by positivity
  -- each summand is `g₁²(α+β)²/(g₁ − β·Δ)²` and is bounded by `g₁²(α+β)²/(g₁ − β)²`
  have hterm : ∀ x : C,
      (P.gPertG lam true x - P.ghatG true x) ^ 2
        ≤ P.g₁ ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ - P.β) ^ 2 := by
    intro x
    have hghat : P.ghatG true x = P.g₁ := by simp [ghatG]
    rw [hghat, P.gPertG_true_sub lam x]
    -- the cleared denominator `g₁ − β·Δ` is nonzero (in fact positive squared)
    have hdne : P.g₁ - P.β * Δ lam x ≠ 0 := by
      rcases Δ_mem lam x with h | h <;> rw [h] <;>
        · have := P.hβg₁; have := P.hβ; intro hc; nlinarith
    have hdenΔ : (0 : ℝ) < (P.g₁ - P.β * Δ lam x) ^ 2 := by positivity
    -- rewrite the squared term using `Δ² = 1`
    have hsq : (P.g₁ * (P.α + P.β) * Δ lam x / (P.g₁ - P.β * Δ lam x)) ^ 2
        = P.g₁ ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ - P.β * Δ lam x) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Δ_sq, mul_one]
    rw [hsq]
    -- compare denominators: `(g₁ − β)² ≤ (g₁ − β·Δ)²`
    have hcmp : (P.g₁ - P.β) ^ 2 ≤ (P.g₁ - P.β * Δ lam x) ^ 2 := by
      have hβ := P.hβ
      have hβg₁ := P.hβg₁
      have hg₁0 := P.hg₁0
      rcases Δ_mem lam x with h | h
      · rw [h]; nlinarith
      · rw [h]; nlinarith
    apply div_le_div_of_nonneg_left (by positivity) hden2 hcmp
  -- average of bounded terms is bounded
  rw [l2sq]
  have hsum : ∑ x : C, (P.gPertG lam true x - P.ghatG true x) ^ 2
      ≤ ∑ _x : C, P.g₁ ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ - P.β) ^ 2 :=
    Finset.sum_le_sum (fun x _ => hterm x)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc (Fintype.card C : ℝ)⁻¹ * ∑ x : C, (P.gPertG lam true x - P.ghatG true x) ^ 2
      ≤ (Fintype.card C : ℝ)⁻¹
          * ((Fintype.card C : ℝ) * (P.g₁ ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ - P.β) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hsum
        positivity
    _ = P.g₁ ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ - P.β) ^ 2 := by
        field_simp

/-- **Class membership.**  With the budgets `(m₀·(β/g₁))² ≤ εm` and
`g₁²(α+β)²/(g₁ − β)² ≤ εg` satisfied, the perturbed DGP `(mλ, gλ)` lies in the
structure-agnostic class `ℱ(εg, εm)` around the constant center `(m̂, ĝ)`. -/
theorem inClassG [NeZero K] {εg εm : ℝ}
    (hm : (P.m₀ * (P.β / P.g₁)) ^ 2 ≤ εm)
    (hg : P.g₁ ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ - P.β) ^ 2 ≤ εg)
    (lam : Fin K → Bool) :
    InClass (P.mhatG (K := K)) P.ghatG εg εm (P.mPertG lam) (P.gPertG lam) := by
  refine ⟨P.validDGP_pertG lam, ?_, ?_⟩
  · intro d
    cases d with
    | false =>
        rw [P.l2sq_gPertG_false lam]
        exact le_trans (by positivity) hg
    | true =>
        exact le_trans (P.l2sq_gPertG_true_le lam) hg
  · rw [P.l2sq_mPertG lam]
    exact hm

end GenConstr

end Causalean.Estimation.MinimaxATE
