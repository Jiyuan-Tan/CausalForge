/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the general-constant-center construction

`Construction.lean` builds the Jin–Syrgkanis 2024 Case-1 perturbation specialized
to the centered estimates `m̂ ≡ 1/2`, `ĝ ≡ 1/2`.  This file generalizes the center
to an **arbitrary constant** nuisance estimate `(m₀, g₀, g₁) ∈ (0,1)³` bounded away
from `{0,1}` — exactly the regime of the paper's Assumption 2, in the constant case.

The covariate is still `C = Fin K × Bool` with the balanced Rademacher bump `Δ`
of `Construction.lean` (reused verbatim).  Around the constant center the perturbed
DGP (eq. 17, the asymmetric / non-linear-in-`λ` construction) is

  `mλ   = m₀ · (1 − (β/g₁)·Δ)`,
  `gλ(1,·) = (g₁ + α·Δ) / (1 − (β/g₁)·Δ)`,
  `gλ(0,·) = g₀`  (control arm unchanged),

which collapses to `Construction.lean` at `m₀ = g₁ = 1/2` (`β/g₁ = 2β`).  The data
are packaged in a `GenConstr` record carrying the two bump scalars `α, β ≥ 0`, the
three center constants, and the inequalities that keep every probability in `[0,1]`.

This file defines the construction and proves it is a `ValidDGP`; the ATE gap,
class membership, and the χ² indistinguishability live in the sibling `ConstCenterGeneral` files.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Construction

/-! # General Constant-Center Lower-Bound Construction

This file generalizes the structure-agnostic ATE lower-bound construction from
the centered half-probability nuisance estimates to arbitrary constant nuisance
centers bounded away from zero and one. It defines the perturbed data-generating
process and proves that the resulting propensity and outcome functions are valid
probability functions.

The record `GenConstr` stores the bump sizes `α, β`, the constant center
`(m₀, g₀, g₁)`, and the inequalities that keep the perturbation in `[0,1]`.
The public definitions `mhatG`, `ghatG`, `mPertG`, and `gPertG` give the null
and sign-indexed perturbed DGPs, while `validDGP_hatG` and `validDGP_pertG`
establish their finite-model validity. -/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

variable {K : ℕ}

/-- **General-constant-center construction data.**  The two Rademacher-bump scalars
`α, β` together with a constant nuisance center `(m₀, g₀, g₁)` bounded away from
`{0,1}`, and the inequalities guaranteeing the perturbed nuisances stay in `[0,1]`. -/
structure GenConstr where
  /-- Bump magnitude on the treated outcome arm. -/
  α : ℝ
  /-- Bump magnitude on the propensity. -/
  β : ℝ
  /-- Constant propensity center `m̂`. -/
  m₀ : ℝ
  /-- Constant control-arm center `ĝ(0,·)`. -/
  g₀ : ℝ
  /-- Constant treated-arm center `ĝ(1,·)`. -/
  g₁ : ℝ
  hα : 0 ≤ α
  hβ : 0 ≤ β
  hm₀0 : 0 < m₀
  hm₀1 : m₀ < 1
  hg₀0 : 0 < g₀
  hg₀1 : g₀ < 1
  hg₁0 : 0 < g₁
  hg₁1 : g₁ < 1
  /-- The propensity bump is smaller than the treated center (keeps the denominator
  `1 − (β/g₁)·Δ` positive). -/
  hβg₁ : β < g₁
  /-- The treated-arm bump does not exceed the treated center (keeps `gλ(1) ≥ 0`). -/
  hαg₁ : α ≤ g₁
  /-- Worst-case upper bound keeping `gλ(1) ≤ 1`. -/
  hgU : g₁ + α + β / g₁ ≤ 1
  /-- Worst-case upper bound keeping `mλ ≤ 1`. -/
  hmU : m₀ * (1 + β / g₁) ≤ 1

namespace GenConstr

variable (P : GenConstr)

/-- `0 < β/g₁` is false in general (β may be 0); but `0 ≤ β/g₁` always. -/
theorem ratio_nonneg : 0 ≤ P.β / P.g₁ := div_nonneg P.hβ P.hg₁0.le

/-- `β/g₁ < 1` since `β < g₁`. -/
theorem ratio_lt_one : P.β / P.g₁ < 1 := (div_lt_one P.hg₁0).mpr P.hβg₁

/-- The constant propensity center as a function of the covariate. -/
noncomputable def mhatG : (Fin K × Bool) → ℝ := fun _ => P.m₀

/-- The constant outcome-regression center: `g₁` on the treated arm, `g₀` on control. -/
noncomputable def ghatG : Bool → (Fin K × Bool) → ℝ := fun d _ => if d then P.g₁ else P.g₀

/-- The perturbed propensity `mλ = m₀·(1 − (β/g₁)·Δ)`. -/
noncomputable def mPertG (lam : Fin K → Bool) : (Fin K × Bool) → ℝ :=
  fun x => P.m₀ * (1 - (P.β / P.g₁) * Δ lam x)

/-- The perturbed outcome regression: control arm `= g₀`, treated arm
`gλ(1,·) = (g₁ + α·Δ)/(1 − (β/g₁)·Δ)`. -/
noncomputable def gPertG (lam : Fin K → Bool) : Bool → (Fin K × Bool) → ℝ :=
  fun d x => if d then (P.g₁ + P.α * Δ lam x) / (1 - (P.β / P.g₁) * Δ lam x) else P.g₀

/-- The denominator `1 − (β/g₁)·Δ` is positive: `Δ ≤ 1` gives
`1 − (β/g₁)·Δ ≥ 1 − β/g₁ > 0`. -/
theorem denomG_pos (lam : Fin K → Bool) (x : Fin K × Bool) :
    0 < 1 - (P.β / P.g₁) * Δ lam x := by
  have hr := P.ratio_nonneg
  have hr1 := P.ratio_lt_one
  rcases Δ_mem lam x with h | h
  · rw [h]; nlinarith
  · rw [h]; nlinarith

/-- The null DGP `(m̂, ĝ) = (m₀, (g₀,g₁))` is valid. -/
theorem validDGP_hatG : ValidDGP (C := Fin K × Bool) P.mhatG P.ghatG := by
  refine ⟨fun x => ?_, fun d x => ?_⟩
  · simp only [mhatG]; exact ⟨P.hm₀0.le, P.hm₀1.le⟩
  · simp only [ghatG]; cases d
    · exact ⟨P.hg₀0.le, P.hg₀1.le⟩
    · exact ⟨P.hg₁0.le, P.hg₁1.le⟩

/-- The perturbed DGP `(mλ, gλ)` is valid. -/
theorem validDGP_pertG (lam : Fin K → Bool) :
    ValidDGP (P.mPertG lam) (P.gPertG lam) := by
  have hr := P.ratio_nonneg
  have hr1 := P.ratio_lt_one
  refine ⟨fun x => ?_, fun d x => ?_⟩
  · -- propensity `m₀·(1 − (β/g₁)·Δ) ∈ [0,1]`
    simp only [mPertG]
    have hmU := P.hmU
    have hm0 := P.hm₀0
    rcases Δ_mem lam x with h | h
    · rw [h]
      constructor
      · nlinarith
      · nlinarith
    · rw [h]
      constructor
      · nlinarith
      · nlinarith
  · -- outcome `gλ(d,·) ∈ [0,1]`
    have hd := P.denomG_pos lam x
    rcases d with _ | _
    · simp only [gPertG, Bool.false_eq_true, if_false]; exact ⟨P.hg₀0.le, P.hg₀1.le⟩
    · simp only [gPertG, if_true]
      have hgU := P.hgU
      have hαg₁ := P.hαg₁
      have hg₁0 := P.hg₁0
      have hg₁1 := P.hg₁1
      have hα := P.hα
      rcases Δ_mem lam x with h | h
      · rw [h] at hd ⊢
        refine ⟨div_nonneg (by nlinarith) hd.le, ?_⟩
        rw [div_le_one hd]; nlinarith
      · rw [h] at hd ⊢
        refine ⟨div_nonneg (by nlinarith) hd.le, ?_⟩
        rw [div_le_one hd]; nlinarith

end GenConstr

end Causalean.Estimation.MinimaxATE
