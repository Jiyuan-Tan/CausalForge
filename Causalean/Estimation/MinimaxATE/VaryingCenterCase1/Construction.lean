/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the cell-varying-center construction

`ConstCenterGeneral/Construction.lean` perturbs around an arbitrary **constant** nuisance center
`(m₀, g₀, g₁) ∈ (0,1)³`.  This file generalizes the center to a **cell-varying
(piecewise-constant) function**: the nuisance estimates are arbitrary functions of
the *pair index* `j : Fin K`, bounded away from `{0,1}`, with the two positions of a
pair sharing the pair's value.  This is the finite-model analogue of the paper's
**functional center** `(m̂, ĝ)` (Jin–Syrgkanis 2024, Assumption 2, general case),
restricted to centers that are constant within each Rademacher pair — the residual
within-pair variation is the only piece not covered here.

Around the cell-varying center `(m₀ j, g₀ j, g₁ j)` the perturbed DGP is the same
asymmetric/non-linear construction as `ConstCenterGeneral/Construction.lean`, applied per pair:

  `mλ x   = m₀ x.1 · (1 − (β/g₁ x.1)·Δ)`,
  `gλ(1,x) = (g₁ x.1 + α·Δ) / (1 − (β/g₁ x.1)·Δ)`,
  `gλ(0,x) = g₀ x.1`.

Because the center is constant *within* each pair, the per-pair ATE gap is exactly
`λ`-independent (no Taylor remainder), and the χ²-overlap keeps the clean form
`1 + Σⱼ (Γⱼ/K)·signOf(λ j)signOf(λ' j)` with a **per-pair** coefficient `Γⱼ` —
exactly what the non-uniform `ingster_bound_general` consumes.

This file defines the construction and proves it is a `ValidDGP`; the ATE gap,
class membership, and the χ² indistinguishability live in the sibling `VaryingCenterCase1` files.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Construction

/-! # Cell-Varying Construction

This file defines the cell-varying-center Rademacher construction for the
structure-agnostic ATE lower bound.  The nuisance center may vary by paired cell while remaining
constant within each pair, preserving the exact cancellation used by the gap and overlap
calculations.

The structure `VarConstr` stores the bump magnitudes `α`, `β`, the pair-indexed nuisance center
`m₀`, `g₀`, `g₁`, and the inequalities that keep all perturbed nuisances in `[0, 1]`.  Its namespace
defines the center functions `mhatV` and `ghatV`, the sign-dependent perturbations `mPertV` and
`gPertV`, the denominator positivity lemma `denomV_pos`, and the validity proofs
`validDGP_hatV` and `validDGP_pertV`. -/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

variable {K : ℕ}

/-- **Cell-varying-center construction data.**  The two Rademacher-bump scalars
`α, β` together with a nuisance center `(m₀ j, g₀ j, g₁ j)` that varies with the pair
index `j : Fin K` (bounded away from `{0,1}`), and the per-pair inequalities
guaranteeing the perturbed nuisances stay in `[0,1]`. -/
structure VarConstr (K : ℕ) where
  /-- Bump magnitude on the treated outcome arm. -/
  α : ℝ
  /-- Bump magnitude on the propensity. -/
  β : ℝ
  /-- Cell-varying propensity center `m̂`. -/
  m₀ : Fin K → ℝ
  /-- Cell-varying control-arm center `ĝ(0,·)`. -/
  g₀ : Fin K → ℝ
  /-- Cell-varying treated-arm center `ĝ(1,·)`. -/
  g₁ : Fin K → ℝ
  hα : 0 ≤ α
  hβ : 0 ≤ β
  hm₀0 : ∀ j, 0 < m₀ j
  hm₀1 : ∀ j, m₀ j < 1
  hg₀0 : ∀ j, 0 < g₀ j
  hg₀1 : ∀ j, g₀ j < 1
  hg₁0 : ∀ j, 0 < g₁ j
  hg₁1 : ∀ j, g₁ j < 1
  /-- The propensity bump is smaller than the treated center (keeps the denominator
  `1 − (β/g₁)·Δ` positive). -/
  hβg₁ : ∀ j, β < g₁ j
  /-- The treated-arm bump does not exceed the treated center (keeps `gλ(1) ≥ 0`). -/
  hαg₁ : ∀ j, α ≤ g₁ j
  /-- Worst-case upper bound keeping `gλ(1) ≤ 1`. -/
  hgU : ∀ j, g₁ j + α + β / g₁ j ≤ 1
  /-- Worst-case upper bound keeping `mλ ≤ 1`. -/
  hmU : ∀ j, m₀ j * (1 + β / g₁ j) ≤ 1

namespace VarConstr

variable (P : VarConstr K)

/-- `0 ≤ β/g₁ j` always. -/
theorem ratio_nonneg (j : Fin K) : 0 ≤ P.β / P.g₁ j := div_nonneg P.hβ (P.hg₁0 j).le

/-- `β/g₁ j < 1` since `β < g₁ j`. -/
theorem ratio_lt_one (j : Fin K) : P.β / P.g₁ j < 1 := (div_lt_one (P.hg₁0 j)).mpr (P.hβg₁ j)

/-- The cell-varying propensity center as a function of the covariate. -/
noncomputable def mhatV : (Fin K × Bool) → ℝ := fun x => P.m₀ x.1

/-- The cell-varying outcome-regression center: `g₁ j` on the treated arm, `g₀ j` on
control, where `j` is the pair index of the cell. -/
noncomputable def ghatV : Bool → (Fin K × Bool) → ℝ :=
  fun d x => if d then P.g₁ x.1 else P.g₀ x.1

/-- The perturbed propensity `mλ x = m₀ x.1·(1 − (β/g₁ x.1)·Δ)`. -/
noncomputable def mPertV (lam : Fin K → Bool) : (Fin K × Bool) → ℝ :=
  fun x => P.m₀ x.1 * (1 - (P.β / P.g₁ x.1) * Δ lam x)

/-- The perturbed outcome regression: control arm `= g₀ x.1`, treated arm
`gλ(1,x) = (g₁ x.1 + α·Δ)/(1 − (β/g₁ x.1)·Δ)`. -/
noncomputable def gPertV (lam : Fin K → Bool) : Bool → (Fin K × Bool) → ℝ :=
  fun d x => if d then (P.g₁ x.1 + P.α * Δ lam x) / (1 - (P.β / P.g₁ x.1) * Δ lam x) else P.g₀ x.1

/-- The denominator `1 − (β/g₁ j)·Δ` is positive. -/
theorem denomV_pos (lam : Fin K → Bool) (x : Fin K × Bool) :
    0 < 1 - (P.β / P.g₁ x.1) * Δ lam x := by
  have hr := P.ratio_nonneg x.1
  have hr1 := P.ratio_lt_one x.1
  rcases Δ_mem lam x with h | h
  · rw [h]; nlinarith
  · rw [h]; nlinarith

/-- The null DGP `(m̂, ĝ)` is valid. -/
theorem validDGP_hatV : ValidDGP (C := Fin K × Bool) P.mhatV P.ghatV := by
  refine ⟨fun x => ?_, fun d x => ?_⟩
  · simp only [mhatV]; exact ⟨(P.hm₀0 x.1).le, (P.hm₀1 x.1).le⟩
  · simp only [ghatV]; cases d
    · exact ⟨(P.hg₀0 x.1).le, (P.hg₀1 x.1).le⟩
    · exact ⟨(P.hg₁0 x.1).le, (P.hg₁1 x.1).le⟩

/-- The perturbed DGP `(mλ, gλ)` is valid. -/
theorem validDGP_pertV (lam : Fin K → Bool) :
    ValidDGP (P.mPertV lam) (P.gPertV lam) := by
  refine ⟨fun x => ?_, fun d x => ?_⟩
  · -- propensity `m₀·(1 − (β/g₁)·Δ) ∈ [0,1]`
    have hr := P.ratio_nonneg x.1
    have hr1 := P.ratio_lt_one x.1
    have hmU := P.hmU x.1
    have hm0 := P.hm₀0 x.1
    simp only [mPertV]
    rcases Δ_mem lam x with h | h
    · rw [h]; constructor
      · nlinarith
      · nlinarith
    · rw [h]; constructor
      · nlinarith
      · nlinarith
  · -- outcome `gλ(d,·) ∈ [0,1]`
    have hd := P.denomV_pos lam x
    rcases d with _ | _
    · simp only [gPertV, Bool.false_eq_true, if_false]; exact ⟨(P.hg₀0 x.1).le, (P.hg₀1 x.1).le⟩
    · simp only [gPertV, if_true]
      have hr := P.ratio_nonneg x.1
      have hgU := P.hgU x.1
      have hαg₁ := P.hαg₁ x.1
      have hg₁0 := P.hg₁0 x.1
      have hg₁1 := P.hg₁1 x.1
      have hα := P.hα
      rcases Δ_mem lam x with h | h
      · rw [h] at hd ⊢
        refine ⟨div_nonneg (by nlinarith) hd.le, ?_⟩
        rw [div_le_one hd]; nlinarith
      · rw [h] at hd ⊢
        refine ⟨div_nonneg (by nlinarith) hd.le, ?_⟩
        rw [div_le_one hd]; nlinarith

end VarConstr

end Causalean.Estimation.MinimaxATE
