/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the *second* (propensity-dominant) construction

`VaryingCenterCase1/Construction.lean` builds the Case-1 construction of Jin–Syrgkanis 2024
(eq. (17), `e_n' ≥ f_n`), which establishes the product rate `s ≍ √(εg·εm)` only
when the **outcome** budget dominates (`εg ≳ εm`): there the treated-arm bump
`α + β/g₁` carries the `√εg` weight and the propensity bump `β` carries `√εm`, so
one needs `√εg ≳ √εm`.

This file builds the **symmetric second construction** (Jin–Syrgkanis 2024,
eq. (18), Case 2 `f_n > e_n'`), which covers the opposite regime `εm > εg`.  The
roles of the two nuisances are swapped: now the *propensity* deviation is the large
one (`O(α+β)`, carrying `√εm`) and the *outcome* deviation is the small one
(`O(β)`, carrying `√εg`).  In the finite-cell model of `Model.lean` (with the
within-cell weight `ŵ ≡ 1`) the construction is, per pair `j` with sign
`Δ = Δ(λ,x) ∈ {−1,+1}`:

  `gλ(0,x) = g₀ j`,
  `gλ(1,x) = g₁ j / D`,        with `D := 1 + (β/g₁ j)·Δ − α·β`,
  `mλ(x)   = m₀ j · (1 + α·g₁ j·Δ) · D`.

As in Case 1 the family is **non-linear in λ** (the outcome arm divides by `D`),
but the *observed* masses are again polynomial in `Δ`: the division cancels in
`mλ·gλ(1) = m₀ g₁ (1 + α g₁ Δ)`, and the propensity collapses (using `Δ² = 1`) to
the affine form

  `mλ = m₀ · (1 + κ·Δ)`,   `κ := β/g₁ j + α·g₁ j − α²·β·g₁ j`,

so every `(d,y)` mass is denominator-free.  This is what later lets the χ²-overlap
keep the clean `1 + Σⱼ (Γⱼ/K)·signOf(λ j)signOf(λ' j)` form.

This file defines the construction and proves it is a `ValidDGP`; the ATE gap,
class membership, and the χ² indistinguishability live in the sibling `VaryingCenterCase2/*`
files.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Construction

/-! # Propensity-Dominant Construction

This file defines the second cell-varying perturbation family for the
structure-agnostic average treatment effect lower bound, in the regime where the
propensity-error budget is larger than the outcome-regression budget.  It proves
that the constructed finite observed-data laws are valid probability models.
-/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

variable {K : ℕ}

/-- **Second (propensity-dominant) cell-varying construction data.**  The two
Rademacher-bump scalars `α, β` together with a nuisance center `(m₀ j, g₀ j, g₁ j)`
that varies with the pair index `j : Fin K` (bounded away from `{0,1}`), and the
per-pair inequalities guaranteeing the perturbed nuisances stay in `[0,1]`. -/
structure VarConstr2 (K : ℕ) where
  /-- Bump magnitude on the propensity (the *large* deviation here). -/
  α : ℝ
  /-- Bump magnitude on the treated outcome arm (the *small* deviation here). -/
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
  /-- Worst-case upper bound keeping `gλ(1) = g₁/D ≤ 1` (equivalently `g₁ ≤ D_min`);
  also forces `D_min = 1 − β/g₁ − αβ > 0`, so the denominator is positive. -/
  hgU : ∀ j, g₁ j + β / g₁ j + α * β ≤ 1
  /-- The propensity bump coefficient `κ = β/g₁ + αg₁ − α²βg₁` does not exceed `1`
  (keeps `mλ = m₀(1 + κΔ) ≥ 0`). -/
  hκ : ∀ j, β / g₁ j + α * g₁ j - α ^ 2 * β * g₁ j ≤ 1
  /-- Worst-case upper bound keeping `mλ ≤ 1`. -/
  hmU : ∀ j, m₀ j * (1 + (β / g₁ j + α * g₁ j - α ^ 2 * β * g₁ j)) ≤ 1

namespace VarConstr2

variable (P : VarConstr2 K)

/-- The propensity bump coefficient `κⱼ = β/g₁ⱼ + α·g₁ⱼ − α²·β·g₁ⱼ`. -/
noncomputable def κ (j : Fin K) : ℝ :=
  P.β / P.g₁ j + P.α * P.g₁ j - P.α ^ 2 * P.β * P.g₁ j

/-- The treated-arm denominator `D = 1 + (β/g₁)·Δ − α·β`. -/
noncomputable def D2 (lam : Fin K → Bool) (x : Fin K × Bool) : ℝ :=
  1 + (P.β / P.g₁ x.1) * Δ lam x - P.α * P.β

/-- `0 ≤ β/g₁ j`. -/
theorem ratio_nonneg (j : Fin K) : 0 ≤ P.β / P.g₁ j := div_nonneg P.hβ (P.hg₁0 j).le

/-- `0 ≤ κⱼ`. -/
theorem κ_nonneg (j : Fin K) : 0 ≤ P.κ j := by
  have hg10 := P.hg₁0 j
  have hg11 := P.hg₁1 j
  have hαβ : P.α * P.β ≤ 1 := by have := P.hgU j; have := P.ratio_nonneg j; nlinarith [hg10]
  have hr := P.ratio_nonneg j
  have hαg : 0 ≤ P.α * P.g₁ j := mul_nonneg P.hα hg10.le
  unfold κ
  -- κ = β/g₁ + α g₁ (1 − αβ) ≥ 0
  have : P.α * P.g₁ j - P.α ^ 2 * P.β * P.g₁ j = P.α * P.g₁ j * (1 - P.α * P.β) := by ring
  rw [show P.β / P.g₁ j + P.α * P.g₁ j - P.α ^ 2 * P.β * P.g₁ j
        = P.β / P.g₁ j + P.α * P.g₁ j * (1 - P.α * P.β) by ring]
  have h1 : 0 ≤ P.α * P.g₁ j * (1 - P.α * P.β) := by
    apply mul_nonneg hαg; linarith
  linarith

/-- The denominator `D = 1 + (β/g₁)·Δ − αβ` is positive (at least `g₁ > 0`). -/
theorem D2_pos (lam : Fin K → Bool) (x : Fin K × Bool) : 0 < P.D2 lam x := by
  have hg10 := P.hg₁0 x.1
  have hgU := P.hgU x.1
  have hr := P.ratio_nonneg x.1
  unfold D2
  rcases Δ_mem lam x with h | h
  · rw [h]; nlinarith
  · rw [h]; nlinarith

/-- The cell-varying propensity center as a function of the covariate. -/
noncomputable def mhat2 : (Fin K × Bool) → ℝ := fun x => P.m₀ x.1

/-- The cell-varying outcome-regression center: `g₁ j` on the treated arm, `g₀ j` on
control, where `j` is the pair index of the cell. -/
noncomputable def ghat2 : Bool → (Fin K × Bool) → ℝ :=
  fun d x => if d then P.g₁ x.1 else P.g₀ x.1

/-- The perturbed propensity `mλ x = m₀ x.1·(1 + α·g₁ x.1·Δ)·D`. -/
noncomputable def mPert2 (lam : Fin K → Bool) : (Fin K × Bool) → ℝ :=
  fun x => P.m₀ x.1 * ((1 + P.α * P.g₁ x.1 * Δ lam x) * P.D2 lam x)

/-- The perturbed outcome regression: control arm `= g₀ x.1`, treated arm
`gλ(1,x) = g₁ x.1 / D`. -/
noncomputable def gPert2 (lam : Fin K → Bool) : Bool → (Fin K × Bool) → ℝ :=
  fun d x => if d then P.g₁ x.1 / P.D2 lam x else P.g₀ x.1

/-- **Affine collapse of the propensity.**  Using `Δ² = 1`, the perturbed propensity
is exactly `mλ = m₀·(1 + κ·Δ)`. -/
theorem mPert2_eq (lam : Fin K → Bool) (x : Fin K × Bool) :
    P.mPert2 lam x = P.m₀ x.1 * (1 + P.κ x.1 * Δ lam x) := by
  have hg₁ne : P.g₁ x.1 ≠ 0 := ne_of_gt (P.hg₁0 x.1)
  unfold mPert2 D2 κ
  -- expand and use Δ² = 1
  have hsq : Δ lam x * Δ lam x = 1 := by have := Δ_sq lam x; nlinarith [this]
  field_simp
  linear_combination (P.m₀ x.1 * P.α * P.g₁ x.1 * P.β) * hsq

/-- The null DGP `(m̂, ĝ)` is valid. -/
theorem validDGP_hat2 : ValidDGP (C := Fin K × Bool) P.mhat2 P.ghat2 := by
  refine ⟨fun x => ?_, fun d x => ?_⟩
  · simp only [mhat2]; exact ⟨(P.hm₀0 x.1).le, (P.hm₀1 x.1).le⟩
  · simp only [ghat2]; cases d
    · exact ⟨(P.hg₀0 x.1).le, (P.hg₀1 x.1).le⟩
    · exact ⟨(P.hg₁0 x.1).le, (P.hg₁1 x.1).le⟩

/-- The perturbed DGP `(mλ, gλ)` is valid. -/
theorem validDGP_pert2 (lam : Fin K → Bool) :
    ValidDGP (P.mPert2 lam) (P.gPert2 lam) := by
  refine ⟨fun x => ?_, fun d x => ?_⟩
  · -- propensity `m₀·(1 + κ·Δ) ∈ [0,1]`
    rw [P.mPert2_eq lam x]
    have hm0 := P.hm₀0 x.1
    have hm1 := P.hm₀1 x.1
    have hκ0 := P.κ_nonneg x.1
    have hκ1 := P.hκ x.1
    have hmU := P.hmU x.1
    have hκeq : P.κ x.1 = P.β / P.g₁ x.1 + P.α * P.g₁ x.1 - P.α ^ 2 * P.β * P.g₁ x.1 := rfl
    rw [← hκeq] at hκ1 hmU
    constructor
    · rcases Δ_mem lam x with h | h
      · rw [h]; nlinarith
      · rw [h]; nlinarith
    · rcases Δ_mem lam x with h | h
      · rw [h]; nlinarith
      · rw [h]; nlinarith
  · -- outcome `gλ(d,·) ∈ [0,1]`
    have hd := P.D2_pos lam x
    rcases d with _ | _
    · simp only [gPert2, Bool.false_eq_true, if_false]; exact ⟨(P.hg₀0 x.1).le, (P.hg₀1 x.1).le⟩
    · simp only [gPert2, if_true]
      have hg10 := P.hg₁0 x.1
      have hgU := P.hgU x.1
      have hr := P.ratio_nonneg x.1
      refine ⟨div_nonneg hg10.le hd.le, ?_⟩
      rw [div_le_one hd]
      -- need g₁ ≤ D = 1 + (β/g₁)Δ − αβ; worst case Δ = −1 covered by hgU
      unfold D2
      rcases Δ_mem lam x with h | h
      · rw [h]; nlinarith
      · rw [h]; nlinarith

end VarConstr2

end Causalean.Estimation.MinimaxATE
