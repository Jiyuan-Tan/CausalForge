/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the explicit Case-1 construction

This file builds the explicit perturbed nuisance families of Jin–Syrgkanis 2024
(§4.4, Case 1) in the finite-covariate model of `Model.lean`, specialized to the
centered estimates `m̂ ≡ 1/2`, `ĝ ≡ 1/2` and the unweighted ATE (`w ≡ 1`).

The covariate is `C = Fin K × Bool`: `K` paired cells, each with two positions.
A Rademacher sign vector `λ : Fin K → Bool` drives the bump

  `Δ λ (j, b) = signOf b · signOf (λ j) ∈ {−1, +1}`,

which satisfies `Δ² = 1` and is **balanced** (within each pair `j`, the two
positions get opposite signs), exactly the two properties the paper's `Δ(λ,·)`
has (`Δ² = 1`, `E_X[Δ] = 0`).  The perturbed DGP (eq. 17 with `m̂ = ĝ = 1/2`,
`ŵ = 1`) is

  `gλ(0,·) = 1/2`,  `mλ = 1/2 − β·Δ`,  `gλ(1,·) = (1/2 + α·Δ)/(1 − 2β·Δ)`,

the **asymmetric / non-linear-in-λ** construction (`gλ(1)` divides by `mλ`).  The
two scalars `α, β ≥ 0` with `α + 2β ≤ 1/2` keep every probability in `[0,1]`.

This file defines the construction and proves it is a `ValidDGP`; class
membership, the ATE gap, and the χ² indistinguishability live in the sibling
files.
-/

import Causalean.Estimation.MinimaxATE.Model

/-! # Base Perturbation Construction

This file defines the paired-cell perturbation family used for the base
structure-agnostic average treatment effect lower bound. The declarations `signOf` and `Δ`
encode the balanced Rademacher signs and prove the elementary facts `signOf_sq`, `Δ_sq`,
`Δ_mem`, `Δ_le_one`, and `neg_one_le_Δ`.

The centered nuisance functions are `mhat` and `ghat`, and the perturbed nuisances are
`mPerturbed` and `gPerturbed`. The validity lemmas `denom_pos`, `validDGP_hat`, and
`validDGP_perturbed` show that the null and perturbed nuisances define finite observed-data
models in the stated parameter regime.
-/

namespace Causalean.Estimation.MinimaxATE

open scoped BigOperators

/-- This maps a Boolean position to its plus-or-minus-one sign. -/
def signOf (b : Bool) : ℝ := if b then 1 else -1

/-- The sign of the true Boolean value is one. -/
@[simp] theorem signOf_true : signOf true = 1 := rfl
/-- The sign of the false Boolean value is minus one. -/
@[simp] theorem signOf_false : signOf false = -1 := rfl

/-- The square of every Boolean sign is one. -/
theorem signOf_sq (b : Bool) : (signOf b) ^ 2 = 1 := by
  cases b <;> norm_num [signOf]

/-- Every Boolean sign is either one or minus one. -/
theorem signOf_mem (b : Bool) : signOf b = 1 ∨ signOf b = -1 := by
  cases b <;> simp [signOf]

variable {K : ℕ}

/-- Paired-cell Rademacher bump used to perturb the nuisance functions.

Within each pair the two positions have opposite signs, and the sign vector chooses the
orientation of each pair. -/
def Δ (lam : Fin K → Bool) (x : Fin K × Bool) : ℝ := signOf x.2 * signOf (lam x.1)

/-- The Rademacher bump has square one at every paired cell. -/
theorem Δ_sq (lam : Fin K → Bool) (x : Fin K × Bool) : (Δ lam x) ^ 2 = 1 := by
  unfold Δ
  rw [mul_pow, signOf_sq, signOf_sq, mul_one]

/-- The Rademacher bump only takes the values one and minus one. -/
theorem Δ_mem (lam : Fin K → Bool) (x : Fin K × Bool) : Δ lam x = 1 ∨ Δ lam x = -1 := by
  unfold Δ
  rcases signOf_mem x.2 with h2 | h2 <;> rcases signOf_mem (lam x.1) with h1 | h1 <;>
    simp [h2, h1]

/-- The Rademacher bump is always at most one. -/
theorem Δ_le_one (lam : Fin K → Bool) (x : Fin K × Bool) : Δ lam x ≤ 1 := by
  rcases Δ_mem lam x with h | h
  · rw [h]
  · rw [h]; norm_num

/-- The Rademacher bump is always at least minus one. -/
theorem neg_one_le_Δ (lam : Fin K → Bool) (x : Fin K × Bool) : -1 ≤ Δ lam x := by
  rcases Δ_mem lam x with h | h
  · rw [h]; norm_num
  · rw [h]

/-- Centered propensity estimate that assigns one half to every covariate
value. -/
noncomputable def mhat : (Fin K × Bool) → ℝ := fun _ => 1 / 2

/-- Centered outcome-regression estimate that assigns one half in both
treatment arms. -/
noncomputable def ghat : Bool → (Fin K × Bool) → ℝ := fun _ _ => 1 / 2

/-- Perturbed propensity obtained by shifting the centered propensity along
the Rademacher bump. -/
noncomputable def mPerturbed (β : ℝ) (lam : Fin K → Bool) : (Fin K × Bool) → ℝ :=
  fun x => 1 / 2 - β * Δ lam x

/-- Perturbed outcome regression with an unchanged control arm and a
nonlinear treated-arm shift.

The treated arm divides by the corresponding propensity denominator, matching the asymmetric
Case-1 construction. -/
noncomputable def gPerturbed (α β : ℝ) (lam : Fin K → Bool) : Bool → (Fin K × Bool) → ℝ :=
  fun d x => if d then (1 / 2 + α * Δ lam x) / (1 - 2 * β * Δ lam x) else 1 / 2

section Validity

variable {α β : ℝ}

/-- The treated-arm denominator in the perturbed outcome regression is positive in the
valid parameter regime. -/
theorem denom_pos (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2) (hα : 0 ≤ α)
    (lam : Fin K → Bool) (x : Fin K × Bool) : 0 < 1 - 2 * β * Δ lam x := by
  have hβ4 : β ≤ 1 / 4 := by linarith
  rcases Δ_mem lam x with h | h
  · rw [h]; nlinarith
  · rw [h]; nlinarith

/-- The centered null nuisance functions define a valid finite observed-data model. -/
theorem validDGP_hat : ValidDGP (C := Fin K × Bool) mhat ghat := by
  refine ⟨fun x => ?_, fun d x => ?_⟩ <;> · simp only [mhat, ghat]; norm_num

/-- The perturbed nuisance functions define a valid finite observed-data model in the
stated parameter regime. -/
theorem validDGP_perturbed (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (lam : Fin K → Bool) :
    ValidDGP (mPerturbed β lam) (gPerturbed α β lam) := by
  have hβ4 : β ≤ 1 / 4 := by linarith
  refine ⟨fun x => ?_, fun d x => ?_⟩
  · -- propensity `1/2 − β·Δ ∈ [0,1]`
    constructor <;> simp only [mPerturbed]
    · rcases Δ_mem lam x with h | h <;> · rw [h]; nlinarith
    · rcases Δ_mem lam x with h | h <;> · rw [h]; nlinarith
  · -- outcome `gλ(d,·) ∈ [0,1]`
    have hd := denom_pos hβ hαβ hα lam x
    rcases d with _ | _
    · -- control arm `= 1/2`
      simp only [gPerturbed, Bool.false_eq_true, if_false]; norm_num
    · -- treated arm `(1/2 + α·Δ)/(1 − 2β·Δ) ∈ [0,1]`
      simp only [gPerturbed, if_true]
      rcases Δ_mem lam x with h | h
      · rw [h] at hd ⊢
        constructor
        · apply div_nonneg <;> nlinarith
        · rw [div_le_one hd]; nlinarith
      · rw [h] at hd ⊢
        constructor
        · apply div_nonneg <;> nlinarith
        · rw [div_le_one hd]; nlinarith

end Validity

end Causalean.Estimation.MinimaxATE
