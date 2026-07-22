/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Scalar Frisch–Waugh–Lovell from the normal equations

The single-regressor (`K = 1`) specialization of the FWL identity, stated in
**normal-equation form** rather than as a joint minimization.  Given a weighted
support `c`, a nuisance subspace `H`, a scalar regressor `X` and response `Y`,
if `(β, α)` with `α ∈ H` satisfies the two weighted normal equations

    ⟨Y − β·X − α, X⟩_ω = 0,
    ⟨Y − β·X − α, h⟩_ω = 0   for every h ∈ H,

and the residualized regressor has positive weighted energy
`⟨X̃, X̃⟩_ω > 0`, then

    β = ⟨X̃, Y⟩_ω / ⟨X̃, X̃⟩_ω,   where  X̃ = c.tildeX H X.

This is the finite weighted-support counterpart of the measure-theoretic
population FWL `Causalean.Panel.residualizedCoefficient_eq_of_normalEqs`. It
bridges the normal-equation inputs that estimand arguments naturally produce to
the residualized-coefficient ratio, without going through the joint-minimization
form of `fwl_identity`.
-/

import Causalean.Panel.Weighted.FWL

/-! # Scalar Frisch-Waugh-Lovell from normal equations

This file proves the single-regressor finite weighted-support
Frisch-Waugh-Lovell formula from weighted normal equations. The supporting lemma
`ip_tildeX_self` identifies the residualized regressor's inner product with the
original regressor and with itself. The main theorem
`scalar_fwl_of_normalEqs` states that any scalar coefficient satisfying the
regressor and nuisance normal equations equals the residualized coefficient
ratio.

The result supplies the normal-equation form needed by downstream
estimand-characterization arguments without requiring them to restate a joint
least-squares minimization problem. -/

open scoped BigOperators

namespace Causalean
namespace Panel.Weighted
namespace WeightedSupport

variable {R : Type*}
variable [Fintype R] [DecidableEq R]

/-- `⟨X̃, X⟩_ω = ⟨X̃, X̃⟩_ω`: the residualized regressor sees `X` and its
residual identically, because the projection part lies in `H` and is orthogonal
to the residual. -/
lemma ip_tildeX_self (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    (X : R → ℝ) :
    c.ip (c.tildeX H X) X = c.ip (c.tildeX H X) (c.tildeX H X) := by
  -- Write `X = tildeX + proj X` only in the *right* slot.
  have hsplit : X = c.tildeX H X + c.proj H X := by
    rw [tildeX_eq]; ext r; simp
  calc c.ip (c.tildeX H X) X
      = c.ip (c.tildeX H X) (c.tildeX H X + c.proj H X) := by rw [← hsplit]
    _ = c.ip (c.tildeX H X) (c.tildeX H X)
          + c.ip (c.tildeX H X) (c.proj H X) := c.ip_add_right _ _ _
    _ = c.ip (c.tildeX H X) (c.tildeX H X) := by
          rw [c.residualize_in_orthogonal H X (c.proj_mem H X), add_zero]

/-- **Scalar FWL from the normal equations.**

If `α ∈ H` and `(β, α)` solves the two weighted normal equations, and the
residualized regressor `X̃ = c.tildeX H X` has positive weighted energy, then
`β` equals the residualized coefficient `⟨X̃, Y⟩_ω / ⟨X̃, X̃⟩_ω`. -/
theorem scalar_fwl_of_normalEqs (c : WeightedSupport R)
    (H : Submodule ℝ (R → ℝ)) (X Y : R → ℝ) (β : ℝ) (α : R → ℝ)
    (hα : α ∈ H)
    (hpos : 0 < c.ip (c.tildeX H X) (c.tildeX H X))
    (h_normal_X : c.ip (Y - β • X - α) X = 0)
    (h_normal_H : ∀ h ∈ H, c.ip (Y - β • X - α) h = 0) :
    β = c.ip (c.tildeX H X) Y / c.ip (c.tildeX H X) (c.tildeX H X) := by
  set Xt : R → ℝ := c.tildeX H X with hXt
  set R₀ : R → ℝ := Y - β • X - α with hR₀
  -- The residualized regressor is orthogonal to the regression residual.
  have hXt_R₀ : c.ip Xt R₀ = 0 := by
    have hsplit : Xt = X + (-1 : ℝ) • c.proj H X := by
      rw [hXt, tildeX_eq]; ext r; simp [sub_eq_add_neg]
    rw [hsplit, c.ip_add_left]
    -- ⟨X, R₀⟩ = ⟨R₀, X⟩ = 0
    have h1 : c.ip X R₀ = 0 := by rw [c.ip_symm]; exact h_normal_X
    -- ⟨(-1)•proj X, R₀⟩ = (-1) * ⟨R₀, proj X⟩ = 0
    have h2 : c.ip ((-1 : ℝ) • c.proj H X) R₀ = 0 := by
      rw [c.ip_smul_left, c.ip_symm]
      rw [h_normal_H (c.proj H X) (c.proj_mem H X)]
      ring
    rw [h1, h2, add_zero]
  -- Expand ⟨Xt, R₀⟩ = ⟨Xt, Y⟩ − β⟨Xt, X⟩ − ⟨Xt, α⟩, and kill ⟨Xt, α⟩.
  have hα_zero : c.ip Xt α = 0 := c.residualize_in_orthogonal H X hα
  have hXt_X : c.ip Xt X = c.ip Xt Xt := ip_tildeX_self c H X
  have hexpand : c.ip Xt R₀ = c.ip Xt Y - β * c.ip Xt Xt := by
    have hrw : R₀ = Y - β • X - α := hR₀
    rw [hrw]
    -- Y - β•X - α = Y + (-(β•X)) + (-α)
    have hsub : Y - β • X - α = Y + (-(β • X)) + (-α) := by
      ext r; simp [sub_eq_add_neg]
    rw [hsub, c.ip_add_right, c.ip_add_right]
    have hneg_smul : c.ip Xt (-(β • X)) = - (β * c.ip Xt X) := by
      have : (-(β • X) : R → ℝ) = (-β) • X := by ext r; simp
      rw [this, c.ip_smul_right]; ring
    have hneg_α : c.ip Xt (-α) = - c.ip Xt α := by
      have : (-α : R → ℝ) = (-1 : ℝ) • α := by ext r; simp
      rw [this, c.ip_smul_right]; ring
    rw [hneg_smul, hneg_α, hα_zero, hXt_X]; ring
  -- Combine: 0 = ⟨Xt, Y⟩ − β⟨Xt, Xt⟩.
  rw [hexpand] at hXt_R₀
  have hne : c.ip Xt Xt ≠ 0 := hpos.ne'
  field_simp at hXt_R₀ ⊢
  linarith [hXt_R₀]

end WeightedSupport
end Panel.Weighted
end Causalean
