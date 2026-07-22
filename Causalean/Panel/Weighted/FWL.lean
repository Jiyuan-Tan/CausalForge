/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Frisch–Waugh–Lovell on a weighted support

This file proves the Frisch-Waugh-Lovell identity for the
`Causalean.Panel.Weighted` substrate. Let `c : WeightedSupport R` be a weighted
support, `H : Submodule ℝ (R → ℝ)` a nuisance subspace, and
`X : Fin K → R → ℝ` a regressor vector.  The long-regression coefficient
`β` minimizing

    ω-WLS objective  c.ip (Y - ∑ k β k • X k - α) (Y - ∑ k β k • X k - α)

over `(β : Fin K → ℝ, α ∈ H)` equals the short-regression coefficient
`θ̂ := Q_XX⁻¹ * ⟨X̃, Y⟩_ω` from the H-residualized regressors
`X̃ := c.tildeXVec H X`.

The theorem is the reusable handoff from a weighted long regression with a
nuisance space to a residualized short regression. Estimand-characterization
modules instantiate `H`, `X`, and the support weights to read off the implicit
weights of their particular design.

## Main definitions

* `Q_XX` — the residualized Gram matrix `⟨X̃, X̃⟩_ω`.
* `rhsVec` — the residualized RHS `⟨X̃, Y⟩_ω`.
* `thetaHat` — the FWL coefficient `Q_XX⁻¹ * rhsVec`.
* `RankCondition` — nonsingularity of `Q_XX`.

## Main results

* `Q_XX_mulVec_thetaHat` — `thetaHat` solves the residualized normal equations.
* `fwl_identity` — long-regression joint minimizer `β` equals `thetaHat`.
-/

import Causalean.Panel.Weighted.WLS
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Weighted Frisch-Waugh-Lovell Identity

This file states and proves the finite weighted-support
Frisch-Waugh-Lovell identity. It constructs the residualized Gram matrix
`Q_XX`, residualized score vector `rhsVec`, residualized coefficient
`thetaHat`, and rank condition `RankCondition`. The lemma
`Q_XX_mulVec_thetaHat` proves that `thetaHat` solves the residualized normal
equations, and the theorem `fwl_identity` proves that any long weighted
least-squares minimizer has coefficient `thetaHat` after residualizing against
the nuisance space. -/

open scoped BigOperators
open Matrix

namespace Causalean
namespace Panel.Weighted
namespace WeightedSupport

variable {R : Type*}
variable [Fintype R] [DecidableEq R]
variable {K : ℕ}

/-! ### Residualized regression objects -/

/-- Residualized regressor Gram matrix `Q_XX = ⟨M_H X, M_H X⟩_ω`. -/
noncomputable def Q_XX (c : WeightedSupport R) (X : Fin K → R → ℝ)
    (H : Submodule ℝ (R → ℝ)) : Matrix (Fin K) (Fin K) ℝ :=
  c.ipMat (c.tildeXVec H X) (c.tildeXVec H X)

/-- Each entry of the residualized Gram matrix is the weighted inner product
of the corresponding residualized regressors. -/
@[simp] lemma Q_XX_apply (c : WeightedSupport R) (X : Fin K → R → ℝ)
    (H : Submodule ℝ (R → ℝ)) (j k : Fin K) :
    Q_XX c X H j k =
      c.ip (c.tildeX H (X j)) (c.tildeX H (X k)) := rfl

/-- Residualized FWL right-hand side `⟨M_H X, Y⟩_ω`. -/
noncomputable def rhsVec (c : WeightedSupport R) (X : Fin K → R → ℝ)
    (H : Submodule ℝ (R → ℝ)) (Y : R → ℝ) : Fin K → ℝ :=
  fun j => c.ip (c.tildeX H (X j)) Y

/-- Each entry of the residualized right-hand side is the weighted inner
product of a residualized regressor with the outcome. -/
@[simp] lemma rhsVec_apply (c : WeightedSupport R) (X : Fin K → R → ℝ)
    (H : Submodule ℝ (R → ℝ)) (Y : R → ℝ) (j : Fin K) :
    rhsVec c X H Y j = c.ip (c.tildeX H (X j)) Y := rfl

/-- Residualized weighted least-squares coefficient
`θ̂ = Q_XX⁻¹ ⟨M_H X, Y⟩_ω`. -/
noncomputable def thetaHat (c : WeightedSupport R) (X : Fin K → R → ℝ)
    (H : Submodule ℝ (R → ℝ)) (Y : R → ℝ) : Fin K → ℝ :=
  (Q_XX c X H)⁻¹.mulVec (rhsVec c X H Y)

/-- Rank condition for the residualized regressors: `Q_XX` is invertible. -/
def RankCondition (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    (X : Fin K → R → ℝ) : Prop :=
  IsUnit (Q_XX c X H).det

/-- Under nonsingularity, `thetaHat` solves the residualized normal equations. -/
lemma Q_XX_mulVec_thetaHat (c : WeightedSupport R) (X : Fin K → R → ℝ)
    (H : Submodule ℝ (R → ℝ)) (Y : R → ℝ)
    (hQ : IsUnit (Q_XX c X H).det) :
    (Q_XX c X H).mulVec (thetaHat c X H Y) = rhsVec c X H Y := by
  unfold thetaHat
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ, Matrix.one_mulVec]

/-! ### Frisch–Waugh–Lovell identity

The headline theorem of the substrate.  Joint minimization in `(β, α)` over
`(Fin K → ℝ) × H` of the long-regression WLS objective forces
`β = thetaHat`. -/

/-- `c.ip` of a finite sum on the left distributes. -/
private lemma ip_sum_left_finset (c : WeightedSupport R) {ι : Type*}
    (s : Finset ι) (f : ι → R → ℝ) (B : R → ℝ) :
    c.ip (∑ i ∈ s, f i) B = ∑ i ∈ s, c.ip (f i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert a s' hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, c.ip_add_left, ih]

private lemma ip_sum_left (c : WeightedSupport R)
    (f : Fin K → R → ℝ) (B : R → ℝ) :
    c.ip (∑ k, f k) B = ∑ k, c.ip (f k) B :=
  c.ip_sum_left_finset Finset.univ f B

/-- `c.ip` of a finite sum on the right distributes. -/
private lemma ip_sum_right (c : WeightedSupport R)
    (A : R → ℝ) (f : Fin K → R → ℝ) :
    c.ip A (∑ k, f k) = ∑ k, c.ip A (f k) := by
  rw [c.ip_symm, c.ip_sum_left]
  refine Finset.sum_congr rfl ?_
  intro k _; exact c.ip_symm _ _

/-- Inner product with the residualized regressor absorbs the H-projection
of the other argument: `⟨X̃ k, A⟩ = ⟨X̃ k, A - proj H A⟩`. -/
private lemma ip_tildeX_eq_ip_tildeX_residual (c : WeightedSupport R)
    (H : Submodule ℝ (R → ℝ)) (X : Fin K → R → ℝ) (A : R → ℝ) (k : Fin K) :
    c.ip (c.tildeX H (X k)) A = c.ip (c.tildeX H (X k)) (c.tildeX H A) := by
  have h1 : c.ip (c.tildeX H (X k)) (c.proj H A) = 0 := by
    have hsymm := c.ip_symm (c.tildeX H (X k)) (c.proj H A)
    rw [hsymm]
    rw [c.ip_symm]
    exact c.residualize_in_orthogonal H (X k) (c.proj_mem H A)
  have hAsplit : A = c.tildeX H A + c.proj H A := by
    simp [tildeX_eq]
  conv_lhs => rw [hAsplit]
  rw [c.ip_add_right, h1, add_zero]

/-- **Frisch–Waugh–Lovell at the WeightedSupport level.**

The long-regression coefficient `β` minimizing the WLS objective
`c.ip (Y - ∑ k β k • X k - α) (Y - ∑ k β k • X k - α)` jointly over
`(β : Fin K → ℝ, α ∈ H)` equals the short-regression coefficient `θ̂`
from the H-residualized regressors.

This is the *uniqueness* direction: if `(β, α)` is a joint minimizer, then
`β = c.thetaHat H X Y`. -/
theorem fwl_identity (c : WeightedSupport R)
    (H : Submodule ℝ (R → ℝ)) (X : Fin K → R → ℝ) (Y : R → ℝ)
    (hRank : c.RankCondition H X) :
    ∀ β : Fin K → ℝ, ∀ α : R → ℝ, α ∈ H →
      (∀ β' : Fin K → ℝ, ∀ α' : R → ℝ, α' ∈ H →
        c.ip (Y - (∑ k, β k • X k) - α) (Y - (∑ k, β k • X k) - α) ≤
        c.ip (Y - (∑ k, β' k • X k) - α') (Y - (∑ k, β' k • X k) - α')) →
      β = thetaHat c X H Y := by
  intro β α hα hmin
  -- Step 1: Set up the residual `R₀ := Y - ∑ k β k • X k - α`.
  set R₀ : R → ℝ := Y - (∑ k, β k • X k) - α with hR₀_def
  -- Step 2: Derive joint orthogonality from joint minimality.
  --
  -- (a) Varying α while fixing β: for any `g ∈ H`, the test point
  --     `(β, α + t • g) ∈ Fin K → ℝ × H` gives a one-parameter family.
  --     The residual at the test point is `R₀ - t • g`.
  --     Minimality gives `⟨R₀, g⟩_ω = 0` for all `g ∈ H`.
  have h_orth_H : ∀ g ∈ H, c.ip R₀ g = 0 := by
    intro g hg
    -- Apply the WLS first-order condition: `R₀ = Y - fitted β X - α`,
    -- treat as `(Y - fitted β X)` projected on `H` with candidate `α`.
    -- Specialize hmin to varying α only.
    have hmin_alpha : ∀ α' ∈ H,
        c.ip (Y - (∑ k, β k • X k) - α) (Y - (∑ k, β k • X k) - α) ≤
        c.ip (Y - (∑ k, β k • X k) - α') (Y - (∑ k, β k • X k) - α') := by
      intro α' hα'
      exact hmin β α' hα'
    -- Use residualize_orth_iff_argmin with X := Y - fitted β X, p := α.
    have := (c.residualize_orth_iff_argmin H (Y - (∑ k, β k • X k)) α hα).mpr
      hmin_alpha
    exact this g hg
  -- (b) Varying β_j while fixing α: for any `j : Fin K` and `t : ℝ`,
  --     the test point `(β + t • e_j, α)` gives residual `R₀ - t • X j`.
  --     The minimality + perturbation argument forces `⟨R₀, X j⟩_ω = 0`.
  have h_orth_X : ∀ j : Fin K, c.ip R₀ (X j) = 0 := by
    intro j
    -- Build the perturbation: replace β by β + t • e_j.
    -- Specialize hmin to such perturbations.
    have hkey : ∀ t : ℝ,
        c.ip R₀ R₀ ≤ c.ip (R₀ - t • X j) (R₀ - t • X j) := by
      intro t
      -- β' := β + t • (Pi.single j 1).  Then `∑ k β' k • X k = (∑ k β k • X k) + t • X j`.
      let δ : Fin K → ℝ := Pi.single j t
      let β' : Fin K → ℝ := β + δ
      have hsum_eq : (∑ k, β' k • X k) = (∑ k, β k • X k) + t • X j := by
        have hsplit : ∀ k, β' k • X k = β k • X k + δ k • X k := by
          intro k; simp only [β', Pi.add_apply, add_smul]
        rw [Finset.sum_congr rfl (fun k _ => hsplit k)]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single j]
        · simp [δ, Pi.single_eq_same]
        · intro k _ hk
          simp [δ, Pi.single_eq_of_ne hk]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hmin' := hmin β' α hα
      have heq : Y - (∑ k, β' k • X k) - α = R₀ - t • X j := by
        rw [hsum_eq, hR₀_def]
        ext s; simp; ring
      rw [heq] at hmin'
      exact hmin'
    -- Now apply the perturbation argument: quadratic-in-t inequality.
    have hquad : ∀ t : ℝ,
        0 ≤ - (2 * t * c.ip R₀ (X j)) + t^2 * c.ip (X j) (X j) := by
      intro t
      have := hkey t
      have hexp := c.ip_sub_smul_expand R₀ 0 (X j) t
      -- ip_sub_smul_expand: `c.ip (X - p - t • h) ... = ⟨X-p,X-p⟩ - 2t⟨X-p,h⟩ + t²⟨h,h⟩`.
      -- Specialize at X := R₀, p := 0, h := X j.
      simp only [sub_zero] at hexp
      linarith
    -- Same case analysis as in WLS.
    by_cases hzero : c.ip (X j) (X j) = 0
    · -- X j vanishes on observed, so `⟨R₀, X j⟩_ω = 0` directly.
      have hvan : ∀ r ∈ c.observed, X j r = 0 :=
        (c.ip_self_eq_zero_iff (X j)).mp hzero
      exact c.ip_eq_zero_of_zero_on_observed R₀ (X j) hvan
    · have hpos : 0 < c.ip (X j) (X j) :=
        lt_of_le_of_ne (c.ip_self_nonneg (X j)) (Ne.symm hzero)
      set a : ℝ := c.ip R₀ (X j) with ha
      set b : ℝ := c.ip (X j) (X j) with hb
      have htest := hquad (a / b)
      have hsimp : - (2 * (a / b) * a) + (a / b)^2 * b = - a^2 / b := by
        field_simp; ring
      rw [hsimp] at htest
      have ha2 : a^2 ≤ 0 := by
        have : - a^2 ≥ 0 := by
          have := (div_nonneg_iff.mp htest).resolve_right ?_
          · exact this.1
          · push_neg; intro _; exact hpos
        linarith
      have ha2nn : 0 ≤ a^2 := sq_nonneg a
      have ha2eq : a^2 = 0 := le_antisymm ha2 ha2nn
      exact sq_eq_zero_iff.mp ha2eq
  -- Step 3: Derive the normal equations `Q_XX β = rhsVec`.
  -- For each k: `⟨tildeX (X k), Y - ∑ j β j X j⟩_ω = 0`
  -- (since `tildeX (X k) ⊥ H` absorbs α, and `tildeX (X k) ⊥ ?`).
  have h_normal : ∀ k : Fin K,
      ∑ j, β j * c.ip (c.tildeX H (X j)) (c.tildeX H (X k)) =
        c.ip (c.tildeX H (X k)) Y := by
    intro k
    -- Use `ip_tildeX_eq_ip_tildeX_residual` to rewrite both sides into the
    -- tildeX-tildeX form, then apply orthogonality of residuals.
    -- Strategy: from h_orth_X applied to j-coordinate, we have
    --   c.ip R₀ (X j) = 0.
    -- Expand R₀ = Y - (∑ β j • X j) - α.
    -- So `c.ip Y (X k) - ∑ j β j • c.ip (X j) (X k) - c.ip α (X k) = 0`.
    -- But we want to work with tildeX. Use the lemma: residualizing one side
    -- of an inner product equals taking ⟨tildeX, tildeX⟩.
    --
    -- Cleaner route: compute c.ip R₀ (tildeX H (X k)).
    -- Since tildeX H (X k) ⊥ H, c.ip α (tildeX H (X k)) = 0.
    -- Since tildeX H (X k) = X k - proj H (X k), and `c.ip R₀ g = 0` for g ∈ H:
    --   c.ip R₀ (tildeX H (X k)) = c.ip R₀ (X k) - c.ip R₀ (proj H (X k))
    --                            = 0 - 0 = 0.
    have hR₀_tilde : c.ip R₀ (c.tildeX H (X k)) = 0 := by
      -- tildeX H (X k) = X k + (- proj H (X k))
      have hsplit : c.tildeX H (X k) = X k + (- c.proj H (X k)) := by
        simp [tildeX_eq, sub_eq_add_neg]
      rw [hsplit, c.ip_add_right]
      have h2 : c.ip R₀ (-c.proj H (X k)) = - c.ip R₀ (c.proj H (X k)) := by
        have heq : (-c.proj H (X k) : R → ℝ) = (-1 : ℝ) • c.proj H (X k) := by
          ext s; simp
        rw [heq, c.ip_smul_right]; ring
      rw [h_orth_X k, h2, h_orth_H (c.proj H (X k)) (c.proj_mem H (X k))]; ring
    -- Now expand c.ip R₀ (tildeX H (X k)) using bilinearity.
    have h_expand : c.ip R₀ (c.tildeX H (X k))
        = c.ip Y (c.tildeX H (X k))
          - ∑ j, β j * c.ip (X j) (c.tildeX H (X k))
          - c.ip α (c.tildeX H (X k)) := by
      have hR₀_split : R₀ = Y - (∑ j, β j • X j) - α := hR₀_def
      have hsubeq : Y - (∑ j, β j • X j) - α
          = Y + (-(∑ j, β j • X j)) + (-α) := by ext s; simp [sub_eq_add_neg]
      rw [hR₀_split, hsubeq]
      rw [c.ip_add_left, c.ip_add_left]
      -- Term 1: c.ip Y (tildeX H (X k))
      -- Term 2: c.ip (-(∑ j, β j • X j)) (tildeX H (X k))
      --       = -c.ip (∑ j, β j • X j) (tildeX H (X k))
      --       = -∑ j, β j * c.ip (X j) (tildeX H (X k))
      -- Term 3: c.ip (-α) (tildeX H (X k)) = -c.ip α (tildeX H (X k))
      have hneg_sum : c.ip (-(∑ j, β j • X j)) (c.tildeX H (X k))
          = -∑ j, β j * c.ip (X j) (c.tildeX H (X k)) := by
        have heq : (-(∑ j, β j • X j) : R → ℝ) = (-1 : ℝ) • (∑ j, β j • X j) := by
          ext s; simp
        rw [heq, c.ip_smul_left, c.ip_sum_left]
        have hinner : ∀ j, c.ip (β j • X j) (c.tildeX H (X k))
            = β j * c.ip (X j) (c.tildeX H (X k)) := by
          intro j; rw [c.ip_smul_left]
        rw [Finset.sum_congr rfl (fun j _ => hinner j)]
        ring
      have hneg_α : c.ip (-α) (c.tildeX H (X k)) = -c.ip α (c.tildeX H (X k)) := by
        have : (-α : R → ℝ) = (-1 : ℝ) • α := by ext s; simp
        rw [this, c.ip_smul_left]; ring
      rw [hneg_sum, hneg_α]; ring
    -- c.ip α (tildeX H (X k)) = 0 because tildeX ⊥ H and α ∈ H.
    have hα_tilde : c.ip α (c.tildeX H (X k)) = 0 := by
      rw [c.ip_symm]
      exact c.residualize_in_orthogonal H (X k) hα
    -- c.ip (X j) (tildeX H (X k)) = c.ip (tildeX H (X j)) (tildeX H (X k)).
    have hX_tilde : ∀ j, c.ip (X j) (c.tildeX H (X k))
        = c.ip (c.tildeX H (X j)) (c.tildeX H (X k)) := by
      intro j
      rw [c.ip_symm (X j), c.ip_symm (c.tildeX H (X j))]
      exact c.ip_tildeX_eq_ip_tildeX_residual H X (X j) k
    -- c.ip Y (tildeX H (X k)) = c.ip (tildeX H (X k)) Y.
    have hY_symm : c.ip Y (c.tildeX H (X k)) = c.ip (c.tildeX H (X k)) Y :=
      c.ip_symm _ _
    -- Substitute everything into h_expand combined with hR₀_tilde = 0.
    rw [hα_tilde, sub_zero] at h_expand
    rw [hY_symm] at h_expand
    have : ∑ j, β j * c.ip (X j) (c.tildeX H (X k))
        = ∑ j, β j * c.ip (c.tildeX H (X j)) (c.tildeX H (X k)) := by
      refine Finset.sum_congr rfl ?_
      intro j _; rw [hX_tilde j]
    rw [this] at h_expand
    linarith [hR₀_tilde]
  -- Step 4: convert h_normal to `Q_XX.mulVec β = rhsVec`.
  have hmat : (Q_XX c X H).mulVec β = rhsVec c X H Y := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Q_XX_apply, rhsVec_apply]
    -- dotProduct: ∑ j, Q_XX k j * β j = ∑ j, c.ip (tildeX (X k)) (tildeX (X j)) * β j
    have hk := h_normal k
    -- h_normal: ∑ j, β j * c.ip (tildeX (X j)) (tildeX (X k)) = c.ip (tildeX (X k)) Y.
    -- Need: ∑ j, c.ip (tildeX (X k)) (tildeX (X j)) * β j = c.ip (tildeX (X k)) Y.
    -- These match by symmetry of c.ip and commutativity of multiplication.
    rw [← hk]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [c.ip_symm (c.tildeX H (X k)) (c.tildeX H (X j))]
    ring
  -- Step 5: β = Q_XX⁻¹ (Q_XX β) = Q_XX⁻¹ rhsVec = thetaHat.
  unfold thetaHat
  have : (Q_XX c X H)⁻¹.mulVec ((Q_XX c X H).mulVec β)
      = (Q_XX c X H)⁻¹.mulVec (rhsVec c X H Y) := by
    rw [hmat]
  rw [Matrix.mulVec_mulVec] at this
  rw [Matrix.nonsing_inv_mul _ hRank, Matrix.one_mulVec] at this
  exact this

end WeightedSupport
end Panel.Weighted
end Causalean
