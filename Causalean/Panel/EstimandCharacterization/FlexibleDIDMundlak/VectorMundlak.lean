/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Wooldridge vector (K-regressor) two-way Mundlak equivalence

Extends the scalar `twfe_twm_equivalence` to the K-vector regressor case: the
matrix Frisch-Waugh-Lovell handoff `matrix_fwl_eq_of_normalEqs` (generalizing
`UniformTwoWayPanel.finite_residualized_coefficient_eq_of_normalEqs`), the
vector two-way Mundlak nuisance span, the coding-free vector Mundlak fit, and
the equivalence theorem `vec_twfe_twm_equivalence` (Wooldridge 2021, Theorem A,
full K-vector form). The full-rank side condition is `IsUnit (gram X).det`.
-/

import Causalean.Panel.EstimandCharacterization.FlexibleDIDMundlak.VectorTWFE

/-! # Wooldridge Vector Mundlak Equivalence

This file extends the finite balanced-panel Mundlak equivalence from one
regressor to a finite vector of regressors.  It defines the generic residualized
`gramOf` and `numerOf`, proves the matrix Frisch-Waugh-Lovell handoff
`matrix_fwl_eq_of_normalEqs`, introduces the vector two-way Mundlak nuisance span
and fit, and proves `vec_twfe_twm_equivalence` together with the optional-control
invariance theorem `vec_twfe_twm_optional_controls_invariant`. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace FlexibleDIDMundlak

open Finset
open UniformTwoWayPanel

variable {Unit Time : Type*} [Fintype Unit] [Fintype Time]
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Generic residualized Gram matrix of a supplied residualized regressor. -/
noncomputable def gramOf (Dt : Unit → Time → K → ℝ) : Matrix K K ℝ :=
  fun j k => ∑ i, ∑ t, Dt i t j * Dt i t k

/-- Generic residualized numerator vector. -/
noncomputable def numerOf (Dt : Unit → Time → K → ℝ) (Yt : Unit → Time → ℝ) : K → ℝ :=
  fun k => ∑ i, ∑ t, Dt i t k * Yt i t

omit [Fintype K] [DecidableEq K] in
/-- `gram` is the residualized instance of the generic version. -/
theorem gram_eq_gramOf (X : Unit → Time → K → ℝ) : gram X = gramOf (ddotVec X) := rfl

omit [Fintype K] [DecidableEq K] in
/-- `numer` is the residualized instance of the generic version. -/
theorem numer_eq_numerOf (X : Unit → Time → K → ℝ) (Y : Unit → Time → ℝ) :
    numer X Y = numerOf (ddotVec X) (ddot Y) := rfl

omit [DecidableEq K] in
/-- Reshuffle: a residualized regressor against a `β`-combination of regressors
factors through the cross-Gram. -/
theorem sum_dotRegressor (Dt D : Unit → Time → K → ℝ) (β : K → ℝ) (k : K) :
    (∑ i, ∑ t, Dt i t k * (∑ j, D i t j * β j))
      = ∑ j, (∑ i, ∑ t, Dt i t k * D i t j) * β j := by
  calc ∑ i, ∑ t, Dt i t k * (∑ j, D i t j * β j)
      = ∑ i, ∑ t, ∑ j, Dt i t k * D i t j * β j := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun t _ => ?_))
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
    _ = ∑ i, ∑ j, ∑ t, Dt i t k * D i t j * β j := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, ∑ t, Dt i t k * D i t j * β j := by
        rw [Finset.sum_comm]
    _ = ∑ j, (∑ i, ∑ t, Dt i t k * D i t j) * β j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]

/-- Matrix Frisch-Waugh-Lovell handoff. If a coefficient vector `β` and nuisance
term `Hβ` satisfy the finite normal equations against the raw vector regressor
`D` and a nuisance class `H`, while each coordinate of the residualized regressor
`Dtilde` is orthogonal to `H` and the residualized Gram matrix is nonsingular,
then `β` is the residualized matrix coefficient. -/
theorem matrix_fwl_eq_of_normalEqs
    (H : (Unit → Time → ℝ) → Prop)
    {Y Yproj Ytilde : Unit → Time → ℝ}
    {D Dproj Dtilde : Unit → Time → K → ℝ}
    {Hβ : Unit → Time → ℝ} {β : K → ℝ}
    (hY : ∀ i t, Y i t = Yproj i t + Ytilde i t)
    (hD : ∀ i t k, D i t k = Dproj i t k + Dtilde i t k)
    (hDproj_mem : ∀ k, H (fun i t => Dproj i t k))
    (hHβ_mem : H Hβ)
    (hDtilde_orth : ∀ k, ∀ h : Unit → Time → ℝ, H h →
      (∑ i, ∑ t, Dtilde i t k * h i t) = 0)
    (hYproj_orth : ∀ k, (∑ i, ∑ t, Dtilde i t k * Yproj i t) = 0)
    (hgram_unit : IsUnit (gramOf Dtilde).det)
    (h_normal_D : ∀ k, (∑ i, ∑ t, D i t k *
        (Y i t - (∑ j, D i t j * β j) - Hβ i t)) = 0)
    (h_normal_H : ∀ h : Unit → Time → ℝ, H h → (∑ i, ∑ t, h i t *
        (Y i t - (∑ j, D i t j * β j) - Hβ i t)) = 0) :
    β = (gramOf Dtilde)⁻¹.mulVec (numerOf Dtilde Ytilde) := by
  -- residual `e`
  set e : Unit → Time → ℝ :=
    fun i t => Y i t - (∑ j, D i t j * β j) - Hβ i t with he
  -- step 1: each residualized coordinate is orthogonal to the residual
  have hDt_e : ∀ k, (∑ i, ∑ t, Dtilde i t k * e i t) = 0 := by
    intro k
    have h1 : (∑ i, ∑ t, D i t k * e i t) = 0 := h_normal_D k
    have h2 : (∑ i, ∑ t, Dproj i t k * e i t) = 0 := h_normal_H _ (hDproj_mem k)
    have hsplit : (∑ i, ∑ t, D i t k * e i t)
        = (∑ i, ∑ t, Dproj i t k * e i t) + (∑ i, ∑ t, Dtilde i t k * e i t) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [hD i t k]; ring
    linarith [h1, h2, hsplit]
  -- step 2: expand the orthogonality into the matrix normal equation
  have hexp : ∀ k, (∑ i, ∑ t, Dtilde i t k * e i t)
      = numerOf Dtilde Ytilde k - (gramOf Dtilde).mulVec β k := by
    intro k
    have hmv : (gramOf Dtilde).mulVec β k
        = ∑ j, (∑ i, ∑ t, Dtilde i t k * Dtilde i t j) * β j := by
      simp only [Matrix.mulVec, dotProduct, gramOf]
    -- cellwise split of `Dtilde·k * e`
    have hcell : ∀ i t, Dtilde i t k * e i t
        = Dtilde i t k * Yproj i t + Dtilde i t k * Ytilde i t
          - Dtilde i t k * (∑ j, D i t j * β j) - Dtilde i t k * Hβ i t := by
      intro i t
      simp only [he]
      rw [hY i t]; ring
    have hsum4 : (∑ i, ∑ t, Dtilde i t k * e i t)
        = (∑ i, ∑ t, Dtilde i t k * Yproj i t)
          + (∑ i, ∑ t, Dtilde i t k * Ytilde i t)
          - (∑ i, ∑ t, Dtilde i t k * (∑ j, D i t j * β j))
          - (∑ i, ∑ t, Dtilde i t k * Hβ i t) := by
      have hcong : (∑ i, ∑ t, Dtilde i t k * e i t)
          = ∑ i, ∑ t, (Dtilde i t k * Yproj i t + Dtilde i t k * Ytilde i t
              - Dtilde i t k * (∑ j, D i t j * β j) - Dtilde i t k * Hβ i t) :=
        Finset.sum_congr rfl (fun i _ =>
          Finset.sum_congr rfl (fun t _ => hcell i t))
      rw [hcong]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    -- the `D·β` cross term factors through the residualized Gram (cross terms vanish)
    have hDj : ∀ j, (∑ i, ∑ t, Dtilde i t k * D i t j)
        = ∑ i, ∑ t, Dtilde i t k * Dtilde i t j := by
      intro j
      have horth : (∑ i, ∑ t, Dtilde i t k * Dproj i t j) = 0 :=
        hDtilde_orth k (fun i t => Dproj i t j) (hDproj_mem j)
      calc (∑ i, ∑ t, Dtilde i t k * D i t j)
          = (∑ i, ∑ t, Dtilde i t k * Dproj i t j)
            + (∑ i, ∑ t, Dtilde i t k * Dtilde i t j) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [hD i t j]; ring
        _ = ∑ i, ∑ t, Dtilde i t k * Dtilde i t j := by rw [horth]; ring
    have hjsum : (∑ j, (∑ i, ∑ t, Dtilde i t k * D i t j) * β j)
        = ∑ j, (∑ i, ∑ t, Dtilde i t k * Dtilde i t j) * β j :=
      Finset.sum_congr rfl (fun j _ => by rw [hDj j])
    rw [hsum4, hmv, hYproj_orth k, hDtilde_orth k Hβ hHβ_mem,
      sum_dotRegressor Dtilde D β k, hjsum]
    unfold numerOf
    ring
  -- assemble: gramOf.mulVec β = numerOf
  have hmatrix : (gramOf Dtilde).mulVec β = numerOf Dtilde Ytilde := by
    funext k
    have := hexp k
    rw [hDt_e k] at this
    linarith [this]
  -- invert
  rw [← hmatrix, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hgram_unit,
    Matrix.one_mulVec]

variable {Z M : Type*} [Fintype Z] [Fintype M]

/-- Two-way Mundlak nuisance span for a K-vector regressor: constants, the unit
means and time means of every coordinate of `X`, optional time-constant controls
`Z_i`, and optional time-only controls `M_t`. -/
def IsVectorTwoWayMundlakNuisance (X : Unit → Time → K → ℝ)
    (Zvar : Z → Unit → ℝ) (Mvar : M → Time → ℝ) (h : Unit → Time → ℝ) : Prop :=
  ∃ c : ℝ, ∃ γu γt : K → ℝ, ∃ ζ : Z → ℝ, ∃ μ : M → ℝ,
    ∀ i t, h i t = c
      + (∑ k, γu k * unitMean (fun i t => X i t k) i)
      + (∑ k, γt k * timeMean (fun i t => X i t k) t)
      + (∑ z, ζ z * Zvar z i) + (∑ m, μ m * Mvar m t)

omit [DecidableEq K] in
/-- Vector two-way Mundlak nuisance terms are unit/time additive, so the optional
controls lie inside the same orthogonality class as for the scalar case. -/
theorem vector_mundlak_nuisance_unit_time
    (X : Unit → Time → K → ℝ) (Zvar : Z → Unit → ℝ) (Mvar : M → Time → ℝ)
    {h : Unit → Time → ℝ}
    (hh : IsVectorTwoWayMundlakNuisance X Zvar Mvar h) :
    IsUnitTimeAdditive h := by
  rcases hh with ⟨c, γu, γt, ζ, μ, hrep⟩
  refine ⟨fun i => c + (∑ k, γu k * unitMean (fun i t => X i t k) i)
      + ∑ z, ζ z * Zvar z i,
    fun t => (∑ k, γt k * timeMean (fun i t => X i t k) t)
      + ∑ m, μ m * Mvar m t, ?_⟩
  intro i t
  rw [hrep i t]; ring

/-- Selecting a single coordinate via a `0/1` indicator collapses the coordinate
sum to that coordinate's value. -/
theorem sum_ite_one_mul (k : K) (f : K → ℝ) :
    (∑ k', (if k' = k then (1 : ℝ) else 0) * f k') = f k := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- A coding-free K-vector two-way Mundlak fit: a coefficient vector, a nuisance
function in the Mundlak span, and the pooled normal equations against each
regressor coordinate and against the nuisance span. -/
structure VectorTWMFit (P : VectorTWFEProblem Unit Time K)
    (Zvar : Z → Unit → ℝ) (Mvar : M → Time → ℝ) where
  beta : K → ℝ
  nuisance : Unit → Time → ℝ
  nuisance_mem : IsVectorTwoWayMundlakNuisance P.X Zvar Mvar nuisance
  normal_X :
    ∀ k, (∑ i, ∑ t, P.X i t k *
      (P.Y i t - (∑ j, P.X i t j * beta j) - nuisance i t)) = 0
  normal_H :
    ∀ h : Unit → Time → ℝ, IsVectorTwoWayMundlakNuisance P.X Zvar Mvar h →
      (∑ i, ∑ t, h i t *
        (P.Y i t - (∑ j, P.X i t j * beta j) - nuisance i t)) = 0

/-- Wooldridge finite-panel **K-vector** TWFE--two-way Mundlak equivalence. Under
the residualized-Gram nonsingularity `P.gram_unit`, the pooled two-way Mundlak
coefficient on `X` equals the K-vector TWFE coefficient (Theorem A, full vector
form). -/
theorem vec_twfe_twm_equivalence (P : VectorTWFEProblem Unit Time K)
    (Zvar : Z → Unit → ℝ) (Mvar : M → Time → ℝ)
    (fit : VectorTWMFit P Zvar Mvar) :
    fit.beta = P.betaTWFE := by
  -- decompositions
  have hY : ∀ i t, P.Y i t = (P.Y i t - ddot P.Y i t) + ddot P.Y i t := by
    intro i t; ring
  have hD : ∀ i t k, P.X i t k
      = unitTimeProjection (fun i t => P.X i t k) i t + ddotVec P.X i t k := by
    intro i t k
    have h := sub_ddot_eq_unitTimeProjection (fun i t => P.X i t k) i t
    simp only [ddotVec]
    linarith [h]
  -- the unit/time projection of each coordinate lies in the Mundlak span
  have hDproj_mem : ∀ k, IsVectorTwoWayMundlakNuisance P.X Zvar Mvar
      (fun i t => unitTimeProjection (fun i t => P.X i t k) i t) := by
    intro k
    refine ⟨-grandMean (fun i t => P.X i t k),
      fun k' => if k' = k then 1 else 0, fun k' => if k' = k then 1 else 0,
      fun _ => 0, fun _ => 0, ?_⟩
    intro i t
    unfold unitTimeProjection
    rw [sum_ite_one_mul k (fun k' => unitMean (fun i t => P.X i t k') i),
      sum_ite_one_mul k (fun k' => timeMean (fun i t => P.X i t k') t)]
    simp only [zero_mul, Finset.sum_const_zero]
    ring
  -- residualized coordinates are orthogonal to the (additive) Mundlak span
  have hDtilde_orth : ∀ k, ∀ h : Unit → Time → ℝ,
      IsVectorTwoWayMundlakNuisance P.X Zvar Mvar h →
      (∑ i, ∑ t, ddotVec P.X i t k * h i t) = 0 := by
    intro k h hh
    have hadd : IsUnitTimeAdditive h :=
      vector_mundlak_nuisance_unit_time P.X Zvar Mvar hh
    have hortho := ddot_orthogonal_unit_time P.panel (fun i t => P.X i t k) h hadd
    simpa [inner, ddotVec] using hortho
  have hYproj_orth : ∀ k,
      (∑ i, ∑ t, ddotVec P.X i t k * (P.Y i t - ddot P.Y i t)) = 0 := by
    intro k
    have hadd : IsUnitTimeAdditive (fun i t => P.Y i t - ddot P.Y i t) := by
      rw [show (fun i t => P.Y i t - ddot P.Y i t) = unitTimeProjection P.Y from
          funext fun i => funext fun t => sub_ddot_eq_unitTimeProjection P.Y i t]
      exact unitTimeProjection_additive P.Y
    have hortho := ddot_orthogonal_unit_time P.panel (fun i t => P.X i t k)
      (fun i t => P.Y i t - ddot P.Y i t) hadd
    simpa [inner, ddotVec] using hortho
  -- apply the matrix FWL handoff
  have hfwl := matrix_fwl_eq_of_normalEqs
    (H := IsVectorTwoWayMundlakNuisance P.X Zvar Mvar)
    (Y := P.Y) (Yproj := fun i t => P.Y i t - ddot P.Y i t) (Ytilde := ddot P.Y)
    (D := P.X) (Dproj := fun i t k => unitTimeProjection (fun i t => P.X i t k) i t)
    (Dtilde := ddotVec P.X) (Hβ := fit.nuisance) (β := fit.beta)
    hY hD hDproj_mem fit.nuisance_mem hDtilde_orth hYproj_orth
    (by rw [← gram_eq_gramOf]; exact P.gram_unit)
    fit.normal_X fit.normal_H
  rw [hfwl]
  rfl

/-- Adding or removing optional time-constant or time-only controls does not
change the K-vector Mundlak coefficient, since both fits equal the vector TWFE
coefficient. -/
theorem vec_twfe_twm_optional_controls_invariant
    {Z₁ M₁ Z₂ M₂ : Type*} [Fintype Z₁] [Fintype M₁] [Fintype Z₂] [Fintype M₂]
    (P : VectorTWFEProblem Unit Time K)
    (Zvar₁ : Z₁ → Unit → ℝ) (Mvar₁ : M₁ → Time → ℝ)
    (Zvar₂ : Z₂ → Unit → ℝ) (Mvar₂ : M₂ → Time → ℝ)
    (fit₁ : VectorTWMFit P Zvar₁ Mvar₁)
    (fit₂ : VectorTWMFit P Zvar₂ Mvar₂) :
    fit₁.beta = fit₂.beta := by
  rw [vec_twfe_twm_equivalence P Zvar₁ Mvar₁ fit₁,
    vec_twfe_twm_equivalence P Zvar₂ Mvar₂ fit₂]

end FlexibleDIDMundlak
end Panel.EstimandCharacterization
end Causalean
