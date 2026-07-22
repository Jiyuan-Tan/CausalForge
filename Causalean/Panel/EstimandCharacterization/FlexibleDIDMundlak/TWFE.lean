/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Wooldridge scalar TWFE and two-way Mundlak equivalence

Finite balanced-panel, scalar-regressor version of Wooldridge's TWFE /
two-way Mundlak equivalence. Vector-regressor TWFE and Mundlak variants live in
the sibling vector files.
-/

import Causalean.Panel.UniformTwoWayPanel

/-! # Wooldridge Scalar TWFE and Mundlak

This file formalizes the scalar-regressor finite balanced-panel version of
Wooldridge's two-way fixed effects and two-way Mundlak equivalence. It defines
the scalar TWFE problem, coefficient, and normal equation, proves
`ScalarTWFEProblem.betaTWFE_normalEq` and `ScalarTWFEProblem.betaTWFE_unique`, and
then proves `twfe_twm_equivalence` and
`twfe_twm_optional_controls_invariant` for coding-free two-way Mundlak fits. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace FlexibleDIDMundlak

open Finset
open UniformTwoWayPanel

variable {Unit Time : Type*} [Fintype Unit] [Fintype Time]

/-- Scalar TWFE problem on a finite balanced panel. The positivity field is
the scalar full-rank condition corresponding to nonsingularity of
`Q_{\ddot X}` in the source. -/
structure ScalarTWFEProblem (Unit Time : Type*) [Fintype Unit] [Fintype Time] where
  panel : BalancedPanel Unit Time
  Y : Unit → Time → ℝ
  X : Unit → Time → ℝ
  ddotX_ss_pos : 0 < ∑ i, ∑ t, (ddot X i t)^2

namespace ScalarTWFEProblem

/-- Residualized-design denominator for scalar TWFE. -/
noncomputable def twfeDenominator (P : ScalarTWFEProblem Unit Time) : ℝ :=
  ∑ i, ∑ t, (ddot P.X i t)^2

/-- Residualized numerator using double-demeaned outcome and regressor. -/
noncomputable def twfeNumerator (P : ScalarTWFEProblem Unit Time) : ℝ :=
  ∑ i, ∑ t, ddot P.X i t * ddot P.Y i t

/-- Population scalar TWFE coefficient from the double-demeaned normal
equation. -/
noncomputable def betaTWFE (P : ScalarTWFEProblem Unit Time) : ℝ :=
  P.twfeNumerator / P.twfeDenominator

/-- Scalar TWFE normal equation after double demeaning. -/
def twfeNormalEq (P : ScalarTWFEProblem Unit Time) (β : ℝ) : Prop :=
  ∑ i, ∑ t, ddot P.X i t * (ddot P.Y i t - ddot P.X i t * β) = 0

/-- The closed-form coefficient satisfies the scalar TWFE normal equation by
dividing through the positive residualized sum of squares. -/
theorem betaTWFE_normalEq (P : ScalarTWFEProblem Unit Time) :
    P.twfeNormalEq P.betaTWFE := by
  let A : ℝ := ∑ i, ∑ t, ddot P.X i t * ddot P.Y i t
  let B : ℝ := ∑ i, ∑ t, (ddot P.X i t)^2
  have hden : B ≠ 0 := by
    dsimp [B]
    exact ne_of_gt P.ddotX_ss_pos
  have hfactor : ∀ c : ℝ,
      (∑ i, ∑ t, ddot P.X i t * (ddot P.X i t * c)) = B * c := by
    intro c
    dsimp [B]
    simp only [← mul_assoc, pow_two, Finset.sum_mul]
  unfold twfeNormalEq betaTWFE twfeNumerator twfeDenominator
  change
    ∑ i, ∑ t, ddot P.X i t *
      (ddot P.Y i t - ddot P.X i t * (A / B)) = 0
  calc
    ∑ i, ∑ t, ddot P.X i t *
        (ddot P.Y i t - ddot P.X i t * (A / B))
        = A - B * (A / B) := by
          dsimp [A]
          simp only [mul_sub, Finset.sum_sub_distrib]
          rw [hfactor]
    _ = 0 := by
          rw [div_eq_mul_inv]
          rw [show B * (A * B⁻¹) = A * (B * B⁻¹) by
            ring]
          rw [mul_inv_cancel₀ hden]
          ring

/-- Scalar full-rank uniqueness of the TWFE normal-equation solution. -/
theorem betaTWFE_unique (P : ScalarTWFEProblem Unit Time) {β : ℝ}
    (hβ : P.twfeNormalEq β) :
    β = P.betaTWFE := by
  unfold twfeNormalEq at hβ
  change β =
    (∑ i, ∑ t, ddot P.X i t * ddot P.Y i t) /
      (∑ i, ∑ t, (ddot P.X i t)^2)
  have hden : (∑ i, ∑ t, (ddot P.X i t)^2) ≠ 0 := ne_of_gt P.ddotX_ss_pos
  have hnormal :
      (∑ i, ∑ t, ddot P.X i t * ddot P.Y i t) -
          (∑ i, ∑ t, (ddot P.X i t)^2) * β = 0 := by
    calc
      (∑ i, ∑ t, ddot P.X i t * ddot P.Y i t) -
          (∑ i, ∑ t, (ddot P.X i t)^2) * β
          = ∑ i, ∑ t, ddot P.X i t *
              (ddot P.Y i t - ddot P.X i t * β) := by
            simp only [mul_sub, Finset.sum_sub_distrib]
            ring_nf
            simp only [pow_two, Finset.sum_mul]
            simp [mul_comm]
      _ = 0 := hβ
  have hnum : (∑ i, ∑ t, ddot P.X i t * ddot P.Y i t) =
      (∑ i, ∑ t, (ddot P.X i t)^2) * β := sub_eq_zero.mp hnormal
  calc
    β = ((∑ i, ∑ t, (ddot P.X i t)^2) * β) /
        (∑ i, ∑ t, (ddot P.X i t)^2) := by
          rw [div_eq_mul_inv]
          rw [show
            ((∑ i, ∑ t, (ddot P.X i t)^2) * β) *
                (∑ i, ∑ t, (ddot P.X i t)^2)⁻¹ =
              β * ((∑ i, ∑ t, (ddot P.X i t)^2) *
                (∑ i, ∑ t, (ddot P.X i t)^2)⁻¹) by
            ring]
          rw [mul_inv_cancel₀ hden, mul_one]
    _ = (∑ i, ∑ t, ddot P.X i t * ddot P.Y i t) /
        (∑ i, ∑ t, (ddot P.X i t)^2) := by
          rw [← hnum]

end ScalarTWFEProblem

variable {Z M : Type*} [Fintype Z] [Fintype M]

/-- Two-way Mundlak nuisance span for a scalar regressor: constants, unit
means of `X`, time means of `X`, optional time-constant controls `Z_i`, and
optional time-only controls `M_t`. -/
def IsTwoWayMundlakNuisance (X : Unit → Time → ℝ)
    (Zvar : Z → Unit → ℝ) (Mvar : M → Time → ℝ)
    (h : Unit → Time → ℝ) : Prop :=
  ∃ c γu γt : ℝ, ∃ ζ : Z → ℝ, ∃ μ : M → ℝ,
    ∀ i t,
      h i t =
        c + γu * unitMean X i + γt * timeMean X t
          + (∑ z, ζ z * Zvar z i) + (∑ m, μ m * Mvar m t)

/-- Mundlak nuisance functions are unit/time additive, so optional
time-constant and time-only controls lie inside the same orthogonality class. -/
theorem mundlak_nuisance_unit_time
    (X : Unit → Time → ℝ) (Zvar : Z → Unit → ℝ) (Mvar : M → Time → ℝ)
    {h : Unit → Time → ℝ}
    (hh : IsTwoWayMundlakNuisance X Zvar Mvar h) :
    IsUnitTimeAdditive h := by
  rcases hh with ⟨c, γu, γt, ζ, μ, hrep⟩
  refine ⟨fun i => c + γu * unitMean X i + ∑ z, ζ z * Zvar z i,
    fun t => γt * timeMean X t + ∑ m, μ m * Mvar m t, ?_⟩
  intro i t
  rw [hrep i t]
  ring

/-- A scalar two-way Mundlak fit, stated by normal equations rather than by a
particular coding of the nuisance regressors. -/
structure ScalarTWMFit (P : ScalarTWFEProblem Unit Time)
    (Zvar : Z → Unit → ℝ) (Mvar : M → Time → ℝ) where
  beta : ℝ
  nuisance : Unit → Time → ℝ
  nuisance_mem : IsTwoWayMundlakNuisance P.X Zvar Mvar nuisance
  normal_X :
    ∑ i, ∑ t, P.X i t * (P.Y i t - P.X i t * beta - nuisance i t) = 0
  normal_H :
    ∀ h : Unit → Time → ℝ, IsTwoWayMundlakNuisance P.X Zvar Mvar h →
      ∑ i, ∑ t, h i t * (P.Y i t - P.X i t * beta - nuisance i t) = 0

/-- Residualizing the scalar regressor against the two-way Mundlak nuisance
span leaves the same residual as double demeaning. -/
theorem twfe_twm_residual_common (P : ScalarTWFEProblem Unit Time)
    (Zvar : Z → Unit → ℝ) (Mvar : M → Time → ℝ) :
    IsUnitTimeAdditive (fun i t => P.X i t - ddot P.X i t) ∧
      (∀ h : Unit → Time → ℝ, IsTwoWayMundlakNuisance P.X Zvar Mvar h →
        inner (ddot P.X) h = 0) := by
  constructor
  · rw [show (fun i t => P.X i t - ddot P.X i t) = unitTimeProjection P.X by
        funext i t
        exact sub_ddot_eq_unitTimeProjection P.X i t]
    exact unitTimeProjection_additive P.X
  · intro h hh
    exact ddot_orthogonal_unit_time P.panel P.X h
      (mundlak_nuisance_unit_time P.X Zvar Mvar hh)

/-- Wooldridge finite-panel scalar TWFE--two-way Mundlak equivalence. The
full-rank side condition is `P.ddotX_ss_pos`; the fit carries the population
normal equations for the pooled Mundlak regression. -/
theorem twfe_twm_equivalence (P : ScalarTWFEProblem Unit Time)
    (Zvar : Z → Unit → ℝ) (Mvar : M → Time → ℝ)
    (fit : ScalarTWMFit P Zvar Mvar) :
    fit.beta = P.betaTWFE := by
  let hres : Unit → Time → ℝ := fun i t => P.X i t - ddot P.X i t
  have hres_mem : IsTwoWayMundlakNuisance P.X Zvar Mvar hres := by
    refine ⟨-grandMean P.X, 1, 1, fun _ => 0, fun _ => 0, ?_⟩
    intro i t
    dsimp [hres]
    rw [sub_ddot_eq_unitTimeProjection P.X i t]
    unfold unitTimeProjection
    simp
    ring
  have hYadd : IsUnitTimeAdditive (fun i t => P.Y i t - ddot P.Y i t) := by
    rw [show (fun i t => P.Y i t - ddot P.Y i t) = unitTimeProjection P.Y by
        funext i t
        exact sub_ddot_eq_unitTimeProjection P.Y i t]
    exact unitTimeProjection_additive P.Y
  have hYorth :
      ∑ i, ∑ t, ddot P.X i t * (P.Y i t - ddot P.Y i t) = 0 := by
    simpa [inner] using ddot_orthogonal_unit_time P.panel P.X
      (fun i t => P.Y i t - ddot P.Y i t) hYadd
  have hfw := finite_residualized_coefficient_eq_of_normalEqs
    (fun h : Unit → Time → ℝ => IsTwoWayMundlakNuisance P.X Zvar Mvar h)
    (Y := P.Y) (D := P.X)
    (Yproj := fun i t => P.Y i t - ddot P.Y i t)
    (Ytilde := ddot P.Y)
    (Dproj := hres) (Dtilde := ddot P.X) (Hβ := fit.nuisance)
    (β := fit.beta)
    (by
      intro i t
      ring)
    (by
      intro i t
      dsimp [hres]
      ring)
    hres_mem
    fit.nuisance_mem
    (twfe_twm_residual_common P Zvar Mvar).2
    (by simpa [inner] using hYorth)
    (by simpa [inner, pow_two] using P.ddotX_ss_pos)
    (by simpa [inner] using fit.normal_X)
    (by
      intro h hh
      simpa [inner] using fit.normal_H h hh)
  simpa [ScalarTWFEProblem.betaTWFE, ScalarTWFEProblem.twfeNumerator,
    ScalarTWFEProblem.twfeDenominator, finiteResidualizedCoefficient, inner,
    pow_two]
    using hfw

/-- Adding or removing optional time-constant or time-only controls does not
change the scalar coefficient, because both fits equal the TWFE coefficient. -/
theorem twfe_twm_optional_controls_invariant
    {Z₁ M₁ Z₂ M₂ : Type*} [Fintype Z₁] [Fintype M₁] [Fintype Z₂] [Fintype M₂]
    (P : ScalarTWFEProblem Unit Time)
    (Zvar₁ : Z₁ → Unit → ℝ) (Mvar₁ : M₁ → Time → ℝ)
    (Zvar₂ : Z₂ → Unit → ℝ) (Mvar₂ : M₂ → Time → ℝ)
    (fit₁ : ScalarTWMFit P Zvar₁ Mvar₁)
    (fit₂ : ScalarTWMFit P Zvar₂ Mvar₂) :
    fit₁.beta = fit₂.beta := by
  rw [twfe_twm_equivalence P Zvar₁ Mvar₁ fit₁,
    twfe_twm_equivalence P Zvar₂ Mvar₂ fit₂]

end FlexibleDIDMundlak
end Panel.EstimandCharacterization
end Causalean
