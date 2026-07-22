/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Panel.EstimandCharacterization.HeterogeneousTWFE.FinitePanel
import Causalean.Panel.UniformTwoWayPanel

/-!
# DCDH residualized treatment as a derived FWL residual

`FinitePanel.lean` takes the residualized treatment `D̃` as a *primitive
orthogonality witness*: it merely posits the membership `D − D̃ ∈ H_GT`, the
orthogonality `∑ π D̃ h = 0`, and positivity `S_D > 0`.  The paper, however,
*derives* `D̃` as the Frisch–Waugh–Lovell residual of the treatment projected on
the two-way fixed-effect span — i.e. the double-demeaned treatment `D̈`.

This file verifies, for the uniform balanced panel, that the DCDH residualized
treatment can be constructed from the usual two-way fixed-effect residual. It
builds a genuine `DCDHPanel` whose `Dtilde` is the double-demeaned treatment
`UniformTwoWayPanel.ddot D`, with the membership and orthogonality fields
*proved* from `UniformTwoWayPanel` (`sub_ddot_eq_unitTimeProjection`,
`unitTimeProjection_additive`, `ddot_orthogonal_unit_time`) rather than assumed.

Only `S_D > 0` (nonzero double-demeaned treatment variation — the genuine
identification input that the treatment is not collinear with the FE span) and
the binary-treatment / consistency primitives remain as hypotheses, exactly as
in the source.  No measure theory is used: the construction is pure uniform
finite-panel algebra.
-/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace HeterogeneousTWFE

open Finset
open UniformTwoWayPanel (ddot unitMean timeMean grandMean inner finiteResidualizedCoefficient)

variable {G T : Type*} [Fintype G] [Fintype T]

/-- Uniform unit-period cell weight `1/(|G|·|T|)`. -/
noncomputable def uniformWeight (G T : Type*) [Fintype G] [Fintype T] : ℝ :=
  ((Fintype.card G : ℝ) * (Fintype.card T : ℝ))⁻¹

/-- In a balanced panel with at least two groups and periods, the uniform
unit-period cell weight is strictly positive. -/
theorem uniformWeight_pos (balanced : UniformTwoWayPanel.BalancedPanel G T) :
    0 < uniformWeight G T := by
  have hG : (0 : ℝ) < (Fintype.card G : ℝ) :=
    by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) balanced.unit_card_ge_two
  have hT : (0 : ℝ) < (Fintype.card T : ℝ) :=
    by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) balanced.time_card_ge_two
  exact inv_pos.mpr (mul_pos hG hT)

/-- Builds the uniform balanced-panel DCDH structure whose residualized treatment
is the Frisch-Waugh-Lovell double-demeaned treatment.

Builds a genuine `DCDHPanel` for the uniform balanced panel in which the
residualized treatment is the double-demeaned treatment `D̈ = ddot D`.  The
`D_minus_resid_mem` and `Dtilde_orthogonal` fields are *derived* from the
double-demeaning algebra in `UniformTwoWayPanel`, not posited.  The remaining
hypotheses (`hD_binary`, `hconsistency`, `hSD`) are the source's genuine
primitives: binary treatment, the consistency identity, and nonzero
double-demeaned treatment variation. -/
noncomputable def ofTwoWayPanel
    (balanced : UniformTwoWayPanel.BalancedPanel G T)
    (D Y Y0 tau : G → T → ℝ)
    (hD_binary : ∀ g t, D g t = 0 ∨ D g t = 1)
    (hconsistency : ∀ g t, Y g t = Y0 g t + D g t * tau g t)
    (hSD : 0 < ∑ g, ∑ t, uniformWeight G T * (ddot D g t) ^ 2) :
    DCDHPanel G T where
  pi := fun _ _ => uniformWeight G T
  D := D
  Y := Y
  Y0 := Y0
  tau := tau
  Dtilde := ddot D
  pi_pos := fun _ _ => uniformWeight_pos balanced
  pi_sum_one := by
    have hcard : ((Fintype.card G : ℝ) * (Fintype.card T : ℝ)) ≠ 0 := by
      have hG : (0 : ℝ) < (Fintype.card G : ℝ) :=
        by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) balanced.unit_card_ge_two
      have hT : (0 : ℝ) < (Fintype.card T : ℝ) :=
        by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) balanced.time_card_ge_two
      exact ne_of_gt (mul_pos hG hT)
    simp only [uniformWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc]
    rw [mul_inv_cancel₀ hcard]
  D_binary := hD_binary
  consistency := hconsistency
  D_minus_resid_mem := by
    refine ⟨unitMean D, fun t => timeMean D t - grandMean D, ?_⟩
    intro i t
    have := UniformTwoWayPanel.sub_ddot_eq_unitTimeProjection D i t
    simp only [UniformTwoWayPanel.unitTimeProjection] at this
    linarith [this]
  Dtilde_orthogonal := by
    intro h hh
    have horth : inner (ddot D) h = 0 :=
      UniformTwoWayPanel.ddot_orthogonal_unit_time balanced D h hh
    have : ∑ g, ∑ t, uniformWeight G T * ddot D g t * h g t
        = uniformWeight G T * inner (ddot D) h := by
      unfold inner
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      ring
    rw [this, horth, mul_zero]
  SD_pos := hSD

/-- The residualized treatment of `ofTwoWayPanel` is exactly the double-demeaned
treatment `D̈`. -/
@[simp] theorem ofTwoWayPanel_Dtilde
    (balanced : UniformTwoWayPanel.BalancedPanel G T)
    (D Y Y0 tau : G → T → ℝ)
    (hD_binary : ∀ g t, D g t = 0 ∨ D g t = 1)
    (hconsistency : ∀ g t, Y g t = Y0 g t + D g t * tau g t)
    (hSD : 0 < ∑ g, ∑ t, uniformWeight G T * (ddot D g t) ^ 2) :
    (ofTwoWayPanel balanced D Y Y0 tau hD_binary hconsistency hSD).Dtilde = ddot D :=
  rfl

/-- The DCDH TWFE coefficient of the FWL-derived panel equals the uniform-panel
Frisch–Waugh–Lovell residualized coefficient of `Y` on the double-demeaned
treatment. -/
theorem ofTwoWayPanel_betaTWFE
    (balanced : UniformTwoWayPanel.BalancedPanel G T)
    (D Y Y0 tau : G → T → ℝ)
    (hD_binary : ∀ g t, D g t = 0 ∨ D g t = 1)
    (hconsistency : ∀ g t, Y g t = Y0 g t + D g t * tau g t)
    (hSD : 0 < ∑ g, ∑ t, uniformWeight G T * (ddot D g t) ^ 2) :
    (ofTwoWayPanel balanced D Y Y0 tau hD_binary hconsistency hSD).betaTWFE
      = finiteResidualizedCoefficient (ddot D) Y := by
  have hwpos : 0 < uniformWeight G T := uniformWeight_pos balanced
  set P := ofTwoWayPanel balanced D Y Y0 tau hD_binary hconsistency hSD with hP
  have hnum : (∑ g, ∑ t, P.pi g t * P.Dtilde g t * P.Y g t)
      = uniformWeight G T * inner (ddot D) Y := by
    change (∑ g, ∑ t, uniformWeight G T * ddot D g t * Y g t)
      = uniformWeight G T * inner (ddot D) Y
    unfold inner
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    ring
  have hden : P.SD = uniformWeight G T * inner (ddot D) (ddot D) := by
    change (∑ g, ∑ t, uniformWeight G T * (ddot D g t) ^ 2)
      = uniformWeight G T * inner (ddot D) (ddot D)
    unfold inner
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    ring
  rw [DCDHPanel.betaTWFE, hnum, hden, finiteResidualizedCoefficient]
  rw [mul_div_mul_left _ _ (ne_of_gt hwpos)]

end HeterogeneousTWFE
end Panel.EstimandCharacterization
end Causalean
