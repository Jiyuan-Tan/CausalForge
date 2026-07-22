/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Uniform finite balanced two-way panel helpers

Paper-agnostic finite-sum infrastructure for balanced unit-period panels under
the uniform unit-period measure: unit means, time means, grand means, double
demeaning, the unit/time additive class, reconstruction, and the orthogonality
statements used by TWFE and two-way Mundlak residualization arguments.

This module intentionally covers the uniform balanced-panel specialization.
Share-weighted panel decompositions with non-uniform cell weights use the
weighted panel substrate instead of this uniform algebra.
-/

import Causalean.Panel.Weighted.AdditiveSpan
import Causalean.Panel.WeightedTwoWayPanel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Uniform Balanced Two-Way Panels

This file provides finite-sum algebra for balanced unit-period panels under the
uniform unit-period measure. It defines `BalancedPanel`, uniform unit weights,
unit means, time means, grand means, double demeaning `ddot`, the unnormalized
inner product, the finite residualized coefficient, and the unit/time additive
nuisance class. Its main results relate the uniform constructions to
`WeightedTwoWayPanel`, prove the finite residualized-coefficient handoff, and
show that double-demeaned arrays are orthogonal to unit-only, time-only, and
unit/time additive functions. -/

namespace Causalean
namespace Panel
namespace UniformTwoWayPanel

open Finset

variable {Unit Time : Type*} [Fintype Unit] [Fintype Time]

/-- Balanced-panel side conditions from the source definition: at least two
units and at least two periods. The current scalar algebra only needs
nonzero cardinals, but the stronger source condition is kept explicit. -/
structure BalancedPanel (Unit Time : Type*) [Fintype Unit] [Fintype Time] where
  unit_card_ge_two : 2 ≤ Fintype.card Unit
  time_card_ge_two : 2 ≤ Fintype.card Time

/-- Uniform unit weights as a probability vector, used to view this module as
the uniform specialization of `WeightedTwoWayPanel`. -/
noncomputable def uniformWeights (hU : 0 < Fintype.card Unit) :
    WeightedTwoWayPanel.UnitWeights Unit :=
  ⟨fun _ => (Fintype.card Unit : ℝ)⁻¹,
    (by
      intro _i
      have hU_real : (0 : ℝ) < Fintype.card Unit := by exact_mod_cast hU
      exact inv_pos.mpr hU_real),
    (by
      have hU_ne : (Fintype.card Unit : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hU)
      calc
        ∑ _i : Unit, (Fintype.card Unit : ℝ)⁻¹ =
            (Fintype.card Unit : ℝ) * (Fintype.card Unit : ℝ)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = 1 := mul_inv_cancel₀ hU_ne)⟩

/-- Unit mean `\bar V_{i·}` under the uniform period measure. -/
noncomputable def unitMean (V : Unit → Time → ℝ) (i : Unit) : ℝ :=
  (Fintype.card Time : ℝ)⁻¹ * ∑ t, V i t

/-- Time mean `\bar V_{·t}` under the uniform unit measure. -/
noncomputable def timeMean (V : Unit → Time → ℝ) (t : Time) : ℝ :=
  (Fintype.card Unit : ℝ)⁻¹ * ∑ i, V i t

/-- Grand mean `\bar V` under the uniform unit-period measure. -/
noncomputable def grandMean (V : Unit → Time → ℝ) : ℝ :=
  ((Fintype.card Unit : ℝ) * (Fintype.card Time : ℝ))⁻¹ *
    ∑ i, ∑ t, V i t

/-- Two-way residual / double-demeaned array. -/
noncomputable def ddot (V : Unit → Time → ℝ) (i : Unit) (t : Time) : ℝ :=
  V i t - unitMean V i - timeMean V t + grandMean V

/-- Uniform finite-panel inner product, without the harmless normalizing
constant. -/
noncomputable def inner (V W : Unit → Time → ℝ) : ℝ :=
  ∑ i, ∑ t, V i t * W i t

omit [Fintype Time] in
private theorem timeMean_eq_weighted (hU : 0 < Fintype.card Unit)
    (V : Unit → Time → ℝ) (t : Time) :
    timeMean V t = WeightedTwoWayPanel.timeMean (uniformWeights hU) V t := by
  unfold timeMean WeightedTwoWayPanel.timeMean uniformWeights
  rw [← Finset.mul_sum]

private theorem grandMean_eq_weighted (hU : 0 < Fintype.card Unit)
    (V : Unit → Time → ℝ) :
    grandMean V = WeightedTwoWayPanel.grandMean (uniformWeights hU) V := by
  unfold grandMean WeightedTwoWayPanel.grandMean uniformWeights
  change
    (((Fintype.card Unit : ℝ) * (Fintype.card Time : ℝ))⁻¹ *
        ∑ i, ∑ t, V i t) =
      ∑ i, (Fintype.card Unit : ℝ)⁻¹ *
        ((Fintype.card Time : ℝ)⁻¹ * ∑ t, V i t)
  calc
    (((Fintype.card Unit : ℝ) * (Fintype.card Time : ℝ))⁻¹ *
        ∑ i, ∑ t, V i t) =
        (Fintype.card Unit : ℝ)⁻¹ *
          ((Fintype.card Time : ℝ)⁻¹ * ∑ i, ∑ t, V i t) := by
      rw [mul_inv]
      ring
    _ = ∑ i, (Fintype.card Unit : ℝ)⁻¹ *
          ((Fintype.card Time : ℝ)⁻¹ * ∑ t, V i t) := by
      rw [Finset.mul_sum, Finset.mul_sum]

/-- Uniform double-demeaning is weighted double-demeaning with uniform unit
weights. -/
theorem ddot_eq_weighted (hU : 0 < Fintype.card Unit)
    (V : Unit → Time → ℝ) (i : Unit) (t : Time) :
    ddot V i t = WeightedTwoWayPanel.ddot (uniformWeights hU) V i t := by
  unfold ddot WeightedTwoWayPanel.ddot
  rw [timeMean_eq_weighted hU V t, grandMean_eq_weighted hU V]
  rfl

private theorem sum_eq_card_mul_uniform_weighted (hU : 0 < Fintype.card Unit)
    (F : Unit → Time → ℝ) :
    ∑ i, ∑ t, F i t =
      (Fintype.card Unit : ℝ) *
        ∑ i, ∑ t, (uniformWeights hU).p i * F i t := by
  have hU_ne : (Fintype.card Unit : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hU)
  unfold uniformWeights
  calc
    ∑ i, ∑ t, F i t =
        ((Fintype.card Unit : ℝ) * (Fintype.card Unit : ℝ)⁻¹) *
          ∑ i, ∑ t, F i t := by
      rw [mul_inv_cancel₀ hU_ne, one_mul]
    _ =
        (Fintype.card Unit : ℝ) *
          ((Fintype.card Unit : ℝ)⁻¹ * ∑ i, ∑ t, F i t) := by
      ring
    _ =
        (Fintype.card Unit : ℝ) *
          ∑ i, (Fintype.card Unit : ℝ)⁻¹ * ∑ t, F i t := by
      rw [Finset.mul_sum]
    _ =
        (Fintype.card Unit : ℝ) *
          ∑ i, ∑ t, (Fintype.card Unit : ℝ)⁻¹ * F i t := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]

/-- The unnormalized uniform inner product is the unit count times the weighted
inner product under uniform unit weights. -/
theorem inner_eq_card_smul_weighted (hU : 0 < Fintype.card Unit)
    (V W : Unit → Time → ℝ) :
    inner V W =
      (Fintype.card Unit : ℝ) *
        WeightedTwoWayPanel.inner (uniformWeights hU) V W := by
  simpa [inner, WeightedTwoWayPanel.inner] using
    sum_eq_card_mul_uniform_weighted (Unit := Unit) (Time := Time) hU
      (fun i t => V i t * W i t)

/-- Finite scalar residualized coefficient for a supplied residualized
regressor `Dtilde` and residualized outcome `Ytilde`. -/
noncomputable def finiteResidualizedCoefficient
    (Dtilde Ytilde : Unit → Time → ℝ) : ℝ :=
  inner Dtilde Ytilde / inner Dtilde Dtilde

/-- Finite scalar Frisch-Waugh-Lovell handoff.

If a proposed coefficient `β` and nuisance term `Hβ` satisfy the finite normal
equations against the raw regressor `D` and a nuisance class `H`, while
`Dtilde` is the residualized regressor orthogonal to `H`, then `β` equals the
finite residualized ratio. The outcome residual only needs the explicit bridge
`inner Dtilde Yproj = 0`; this covers the common TWFE case where `Yproj` is
unit/time additive but not necessarily in the paper-specific nuisance class. -/
theorem finite_residualized_coefficient_eq_of_normalEqs
    (H : (Unit → Time → ℝ) → Prop)
    {Y D Yproj Ytilde Dproj Dtilde Hβ : Unit → Time → ℝ} {β : ℝ}
    (hY_decomp : ∀ i t, Y i t = Yproj i t + Ytilde i t)
    (hD_decomp : ∀ i t, D i t = Dproj i t + Dtilde i t)
    (hDproj_mem : H Dproj)
    (hHβ_mem : H Hβ)
    (hDtilde_orth_H : ∀ h : Unit → Time → ℝ, H h → inner Dtilde h = 0)
    (hYproj_orth : inner Dtilde Yproj = 0)
    (hDtilde_pos : 0 < inner Dtilde Dtilde)
    (h_normal_D :
      inner D (fun i t => Y i t - D i t * β - Hβ i t) = 0)
    (h_normal_H : ∀ h : Unit → Time → ℝ, H h →
      inner h (fun i t => Y i t - D i t * β - Hβ i t) = 0) :
    β = finiteResidualizedCoefficient Dtilde Ytilde := by
  let e : Unit → Time → ℝ := fun i t => Y i t - D i t * β - Hβ i t
  have hDproj_e : inner Dproj e = 0 := h_normal_H Dproj hDproj_mem
  have hD_split : inner D e = inner Dproj e + inner Dtilde e := by
    unfold inner
    dsimp [e]
    calc
      ∑ i, ∑ t, D i t * (Y i t - D i t * β - Hβ i t)
          = ∑ i, ∑ t,
              (Dproj i t * (Y i t - D i t * β - Hβ i t) +
                Dtilde i t * (Y i t - D i t * β - Hβ i t)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro t _ht
            rw [hD_decomp i t]
            ring
      _ = (∑ i, ∑ t, Dproj i t * (Y i t - D i t * β - Hβ i t)) +
          ∑ i, ∑ t, Dtilde i t * (Y i t - D i t * β - Hβ i t) := by
            simp only [Finset.sum_add_distrib]
  have hDtilde_e : inner Dtilde e = 0 := by
    linarith [h_normal_D, hDproj_e, hD_split]
  have hDproj_orth : inner Dtilde Dproj = 0 :=
    hDtilde_orth_H Dproj hDproj_mem
  have hHβ_orth : inner Dtilde Hβ = 0 :=
    hDtilde_orth_H Hβ hHβ_mem
  have hYproj_orth' : (∑ i, ∑ t, Dtilde i t * Yproj i t) = 0 := by
    simpa [inner] using hYproj_orth
  have hDproj_orth' : (∑ i, ∑ t, Dtilde i t * Dproj i t) = 0 := by
    simpa [inner] using hDproj_orth
  have hHβ_orth' : (∑ i, ∑ t, Dtilde i t * Hβ i t) = 0 := by
    simpa [inner] using hHβ_orth
  have hExpand :
      inner Dtilde e = inner Dtilde Ytilde - β * inner Dtilde Dtilde := by
    unfold inner
    dsimp [e]
    calc
      ∑ i, ∑ t, Dtilde i t * (Y i t - D i t * β - Hβ i t)
          = ∑ i, ∑ t,
              (Dtilde i t * Yproj i t + Dtilde i t * Ytilde i t -
                (Dtilde i t * Dproj i t) * β -
                (Dtilde i t * Dtilde i t) * β -
                Dtilde i t * Hβ i t) := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro t _ht
            rw [hY_decomp i t, hD_decomp i t]
            ring
      _ = (∑ i, ∑ t, Dtilde i t * Yproj i t) +
            (∑ i, ∑ t, Dtilde i t * Ytilde i t) -
            (∑ i, ∑ t, Dtilde i t * Dproj i t) * β -
            (∑ i, ∑ t, Dtilde i t * Dtilde i t) * β -
            (∑ i, ∑ t, Dtilde i t * Hβ i t) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_mul]
      _ = (∑ i, ∑ t, Dtilde i t * Ytilde i t) -
            β * (∑ i, ∑ t, Dtilde i t * Dtilde i t) := by
            rw [hYproj_orth', hDproj_orth', hHβ_orth']
            ring
  have hcoeff : β * inner Dtilde Dtilde = inner Dtilde Ytilde := by
    linarith [hDtilde_e, hExpand]
  have hden_ne : inner Dtilde Dtilde ≠ 0 := hDtilde_pos.ne'
  have hβ_eq :
      β = inner Dtilde Ytilde / inner Dtilde Dtilde :=
    (eq_div_iff hden_ne).2 hcoeff
  simpa [finiteResidualizedCoefficient] using hβ_eq

/-- Unit-time additive nuisance class `h_it = a_i + b_t`.

Compatibility alias for the shared additive-span predicate. -/
abbrev IsUnitTimeAdditive (h : Unit → Time → ℝ) : Prop :=
  Causalean.Panel.Weighted.IsUnitTimeAdditive h

/-- The unit/time component removed by double demeaning. -/
noncomputable def unitTimeProjection (V : Unit → Time → ℝ) (i : Unit) (t : Time) : ℝ :=
  unitMean V i + timeMean V t - grandMean V

/-- Reconstruction identity
`V_it = ddot V_it + unitMean V_i + timeMean V_t - grandMean V`. -/
theorem ddot_reconstruct (V : Unit → Time → ℝ) (i : Unit) (t : Time) :
    ddot V i t + unitMean V i + timeMean V t - grandMean V = V i t := by
  unfold ddot
  ring

/-- The removed component is itself unit/time additive. -/
theorem unitTimeProjection_additive (V : Unit → Time → ℝ) :
    IsUnitTimeAdditive (unitTimeProjection V) := by
  refine ⟨unitMean V, fun t => timeMean V t - grandMean V, ?_⟩
  intro i t
  unfold unitTimeProjection
  ring

/-- Pointwise residual decomposition `V - ddot V` into the unit/time
projection. -/
theorem sub_ddot_eq_unitTimeProjection (V : Unit → Time → ℝ) (i : Unit) (t : Time) :
    V i t - ddot V i t = unitTimeProjection V i t := by
  unfold ddot unitTimeProjection
  ring

/-- Double-demeaned arrays are orthogonal to arbitrary unit-only functions. -/
theorem ddot_orthogonal_unit (P : BalancedPanel Unit Time)
    (V : Unit → Time → ℝ) (a : Unit → ℝ) :
    ∑ i, ∑ t, ddot V i t * a i = 0 := by
  classical
  have hU : 0 < Fintype.card Unit :=
    lt_of_lt_of_le (by decide : 0 < 2) P.unit_card_ge_two
  have hT : (0 : ℝ) < Fintype.card Time := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) P.time_card_ge_two)
  let w := uniformWeights (Unit := Unit) hU
  have hweighted :
      ∑ i, ∑ t, w.p i * (WeightedTwoWayPanel.ddot w V i t * a i) = 0 :=
    WeightedTwoWayPanel.ddot_orthogonal_unit w hT V a
  calc
    ∑ i, ∑ t, ddot V i t * a i =
        (Fintype.card Unit : ℝ) * ∑ i, ∑ t, w.p i * (ddot V i t * a i) := by
      simpa [w] using
        sum_eq_card_mul_uniform_weighted (Unit := Unit) (Time := Time) hU
          (fun i t => ddot V i t * a i)
    _ =
        (Fintype.card Unit : ℝ) *
          ∑ i, ∑ t, w.p i * (WeightedTwoWayPanel.ddot w V i t * a i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro t _ht
      rw [ddot_eq_weighted hU V i t]
    _ = 0 := by
      rw [hweighted, mul_zero]

/-- Double-demeaned arrays are orthogonal to arbitrary time-only functions. -/
theorem ddot_orthogonal_time (P : BalancedPanel Unit Time)
    (V : Unit → Time → ℝ) (b : Time → ℝ) :
    ∑ i, ∑ t, ddot V i t * b t = 0 := by
  classical
  have hU : 0 < Fintype.card Unit :=
    lt_of_lt_of_le (by decide : 0 < 2) P.unit_card_ge_two
  let w := uniformWeights (Unit := Unit) hU
  have hweighted :
      ∑ i, ∑ t, w.p i * (WeightedTwoWayPanel.ddot w V i t * b t) = 0 :=
    WeightedTwoWayPanel.ddot_orthogonal_time w V b
  calc
    ∑ i, ∑ t, ddot V i t * b t =
        (Fintype.card Unit : ℝ) * ∑ i, ∑ t, w.p i * (ddot V i t * b t) := by
      simpa [w] using
        sum_eq_card_mul_uniform_weighted (Unit := Unit) (Time := Time) hU
          (fun i t => ddot V i t * b t)
    _ =
        (Fintype.card Unit : ℝ) *
          ∑ i, ∑ t, w.p i * (WeightedTwoWayPanel.ddot w V i t * b t) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro t _ht
      rw [ddot_eq_weighted hU V i t]
    _ = 0 := by
      rw [hweighted, mul_zero]

/-- Double-demeaned arrays are orthogonal to every unit/time additive
nuisance function. -/
theorem ddot_orthogonal_unit_time (P : BalancedPanel Unit Time)
    (V h : Unit → Time → ℝ) (hh : IsUnitTimeAdditive h) :
    inner (ddot V) h = 0 := by
  classical
  have hU : 0 < Fintype.card Unit :=
    lt_of_lt_of_le (by decide : 0 < 2) P.unit_card_ge_two
  have hT : (0 : ℝ) < Fintype.card Time := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) P.time_card_ge_two)
  let w := uniformWeights (Unit := Unit) hU
  calc
    inner (ddot V) h =
        (Fintype.card Unit : ℝ) *
          WeightedTwoWayPanel.inner w (ddot V) h := by
      simpa [w] using inner_eq_card_smul_weighted
        (Unit := Unit) (Time := Time) hU (ddot V) h
    _ =
        (Fintype.card Unit : ℝ) *
          WeightedTwoWayPanel.inner w (WeightedTwoWayPanel.ddot w V) h := by
      apply congrArg
        (fun F => (Fintype.card Unit : ℝ) * WeightedTwoWayPanel.inner w F h)
      funext i t
      rw [ddot_eq_weighted hU V i t]
    _ = 0 := by
      rw [WeightedTwoWayPanel.ddot_orthogonal_unit_time w hT V h hh, mul_zero]

end UniformTwoWayPanel
end Panel
end Causalean
