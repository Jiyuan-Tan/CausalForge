/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Recovery from set integrals

This file recovers either a weighted measure or an almost-everywhere pointwise bound from
identities and inequalities known for every measurable set integral.
-/

open MeasureTheory
open scoped ENNReal

namespace Causalean.Mathlib.MeasureTheory

/-- If [a weight function `w` is integrable with respect to a reference measure `μ`](hyp:hwint)
and [a finite measure `ν`'s mass on every measurable event `A` equals, as a real number, the
integral of `w` over `A` against `μ`](hyp:hν), then [`ν` is obtained from `μ` by weighting with
the nonnegative part of `w`: `ν = μ.withDensity (fun x => ENNReal.ofReal (w x))`](goal). -/
lemma measure_eq_withDensity_of_toReal_setIntegral
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [IsFiniteMeasure ν]
    {w : α → ℝ} (hwint : Integrable w μ)
    (hν : ∀ A, MeasurableSet A →
      (ν A).toReal = ∫ x in A, w x ∂μ) :
    ν = μ.withDensity (fun x => ENNReal.ofReal (w x)) := by
  have hw0 : ∀ᵐ x ∂μ, 0 ≤ w x :=
    ae_nonneg_of_forall_setIntegral_nonneg hwint fun A hA _ => by
      rw [← hν A hA]
      exact ENNReal.toReal_nonneg
  ext A hA
  rw [withDensity_apply _ hA]
  rw [← ofReal_integral_eq_lintegral_ofReal hwint.integrableOn
    ((ae_restrict_iff' hA).2
      (Filter.Eventually.mono hw0 fun _ hx _ => hx))]
  rw [← hν A hA, ENNReal.ofReal_toReal (measure_ne_top ν A)]

/-- A measurable function is bounded in absolute value by one almost everywhere if the
absolute value of its integral over every measurable event is at most that event's measure.

No global integrability assumption is needed: the proof restricts attention to bounded
slices on which the function is automatically integrable, then exhausts the regions above
one and below minus one. -/
lemma abs_le_one_ae_of_setIntegral_le_measure
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    [IsFiniteMeasure mu] (f : Ω → ℝ) (hf : Measurable f)
    (hdom : ∀ A, MeasurableSet A →
      |∫ x in A, f x ∂mu| ≤ (mu A).toReal) :
    ∀ᵐ x ∂mu, |f x| ≤ 1 := by
  have hupper : ∀ q : ℝ, 1 < q → ∀ᵐ x ∂mu, f x ≤ q := by
    intro q hq
    have hslice : ∀ m : ℕ,
        ∀ᵐ x ∂mu, ¬(q < f x ∧ f x ≤ (m : ℝ)) := by
      intro m
      let A : Set Ω := {x | q < f x ∧ f x ≤ (m : ℝ)}
      have hA : MeasurableSet A :=
        (measurableSet_Ioi.preimage hf).inter
          (measurableSet_Iic.preimage hf)
      have hfin : mu A < ∞ := measure_lt_top mu A
      have hfA : IntegrableOn f A mu := by
        apply IntegrableOn.of_bound hfin hf.aestronglyMeasurable.restrict
          (m : ℝ)
        filter_upwards [self_mem_ae_restrict hA] with x hxA
        rw [Real.norm_eq_abs, abs_of_pos (lt_trans (by linarith) hxA.1)]
        exact hxA.2
      have hconst : IntegrableOn (fun _ : Ω => q) A mu :=
        integrableOn_const hfin.ne
      have hlower :
          q * (mu A).toReal ≤ ∫ x in A, f x ∂mu := by
        calc
          q * (mu A).toReal = ∫ _ in A, q ∂mu := by
            rw [setIntegral_const]
            simp [Measure.real]
            ring
          _ ≤ ∫ x in A, f x ∂mu :=
            integral_mono_ae hconst hfA
              (ae_restrict_iff' hA |>.2 <| by
                filter_upwards with x hx
                exact hx.1.le)
      have hupperInt :
          (∫ x in A, f x ∂mu) ≤ (mu A).toReal :=
        (le_abs_self _).trans (hdom A hA)
      have hzeroReal : (mu A).toReal = 0 := by
        have hnonneg : 0 ≤ (mu A).toReal := ENNReal.toReal_nonneg
        nlinarith
      have hzero : mu A = 0 := by
        rw [ENNReal.toReal_eq_zero_iff] at hzeroReal
        exact hzeroReal.resolve_right hfin.ne
      rw [ae_iff]
      simpa [A] using hzero
    rw [← ae_all_iff] at hslice
    filter_upwards [hslice] with x hx
    by_contra hqx
    have hqfx : q < f x := lt_of_not_ge hqx
    obtain ⟨m, hm⟩ := exists_nat_ge (f x)
    exact hx m ⟨hqfx, hm⟩
  have hlower : ∀ q : ℝ, 1 < q → ∀ᵐ x ∂mu, -q ≤ f x := by
    intro q hq
    have hslice : ∀ m : ℕ,
        ∀ᵐ x ∂mu, ¬(-(m : ℝ) ≤ f x ∧ f x < -q) := by
      intro m
      let A : Set Ω := {x | -(m : ℝ) ≤ f x ∧ f x < -q}
      have hA : MeasurableSet A :=
        (measurableSet_Ici.preimage hf).inter
          (measurableSet_Iio.preimage hf)
      have hfin : mu A < ∞ := measure_lt_top mu A
      have hfA : IntegrableOn f A mu := by
        apply IntegrableOn.of_bound hfin hf.aestronglyMeasurable.restrict
          (m : ℝ)
        filter_upwards [self_mem_ae_restrict hA] with x hxA
        rw [Real.norm_eq_abs,
          abs_of_neg (lt_trans hxA.2 (neg_lt_zero.mpr (by linarith)))]
        linarith [hxA.1]
      have hconst : IntegrableOn (fun _ : Ω => -q) A mu :=
        integrableOn_const hfin.ne
      have hupperSlice :
          (∫ x in A, f x ∂mu) ≤ -q * (mu A).toReal := by
        calc
          (∫ x in A, f x ∂mu) ≤ ∫ _ in A, -q ∂mu :=
            integral_mono_ae hfA hconst
              (ae_restrict_iff' hA |>.2 <| by
                filter_upwards with x hx
                exact hx.2.le)
          _ = -q * (mu A).toReal := by
            rw [setIntegral_const]
            simp [Measure.real]
            ring
      have hlowerInt :
          -(mu A).toReal ≤ ∫ x in A, f x ∂mu := by
        have := hdom A hA
        linarith [neg_abs_le (∫ x in A, f x ∂mu)]
      have hzeroReal : (mu A).toReal = 0 := by
        have hnonneg : 0 ≤ (mu A).toReal := ENNReal.toReal_nonneg
        nlinarith
      have hzero : mu A = 0 := by
        rw [ENNReal.toReal_eq_zero_iff] at hzeroReal
        exact hzeroReal.resolve_right hfin.ne
      rw [ae_iff]
      simpa [A] using hzero
    rw [← ae_all_iff] at hslice
    filter_upwards [hslice] with x hx
    by_contra hqx
    have hfxq : f x < -q := lt_of_not_ge hqx
    obtain ⟨m, hm⟩ := exists_nat_ge (-f x)
    exact hx m ⟨by linarith, hfxq⟩
  have hupperOne : ∀ᵐ x ∂mu, f x ≤ 1 := by
    have hq := fun j : ℕ => hupper (1 + 1 / ((j + 1 : ℕ) : ℝ))
      (by
        have : 0 < 1 / ((j + 1 : ℕ) : ℝ) := by positivity
        linarith)
    rw [← ae_all_iff] at hq
    filter_upwards [hq] with x hx
    by_contra hx1
    have hpos : 0 < f x - 1 := sub_pos.mpr (lt_of_not_ge hx1)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
    have hxj := hx j
    norm_num [Nat.cast_add, Nat.cast_one] at hxj
    have hj' : ((j : ℝ) + 1)⁻¹ < f x - 1 := by
      simpa [one_div] using hj
    linarith
  have hlowerOne : ∀ᵐ x ∂mu, -1 ≤ f x := by
    have hq := fun j : ℕ => hlower (1 + 1 / ((j + 1 : ℕ) : ℝ))
      (by
        have : 0 < 1 / ((j + 1 : ℕ) : ℝ) := by positivity
        linarith)
    rw [← ae_all_iff] at hq
    filter_upwards [hq] with x hx
    by_contra hx1
    have hlt : f x < -1 := lt_of_not_ge hx1
    have hpos : 0 < -f x - 1 := by linarith
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
    have hxj := hx j
    norm_num [Nat.cast_add, Nat.cast_one] at hxj
    have hj' : ((j : ℝ) + 1)⁻¹ < -f x - 1 := by
      simpa [one_div] using hj
    linarith
  filter_upwards [hupperOne, hlowerOne] with x hxU hxL
  exact abs_le.mpr ⟨by linarith, hxU⟩

end Causalean.Mathlib.MeasureTheory
