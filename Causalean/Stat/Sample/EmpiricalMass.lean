/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Probability.IidMeanVariance

/-!
# Empirical mass of a point

This module defines the empirical frequency of one point in a finite i.i.d.
sample and establishes its range, expectation, and second moment.
-/

namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {𝒳 : Type*}

/-- The empirical mass of a point is the fraction of sample observations equal to that point. -/
def empiricalMass {N : ℕ} (sample : Fin N → 𝒳) (x : 𝒳) : ℝ :=
  by
    classical
    exact (N : ℝ)⁻¹ * ∑ j, if sample j = x then 1 else 0

/-- The absolute empirical mass of any point is at most one, including for the empty sample. -/
lemma abs_empiricalMass_le_one
    {N : ℕ} (sample : Fin N → 𝒳) (x : 𝒳) :
    |empiricalMass sample x| ≤ 1 := by
  by_cases hN : 0 < N
  · classical
    unfold empiricalMass
    have hcount_nonneg :
        0 ≤ ∑ j : Fin N, if sample j = x then (1 : ℝ) else 0 := by
      positivity
    have hcount_le :
        ∑ j : Fin N, (if sample j = x then (1 : ℝ) else 0) ≤ N := by
      calc
        _ ≤ ∑ _j : Fin N, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          split_ifs <;> norm_num
        _ = N := by simp
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hNreal.le) hcount_nonneg)]
    calc
      (N : ℝ)⁻¹ * ∑ j : Fin N, (if sample j = x then 1 else 0) ≤
          (N : ℝ)⁻¹ * N := by gcongr
      _ = 1 := by field_simp
  · have hzero : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    simp [empiricalMass]

/-- The expected empirical mass of a measurable point equals that point's population probability. -/
lemma integral_empiricalMass
    [MeasurableSpace 𝒳] (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m)
    (a : 𝒳) (ha : MeasurableSet {a}) :
    (∫ sample : Fin m → 𝒳, empiricalMass sample a
        ∂Measure.pi (fun _ : Fin m => μ)) =
      μ.real {a} := by
  classical
  let F : 𝒳 → ℝ := fun x => if x = a then 1 else 0
  have hFMeas : Measurable F := by
    exact Measurable.ite ha measurable_const measurable_const
  have hFMem : MemLp F 2 μ :=
    MemLp.of_bound hFMeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        by_cases hx : x = a <;> simp [F, hx])
  have hstat :
      (fun sample : Fin m → 𝒳 => empiricalMass sample a) =
        fun sample => (m : ℝ)⁻¹ * ∑ j, F (sample j) := by
    funext sample
    unfold empiricalMass
    apply congrArg ((m : ℝ)⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hx : sample j = a <;> simp [F, hx]
  rw [hstat, Causalean.Mathlib.Probability.iid_average_integral μ m hm F
    (hFMem.integrable (by norm_num))]
  change
    (∫ x, ({a} : Set 𝒳).indicator (fun _ => (1 : ℝ)) x ∂μ) =
      μ.real {a}
  rw [integral_indicator_const (μ := μ) (1 : ℝ) ha]
  simp

/-- The second moment of a point's empirical mass is its squared population probability plus the
usual binomial sampling correction. -/
lemma integral_empiricalMass_sq
    [MeasurableSpace 𝒳] (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m)
    (a : 𝒳) (ha : MeasurableSet {a}) :
    (∫ sample : Fin m → 𝒳, empiricalMass sample a ^ 2
        ∂Measure.pi (fun _ : Fin m => μ)) =
      μ.real {a} ^ 2 + (m : ℝ)⁻¹ * (μ.real {a} - μ.real {a} ^ 2) := by
  classical
  let F : 𝒳 → ℝ := fun x => if x = a then 1 else 0
  have hFMeas : Measurable F := by
    dsimp [F]
    exact Measurable.ite (ha.preimage measurable_id)
      measurable_const measurable_const
  have hFBound : ∀ x, |F x| ≤ 1 := by
    intro x
    by_cases hx : x = a <;> simp [F, hx]
  have hFMem : MemLp F 2 μ :=
    MemLp.of_bound hFMeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hFBound x)
  have hmeanF : (∫ x, F x ∂μ) = μ.real {a} := by
    change (∫ x, ({a} : Set 𝒳).indicator (fun _ => (1 : ℝ)) x ∂μ) = _
    rw [integral_indicator_const (μ := μ) (1 : ℝ) ha]
    simp
  have hsquareF : (∫ x, F x ^ 2 ∂μ) = μ.real {a} := by
    have hpoint : (fun x => F x ^ 2) = F := by
      funext x
      by_cases hx : x = a <;> simp [F, hx]
    rw [hpoint, hmeanF]
  have hstat :
      (fun sample : Fin m → 𝒳 => empiricalMass sample a) =
        fun sample => (m : ℝ)⁻¹ * ∑ j, F (sample j) := by
    funext sample
    unfold empiricalMass
    apply congrArg ((m : ℝ)⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hx : sample j = a <;> simp [F, hx]
  have hAvgMem :
      MemLp (fun sample : Fin m → 𝒳 =>
        (m : ℝ)⁻¹ * ∑ j, F (sample j)) 2
        (Measure.pi (fun _ : Fin m => μ)) := by
    apply MemLp.const_mul
    apply memLp_finset_sum
    intro j hj
    exact hFMem.comp_measurePreserving (measurePreserving_eval _ j)
  have hvar :=
    Causalean.Mathlib.Probability.iid_average_variance μ m F hFMem
  rw [ProbabilityTheory.variance_eq_sub hAvgMem,
    ProbabilityTheory.variance_eq_sub hFMem] at hvar
  have hmean :=
    Causalean.Mathlib.Probability.iid_average_integral μ m hm F
      (hFMem.integrable (by norm_num))
  rw [hmeanF] at hmean
  have hstat' (sample : Fin m → 𝒳) :
      empiricalMass sample a =
        (m : ℝ)⁻¹ * ∑ j, F (sample j) :=
    congrFun hstat sample
  simp_rw [hstat']
  simp only [Pi.pow_apply] at hvar
  rw [hmean, hmeanF, hsquareF] at hvar
  linarith

end

end Causalean.Stat
