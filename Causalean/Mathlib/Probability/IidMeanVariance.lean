/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Probability.Moments.Variance

/-!
# Deviation bounds for i.i.d. empirical means

This module gives scalar and finite-dimensional `L²` and `L¹` bounds for an
empirical mean sampled from a finite i.i.d. product measure.  Boundedness is
assumed explicitly so that all integrability obligations are automatic.
-/

namespace Causalean.Mathlib.Probability

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private lemma integral_abs_le_sqrt_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    ∫ ω, |X ω| ∂μ ≤ Real.sqrt (∫ ω, (X ω) ^ 2 ∂μ) := by
  have habs : MemLp (fun ω => |X ω|) 2 μ := hX.abs
  have hsquare : (∫ ω, |X ω| ∂μ) ^ 2 ≤ ∫ ω, (X ω) ^ 2 ∂μ := by
    have hv := ProbabilityTheory.variance_nonneg (fun ω => |X ω|) μ
    rw [ProbabilityTheory.variance_eq_sub habs] at hv
    simpa [sq_abs] using hv
  exact Real.le_sqrt_of_sq_le hsquare

/-- The mean squared error of a bounded scalar sample average from independent, identically
distributed observations is at most the population second moment divided by the sample size. -/
theorem iid_mean_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (ξ : Ω → ℝ) (hξ : Measurable ξ) (hbounded : ∃ B, ∀ ω, |ξ ω| ≤ B) :
    ∫ s, ((n : ℝ)⁻¹ * (∑ i : Fin n, ξ (s i)) - ∫ ω, ξ ω ∂μ) ^ 2
        ∂(Measure.pi fun _ : Fin n => μ) ≤
      (∫ ω, (ξ ω) ^ 2 ∂μ) / (n : ℝ) := by
  let P : Measure (Fin n → Ω) := Measure.pi fun _ : Fin n => μ
  let X : (Fin n → Ω) → ℝ := fun s => ∑ i : Fin n, ξ (s i)
  obtain ⟨B, hB⟩ := hbounded
  have hξLp : MemLp ξ 2 μ :=
    MemLp.of_bound hξ.aestronglyMeasurable B (ae_of_all μ hB)
  have hXLp : MemLp X 2 P := by
    simpa [X, P] using memLp_finset_sum Finset.univ fun i _ =>
      hξLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i)
  have hmean : ∫ s, (n : ℝ)⁻¹ * X s ∂P = ∫ ω, ξ ω ∂μ := by
    rw [integral_const_mul]
    change (n : ℝ)⁻¹ * ∫ s, ∑ i : Fin n, ξ (s i) ∂(Measure.pi fun _ : Fin n => μ) = _
    have hsum_integral := integral_finset_sum Finset.univ fun i _ =>
      (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable
        (hξLp.integrable (by norm_num))
    rw [show (∫ s, ∑ i : Fin n, ξ (s i) ∂(Measure.pi fun _ : Fin n => μ)) =
        ∑ i : Fin n, ∫ s, ξ (s i) ∂(Measure.pi fun _ : Fin n => μ) by
      simpa using hsum_integral]
    have hcoord (i : Fin n) :
        ∫ s, ξ (s i) ∂(Measure.pi fun _ : Fin n => μ) = ∫ ω, ξ ω ∂μ :=
      integral_comp_eval (μ := fun _ : Fin n => μ) (i := i) hξ.aestronglyMeasurable
    simp_rw [hcoord]
    simp [hn.ne']
  calc
    ∫ s, ((n : ℝ)⁻¹ * (∑ i : Fin n, ξ (s i)) - ∫ ω, ξ ω ∂μ) ^ 2 ∂P =
        ProbabilityTheory.variance (fun s => (n : ℝ)⁻¹ * X s) P := by
          rw [ProbabilityTheory.variance_eq_integral]
          · simp only [hmean]
            rfl
          · exact hXLp.const_mul (n : ℝ)⁻¹ |>.aemeasurable
    _ = ((n : ℝ)⁻¹) ^ 2 * ProbabilityTheory.variance X P := by
      exact ProbabilityTheory.variance_const_mul _ _ _
    _ = ((n : ℝ)⁻¹) ^ 2 *
        (∑ _i : Fin n, ProbabilityTheory.variance ξ μ) := by
      congr 1
      change ProbabilityTheory.variance (fun s => ∑ i : Fin n, ξ (s i))
          (Measure.pi fun _ : Fin n => μ) = _
      calc
        ProbabilityTheory.variance (fun s => ∑ i : Fin n, ξ (s i))
            (Measure.pi fun _ : Fin n => μ) =
            ProbabilityTheory.variance (∑ i : Fin n, fun s => ξ (s i))
              (Measure.pi fun _ : Fin n => μ) := by
                congr 1
                funext s
                simp
        _ = _ := ProbabilityTheory.variance_sum_pi (fun _ : Fin n => hξLp)
    _ ≤ ((n : ℝ)⁻¹) ^ 2 *
        (∑ _i : Fin n, ∫ ω, (ξ ω) ^ 2 ∂μ) := by
      gcongr
      exact ProbabilityTheory.variance_le_expectation_sq hξ.aestronglyMeasurable
    _ = (∫ ω, (ξ ω) ^ 2 ∂μ) / (n : ℝ) := by
      simp
      field_simp

/-- The mean absolute error of a bounded scalar sample average from independent, identically
distributed observations is at most the square root of the population second moment divided by
the sample size. -/
theorem iid_mean_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (ξ : Ω → ℝ) (hξ : Measurable ξ) (hbounded : ∃ B, ∀ ω, |ξ ω| ≤ B) :
    ∫ s, |(n : ℝ)⁻¹ * (∑ i : Fin n, ξ (s i)) - ∫ ω, ξ ω ∂μ|
        ∂(Measure.pi fun _ : Fin n => μ) ≤
      Real.sqrt ((∫ ω, (ξ ω) ^ 2 ∂μ) / (n : ℝ)) := by
  let P : Measure (Fin n → Ω) := Measure.pi fun _ : Fin n => μ
  let Y : (Fin n → Ω) → ℝ := fun s =>
    (n : ℝ)⁻¹ * (∑ i : Fin n, ξ (s i)) - ∫ ω, ξ ω ∂μ
  obtain ⟨B, hB⟩ := hbounded
  have hξLp : MemLp ξ 2 μ :=
    MemLp.of_bound hξ.aestronglyMeasurable B (ae_of_all μ hB)
  have hYLp : MemLp Y 2 P := by
    apply MemLp.sub (MemLp.const_mul (by
      simpa [P] using memLp_finset_sum Finset.univ fun i _ =>
        hξLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i)) _)
    exact memLp_const _
  exact (integral_abs_le_sqrt_integral_sq P hYLp).trans
    (Real.sqrt_le_sqrt (iid_mean_sq_le μ hn ξ hξ ⟨B, hB⟩))

/-- The expected Euclidean error of finitely many bounded sample averages from the same independent,
identically distributed sample is controlled by their summed population second moments and the
sample size. -/
theorem iid_mean_euclidean_abs_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (ξ : ι → Ω → ℝ) (hξ : ∀ k, Measurable (ξ k))
    (B : ℝ) (hbounded : ∀ k ω, |ξ k ω| ≤ B) :
    ∫ s, Real.sqrt (∑ k : ι,
        ((n : ℝ)⁻¹ * (∑ i : Fin n, ξ k (s i)) - ∫ ω, ξ k ω ∂μ) ^ 2)
        ∂(Measure.pi fun _ : Fin n => μ) ≤
      Real.sqrt ((∑ k : ι, ∫ ω, (ξ k ω) ^ 2 ∂μ) / (n : ℝ)) := by
  let P : Measure (Fin n → Ω) := Measure.pi fun _ : Fin n => μ
  let Y : ι → (Fin n → Ω) → ℝ := fun k s =>
    (n : ℝ)⁻¹ * (∑ i : Fin n, ξ k (s i)) - ∫ ω, ξ k ω ∂μ
  let R : (Fin n → Ω) → ℝ := fun s => Real.sqrt (∑ k : ι, (Y k s) ^ 2)
  have hYLp (k : ι) : MemLp (Y k) 2 P := by
    have hkLp : MemLp (ξ k) 2 μ :=
      MemLp.of_bound (hξ k).aestronglyMeasurable B (ae_of_all μ (hbounded k))
    apply MemLp.sub (MemLp.const_mul (by
      simpa [P] using memLp_finset_sum Finset.univ fun i _ =>
        hkLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i)) _)
    exact memLp_const _
  have hRLp : MemLp R 2 P := by
    have hsum_int : Integrable (fun s => ∑ k : ι, (Y k s) ^ 2) P :=
      integrable_finset_sum _ fun k _ => (hYLp k).integrable_sq
    have hR_ae : AEStronglyMeasurable R P := by
      simpa [R] using hsum_int.aemeasurable.sqrt.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hR_ae).2
    convert hsum_int using 1
    funext s
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc
    ∫ s, Real.sqrt (∑ k : ι, (Y k s) ^ 2) ∂P ≤
        Real.sqrt (∫ s, (R s) ^ 2 ∂P) :=
      by
        simpa [R, abs_of_nonneg (Real.sqrt_nonneg _)] using
          integral_abs_le_sqrt_integral_sq P hRLp
    _ = Real.sqrt (∑ k : ι, ∫ s, (Y k s) ^ 2 ∂P) := by
      congr 1
      rw [show (fun s => (R s) ^ 2) = fun s => ∑ k : ι, (Y k s) ^ 2 by
        funext s
        exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      exact integral_finset_sum _ fun k _ => (hYLp k).integrable_sq
    _ ≤ Real.sqrt ((∑ k : ι, ∫ ω, (ξ k ω) ^ 2 ∂μ) / (n : ℝ)) := by
      apply Real.sqrt_le_sqrt
      calc
        (∑ k : ι, ∫ s, (Y k s) ^ 2 ∂P) ≤
            ∑ k : ι, (∫ ω, (ξ k ω) ^ 2 ∂μ) / (n : ℝ) := by
          exact Finset.sum_le_sum fun k _ =>
            iid_mean_sq_le μ hn (ξ k) (hξ k) ⟨B, hbounded k⟩
        _ = _ := by rw [Finset.sum_div]

end

end Causalean.Mathlib.Probability
