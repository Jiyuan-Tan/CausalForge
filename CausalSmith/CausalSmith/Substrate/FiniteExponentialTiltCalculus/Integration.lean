import CausalSmith.Substrate.FiniteExponentialTiltCalculus.Core
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integral identities for finite exponential tilts
-/

namespace CausalSmith.Substrate.FiniteExponentialTiltCalculus

open MeasureTheory

variable {ι : Type*} [Fintype ι]

private theorem setIntegral_Icc_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ t in Set.Icc (0 : ℝ) 1, f t) = ∫ t in (0 : ℝ)..1, f t := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  symm
  exact intervalIntegral.integral_of_le zero_le_one

theorem integral_mean_eq_logPartition_sub (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    (∫ t in (0 : ℝ)..1, mean w h t) =
      Real.log (partition w h 1) - Real.log (partition w h 0) := by
  have hd : deriv (fun t => Real.log (partition w h t)) = mean w h := by
    funext t
    exact (hasDerivAt_logPartition w h t hw hmass).deriv
  rw [← hd]
  apply intervalIntegral.integral_deriv_eq_sub
  · intro t _
    exact (hasDerivAt_logPartition w h t hw hmass).differentiableAt
  · rw [hd]
    exact (continuous_mean w h hw hmass).intervalIntegrable 0 1

theorem endpointRemainder_eq_intervalIntegral (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0)) =
      ∫ t in (0 : ℝ)..1, t * variance w h t := by
  have hip := intervalIntegral.integral_deriv_mul_eq_sub
    (a := (0 : ℝ)) (b := 1)
    (u := fun t : ℝ => t) (v := mean w h)
    (u' := fun _ => (1 : ℝ)) (v' := variance w h)
    (fun t _ => hasDerivAt_id t)
    (fun t _ => hasDerivAt_mean w h t hw hmass)
    (continuous_const.intervalIntegrable 0 1)
    ((continuous_variance w h hw hmass).intervalIntegrable 0 1)
  have hmeanInt : IntervalIntegrable (mean w h) volume 0 1 :=
    (continuous_mean w h hw hmass).intervalIntegrable 0 1
  have htvInt : IntervalIntegrable (fun t : ℝ => t * variance w h t)
      volume 0 1 := (continuous_id.mul
    (continuous_variance w h hw hmass)).intervalIntegrable 0 1
  simp only [one_mul, one_mul, zero_mul, sub_zero] at hip
  rw [intervalIntegral.integral_add hmeanInt htvInt,
    integral_mean_eq_logPartition_sub w h hw hmass] at hip
  linarith

theorem endpointRemainder_eq_setIntegral (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0)) =
      ∫ t in Set.Icc (0 : ℝ) 1, t * variance w h t := by
  rw [setIntegral_Icc_eq_intervalIntegral]
  exact endpointRemainder_eq_intervalIntegral w h hw hmass

theorem logPartition_bregman_eq_intervalIntegral (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    Real.log (partition w h 1) - Real.log (partition w h 0) - mean w h 0 =
      ∫ t in (0 : ℝ)..1, (1 - t) * variance w h t := by
  have hip := intervalIntegral.integral_deriv_mul_eq_sub
    (a := (0 : ℝ)) (b := 1)
    (u := fun t : ℝ => 1 - t) (v := mean w h)
    (u' := fun _ => (-1 : ℝ)) (v' := variance w h)
    (fun t _ => ((hasDerivAt_id t).const_sub (1 : ℝ)).congr_deriv (by norm_num))
    (fun t _ => hasDerivAt_mean w h t hw hmass)
    (continuous_const.intervalIntegrable 0 1)
    ((continuous_variance w h hw hmass).intervalIntegrable 0 1)
  have hnegMeanInt : IntervalIntegrable (fun t => -mean w h t) volume 0 1 :=
    (continuous_mean w h hw hmass).neg.intervalIntegrable 0 1
  have hweightedInt :
      IntervalIntegrable (fun t : ℝ => (1 - t) * variance w h t) volume 0 1 :=
    ((continuous_const.sub continuous_id).mul
    (continuous_variance w h hw hmass)).intervalIntegrable 0 1
  change (∫ x in (0 : ℝ)..1,
      (-1 : ℝ) * mean w h x + (1 - x) * variance w h x) =
    ((1 : ℝ) - 1) * mean w h 1 - ((1 : ℝ) - 0) * mean w h 0 at hip
  rw [sub_self, sub_zero, zero_mul, one_mul, zero_sub] at hip
  simp only [neg_one_mul] at hip
  rw [intervalIntegral.integral_add hnegMeanInt hweightedInt,
    intervalIntegral.integral_neg,
    integral_mean_eq_logPartition_sub w h hw hmass] at hip
  have hip' :
      -(Real.log (partition w h 1) - Real.log (partition w h 0)) +
          (∫ t in (0 : ℝ)..1, (1 - t) * variance w h t) =
        -mean w h 0 := by
    exact hip
  linarith

theorem logPartition_bregman_eq_reversed_intervalIntegral (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    Real.log (partition w h 1) - Real.log (partition w h 0) - mean w h 0 =
      ∫ t in (0 : ℝ)..1, t * variance w h (1 - t) := by
  rw [logPartition_bregman_eq_intervalIntegral w h hw hmass]
  have hs := intervalIntegral.integral_comp_sub_left
    (fun s : ℝ => (1 - s) * variance w h s) 1 (a := (0 : ℝ)) (b := 1)
  norm_num at hs
  simpa only [sub_sub_cancel_left] using hs.symm

theorem logPartition_bregman_eq_reversed_setIntegral (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    Real.log (partition w h 1) - Real.log (partition w h 0) - mean w h 0 =
      ∫ t in Set.Icc (0 : ℝ) 1, t * variance w h (1 - t) := by
  rw [setIntegral_Icc_eq_intervalIntegral]
  exact logPartition_bregman_eq_reversed_intervalIntegral w h hw hmass

theorem endpointRemainder_nonneg (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    0 ≤ mean w h 1 -
      (Real.log (partition w h 1) - Real.log (partition w h 0)) := by
  rw [endpointRemainder_eq_intervalIntegral w h hw hmass]
  exact intervalIntegral.integral_nonneg zero_le_one fun t ht =>
    mul_nonneg ht.1 (variance_nonneg w h t hw hmass)

end CausalSmith.Substrate.FiniteExponentialTiltCalculus
