import CausalSmith.Substrate.FiniteExponentialTiltCalculus.Integration
import Causalean.Mathlib.Analysis.WeightedCauchySchwarz

/-!
# Bounds for finite exponential tilts
-/

namespace CausalSmith.Substrate.FiniteExponentialTiltCalculus

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem secondMoment_nonneg (w h : ι → ℝ) (t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    0 ≤ secondMoment w h t := by
  rw [secondMoment_eq_sum_tilt]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (tilt_nonneg w h t hw hmass i) (sq_nonneg _)

theorem mean_sq_le_secondMoment (w h : ι → ℝ) (t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    (mean w h t) ^ 2 ≤ secondMoment w h t := by
  have := variance_nonneg w h t hw hmass
  simpa only [variance, sub_nonneg] using this

/-- The tilted mean is dominated in absolute value by the root of the tilted
second moment.  This is `Causalean.Mathlib.Analysis`'s weighted Jensen
inequality applied to the tilt weights. -/
theorem abs_mean_le_sqrt_secondMoment (w h : ι → ℝ) (t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    |mean w h t| ≤ Real.sqrt (secondMoment w h t) := by
  rw [mean_eq_sum_tilt, secondMoment_eq_sum_tilt]
  exact Causalean.Mathlib.Analysis.abs_weighted_mean_le_sqrt_weighted_sq
    (tilt w h t) h (tilt_nonneg w h t hw hmass) (sum_tilt w h t hw hmass).le

/-- For nonpositive observations, the covariance of the square and the observation
itself is nonpositive under any finite probability weights. -/
theorem weighted_cube_covariance_nonpos_of_nonpos
    (p x : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hx : ∀ i, x i ≤ 0) :
    (∑ i, p i * (x i) ^ 3) -
        (∑ i, p i * (x i) ^ 2) * (∑ i, p i * x i) ≤ 0 := by
  have hpair : ∀ i j,
      p i * p j * ((x i) ^ 2 - (x j) ^ 2) * (x i - x j) ≤ 0 := by
    intro i j
    have hprod :
        ((x i) ^ 2 - (x j) ^ 2) * (x i - x j) ≤ 0 := by
      calc
        ((x i) ^ 2 - (x j) ^ 2) * (x i - x j) =
            (x i + x j) * (x i - x j) ^ 2 := by ring
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
          (add_nonpos (hx i) (hx j)) (sq_nonneg _)
    calc
      p i * p j * ((x i) ^ 2 - (x j) ^ 2) * (x i - x j) =
          (p i * p j) *
            (((x i) ^ 2 - (x j) ^ 2) * (x i - x j)) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (hp i) (hp j)) hprod
  have hdouble :
      (∑ i, ∑ j, p i * p j *
        ((x i) ^ 2 - (x j) ^ 2) * (x i - x j)) ≤ 0 :=
    Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => hpair i j
  have hid :
      (∑ i, ∑ j, p i * p j *
        ((x i) ^ 2 - (x j) ^ 2) * (x i - x j)) =
      2 * ((∑ i, p i * (x i) ^ 3) -
        (∑ i, p i * (x i) ^ 2) * (∑ i, p i * x i)) := by
    have hcube_left :
        (∑ i, ∑ j, p i * p j * (x i) ^ 3) =
          ∑ i, p i * (x i) ^ 3 := by
      calc
        (∑ i, ∑ j, p i * p j * (x i) ^ 3) =
            ∑ i, (p i * (x i) ^ 3) * ∑ j, p j := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = _ := by rw [hpsum]; simp
    have hcross_left :
        (∑ i, ∑ j, p i * p j * (x i) ^ 2 * x j) =
          (∑ i, p i * (x i) ^ 2) * (∑ j, p j * x j) := by
      calc
        (∑ i, ∑ j, p i * p j * (x i) ^ 2 * x j) =
            ∑ i, (p i * (x i) ^ 2) * ∑ j, p j * x j := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = _ := (Finset.sum_mul ..).symm
    have hcross_right :
        (∑ i, ∑ j, p i * p j * (x j) ^ 2 * x i) =
          (∑ i, p i * (x i) ^ 2) * (∑ j, p j * x j) := by
      calc
        (∑ i, ∑ j, p i * p j * (x j) ^ 2 * x i) =
            ∑ i, (p i * x i) * ∑ j, p j * (x j) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = (∑ i, p i * x i) * (∑ j, p j * (x j) ^ 2) :=
          (Finset.sum_mul ..).symm
        _ = _ := by ring
    have hcube_right :
        (∑ i, ∑ j, p i * p j * (x j) ^ 3) =
          ∑ i, p i * (x i) ^ 3 := by
      calc
        (∑ i, ∑ j, p i * p j * (x j) ^ 3) =
            ∑ i, p i * ∑ j, p j * (x j) ^ 3 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = (∑ i, p i) * ∑ j, p j * (x j) ^ 3 :=
          (Finset.sum_mul ..).symm
        _ = _ := by rw [hpsum]; simp
    calc
      (∑ i, ∑ j, p i * p j *
          ((x i) ^ 2 - (x j) ^ 2) * (x i - x j)) =
          ∑ i, ∑ j,
            (p i * p j * (x i) ^ 3 -
              p i * p j * (x i) ^ 2 * x j -
              p i * p j * (x j) ^ 2 * x i +
              p i * p j * (x j) ^ 3) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = 2 * ((∑ i, p i * (x i) ^ 3) -
          (∑ i, p i * (x i) ^ 2) * (∑ i, p i * x i)) := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [hcube_left, hcross_left, hcross_right, hcube_right]
        ring
  rw [hid] at hdouble
  linarith

/-- If every score is nonpositive, its raw tilted second moment decreases with
the tilt parameter. -/
theorem secondMoment_antitone_of_nonpos
    (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hnonpos : ∀ i, h i ≤ 0) :
    Antitone (secondMoment w h) := by
  apply antitone_of_deriv_nonpos
  · intro t
    exact (hasDerivAt_secondMoment w h t hw hmass).differentiableAt
  · intro t
    rw [(hasDerivAt_secondMoment w h t hw hmass).deriv]
    rw [thirdMoment_eq_sum_tilt, secondMoment_eq_sum_tilt,
      mean_eq_sum_tilt]
    exact weighted_cube_covariance_nonpos_of_nonpos
      (tilt w h t) h
      (fun i => tilt_nonneg w h t hw hmass i)
      (sum_tilt w h t hw hmass) hnonpos

/-- Pointwise form of raw tilted second-moment antitonicity. -/
theorem secondMoment_le_of_le_of_nonpos
    (w h : ι → ℝ) (s t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hnonpos : ∀ i, h i ≤ 0) (hst : s ≤ t) :
    secondMoment w h t ≤ secondMoment w h s :=
  secondMoment_antitone_of_nonpos w h hw hmass hnonpos hst

private theorem partition_lower_of_abs_le (w h : ι → ℝ) (t eta : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (ht : 0 ≤ t) (hbound : ∀ i, |h i| ≤ eta) :
    Real.exp (-eta * t) ≤ partition w h t := by
  calc
    Real.exp (-eta * t) = ∑ i, w i * Real.exp (-eta * t) := by
      rw [← Finset.sum_mul, hmass, one_mul]
    _ ≤ ∑ i, w i * Real.exp (t * h i) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      apply Real.exp_le_exp.mpr
      have hi := neg_le_of_abs_le (hbound i)
      nlinarith
    _ = partition w h t := rfl

private theorem secondNumerator_upper_of_abs_le (w h : ι → ℝ) (t eta : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : 0 ≤ t)
    (hbound : ∀ i, |h i| ≤ eta) :
    (∑ i, w i * Real.exp (t * h i) * (h i) ^ 2) ≤
      Real.exp (eta * t) * ∑ i, w i * (h i) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hexp : Real.exp (t * h i) ≤ Real.exp (eta * t) := by
    apply Real.exp_le_exp.mpr
    have hi := le_of_abs_le (hbound i)
    nlinarith
  have hfac : 0 ≤ w i * (h i) ^ 2 :=
    mul_nonneg (hw i) (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hexp hfac]

theorem secondMoment_le_exp_two_mul_secondMoment_zero
    (w h : ι → ℝ) (t eta : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (ht : 0 ≤ t) (hbound : ∀ i, |h i| ≤ eta) :
    secondMoment w h t ≤
      Real.exp (2 * eta * t) * secondMoment w h 0 := by
  have hZpos := partition_pos w h t hw hmass
  have hZlower := partition_lower_of_abs_le w h t eta hw hmass ht hbound
  have hnum := secondNumerator_upper_of_abs_le w h t eta hw ht hbound
  rw [secondMoment, secondMoment_zero w h hmass]
  apply (div_le_iff₀ hZpos).2
  calc
    (∑ i, w i * Real.exp (t * h i) * h i ^ 2) ≤
        Real.exp (eta * t) * ∑ i, w i * h i ^ 2 := hnum
    _ = Real.exp (2 * eta * t) *
          (∑ i, w i * h i ^ 2) * Real.exp (-eta * t) := by
      calc
        Real.exp (eta * t) * ∑ i, w i * h i ^ 2 =
            (Real.exp (2 * eta * t) * Real.exp (-eta * t)) *
              ∑ i, w i * h i ^ 2 := by
                rw [← Real.exp_add]
                congr 2
                ring
        _ = _ := by ring
    _ ≤ Real.exp (2 * eta * t) *
          (∑ i, w i * h i ^ 2) * partition w h t := by
      apply mul_le_mul_of_nonneg_left hZlower
      exact mul_nonneg (Real.exp_pos _).le
        (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _))

theorem variance_le_exp_two_mul_secondMoment_zero
    (w h : ι → ℝ) (t eta : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (ht : 0 ≤ t) (hbound : ∀ i, |h i| ≤ eta) :
    variance w h t ≤
      Real.exp (2 * eta * t) * secondMoment w h 0 := by
  calc
    variance w h t ≤ secondMoment w h t := by
      simp only [variance]
      nlinarith [sq_nonneg (mean w h t)]
    _ ≤ _ :=
      secondMoment_le_exp_two_mul_secondMoment_zero
        w h t eta hw hmass ht hbound

private theorem setIntegral_Icc_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ t in Set.Icc (0 : ℝ) 1, f t) = ∫ t in (0 : ℝ)..1, f t := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  symm
  exact intervalIntegral.integral_of_le zero_le_one

theorem endpointRemainder_le_expIntegral
    (w h : ι → ℝ) (eta : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hbound : ∀ i, |h i| ≤ eta) :
    mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0)) ≤
      (∫ t in Set.Icc (0 : ℝ) 1, t * Real.exp (2 * eta * t)) *
        secondMoment w h 0 := by
  rw [endpointRemainder_eq_intervalIntegral w h hw hmass]
  rw [setIntegral_Icc_eq_intervalIntegral]
  have hleft : IntervalIntegrable (fun t : ℝ => t * variance w h t)
      volume 0 1 :=
    (continuous_id.mul (continuous_variance w h hw hmass)).intervalIntegrable 0 1
  have hright : IntervalIntegrable
      (fun t : ℝ => (t * Real.exp (2 * eta * t)) * secondMoment w h 0)
      volume 0 1 := by
    have hc : Continuous
        (fun t : ℝ => (t * Real.exp (2 * eta * t)) * secondMoment w h 0) := by
      fun_prop
    exact hc.intervalIntegrable 0 1
  rw [← intervalIntegral.integral_mul_const]
  exact intervalIntegral.integral_mono_on zero_le_one hleft hright fun t ht => by
    convert mul_le_mul_of_nonneg_left
      (variance_le_exp_two_mul_secondMoment_zero
        w h t eta hw hmass ht.1 hbound) ht.1 using 1 <;> ring

theorem endpointRemainder_le_neg_mean_zero_of_nonpos
    (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hnonpos : ∀ i, h i ≤ 0) :
    mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0)) ≤
      -mean w h 0 := by
  have hm1 : mean w h 1 ≤ 0 := by
    rw [mean_eq_sum_tilt]
    exact Finset.sum_nonpos fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (tilt_nonneg w h 1 hw hmass i) (hnonpos i)
  have hbreg : mean w h 0 ≤
      Real.log (partition w h 1) - Real.log (partition w h 0) := by
    have := logPartition_bregman_eq_intervalIntegral w h hw hmass
    have hint : 0 ≤ ∫ t in (0 : ℝ)..1, (1 - t) * variance w h t :=
      intervalIntegral.integral_nonneg zero_le_one fun t ht =>
        mul_nonneg (sub_nonneg.mpr ht.2) (variance_nonneg w h t hw hmass)
    linarith
  linarith

/-- For nonpositive scores, the endpoint remainder is at most one half of the
untilted raw second moment. -/
theorem endpointRemainder_le_half_secondMoment_zero_of_nonpos
    (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hnonpos : ∀ i, h i ≤ 0) :
    mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0)) ≤
      (2 : ℝ)⁻¹ * secondMoment w h 0 := by
  rw [endpointRemainder_eq_intervalIntegral w h hw hmass]
  have hleft : IntervalIntegrable (fun t : ℝ => t * variance w h t)
      volume 0 1 :=
    (continuous_id.mul (continuous_variance w h hw hmass)).intervalIntegrable 0 1
  have hright :
      IntervalIntegrable (fun t : ℝ => t * secondMoment w h 0)
        volume 0 1 :=
    (continuous_id.mul continuous_const).intervalIntegrable 0 1
  calc
    (∫ t in (0 : ℝ)..1, t * variance w h t) ≤
        ∫ t in (0 : ℝ)..1, t * secondMoment w h 0 := by
      exact intervalIntegral.integral_mono_on zero_le_one hleft hright
        fun t ht => by
          apply mul_le_mul_of_nonneg_left _ ht.1
          calc
            variance w h t ≤ secondMoment w h t := by
              simp only [variance]
              nlinarith [sq_nonneg (mean w h t)]
            _ ≤ secondMoment w h 0 :=
              secondMoment_le_of_le_of_nonpos
                w h 0 t hw hmass hnonpos ht.1
    _ = (2 : ℝ)⁻¹ * secondMoment w h 0 := by
      rw [intervalIntegral.integral_mul_const, integral_id]
      norm_num

theorem endpointRemainder_le_abs_means (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0)) ≤
      |mean w h 1| + |mean w h 0| := by
  have hbreg : mean w h 0 ≤
      Real.log (partition w h 1) - Real.log (partition w h 0) := by
    have hi := logPartition_bregman_eq_intervalIntegral w h hw hmass
    have hn : 0 ≤ ∫ t in (0 : ℝ)..1, (1 - t) * variance w h t :=
      intervalIntegral.integral_nonneg zero_le_one fun t ht =>
        mul_nonneg (sub_nonneg.mpr ht.2) (variance_nonneg w h t hw hmass)
    linarith
  have h1 : mean w h 1 ≤ |mean w h 1| := le_abs_self _
  have h0 : -mean w h 0 ≤ |mean w h 0| := neg_le_abs _
  linarith

theorem endpointRemainder_le_one_add_exp_mul_sqrt
    (w h : ι → ℝ) (eta : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (hbound : ∀ i, |h i| ≤ eta) :
    mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0)) ≤
      (1 + Real.exp eta) * Real.sqrt (secondMoment w h 0) := by
  have hsm := secondMoment_le_exp_two_mul_secondMoment_zero
    w h 1 eta hw hmass zero_le_one hbound
  have hsm' : secondMoment w h 1 ≤
      Real.exp (2 * eta) * secondMoment w h 0 := by
    convert hsm using 1 <;> ring
  have hA := secondMoment_nonneg w h 0 hw hmass
  have hB := secondMoment_nonneg w h 1 hw hmass
  have hsqrt :
      Real.sqrt (secondMoment w h 1) ≤
        Real.exp eta * Real.sqrt (secondMoment w h 0) := by
    have hx := Real.sq_sqrt hB
    have hy := Real.sq_sqrt hA
    have hexp : (Real.exp eta * Real.sqrt (secondMoment w h 0)) ^ 2 =
        Real.exp (2 * eta) * secondMoment w h 0 := by
      rw [mul_pow, pow_two (Real.exp eta), ← Real.exp_add, hy]
      congr 1
      ring
    have hsquares :
        (Real.sqrt (secondMoment w h 1)) ^ 2 ≤
          (Real.exp eta * Real.sqrt (secondMoment w h 0)) ^ 2 := by
      rw [hx, hexp]
      exact hsm'
    have hxnonneg := Real.sqrt_nonneg (secondMoment w h 1)
    have hynonneg : 0 ≤
        Real.exp eta * Real.sqrt (secondMoment w h 0) :=
      mul_nonneg (Real.exp_pos eta).le
        (Real.sqrt_nonneg (secondMoment w h 0))
    nlinarith
  calc
    mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0)) ≤
        |mean w h 1| + |mean w h 0| :=
      endpointRemainder_le_abs_means w h hw hmass
    _ ≤ Real.sqrt (secondMoment w h 1) +
        Real.sqrt (secondMoment w h 0) :=
      add_le_add (abs_mean_le_sqrt_secondMoment w h 1 hw hmass)
        (abs_mean_le_sqrt_secondMoment w h 0 hw hmass)
    _ ≤ _ := by nlinarith

theorem scaledEndpointRemainder_le_exact_expIntegral
    (w delta : ι → ℝ) (eta : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1)
    (heta : 0 < eta) (hdelta : ∀ i, |delta i| ≤ 1) :
    eta⁻¹ * (mean w (fun i => eta * delta i) 1 -
        (Real.log (partition w (fun i => eta * delta i) 1) -
          Real.log (partition w (fun i => eta * delta i) 0))) ≤
      (eta * ∫ t in Set.Icc (0 : ℝ) 1, t * Real.exp (2 * eta * t)) *
        ∑ i, w i * (delta i) ^ 2 := by
  let h : ι → ℝ := fun i => eta * delta i
  have hbound : ∀ i, |h i| ≤ eta := by
    intro i
    simp only [h, abs_mul, abs_of_pos heta]
    nlinarith [hdelta i]
  have hb := endpointRemainder_le_expIntegral w h eta hw hmass hbound
  have hsm : secondMoment w h 0 =
      eta ^ 2 * ∑ i, w i * (delta i) ^ 2 := by
    rw [secondMoment_zero w h hmass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [h]
    ring
  have hinv : 0 ≤ eta⁻¹ := (inv_pos.mpr heta).le
  change eta⁻¹ * (mean w h 1 -
      (Real.log (partition w h 1) - Real.log (partition w h 0))) ≤ _
  calc
    eta⁻¹ * (mean w h 1 -
        (Real.log (partition w h 1) - Real.log (partition w h 0))) ≤
      eta⁻¹ * ((∫ t in Set.Icc (0 : ℝ) 1,
        t * Real.exp (2 * eta * t)) * secondMoment w h 0) :=
      mul_le_mul_of_nonneg_left hb hinv
    _ = _ := by
      rw [hsm]
      let I : ℝ :=
        ∫ t in Set.Icc (0 : ℝ) 1, t * Real.exp (2 * eta * t)
      change eta⁻¹ * (I * (eta ^ 2 *
        ∑ i, w i * (delta i) ^ 2)) =
        (eta * I) * ∑ i, w i * (delta i) ^ 2
      field_simp [ne_of_gt heta]

end CausalSmith.Substrate.FiniteExponentialTiltCalculus
