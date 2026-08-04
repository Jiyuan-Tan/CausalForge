import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Finite exponential tilts

Paper-independent definitions and differential identities for a finite exponential family.
-/

namespace CausalSmith.Substrate.FiniteExponentialTiltCalculus

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The partition function of a finite exponential tilt. -/
noncomputable def partition (w h : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, w i * Real.exp (t * h i)

/-- The normalized exponential tilt. -/
noncomputable def tilt (w h : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  w i * Real.exp (t * h i) / partition w h t

/-- The tilted mean of the score. -/
noncomputable def mean (w h : ι → ℝ) (t : ℝ) : ℝ :=
  (∑ i, w i * Real.exp (t * h i) * h i) / partition w h t

/-- The tilted second moment of the score. -/
noncomputable def secondMoment (w h : ι → ℝ) (t : ℝ) : ℝ :=
  (∑ i, w i * Real.exp (t * h i) * (h i) ^ 2) / partition w h t

/-- The tilted third raw moment of the score. -/
noncomputable def thirdMoment (w h : ι → ℝ) (t : ℝ) : ℝ :=
  (∑ i, w i * Real.exp (t * h i) * (h i) ^ 3) / partition w h t

/-- The tilted variance of the score. -/
noncomputable def variance (w h : ι → ℝ) (t : ℝ) : ℝ :=
  secondMoment w h t - (mean w h t) ^ 2

theorem partition_pos (w h : ι → ℝ) (t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    0 < partition w h t := by
  have hsum_ne : ∑ i, w i ≠ 0 := by simp [hmass]
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) hsum_ne
  have hwi : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hi)
  exact Finset.sum_pos'
    (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, mul_pos hwi (Real.exp_pos _)⟩

theorem tilt_nonneg (w h : ι → ℝ) (t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) (i : ι) :
    0 ≤ tilt w h t i :=
  div_nonneg (mul_nonneg (hw i) (Real.exp_pos _).le)
    (partition_pos w h t hw hmass).le

theorem sum_tilt (w h : ι → ℝ) (t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    ∑ i, tilt w h t i = 1 := by
  rw [show (∑ i, tilt w h t i) =
      partition w h t / partition w h t by
    simp only [tilt, partition]
    rw [← Finset.sum_div]]
  exact div_self (ne_of_gt (partition_pos w h t hw hmass))

theorem mean_eq_sum_tilt (w h : ι → ℝ) (t : ℝ) :
    mean w h t = ∑ i, tilt w h t i * h i := by
  simp only [mean, tilt]
  rw [Finset.sum_div]
  congr 1
  funext i
  ring

theorem secondMoment_eq_sum_tilt (w h : ι → ℝ) (t : ℝ) :
    secondMoment w h t = ∑ i, tilt w h t i * (h i) ^ 2 := by
  simp only [secondMoment, tilt]
  rw [Finset.sum_div]
  congr 1
  funext i
  ring

theorem thirdMoment_eq_sum_tilt (w h : ι → ℝ) (t : ℝ) :
    thirdMoment w h t = ∑ i, tilt w h t i * (h i) ^ 3 := by
  simp only [thirdMoment, tilt]
  rw [Finset.sum_div]
  congr 1
  funext i
  ring

theorem partition_zero (w h : ι → ℝ) (hmass : ∑ i, w i = 1) :
    partition w h 0 = 1 := by
  simp [partition, hmass]

theorem tilt_zero (w h : ι → ℝ) (hmass : ∑ i, w i = 1) (i : ι) :
    tilt w h 0 i = w i := by
  simp [tilt, partition_zero w h hmass]

theorem mean_zero (w h : ι → ℝ) (hmass : ∑ i, w i = 1) :
    mean w h 0 = ∑ i, w i * h i := by
  simp [mean, partition_zero w h hmass]

theorem secondMoment_zero (w h : ι → ℝ) (hmass : ∑ i, w i = 1) :
    secondMoment w h 0 = ∑ i, w i * (h i) ^ 2 := by
  simp [secondMoment, partition_zero w h hmass]

theorem hasDerivAt_partition (w h : ι → ℝ) (t : ℝ) :
    HasDerivAt (partition w h)
      (∑ i, w i * Real.exp (t * h i) * h i) t := by
  unfold partition
  convert HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => by
    have hin : HasDerivAt (fun s : ℝ => s * h i) (h i) t := by
      convert (hasDerivAt_id t).mul (hasDerivAt_const t (h i)) using 1 <;> ring
    convert (((Real.hasDerivAt_exp (t * h i)).comp t hin).const_mul
      (w i)) using 1 <;> ring) using 1
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem hasDerivAt_logPartition (w h : ι → ℝ) (t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    HasDerivAt (fun s => Real.log (partition w h s)) (mean w h t) t := by
  simpa only [mean] using
    (hasDerivAt_partition w h t).log
      (ne_of_gt (partition_pos w h t hw hmass))

private theorem hasDerivAt_firstNumerator (w h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∑ i, w i * Real.exp (s * h i) * h i)
      (∑ i, w i * Real.exp (t * h i) * (h i) ^ 2) t := by
  convert HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => by
    have hin : HasDerivAt (fun s : ℝ => s * h i) (h i) t := by
      convert (hasDerivAt_id t).mul (hasDerivAt_const t (h i)) using 1 <;> ring
    convert ((((Real.hasDerivAt_exp (t * h i)).comp t hin).const_mul
      (w i)).mul_const (h i)) using 1 <;> ring) using 1
  · apply Finset.sum_congr rfl
    intro i _
    ring

private theorem hasDerivAt_secondNumerator (w h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∑ i, w i * Real.exp (s * h i) * (h i) ^ 2)
      (∑ i, w i * Real.exp (t * h i) * (h i) ^ 3) t := by
  convert HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => by
    have hin : HasDerivAt (fun s : ℝ => s * h i) (h i) t := by
      convert (hasDerivAt_id t).mul (hasDerivAt_const t (h i)) using 1 <;> ring
    convert ((((Real.hasDerivAt_exp (t * h i)).comp t hin).const_mul
      (w i)).mul_const ((h i) ^ 2)) using 1 <;> ring) using 1
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem hasDerivAt_mean (w h : ι → ℝ) (t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    HasDerivAt (mean w h) (variance w h t) t := by
  let A := ∑ i, w i * Real.exp (t * h i) * h i
  let B := ∑ i, w i * Real.exp (t * h i) * (h i) ^ 2
  let Z := partition w h t
  have hZ : Z ≠ 0 := ne_of_gt (partition_pos w h t hw hmass)
  have hd := (hasDerivAt_firstNumerator w h t).div
    (hasDerivAt_partition w h t) hZ
  change HasDerivAt (mean w h) ((B * Z - A * A) / Z ^ 2) t at hd
  convert hd using 1
  simp only [variance, secondMoment, mean, A, B, Z]
  field_simp

theorem hasDerivAt_secondMoment (w h : ι → ℝ) (t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    HasDerivAt (secondMoment w h)
      (thirdMoment w h t - secondMoment w h t * mean w h t) t := by
  let A := ∑ i, w i * Real.exp (t * h i) * h i
  let B := ∑ i, w i * Real.exp (t * h i) * (h i) ^ 2
  let C := ∑ i, w i * Real.exp (t * h i) * (h i) ^ 3
  let Z := partition w h t
  have hZ : Z ≠ 0 := ne_of_gt (partition_pos w h t hw hmass)
  have hd := (hasDerivAt_secondNumerator w h t).div
    (hasDerivAt_partition w h t) hZ
  change HasDerivAt (secondMoment w h) ((C * Z - B * A) / Z ^ 2) t at hd
  convert hd using 1
  simp only [thirdMoment, secondMoment, mean, A, B, C, Z]
  field_simp

theorem continuous_partition (w h : ι → ℝ) : Continuous (partition w h) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_partition w h t).continuousAt

theorem continuous_logPartition (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    Continuous (fun t => Real.log (partition w h t)) :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_logPartition w h t hw hmass).continuousAt

theorem continuous_mean (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    Continuous (mean w h) :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_mean w h t hw hmass).continuousAt

theorem continuous_secondMoment (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    Continuous (secondMoment w h) :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_secondMoment w h t hw hmass).continuousAt

theorem continuous_variance (w h : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    Continuous (variance w h) := by
  apply Continuous.sub
  · apply Continuous.div
    · fun_prop
    · exact continuous_partition w h
    · intro t
      exact ne_of_gt (partition_pos w h t hw hmass)
  · exact (continuous_mean w h hw hmass).pow 2

theorem variance_eq_sum_tilt_centered (w h : ι → ℝ) (t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    variance w h t = ∑ i, tilt w h t i * (h i - mean w h t) ^ 2 := by
  rw [variance, secondMoment_eq_sum_tilt, mean_eq_sum_tilt]
  have ht := sum_tilt w h t hw hmass
  calc
    (∑ i, tilt w h t i * h i ^ 2) -
        (∑ i, tilt w h t i * h i) ^ 2 =
      ∑ i, (tilt w h t i * h i ^ 2 -
        2 * (∑ j, tilt w h t j * h j) * (tilt w h t i * h i) +
        tilt w h t i * (∑ j, tilt w h t j * h j) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.sum_mul, ht]
          ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem variance_nonneg (w h : ι → ℝ) (t : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 1) :
    0 ≤ variance w h t := by
  rw [variance_eq_sum_tilt_centered w h t hw hmass]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (tilt_nonneg w h t hw hmass i) (sq_nonneg _)

end CausalSmith.Substrate.FiniteExponentialTiltCalculus
