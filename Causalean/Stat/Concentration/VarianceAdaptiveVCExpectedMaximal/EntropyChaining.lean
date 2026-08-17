/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.Separability
import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.ExpectedMaximal

/-!
# VC entropy chaining for expected empirical maxima

This file packages the measurable envelope, population-radius, and uniform
polynomial-cover hypotheses needed by the variance-adaptive expected maximal
inequality, and derives the corresponding countable chaining bound.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Causalean.Stat.Concentration

/-- A function class has uniform VC-type entropy when it has a measurable
uniform envelope, a strict population L2 radius, and polynomial empirical L2
covers along every countable enumeration. -/
def HasVCUniformEntropy {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : ι → Ω → ℝ) (U σ A v : ℝ) : Prop :=
  0 < σ ∧ σ < U ∧ Real.exp 1 ≤ A ∧ 1 ≤ v ∧
  (∀ i, Measurable (g i)) ∧
  (∀ i z, |g i z| ≤ U) ∧
  (∀ i, Causalean.Stat.Concentration.measureL2Dist μ (g i) (fun _ => 0) ≤ σ) ∧
  ∀ g0 : ℕ → ι,
    Causalean.Stat.Concentration.HasPolynomialEmpiricalL2Cover
      (fun k => g (g0 k)) U A v

/-- Countable empirical-process supremum associated with an enumeration. -/
noncomputable def countableEmpiricalProcessSup
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : ι → Ω → ℝ) (g0 : ℕ → ι) {n : ℕ} (w : Fin n → Ω) : ℝ≥0∞ :=
  ⨆ k : ℕ, ENNReal.ofReal |centeredEmpiricalAverage μ w (g (g0 k))|

private lemma countableEmpiricalProcessSup_eq_of_envelope {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ι → Ω → ℝ) (g0 : ℕ → ι) {U : ℝ} (hU : 0 < U)
    (hmeas : ∀ i, Measurable (g i)) (henv : ∀ i x, |g i x| ≤ U)
    {n : ℕ} (hn : 0 < n)
    (w : Fin n → Ω) :
    countableEmpiricalProcessSup μ g g0 w =
      ENNReal.ofReal (countableEmpiricalSup μ (fun k => g (g0 k)) w) := by
  simp only [countableEmpiricalProcessSup, countableEmpiricalSup, uniformDeviation,
    centeredEmpiricalAverage, id_eq]
  refine (Monotone.map_ciSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt
    ENNReal.ofReal_mono (bdd := ?_)).symm
  refine ⟨2 * U, ?_⟩
  rintro _ ⟨k, rfl⟩
  have hint : Integrable (g (g0 k)) μ :=
    Integrable.of_bound (hmeas (g0 k)).aestronglyMeasurable U
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using henv (g0 k) x)
  have hmean : |∫ x, g (g0 k) x ∂μ| ≤ U := by
    calc
      |∫ x, g (g0 k) x ∂μ| ≤ ∫ x, |g (g0 k) x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _x, U ∂μ := integral_mono hint.abs (integrable_const U) (henv (g0 k))
      _ = U := by simp
  have havg : |(n : ℝ)⁻¹ * ∑ i, g (g0 k) (w i)| ≤ U := by
    calc
      |(n : ℝ)⁻¹ * ∑ i, g (g0 k) (w i)| =
          (n : ℝ)⁻¹ * |∑ i, g (g0 k) (w i)| := by
            rw [abs_mul, abs_of_pos (inv_pos.mpr (Nat.cast_pos.mpr hn))]
      _ ≤ (n : ℝ)⁻¹ * ∑ i, |g (g0 k) (w i)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, U := by gcongr with i; exact henv (g0 k) (w i)
      _ = U := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  change |(n : ℝ)⁻¹ * ∑ i, g (g0 k) (w i) - ∫ x, g (g0 k) x ∂μ| ≤ 2 * U
  exact (abs_sub _ _).trans (by linarith)

private lemma varianceAdaptiveRate_le_logRatio {U σ A v : ℝ} {n : ℕ}
    (hσ : 0 < σ) (hσU : σ < U) (hA : Real.exp 1 ≤ A) (hv : 1 ≤ v)
    (hn : 0 < n) :
    let L0 := Real.log (U / σ)
    let L := vcMaximalLog A U σ
    let q := max (Real.sqrt (v * L / L0)) (v * L / L0)
    vcExpectedMaximalRate U σ A v n ≤
      q * (σ * Real.sqrt (L0 / n) + U * L0 / n) := by
  dsimp only
  have hU : 0 < U := hσ.trans hσU
  have hratio : 1 < U / σ := (lt_div_iff₀ hσ).2 (by simpa using hσU)
  have hL0 : 0 < Real.log (U / σ) := Real.log_pos hratio
  have hA1 : 1 ≤ A := (Real.one_le_exp (by norm_num)).trans hA
  have hbase : U / σ ≤ max (Real.exp 1) (A * U / σ) := by
    apply le_trans ?_ (le_max_right _ _)
    calc
      U / σ ≤ A * (U / σ) := le_mul_of_one_le_left (div_nonneg hU.le hσ.le) hA1
      _ = A * U / σ := by ring
  have hLle : Real.log (U / σ) ≤ vcMaximalLog A U σ := by
    unfold vcMaximalLog
    exact Real.log_le_log (div_pos hU hσ) hbase
  have hL : 0 < vcMaximalLog A U σ := hL0.trans_le hLle
  have hvl : 0 ≤ v * vcMaximalLog A U σ / Real.log (U / σ) := by positivity
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt :
      Real.sqrt (v * vcMaximalLog A U σ / (n : ℝ)) =
        Real.sqrt (v * vcMaximalLog A U σ / Real.log (U / σ)) *
          Real.sqrt (Real.log (U / σ) / (n : ℝ)) := by
    rw [← Real.sqrt_mul hvl]
    congr 1
    field_simp
  have hlead :
      σ * Real.sqrt (v * vcMaximalLog A U σ / (n : ℝ)) ≤
        max (Real.sqrt (v * vcMaximalLog A U σ / Real.log (U / σ)))
            (v * vcMaximalLog A U σ / Real.log (U / σ)) *
          (σ * Real.sqrt (Real.log (U / σ) / (n : ℝ))) := by
    rw [hsqrt]
    calc
      σ * (Real.sqrt (v * vcMaximalLog A U σ / Real.log (U / σ)) *
          Real.sqrt (Real.log (U / σ) / (n : ℝ))) =
          Real.sqrt (v * vcMaximalLog A U σ / Real.log (U / σ)) *
            (σ * Real.sqrt (Real.log (U / σ) / (n : ℝ))) := by ring
      _ ≤ max (Real.sqrt (v * vcMaximalLog A U σ / Real.log (U / σ)))
            (v * vcMaximalLog A U σ / Real.log (U / σ)) *
          (σ * Real.sqrt (Real.log (U / σ) / (n : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (mul_nonneg hσ.le (Real.sqrt_nonneg _))
  have hsecond :
      v * U * vcMaximalLog A U σ / (n : ℝ) ≤
        max (Real.sqrt (v * vcMaximalLog A U σ / Real.log (U / σ)))
            (v * vcMaximalLog A U σ / Real.log (U / σ)) *
          (U * Real.log (U / σ) / (n : ℝ)) := by
    have heq : v * U * vcMaximalLog A U σ / (n : ℝ) =
        (v * vcMaximalLog A U σ / Real.log (U / σ)) *
          (U * Real.log (U / σ) / (n : ℝ)) := by field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by positivity)
  unfold vcExpectedMaximalRate
  nlinarith [hlead, hsecond]

private lemma countableEmpiricalSup_le_two_envelope {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ι → Ω → ℝ) (g0 : ℕ → ι) {U : ℝ} (hU : 0 < U)
    (hmeas : ∀ i, Measurable (g i)) (henv : ∀ i x, |g i x| ≤ U)
    {n : ℕ} (hn : 0 < n) (w : Fin n → Ω) :
    countableEmpiricalSup μ (fun k => g (g0 k)) w ≤ 2 * U := by
  unfold countableEmpiricalSup uniformDeviation
  apply ciSup_le
  intro k
  have hint : Integrable (g (g0 k)) μ :=
    Integrable.of_bound (hmeas (g0 k)).aestronglyMeasurable U
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using henv (g0 k) x)
  have hmean : |∫ x, g (g0 k) x ∂μ| ≤ U := by
    calc
      |∫ x, g (g0 k) x ∂μ| ≤ ∫ x, |g (g0 k) x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _x, U ∂μ := integral_mono hint.abs (integrable_const U) (henv (g0 k))
      _ = U := by simp
  have havg : |(n : ℝ)⁻¹ * ∑ i, g (g0 k) (w i)| ≤ U := by
    calc
      |(n : ℝ)⁻¹ * ∑ i, g (g0 k) (w i)| =
          (n : ℝ)⁻¹ * |∑ i, g (g0 k) (w i)| := by
            rw [abs_mul, abs_of_pos (inv_pos.mpr (Nat.cast_pos.mpr hn))]
      _ ≤ (n : ℝ)⁻¹ * ∑ i, |g (g0 k) (w i)| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, U := by gcongr with i; exact henv (g0 k) (w i)
      _ = U := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  change |(n : ℝ)⁻¹ * ∑ i, g (g0 k) (w i) - ∫ x, g (g0 k) x ∂μ| ≤ 2 * U
  exact (abs_sub _ _).trans (by linarith)

/-- Dudley chaining plus the proved VC covering layer gives a sub-root
Rademacher envelope from polynomial entropy. -/
lemma vcEntropy_chaining_bound
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : ι → Ω → ℝ) (g0 : ℕ → ι) (U σ A v : ℝ)
    (hent : HasVCUniformEntropy μ g U σ A v) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∫⁻ w, countableEmpiricalProcessSup μ g g0 w
          ∂Measure.pi (fun _ : Fin n => μ) ≤
        ENNReal.ofReal (C *
          (σ * Real.sqrt (Real.log (U / σ) / n) +
            U * Real.log (U / σ) / n)) := by
  rcases hent with ⟨hσ, hσU, hA, hv, hmeas, henv, hL2, hcover⟩
  let L0 := Real.log (U / σ)
  let L := vcMaximalLog A U σ
  let q := max (Real.sqrt (v * L / L0)) (v * L / L0)
  let C := varianceAdaptiveVCConstant * q
  have hU : 0 < U := hσ.trans hσU
  have hratio : 1 < U / σ := (lt_div_iff₀ hσ).2 (by simpa using hσU)
  have hL0 : 0 < L0 := Real.log_pos hratio
  have hA1 : 1 ≤ A := (Real.one_le_exp (by norm_num)).trans hA
  have hbase : U / σ ≤ max (Real.exp 1) (A * U / σ) := by
    apply le_trans ?_ (le_max_right _ _)
    calc
      U / σ ≤ A * (U / σ) := le_mul_of_one_le_left (div_nonneg hU.le hσ.le) hA1
      _ = A * U / σ := by ring
  have hLle : L0 ≤ L := by
    dsimp only [L0, L, vcMaximalLog]
    exact Real.log_le_log (div_pos hU hσ) hbase
  have hL : 0 < L := hL0.trans_le hLle
  have hq : 0 < q := by
    dsimp only [q]
    exact lt_of_lt_of_le (div_pos (mul_pos (lt_of_lt_of_le zero_lt_one hv) hL) hL0)
      (le_max_right _ _)
  refine ⟨C, mul_pos (by norm_num [varianceAdaptiveVCConstant]) hq, ?_⟩
  intro n hn
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  let F : ℕ → Ω → ℝ := fun k => g (g0 k)
  let μn : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  have hFmeas : ∀ k, Measurable (F k) := fun k => hmeas (g0 k)
  have hFenv : ∀ k x, |F k x| ≤ U := fun k x => henv (g0 k) x
  have hmain := varianceAdaptiveExpectedMaximal_le μ F hσ hσU hA hv
    hFmeas hFenv (fun k => hL2 (g0 k)) (hcover g0) n hn0
  have hrate := varianceAdaptiveRate_le_logRatio hσ hσU hA hv hn0
  have hreal :
      ∫ w, countableEmpiricalSup μ F w ∂μn ≤
        C * (σ * Real.sqrt (Real.log (U / σ) / (n : ℝ)) +
          U * Real.log (U / σ) / (n : ℝ)) := by
    calc
      ∫ w, countableEmpiricalSup μ F w ∂μn ≤
          varianceAdaptiveVCConstant * vcExpectedMaximalRate U σ A v n := hmain
      _ ≤ varianceAdaptiveVCConstant *
          (q * (σ * Real.sqrt (Real.log (U / σ) / (n : ℝ)) +
            U * Real.log (U / σ) / (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hrate (by norm_num [varianceAdaptiveVCConstant])
      _ = C * (σ * Real.sqrt (Real.log (U / σ) / (n : ℝ)) +
          U * Real.log (U / σ) / (n : ℝ)) := by simp only [C]; ring
  have hdevMeas : Measurable (fun w : Fin n → Ω => countableEmpiricalSup μ F w) := by
    exact uniformDeviation_measurable id hFmeas
  have hdevBound : ∀ w : Fin n → Ω, countableEmpiricalSup μ F w ≤ 2 * U := by
    intro w
    exact countableEmpiricalSup_le_two_envelope μ g g0 hU hmeas henv hn0 w
  have hdevNonneg : ∀ w : Fin n → Ω, 0 ≤ countableEmpiricalSup μ F w := by
    intro w
    exact Real.iSup_nonneg fun k => abs_nonneg _
  have hdevInt : Integrable (fun w : Fin n → Ω => countableEmpiricalSup μ F w) μn :=
    Integrable.of_bound hdevMeas.aestronglyMeasurable (2 * U)
      (ae_of_all _ fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hdevNonneg w)]
        exact hdevBound w)
  simp_rw [countableEmpiricalProcessSup_eq_of_envelope μ g g0 hU hmeas henv hn0]
  rw [← ofReal_integral_eq_lintegral_ofReal hdevInt (ae_of_all _ hdevNonneg)]
  exact ENNReal.ofReal_le_ofReal hreal

end Causalean.Stat.Concentration
