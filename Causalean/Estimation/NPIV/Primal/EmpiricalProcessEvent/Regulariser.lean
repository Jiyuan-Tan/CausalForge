/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEvents

/-! # Regularizer Event for the Primal NPIV Rate

This file derives the localized empirical-process event needed to compare the
empirical regularized objective at the estimator with the objective at a
population Tikhonov candidate. The bounds connect the localized deviation
events to the regularization terms in the primal NPIV rate proof, producing an
all-sample-size centred empirical regularizer bound from the localized event for
the squared candidate-difference class. -/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- If each event in a countable family has probability at least one minus its
assigned error, then their intersection has probability at least one minus the
sum of those errors. -/
lemma measure_iInter_nat_ge_one_sub_tsum_of_ge
    [IsProbabilityMeasure μ]
    {E : ℕ → Set Ω} {a : ℕ → ENNReal}
    (hE_meas : ∀ n, MeasurableSet (E n))
    (hE : ∀ n, μ (E n) ≥ 1 - a n) :
    μ (⋂ n, E n) ≥ 1 - ∑' n, a n := by
  have hE_compl : ∀ n, μ (E n)ᶜ ≤ a n := by
    intro n
    have hone_le : (1 : ENNReal) ≤ a n + μ (E n) :=
      tsub_le_iff_left.mp (hE n)
    rw [measure_compl (hE_meas n) (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
  have hbad_subset : (⋂ n, E n)ᶜ ⊆ ⋃ n, (E n)ᶜ := by
    simp
  have hbad_le : μ (⋂ n, E n)ᶜ ≤ ∑' n, a n := by
    calc
      μ (⋂ n, E n)ᶜ ≤ μ (⋃ n, (E n)ᶜ) := measure_mono hbad_subset
      _ ≤ ∑' n, μ (E n)ᶜ := measure_iUnion_le fun n => (E n)ᶜ
      _ ≤ ∑' n, a n := ENNReal.tsum_le_tsum hE_compl
  have hA_meas : MeasurableSet (⋂ n, E n) := MeasurableSet.iInter hE_meas
  rw [measure_compl hA_meas (measure_ne_top _ _), measure_univ] at hbad_le
  have hone_le : (1 : ENNReal) ≤ (∑' n, a n) + μ (⋂ n, E n) :=
    tsub_le_iff_right.mp hbad_le
  exact tsub_le_iff_left.mpr hone_le

/-- The centred empirical regularizer gap is bounded uniformly over all sample
sizes by the localized rate from the squared candidate-difference event.

For every confidence level, there is a high-probability event on which the
empirical-vs-population regularizer discrepancy between the estimator and the
population Tikhonov candidate is controlled for every eligible split size:

    |λ ((‖h*‖²_{A(n)} − ‖ĥ‖²_{A(n)}) − (‖h*‖² − ‖ĥ‖²))|
      ≤ K_reg · λ · (δ_n · ‖ĥ − h*‖ + δ_n²).
-/
theorem centred_regulariser_bound_from_localized
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    {is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat}
    (sc : SourceCondition S β)
    (tb : TikhonovBiasBound S β lambda sc)
    [IsProbabilityMeasure μ]
    (regimes : ∀ n, LocalizedRegimes S TC sample sc tb (split.n₁ n) (delta n))
    (lambda_nonneg : 0 ≤ lambda)
    {ζ : ℝ} (hζ_pos : 0 < ζ) (hζ_lt : ζ < 1) :
    ∃ Aζ_reg : Set Ω,
      MeasurableSet Aζ_reg ∧ μ Aζ_reg ≥ 1 - ENNReal.ofReal ζ ∧
      ∀ ω ∈ Aζ_reg, ∀ n : ℕ, 1 ≤ split.n₁ n →
        |lambda *
            ((((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                (tb.h_lambda_star_fun (S.xOf (sample.Z (k : ℕ) ω))) ^ 2
              - ((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                  (h_hat n ω (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
              - ((S.strongNorm (S.hL2 tb.h_lambda_star_mem)) ^ 2
                - (S.strongNorm
                    (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)))) ^ 2))|
        ≤ lambda *
            (4 * ((regimes n).H_diameter + delta n) *
                criticalRadius ((regimes n).bundle_H.regime.ψ (split.n₁ n))
              + (regimes n).bundle_H.regime.b *
                  Real.sqrt
                    (2 * Real.log ((2 : ℝ) ^ (n + 1) / ζ)
                      / (split.n₁ n))) := by
  classical
  let ε : ℕ → ℝ := fun n => ζ * ((1 / 2 : ℝ) ^ (n + 1))
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    exact mul_pos hζ_pos (pow_pos (by norm_num) _)
  have hε_le_one : ∀ n, ε n ≤ 1 := by
    intro n
    have hζ_le : ζ ≤ 1 := le_of_lt hζ_lt
    have hpow_le_one : ((1 / 2 : ℝ) ^ (n + 1)) ≤ 1 := by
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hpow_nonneg : 0 ≤ ((1 / 2 : ℝ) ^ (n + 1)) := by positivity
    nlinarith
  let En : ℕ → Set Ω := fun n =>
    if hn : 0 < split.n₁ n then
      (localized_omega_event_for_H
        (regime := regimes n) hn (hε_pos n) (hε_le_one n)).choose
    else Set.univ
  have hEn_meas : ∀ n, MeasurableSet (En n) := by
    intro n
    dsimp [En]
    split
    · rename_i hn
      exact (localized_omega_event_for_H
        (regime := regimes n) hn (hε_pos n) (hε_le_one n)).choose_spec.1
    · exact MeasurableSet.univ
  have hEn_mass : ∀ n, μ (En n) ≥ 1 - ENNReal.ofReal (ε n) := by
    intro n
    dsimp [En]
    split
    · rename_i hn
      exact (localized_omega_event_for_H
        (regime := regimes n) hn (hε_pos n) (hε_le_one n)).choose_spec.2.1
    · rw [measure_univ]
      exact tsub_le_self
  have htsum_ε : (∑' n, ENNReal.ofReal (ε n)) ≤ ENNReal.ofReal ζ := by
    have hterm :
        (fun n => ENNReal.ofReal (ε n))
          =
        fun n => ENNReal.ofReal ζ * (2⁻¹ : ENNReal) ^ (n + 1) := by
      funext n
      rw [show ε n = ζ * (1 / 2 : ℝ) ^ (n + 1) by rfl]
      rw [ENNReal.ofReal_mul (le_of_lt hζ_pos)]
      simp [one_div, ENNReal.inv_pow]
    rw [hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
    have hgeom : (2⁻¹ : ENNReal) * (1 - 2⁻¹)⁻¹ = 1 := by
      rw [ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' (2 : ENNReal)))
        (by norm_num : (2 : ENNReal) ≠ ⊤)
    rw [hgeom, mul_one]
  let Aζ_reg : Set Ω := ⋂ n, En n
  refine ⟨Aζ_reg, MeasurableSet.iInter hEn_meas, ?_, ?_⟩
  · exact (tsub_le_tsub_left htsum_ε 1).trans
      (measure_iInter_nat_ge_one_sub_tsum_of_ge hEn_meas hEn_mass)
  · intro ω hω n hn
    have hn_pos : 0 < split.n₁ n := lt_of_lt_of_le zero_lt_one hn
    have hωn : ω ∈ En n := Set.mem_iInter.mp hω n
    have hωn_event :
        ω ∈ (localized_omega_event_for_H
          (regime := regimes n) hn_pos (hε_pos n) (hε_le_one n)).choose := by
      simpa [En, hn_pos] using hωn
    have hdev :=
      (localized_omega_event_for_H
        (regime := regimes n) hn_pos (hε_pos n) (hε_le_one n)).choose_spec.2.2
        ω hωn_event
        tb.h_lambda_star_fun (regimes n).realizability
        (h_hat n ω) (is_estimator.mem_H n ω)
    have hstar_sq :
        (S.strongNorm (S.hL2 tb.h_lambda_star_mem)) ^ 2 =
          ∫ ω', (tb.h_lambda_star_fun (S.xOf (S.W ω'))) ^ 2 ∂μ :=
      S.strongNorm_sq_hL2_eq_integral tb.h_lambda_star_mem
    have hhat_sq :
        (S.strongNorm (S.hL2 (TC.H_subset (is_estimator.mem_H n ω)))) ^ 2 =
          ∫ ω', (h_hat n ω (S.xOf (S.W ω'))) ^ 2 ∂μ :=
      S.strongNorm_sq_hL2_eq_integral (TC.H_subset (is_estimator.mem_H n ω))
    have hlog :
        1 / ε n = (2 : ℝ) ^ (n + 1) / ζ := by
      dsimp [ε]
      simp only [one_div]
      rw [inv_pow]
      field_simp [ne_of_gt hζ_pos,
        pow_ne_zero (n + 1) (show (2 : ℝ) ≠ 0 by norm_num)]
    rw [hlog] at hdev
    have hmul := mul_le_mul_of_nonneg_left hdev lambda_nonneg
    simpa [abs_mul, abs_of_nonneg lambda_nonneg, hstar_sq, hhat_sq, mul_assoc]
      using hmul


end Primal
end NPIV
end Estimation
end Causalean
