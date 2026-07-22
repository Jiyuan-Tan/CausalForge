/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sequential DR remainder identity — proof helpers

Private-style lemmas used by `RemainderIdentity.lean`:
indicator equalities, overlap positivity, and integrability
of indicator-weighted residuals.
-/

import Causalean.Estimation.DTR.MeanZero
import Causalean.Estimation.DTR.ScorePullout
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Sequential DR Remainder Helpers

This file provides the helper lemmas used to expand the two-stage sequential
doubly robust DTR remainder identity. It relates factual treatment equality
checks to the target-regime indicators (`indEq_factualD0_eq_indicator`,
`indEq_factualD1_eq_indicator`), extracts positivity from the overlap-bounded
nuisance set (`eta_e0_pos_of_mem_Hε`, `eta_e1_pos_of_mem_Hε`), proves the
indicator-weighted outcome-regression error terms are integrable, and supplies
`split_stage_history_integral` to split integrals over the full observed DTR
law into the stage-history marginals `P_H₀` and `P_H₁`. -/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- The stage-zero equality indicator agrees with the stage-zero treatment
indicator for the target regime. -/
lemma indEq_factualD0_eq_indicator
    (S : DTREstimationSystem P δ γ) (ω : P.Ω) :
    indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
        (S.dbar ⟨0, by decide⟩)
      =
      (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
        (S.dbar ⟨0, by decide⟩) ω := by
  by_cases hD : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω =
      S.dbar ⟨0, by decide⟩
  · have hI :
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
          (S.dbar ⟨0, by decide⟩) ω = 1 :=
      (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_one hD
    have hDn : S.toPODTRSystem.factualD 0 ω = S.dbar 0 := by simpa using hD
    have hIn : (S.toPODTRSystem.dVar 0).indicator (S.dbar 0) ω = 1 := by
      simpa using hI
    simp [indEq, hDn, hIn]
  · have hI :
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
          (S.dbar ⟨0, by decide⟩) ω = 0 :=
      (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_zero hD
    have hDn : ¬ S.toPODTRSystem.factualD 0 ω = S.dbar 0 := by simpa using hD
    have hIn : (S.toPODTRSystem.dVar 0).indicator (S.dbar 0) ω = 0 := by
      simpa using hI
    simp [indEq, hDn, hIn]

/-- The stage-one equality indicator agrees with the stage-one treatment
indicator for the target regime. -/
lemma indEq_factualD1_eq_indicator
    (S : DTREstimationSystem P δ γ) (ω : P.Ω) :
    indEq (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
        (S.dbar ⟨1, by decide⟩)
      =
      (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
        (S.dbar ⟨1, by decide⟩) ω := by
  by_cases hD : S.toPODTRSystem.factualD ⟨1, by decide⟩ ω =
      S.dbar ⟨1, by decide⟩
  · have hI :
        (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
          (S.dbar ⟨1, by decide⟩) ω = 1 :=
      (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_one hD
    have hDn : S.toPODTRSystem.factualD 1 ω = S.dbar 1 := by simpa using hD
    have hIn : (S.toPODTRSystem.dVar 1).indicator (S.dbar 1) ω = 1 := by
      simpa using hI
    simp [indEq, hDn, hIn]
  · have hI :
        (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
          (S.dbar ⟨1, by decide⟩) ω = 0 :=
      (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_zero hD
    have hDn : ¬ S.toPODTRSystem.factualD 1 ω = S.dbar 1 := by simpa using hD
    have hIn : (S.toPODTRSystem.dVar 1).indicator (S.dbar 1) ω = 0 := by
      simpa using hI
    simp [indEq, hDn, hIn]

/-- Any nuisance vector in the overlap-bounded set has a positive stage-zero propensity. -/
lemma eta_e0_pos_of_mem_Hε
    {η : DTRNuisanceVec₂ δ γ} {ε : ℝ}
    (hε : 0 < ε) (hη : η ∈ DTREstimationSystem.H_ε (δ := δ) (γ := γ) ε)
    (s₀ : γ 0) :
    0 < η.e₀_fn s₀ :=
  lt_of_lt_of_le hε (hη.1 s₀).1

/-- Any nuisance vector in the overlap-bounded set has a positive stage-one propensity. -/
lemma eta_e1_pos_of_mem_Hε
    {η : DTRNuisanceVec₂ δ γ} {ε : ℝ}
    (hε : 0 < ε) (hη : η ∈ DTREstimationSystem.H_ε (δ := δ) (γ := γ) ε)
    (h : γ 1 × δ × γ 0) :
    0 < η.e₁_fn h :=
  lt_of_lt_of_le hε (hη.2 h).1

/-- The stage-zero indicator-weighted stage-zero outcome-regression error is integrable. -/
lemma indicator_weighted_delta_mu0_integrable
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (hε : 0 < ε)
    (η : DTRNuisanceVec₂ δ γ) (hη : η ∈ DTREstimationSystem.H_ε ε)
    (hΔμ₀_memLp : MemLp (fun s₀ => η.μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀) :
    Integrable
      (fun ω =>
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          (1 / η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) *
          (η.μ₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
            S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) P.μ := by
  let I0 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
      (S.dbar ⟨0, by decide⟩)
  let W0 : P.Ω → ℝ := fun ω =>
    I0 ω * (1 / η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))
  let dμ0 : P.Ω → ℝ := fun ω =>
    η.μ₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
      S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  have hdμ0_L2 : MemLp dμ0 2 P.μ := by
    have hd := MemLp.comp_of_map
      (f := S.toPODTRSystem.factualS ⟨0, by decide⟩) hΔμ₀_memLp
      (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩).aemeasurable
    simpa [dμ0, DTREstimationSystem.P_H₀] using hd
  have hW0_meas : Measurable W0 := by
    dsimp [W0, I0]
    exact ((S.toPODTRSystem.dVar ⟨0, by decide⟩).measurable_indicator
      (S.dbar ⟨0, by decide⟩)).mul
      (measurable_const.div
        (η.e₀_meas.comp (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩)))
  have hW0_bound : ∀ᵐ ω ∂P.μ, ‖W0 ω‖ ≤ ε⁻¹ := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    by_cases hD : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · have hI : I0 ω = 1 :=
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_one hD
      have hpos := eta_e0_pos_of_mem_Hε hε hη
        (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
      have hle : (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hpos hε).2
          (hη.1 (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)).1
      have hle_abs :
          |η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)|⁻¹ ≤ ε⁻¹ := by
        rw [abs_of_pos hpos]
        exact hle
      simpa [W0, hI, one_div, Real.norm_eq_abs] using hle_abs
    · have hI : I0 ω = 0 :=
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_zero hD
      have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
      simpa [W0, hI] using hεinv_nonneg
  have hW0_Linf : MemLp W0 ⊤ P.μ :=
    MemLp.of_bound hW0_meas.aestronglyMeasurable ε⁻¹ hW0_bound
  have hL2 : MemLp (fun ω => W0 ω * dμ0 ω) 2 P.μ :=
    hdμ0_L2.mul hW0_Linf
  exact (hL2.integrable (by norm_num)).congr
    (Filter.Eventually.of_forall (fun ω => by
      simp [W0, I0, dμ0]))

/-- The stage-zero indicator-weighted stage-one outcome-regression error is integrable. -/
lemma indicator_weighted_delta_mu1_stage0_integrable
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (hε : 0 < ε)
    (η : DTRNuisanceVec₂ δ γ) (hη : η ∈ DTREstimationSystem.H_ε ε)
    (hΔμ₁_memLp : MemLp (fun h => η.μ₁_fn h - S.μ₁_val h) 2 S.P_H₁) :
    Integrable
      (fun ω =>
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          (1 / η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) *
          (η.μ₁_fn
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
            S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) P.μ := by
  let H1 : P.Ω → γ 1 × δ × γ 0 := fun ω =>
    (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
     S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
     S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  let I0 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
      (S.dbar ⟨0, by decide⟩)
  let W0 : P.Ω → ℝ := fun ω =>
    I0 ω * (1 / η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))
  let dμ1 : P.Ω → ℝ := fun ω => η.μ₁_fn (H1 ω) - S.μ₁_val (H1 ω)
  have hH1_meas : Measurable H1 := by
    dsimp [H1]
    exact (S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩).prod
      ((S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩).prod
        (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩))
  have hdμ1_L2 : MemLp dμ1 2 P.μ := by
    have hd := MemLp.comp_of_map (f := H1) hΔμ₁_memLp hH1_meas.aemeasurable
    simpa [dμ1, H1, DTREstimationSystem.P_H₁] using hd
  have hW0_meas : Measurable W0 := by
    dsimp [W0, I0]
    exact ((S.toPODTRSystem.dVar ⟨0, by decide⟩).measurable_indicator
      (S.dbar ⟨0, by decide⟩)).mul
      (measurable_const.div
        (η.e₀_meas.comp (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩)))
  have hW0_bound : ∀ᵐ ω ∂P.μ, ‖W0 ω‖ ≤ ε⁻¹ := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    by_cases hD : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · have hI : I0 ω = 1 :=
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_one hD
      have hpos := eta_e0_pos_of_mem_Hε hε hη
        (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
      have hle : (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hpos hε).2
          (hη.1 (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)).1
      have hle_abs :
          |η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)|⁻¹ ≤ ε⁻¹ := by
        rw [abs_of_pos hpos]
        exact hle
      simpa [W0, hI, one_div, Real.norm_eq_abs] using hle_abs
    · have hI : I0 ω = 0 :=
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_zero hD
      have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
      simpa [W0, hI] using hεinv_nonneg
  have hW0_Linf : MemLp W0 ⊤ P.μ :=
    MemLp.of_bound hW0_meas.aestronglyMeasurable ε⁻¹ hW0_bound
  have hL2 : MemLp (fun ω => W0 ω * dμ1 ω) 2 P.μ :=
    hdμ1_L2.mul hW0_Linf
  exact (hL2.integrable (by norm_num)).congr
    (Filter.Eventually.of_forall (fun ω => by
      simp [W0, I0, dμ1, H1]))

/-- The double-indicator-weighted stage-one outcome-regression error is integrable. -/
lemma indicator_weighted_delta_mu1_stage1_integrable
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (hε : 0 < ε)
    (η : DTRNuisanceVec₂ δ γ) (hη : η ∈ DTREstimationSystem.H_ε ε)
    (hΔμ₁_memLp : MemLp (fun h => η.μ₁_fn h - S.μ₁_val h) 2 S.P_H₁) :
    Integrable
      (fun ω =>
        ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩) ω *
          (1 / (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            η.e₁_fn
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)))) *
          (η.μ₁_fn
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
            S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) P.μ := by
  let H1 : P.Ω → γ 1 × δ × γ 0 := fun ω =>
    (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
     S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
     S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  let I0 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
      (S.dbar ⟨0, by decide⟩)
  let I1 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
      (S.dbar ⟨1, by decide⟩)
  let W1 : P.Ω → ℝ := fun ω =>
    I0 ω * I1 ω *
      (1 / (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        η.e₁_fn (H1 ω)))
  let dμ1 : P.Ω → ℝ := fun ω => η.μ₁_fn (H1 ω) - S.μ₁_val (H1 ω)
  have hH1_meas : Measurable H1 := by
    dsimp [H1]
    exact (S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩).prod
      ((S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩).prod
        (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩))
  have hdμ1_L2 : MemLp dμ1 2 P.μ := by
    have hd := MemLp.comp_of_map (f := H1) hΔμ₁_memLp hH1_meas.aemeasurable
    simpa [dμ1, H1, DTREstimationSystem.P_H₁] using hd
  have hW1_meas : Measurable W1 := by
    dsimp [W1, I0, I1, H1]
    exact (((S.toPODTRSystem.dVar ⟨0, by decide⟩).measurable_indicator
      (S.dbar ⟨0, by decide⟩)).mul
      ((S.toPODTRSystem.dVar ⟨1, by decide⟩).measurable_indicator
        (S.dbar ⟨1, by decide⟩))).mul
      (measurable_const.div
        ((η.e₀_meas.comp (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩)).mul
          (η.e₁_meas.comp hH1_meas)))
  have hW1_bound : ∀ᵐ ω ∂P.μ, ‖W1 ω‖ ≤ (ε * ε)⁻¹ := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    by_cases hD0 : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · by_cases hD1 : S.toPODTRSystem.factualD ⟨1, by decide⟩ ω =
          S.dbar ⟨1, by decide⟩
      · have hI0 : I0 ω = 1 :=
          (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_one hD0
        have hI1 : I1 ω = 1 :=
          (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_one hD1
        have hpos0 := eta_e0_pos_of_mem_Hε hε hη
          (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
        have hpos1 := eta_e1_pos_of_mem_Hε hε hη (H1 ω)
        have hprod_le :
            ε * ε ≤ η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
              η.e₁_fn (H1 ω) :=
          mul_le_mul
            (hη.1 (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)).1
            (hη.2 (H1 ω)).1 hε.le hpos0.le
        have hle :
            (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
              η.e₁_fn (H1 ω))⁻¹ ≤ (ε * ε)⁻¹ :=
          (inv_le_inv₀ (mul_pos hpos0 hpos1) (mul_pos hε hε)).2 hprod_le
        have hle_abs :
            |η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
              η.e₁_fn (H1 ω)|⁻¹ ≤ (ε * ε)⁻¹ := by
          rw [abs_of_pos (mul_pos hpos0 hpos1)]
          exact hle
        simpa [W1, hI0, hI1, one_div, Real.norm_eq_abs] using hle_abs
      · have hI1 : I1 ω = 0 :=
          (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_zero hD1
        have hnonneg : 0 ≤ (ε * ε)⁻¹ := inv_nonneg.mpr (mul_nonneg hε.le hε.le)
        simpa [W1, hI1] using hnonneg
    · have hI0 : I0 ω = 0 :=
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_zero hD0
      have hnonneg : 0 ≤ (ε * ε)⁻¹ := inv_nonneg.mpr (mul_nonneg hε.le hε.le)
      simpa [W1, hI0] using hnonneg
  have hW1_Linf : MemLp W1 ⊤ P.μ :=
    MemLp.of_bound hW1_meas.aestronglyMeasurable (ε * ε)⁻¹ hW1_bound
  have hL2 : MemLp (fun ω => W1 ω * dμ1 ω) 2 P.μ :=
    hdμ1_L2.mul hW1_Linf
  exact (hL2.integrable (by norm_num)).congr
    (Filter.Eventually.of_forall (fun ω => by
      simp [W1, I0, I1, dμ1, H1]))

/-- An integral over the full observed DTR law splits into the sum of integrals
over the two stage-history marginals. -/
lemma split_stage_history_integral
    (S : DTREstimationSystem P δ γ)
    (f₀ : γ 0 → ℝ) (f₁ : γ 1 × δ × γ 0 → ℝ)
    (hf₀_meas : Measurable f₀) (hf₁_meas : Measurable f₁)
    (hf₀_int : Integrable f₀ S.P_H₀)
    (hf₁_int : Integrable f₁ S.P_H₁) :
    ∫ z, f₀ (projS₀ z) + f₁ (histH₁ z) ∂(S.P_Z)
      = ∫ s₀, f₀ s₀ ∂(S.P_H₀) + ∫ h, f₁ h ∂(S.P_H₁) := by
  have hcomp₀_int :
      Integrable (fun z : γ 0 × δ × γ 1 × δ × ℝ => f₀ (projS₀ z)) S.P_Z := by
    rw [← P_Z_map_projS₀_eq_P_H₀ S] at hf₀_int
    exact (MeasureTheory.integrable_map_measure
      hf₀_meas.aestronglyMeasurable measurable_projS₀.aemeasurable).1 hf₀_int
  have hcomp₁_int :
      Integrable (fun z : γ 0 × δ × γ 1 × δ × ℝ => f₁ (histH₁ z)) S.P_Z := by
    rw [← P_Z_map_histH₁_eq_P_H₁ S] at hf₁_int
    exact (MeasureTheory.integrable_map_measure
      hf₁_meas.aestronglyMeasurable measurable_histH₁.aemeasurable).1 hf₁_int
  calc
    ∫ z, f₀ (projS₀ z) + f₁ (histH₁ z) ∂(S.P_Z)
        = ∫ z, f₀ (projS₀ z) ∂(S.P_Z) +
            ∫ z, f₁ (histH₁ z) ∂(S.P_Z) := by
          exact MeasureTheory.integral_add hcomp₀_int hcomp₁_int
    _ = ∫ s₀, f₀ s₀ ∂(S.P_H₀) +
            ∫ h, f₁ h ∂(S.P_H₁) := by
          have hmap₀ :
              ∫ z, f₀ (projS₀ z) ∂(S.P_Z) = ∫ s₀, f₀ s₀ ∂(S.P_H₀) := by
            rw [← MeasureTheory.integral_map measurable_projS₀.aemeasurable
              hf₀_meas.aestronglyMeasurable]
            rw [P_Z_map_projS₀_eq_P_H₀ S]
          have hmap₁ :
              ∫ z, f₁ (histH₁ z) ∂(S.P_Z) = ∫ h, f₁ h ∂(S.P_H₁) := by
            rw [← MeasureTheory.integral_map measurable_histH₁.aemeasurable
              hf₁_meas.aestronglyMeasurable]
            rw [P_Z_map_histH₁_eq_P_H₁ S]
          rw [hmap₀, hmap₁]

end DTREstimationSystem

end DTR
end Estimation
end Causalean
