/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite variance of the sequential DR (DTR) influence function

`E[ψ_seqDR²] < ∞` under DTR backdoor assumptions, two-stage strict
overlap, `E[Y²] < ∞`, and square-integrability of every counterfactual
outcome `Y(dbar)`.

Mirrors `Estimation/ATE/FiniteVar.lean` but with two stages of L²
nuisance bookkeeping: stagewise outcome regressions and stagewise
inverse-propensity weights are L^∞ on the bounded-overlap set.
-/

import Causalean.Estimation.DTR.SeqDRMoment
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Finite Variance for Sequential DR

This file proves square integrability of the sequential doubly robust
influence function for a two-stage dynamic treatment regime. The proof extends
the average-treatment-effect finite-variance argument to stagewise histories,
propensity weights, and counterfactual outcome regressions under strict
overlap. -/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- Measurability helper: the squared sequential DR influence function on
the data tuple is measurable.  Used in the L² bookkeeping for
`seqDR_finite_var`. -/
lemma measurable_ψ_seqDR_squared (S : DTREstimationSystem P δ γ) :
    Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ => (S.ψ_seqDR z) ^ 2) := by
  exact (S.measurable_seqDRMomentFunctional S.η₀ S.θ₀).pow_const 2

private lemma measurable_indEq_left (d : δ) :
    Measurable (fun x : δ => indEq x d) := by
  have hset : MeasurableSet {x : δ | x = d} :=
    MeasurableSet.singleton d
  convert (measurable_const.indicator hset :
    Measurable (Set.indicator {x : δ | x = d} (fun _ => (1 : ℝ)))) using 1

/-- **Finite variance of `ψ_seqDR`** — sequential DR (DTR) analogue of
`aipw_finite_var`.

Under DTR backdoor assumptions, two-stage strict overlap (`ε ∈ (0, 1/2]`
on each stagewise propensity), `E[Y²] < ∞`, and square-integrability of
every counterfactual outcome `Y(dbar)`, the sequential DR influence
function is square-integrable against the data law `P_Z`.

The `h_yd2` family is needed because each stagewise value-space
regression `μ_k_val` is identified a.e. with the corresponding
σ(historyBundle k)-conditional expectation of `Y(dbar)`, and conditional
Jensen converts L²(Y(dbar)) into L² of the conditional expectation. -/
theorem seqDR_finite_var (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ dbar : Fin 2 → δ,
      Integrable (fun ω => (S.toPODTRSystem.Y_of dbar ω) ^ 2) P.μ) :
    Integrable (fun z => (S.ψ_seqDR z) ^ 2) (S.P_Z) := by
  have hψ_meas : Measurable S.ψ_seqDR := by
    simpa [DTREstimationSystem.ψ_seqDR] using
      S.measurable_seqDRMomentFunctional S.η₀ S.θ₀
  have hY_L2 : MemLp S.toPODTRSystem.factualY 2 P.μ :=
    (memLp_two_iff_integrable_sq
      S.toPODTRSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hYd_L2 : MemLp (S.toPODTRSystem.Y_of S.dbar) 2 P.μ :=
    (memLp_two_iff_integrable_sq
      (S.toPODTRSystem.measurable_Y_of S.dbar).aestronglyMeasurable).2
        (h_yd2 S.dbar)
  have hμ0_L2 :
      MemLp
        (fun ω => S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))
        2 P.μ := by
    have hcond_L2 :
        MemLp ((S.toPODTRSystem.historyBundle 0 (by decide)).condExpGiven
          (S.toPODTRSystem.Y_of S.dbar) P.μ) 2 P.μ := by
      simpa [POCFBundle.condExpGiven] using hYd_L2.condExp
    exact hcond_L2.ae_eq (S.μ₀_compat hA)
  have hμ1_L2 :
      MemLp
        (fun ω => S.μ₁_val
          (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
           S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
           S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) 2 P.μ := by
    exact (S.stageOneReg_memLp h_overlap h_y2).ae_eq
      (S.μ₁_val_comp_eq_stageOneReg).symm
  have he0_lower :
      ∀ᵐ ω ∂P.μ,
        ε ≤ S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) := by
    filter_upwards [h_overlap.2.2, S.e₀_compat] with ω hover hcomp
    rw [← hcomp]
    exact hover.1.1
  have he1_lower :
      ∀ᵐ ω ∂P.μ,
        ε ≤ S.e₁_val
          (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
           S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
           S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) := by
    filter_upwards [h_overlap.2.2, S.e₁_compat] with ω hover hcomp
    rw [← hcomp]
    exact hover.2.1
  have hw0_bound :
      ∀ᵐ ω ∂P.μ,
        ‖indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩) /
          S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)‖ ≤ ε⁻¹ := by
    filter_upwards [he0_lower] with ω he
    by_cases hD : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · have hpos : 0 < S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) :=
        S.e₀_pos _
      have hle : (S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hpos h_overlap.1).2 he
      rw [indEq, if_pos hD, norm_div, norm_one, Real.norm_eq_abs, abs_of_pos hpos]
      simpa [one_div] using hle
    · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
      rw [indEq, if_neg hD, zero_div, norm_zero]
      exact hεinv_nonneg
  have hw1_bound :
      ∀ᵐ ω ∂P.μ,
        ‖(indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩) *
            indEq (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
              (S.dbar ⟨1, by decide⟩)) /
          (S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            S.e₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))‖ ≤ (ε * ε)⁻¹ := by
    filter_upwards [he0_lower, he1_lower] with ω he0 he1
    by_cases hD0 : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · by_cases hD1 : S.toPODTRSystem.factualD ⟨1, by decide⟩ ω =
          S.dbar ⟨1, by decide⟩
      · have hpos0 : 0 < S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) :=
          S.e₀_pos _
        have hpos1 : 0 < S.e₁_val
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) :=
          S.e₁_pos _
        have hle0 : (S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹
            ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos0 h_overlap.1).2 he0
        have hle1 :
            (S.e₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos1 h_overlap.1).2 he1
        have hle :
            (S.e₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹ *
              (S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹
              ≤ ε⁻¹ * ε⁻¹ :=
          mul_le_mul hle1 hle0 (inv_nonneg.mpr hpos0.le)
            (inv_nonneg.mpr h_overlap.1.le)
        have hD0n : S.toPODTRSystem.factualD 0 ω = S.dbar 0 := by
          simpa using hD0
        have hD1n : S.toPODTRSystem.factualD 1 ω = S.dbar 1 := by
          simpa using hD1
        have hind0eq : indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩) = 1 := by
          simpa using (show indEq (S.toPODTRSystem.factualD 0 ω) (S.dbar 0) = 1 by
            simp [indEq, hD0n])
        have hind1eq : indEq (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
            (S.dbar ⟨1, by decide⟩) = 1 := by
          simpa using (show indEq (S.toPODTRSystem.factualD 1 ω) (S.dbar 1) = 1 by
            simp [indEq, hD1n])
        rw [hind0eq, hind1eq, one_mul, norm_div, norm_one, norm_mul]
        rw [show ‖S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)‖ =
            S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) from
          Real.norm_of_nonneg hpos0.le]
        rw [show ‖S.e₁_val
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)‖ =
            S.e₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) from
          Real.norm_of_nonneg hpos1.le]
        simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hle
      · have hεεinv_nonneg : 0 ≤ (ε * ε)⁻¹ :=
          inv_nonneg.mpr (mul_nonneg h_overlap.1.le h_overlap.1.le)
        have hD1n : ¬S.toPODTRSystem.factualD 1 ω = S.dbar 1 := by
          simpa using hD1
        have hind1eq : indEq (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
            (S.dbar ⟨1, by decide⟩) = 0 := by
          simpa using (show indEq (S.toPODTRSystem.factualD 1 ω) (S.dbar 1) = 0 by
            simp [indEq, hD1n])
        rw [hind1eq, mul_zero, zero_div, norm_zero]
        exact hεεinv_nonneg
    · have hεεinv_nonneg : 0 ≤ (ε * ε)⁻¹ :=
        inv_nonneg.mpr (mul_nonneg h_overlap.1.le h_overlap.1.le)
      rw [indEq, if_neg hD0, zero_mul, zero_div, norm_zero]
      exact hεεinv_nonneg
  have hw0_Linf :
      MemLp
        (fun ω => indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩) /
          S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ hw0_bound
    apply Measurable.aestronglyMeasurable
    exact ((measurable_indEq_left (S.dbar ⟨0, by decide⟩)).comp
      (S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩)).div
        (S.e₀_meas.comp (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩))
  have hw1_Linf :
      MemLp
        (fun ω =>
          (indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩) *
            indEq (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
              (S.dbar ⟨1, by decide⟩)) /
          (S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            S.e₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ (ε * ε)⁻¹ hw1_bound
    apply Measurable.aestronglyMeasurable
    have hind0 : Measurable (fun ω => indEq
        (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
        (S.dbar ⟨0, by decide⟩)) :=
      (measurable_indEq_left (S.dbar ⟨0, by decide⟩)).comp
        (S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩)
    have hind1 : Measurable (fun ω => indEq
        (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
        (S.dbar ⟨1, by decide⟩)) :=
      (measurable_indEq_left (S.dbar ⟨1, by decide⟩)).comp
        (S.toPODTRSystem.measurable_factualD ⟨1, by decide⟩)
    have he0 : Measurable (fun ω =>
        S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) :=
      S.e₀_meas.comp (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩)
    have he1 : Measurable (fun ω =>
        S.e₁_val
          (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
           S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
           S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) :=
      S.e₁_meas.comp
        ((S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩).prod
          ((S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩).prod
            (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩)))
    exact (hind0.mul hind1).div (he0.mul he1)
  have hterm0_L2 :
      MemLp
        (fun ω =>
          (indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩) /
            S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) *
          (S.μ₁_val
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
            S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) 2 P.μ := by
    simpa using (hμ1_L2.sub hμ0_L2).mul hw0_Linf
  have hterm1_L2 :
      MemLp
        (fun ω =>
          ((indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩) *
            indEq (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
              (S.dbar ⟨1, by decide⟩)) /
            (S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
              S.e₁_val
                (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                 S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                 S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) *
          (S.toPODTRSystem.factualY ω -
            S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) 2 P.μ := by
    simpa using (hY_L2.sub hμ1_L2).mul hw1_Linf
  have hψ_comp_L2 : MemLp (fun ω => S.ψ_seqDR (S.factualZ ω)) 2 P.μ := by
    have hconst_L2 : MemLp (fun _ : P.Ω => S.θ₀) 2 P.μ := memLp_const _
    have hsum_L2 :=
      ((hμ0_L2.add hterm0_L2).add hterm1_L2).sub hconst_L2
    simpa [DTREstimationSystem.ψ_seqDR, DTREstimationSystem.seqDRMoment,
      Causalean.Estimation.DTR.seqDRMoment, DTREstimationSystem.factualZ,
      projS₀, projD₀, projS₁, projD₁, projY, histH₁,
      DTREstimationSystem.η₀] using hsum_L2
  have hψ_L2 : MemLp S.ψ_seqDR 2 (S.P_Z) := by
    rw [DTREstimationSystem.P_Z]
    exact (memLp_map_measure_iff hψ_meas.aestronglyMeasurable
      S.measurable_factualZ.aemeasurable).2 hψ_comp_L2
  exact hψ_L2.integrable_sq

end DTREstimationSystem

end DTR
end Estimation
end Causalean
