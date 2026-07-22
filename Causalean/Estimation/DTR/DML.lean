/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# One-shot DML / sequential DR estimator for the DTR (`n = 2`) effect

`def:est-dml-dtr` and `thm:est-dml-dtr-al` instantiated for the
`DTREstimationSystem` from `Setup.lean`.

The estimator is

    θ̂ⁿ_DML := (1/|B(n)|) Σ_{i ∈ B(n)} m_seqDR( dbar, Zᵢ, η̂(n), 0 )
            + θ_correction,

mirroring `Estimation/ATE/DML.lean` stage-by-stage.  The empirical mean
of `m_seqDR(·, ·, ·, 0)` over fold `B(n)` equals the empirical
sequential-DR pseudo-outcome.

The headline `dml_DTR_isAsymLinear` translates user-friendly stagewise
hypotheses (`μ̂_k_n`, `ê_k_n` for `k ∈ {0, 1}`) into the abstract
`seqDR_dml_isAsymLinear` interface, which in turn delegates to
`dml_chernozhukov_asymptoticLinear`.

The estimator definition accepts the bundled nuisance process
`η_hat : ℕ → P.Ω → DTRNuisanceVec₂ δ γ`.  The asymptotic-linearity theorem
is the public wrapper: it builds that bundle from the four stagewise nuisance
learners, checks the score measurability and integrability obligations, and
transports the abstract Chernozhukov estimator conclusion back to
`dml_DTR_estimator`.
-/

import Causalean.Estimation.DTR.DTRInstance
import Causalean.Estimation.DTR.ScoreL2
import Causalean.Stat.Sample
import Causalean.Stat.SampleSplit
import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.SampleSplit.PartialFoldCLT
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess

/-! # Dynamic-Treatment-Regime DML Estimator

This file defines the one-shot double machine learning estimator for the
two-period dynamic-treatment-regime effect. The main declarations are
`dml_DTR_estimator`, the fold-B empirical mean of the sequential doubly robust
pseudo-outcome, and `dml_DTR_isAsymLinear`, which proves asymptotic linearity
from stagewise nuisance overlap, measurability, L2 integrability, individual
`o_p(1)` rates, and the four cross-product `o_p(n^{-1/2})` rates. -/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

private lemma measurable_indEq_left (d : δ) :
    Measurable (fun x : δ => indEq x d) := by
  have hset : MeasurableSet {x : δ | x = d} :=
    MeasurableSet.singleton d
  convert (measurable_const.indicator hset :
    Measurable (Set.indicator {x : δ | x = d} (fun _ => (1 : ℝ)))) using 1

private lemma measurable_seqDRMomentFunctional_uncurry
    {Ω' : Type*} [MeasurableSpace Ω']
    (S : DTREstimationSystem P δ γ) (θ : ℝ)
    (η_fn : Ω' → DTRNuisanceVec₂ δ γ)
    (h_mu0 : Measurable (fun p : Ω' × γ 0 => (η_fn p.1).μ₀_fn p.2))
    (h_e0 : Measurable (fun p : Ω' × γ 0 => (η_fn p.1).e₀_fn p.2))
    (h_mu1 : Measurable (fun p : Ω' × (γ 1 × δ × γ 0) =>
      (η_fn p.1).μ₁_fn p.2))
    (h_e1 : Measurable (fun p : Ω' × (γ 1 × δ × γ 0) =>
      (η_fn p.1).e₁_fn p.2)) :
    Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      S.seqDRMomentFunctional (η_fn p.1) p.2 θ) := by
  unfold DTREstimationSystem.seqDRMomentFunctional
  unfold Causalean.Estimation.DTR.seqDRMoment
  have hpS0 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (p.1, projS₀ p.2)) := by
    unfold projS₀
    exact Measurable.prodMk measurable_fst measurable_snd.fst
  have hpH1 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (p.1, histH₁ p.2)) := by
    unfold histH₁ projS₁ projD₀ projS₀
    measurability
  have hμ0 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (η_fn p.1).μ₀_fn (projS₀ p.2)) := h_mu0.comp hpS0
  have he0 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (η_fn p.1).e₀_fn (projS₀ p.2)) := h_e0.comp hpS0
  have hμ1 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (η_fn p.1).μ₁_fn (histH₁ p.2)) := h_mu1.comp hpH1
  have he1 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (η_fn p.1).e₁_fn (histH₁ p.2)) := h_e1.comp hpH1
  have hind0 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      indEq (projD₀ p.2) (S.dbar 0)) := by
    unfold projD₀
    exact (measurable_indEq_left (S.dbar 0)).comp measurable_snd.snd.fst
  have hind1 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      indEq (projD₁ p.2) (S.dbar 1)) := by
    unfold projD₁
    exact (measurable_indEq_left (S.dbar 1)).comp measurable_snd.snd.snd.snd.fst
  have hy : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      projY p.2) := by
    unfold projY
    exact measurable_snd.snd.snd.snd.snd
  exact ((hμ0.add ((hind0.div he0).mul (hμ1.sub hμ0))).add
    (((hind0.mul hind1).div (he0.mul he1)).mul (hy.sub hμ1))).sub measurable_const

private lemma seqDRMomentFunctional_memLp_two
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ)
    (η : DTRNuisanceVec₂ δ γ)
    (hη : η ∈ DTREstimationSystem.H_ε ε)
    (h_mu0 : MemLp η.μ₀_fn 2 S.P_H₀)
    (h_mu1 : MemLp η.μ₁_fn 2 S.P_H₁) :
    MemLp (fun z => S.seqDRMomentFunctional η z S.θ₀) 2 S.P_Z := by
  have hY_L2 : MemLp S.toPODTRSystem.factualY 2 P.μ :=
    (memLp_two_iff_integrable_sq
      S.toPODTRSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hμ0_comp_L2 :
      MemLp (fun ω => η.μ₀_fn
        (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) 2 P.μ := by
    have hmap : MemLp η.μ₀_fn 2
        (P.μ.map (S.toPODTRSystem.factualS ⟨0, by decide⟩)) := by
      simpa [DTREstimationSystem.P_H₀] using h_mu0
    exact (memLp_map_measure_iff hmap.aestronglyMeasurable
      (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩).aemeasurable).1 hmap
  have hμ1_comp_L2 :
      MemLp (fun ω => η.μ₁_fn
        (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
         S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
         S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) 2 P.μ := by
    let H1 : P.Ω → γ 1 × δ × γ 0 := fun ω =>
      (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
       S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
       S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
    have hH1_meas : Measurable H1 := by
      dsimp [H1]
      exact (S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩).prod
        ((S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩).prod
          (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩))
    have hmap : MemLp η.μ₁_fn 2 (P.μ.map H1) := by
      simpa [DTREstimationSystem.P_H₁, H1] using h_mu1
    exact (memLp_map_measure_iff hmap.aestronglyMeasurable
      hH1_meas.aemeasurable).1 hmap
  have hw0_bound :
      ∀ᵐ ω ∂P.μ,
        ‖indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩) /
          η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)‖ ≤ ε⁻¹ := by
    refine Eventually.of_forall fun ω => ?_
    have he := hη.1 (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
    by_cases hD : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · have hpos : 0 < η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) :=
        lt_of_lt_of_le h_overlap.1 he.1
      have hle : (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hpos h_overlap.1).2 he.1
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
          (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            η.e₁_fn
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))‖ ≤ (ε * ε)⁻¹ := by
    refine Eventually.of_forall fun ω => ?_
    have he0 := hη.1 (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
    have he1 := hη.2
      (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
       S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
       S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
    by_cases hD0 : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · by_cases hD1 : S.toPODTRSystem.factualD ⟨1, by decide⟩ ω =
          S.dbar ⟨1, by decide⟩
      · have hpos0 : 0 < η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) :=
          lt_of_lt_of_le h_overlap.1 he0.1
        have hpos1 : 0 < η.e₁_fn
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) :=
          lt_of_lt_of_le h_overlap.1 he1.1
        have hle0 : (η.e₀_fn
            (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos0 h_overlap.1).2 he0.1
        have hle1 : (η.e₁_fn
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos1 h_overlap.1).2 he1.1
        have hle :
            (η.e₁_fn
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹ *
              (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹
              ≤ ε⁻¹ * ε⁻¹ :=
          mul_le_mul hle1 hle0 (inv_nonneg.mpr hpos0.le)
            (inv_nonneg.mpr h_overlap.1.le)
        have hind0eq : indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩) = 1 := by
          unfold indEq
          rw [if_pos]
          simpa using hD0
        have hind1eq : indEq (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
            (S.dbar ⟨1, by decide⟩) = 1 := by
          unfold indEq
          rw [if_pos]
          simpa using hD1
        rw [hind0eq, hind1eq, one_mul, norm_div, norm_one, norm_mul]
        rw [show ‖η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)‖ =
            η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) from
          Real.norm_of_nonneg hpos0.le]
        rw [show ‖η.e₁_fn
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)‖ =
            η.e₁_fn
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) from
          Real.norm_of_nonneg hpos1.le]
        simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hle
      · have hεεinv_nonneg : 0 ≤ (ε * ε)⁻¹ :=
          inv_nonneg.mpr (mul_nonneg h_overlap.1.le h_overlap.1.le)
        have hind1zero : indEq (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
            (S.dbar ⟨1, by decide⟩) = 0 := by
          unfold indEq
          rw [if_neg]
          simpa using hD1
        rw [hind1zero, mul_zero, zero_div, norm_zero]
        exact hεεinv_nonneg
    · have hεεinv_nonneg : 0 ≤ (ε * ε)⁻¹ :=
        inv_nonneg.mpr (mul_nonneg h_overlap.1.le h_overlap.1.le)
      have hind0zero : indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
          (S.dbar ⟨0, by decide⟩) = 0 := by
        unfold indEq
        rw [if_neg]
        simpa using hD0
      rw [hind0zero, zero_mul, zero_div, norm_zero]
      exact hεεinv_nonneg
  have hw0_Linf :
      MemLp
        (fun ω => indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩) /
          η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ hw0_bound
    apply Measurable.aestronglyMeasurable
    exact ((measurable_indEq_left (S.dbar ⟨0, by decide⟩)).comp
      (S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩)).div
        (η.e₀_meas.comp (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩))
  have hw1_Linf :
      MemLp
        (fun ω =>
          (indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩) *
            indEq (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
              (S.dbar ⟨1, by decide⟩)) /
          (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            η.e₁_fn
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
        η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) :=
      η.e₀_meas.comp (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩)
    have he1 : Measurable (fun ω =>
        η.e₁_fn
          (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
           S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
           S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) :=
      η.e₁_meas.comp
        ((S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩).prod
          ((S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩).prod
            (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩)))
    exact (hind0.mul hind1).div (he0.mul he1)
  have hterm0_L2 :
      MemLp
        (fun ω =>
          (indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩) /
            η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) *
          (η.μ₁_fn
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
            η.μ₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) 2 P.μ := by
    simpa using (hμ1_comp_L2.sub hμ0_comp_L2).mul hw0_Linf
  have hterm1_L2 :
      MemLp
        (fun ω =>
          ((indEq (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩) *
            indEq (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
              (S.dbar ⟨1, by decide⟩)) /
            (η.e₀_fn (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
              η.e₁_fn
                (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                 S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                 S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) *
          (S.toPODTRSystem.factualY ω -
            η.μ₁_fn
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) 2 P.μ := by
    simpa using (hY_L2.sub hμ1_comp_L2).mul hw1_Linf
  have hscore_comp_L2 :
      MemLp (fun ω => S.seqDRMomentFunctional η (S.factualZ ω) S.θ₀) 2 P.μ := by
    have hconst_L2 : MemLp (fun _ : P.Ω => S.θ₀) 2 P.μ := memLp_const _
    have hsum_L2 :=
      ((hμ0_comp_L2.add hterm0_L2).add hterm1_L2).sub hconst_L2
    simpa [DTREstimationSystem.seqDRMomentFunctional,
      Causalean.Estimation.DTR.seqDRMoment, DTREstimationSystem.factualZ,
      projS₀, projD₀, projS₁, projD₁, projY, histH₁] using hsum_L2
  have hscore_meas :
      Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ =>
        S.seqDRMomentFunctional η z S.θ₀) :=
    S.measurable_seqDRMomentFunctional η S.θ₀
  rw [DTREstimationSystem.P_Z]
  exact (memLp_map_measure_iff hscore_meas.aestronglyMeasurable
    S.measurable_factualZ.aemeasurable).2 hscore_comp_L2

/-- One-shot DML / sequential DR estimator of the DTR effect
(`def:est-dml-dtr`).

Inputs:
* `S`         — DTR estimation system carrying the value-space truth
                `(μ₀_val, e₀_val, μ₁_val, e₁_val)` at the target regime
                `S.dbar`.
* `sample`    — i.i.d. sample of data tuples `(S₀, D₀, S₁, D₁, Y) ∼ P_Z`.
* `split`     — one-shot split of the sample.
* `η_hat`     — bundled stagewise nuisance estimator at horizon `n`.

Output: empirical mean over `B(n)` of `m_seqDR(S.dbar, Zᵢ, η̂(n), 0)`.
Equivalently, the empirical sequential-DR pseudo-outcome.

The estimator takes a single bundled `DTRNuisanceVec₂` process.  The theorem
`dml_DTR_isAsymLinear` constructs this bundle from the four stagewise learners
`μ₀_hat`, `e₀_hat`, `μ₁_hat`, and `e₁_hat`. -/
noncomputable def dml_DTR_estimator
    (S : DTREstimationSystem P δ γ)
    (sample : IIDSample P.Ω (γ 0 × δ × γ 1 × δ × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    (η_hat : ℕ → P.Ω → DTRNuisanceVec₂ δ γ)
    (n : ℕ) : P.Ω → ℝ :=
  fun ω =>
    ((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n,
        Causalean.Estimation.DTR.seqDRMoment S.dbar (sample.Z i ω) (η_hat n ω) 0

set_option maxHeartbeats 1200000 in
-- The wrapper composes ~25 derived hypotheses (rate translations, score
-- measurability, integrability, two transport equalities) and applies
-- the abstract `seqDR_dml_isAsymLinear`; the resulting elaboration
-- exceeds the default heartbeat budget.  Mirrors ATE/DML.lean.
/-- **Asymptotic linearity of the one-shot DML DTR (`n = 2`) estimator** —
`thm:est-dml-dtr-al`.

Hypotheses (mirroring the NL doc and `dml_ATE_isAsymLinear`):

1. DTR backdoor `Assumptions`;
2. strict overlap for both the truth and the estimator: there exists
   `ε ∈ (0, 1/2]` with `ε ≤ e_k(H_k) ≤ 1-ε` a.s. for `k ∈ {0, 1}` and
   pointwise `ε ≤ ê_k_n(h) ≤ 1-ε` for all `n, ω, h`;
3. pointwise overlap on the value-space truth `S.e_k_val` (used to
   place `S.η₀ ∈ H_ε`, see `seqDRGeneralMoment.η₀_mem`);
4. `E[Y²] < ∞` and square-integrability of every counterfactual outcome
   `Y(dbar)`;
5. one-shot split with `|B(n)|/n → c` for some `c ∈ (0, 1)`;
6. `μ̂_k_n` and `ê_k_n` depend only on the nuisance fold `A(n)`;
7. individual stagewise rates
   `‖μ̂_k_n(H_k) − μ_k_val(H_k)‖_{L²(P_H_k)} = o_p(1)` and
   `‖ê_k_n(H_k) − e_k_val(H_k)‖_{L²(P_H_k)} = o_p(1)` for `k ∈ {0, 1}`;
8. four cross-stage product rates of the form
   `‖Δμ_a‖₂ · ‖Δe_b‖₂ = o_p(n^{-1/2})` for `a, b ∈ {0, 1}`.

Conclusion: `IsAsymLinear (dml_DTR_estimator …) θ₀ ψ_seqDR sample
split.foldB`.

The proof is a thin wrapper over the abstract
`seqDR_dml_isAsymLinear`: build the abstract `η_hat` from the four
stagewise hats, translate the rate / measurability / integrability
hypotheses, apply the abstract theorem, then transport the conclusion
along two algebraic equalities (a pointwise rescaled-error equality
`√|B(n)| · (dmlChern − θ₀) = √|B(n)| · (dml_DTR_estimator − θ₀)` and
the influence-function equality `−J₀_inv · seqDRMomentFunctional S.η₀ z
S.θ₀ = S.ψ_seqDR z`). -/
theorem dml_DTR_isAsymLinear
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (hA : S.toPODTRSystem.Assumptions)
    (h_overlap : S.StrictOverlap ε)
    (h_e_val_pointwise :
      (∀ s₀, ε ≤ S.e₀_val s₀ ∧ S.e₀_val s₀ ≤ 1 - ε)
        ∧ (∀ h, ε ≤ S.e₁_val h ∧ S.e₁_val h ≤ 1 - ε))
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ dbar : Fin 2 → δ,
      Integrable (fun ω => (S.toPODTRSystem.Y_of dbar ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ 0 × δ × γ 1 × δ × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    -- Stagewise nuisance hats.
    (μ₀_hat : ℕ → P.Ω → (γ 0 → ℝ))
    (e₀_hat : ℕ → P.Ω → (γ 0 → ℝ))
    (μ₁_hat : ℕ → P.Ω → (γ 1 × δ × γ 0 → ℝ))
    (e₁_hat : ℕ → P.Ω → (γ 1 × δ × γ 0 → ℝ))
    -- Joint measurability (`(ω, x) ↦ hat(n, ω, x)`) for each stage.
    (h_mu0_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ 0) => μ₀_hat n p.1 p.2))
    (h_e0_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ 0) => e₀_hat n p.1 p.2))
    (h_mu1_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ 1 × δ × γ 0)) => μ₁_hat n p.1 p.2))
    (h_e1_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ 1 × δ × γ 0)) => e₁_hat n p.1 p.2))
    -- Pointwise overlap of the estimator on `H_ε` at both stages.
    (h_e_overlap_hat :
      ∀ n ω,
        (∀ s₀, ε ≤ e₀_hat n ω s₀ ∧ e₀_hat n ω s₀ ≤ 1 - ε)
          ∧ (∀ h, ε ≤ e₁_hat n ω h ∧ e₁_hat n ω h ≤ 1 - ε))
    -- Per-`(n, ω)` `MemLp` hypotheses on each hat.
    (h_mu0_memLp : ∀ n ω, MemLp (fun s₀ => μ₀_hat n ω s₀) 2 S.P_H₀)
    (h_e0_memLp  : ∀ n ω, MemLp (fun s₀ => e₀_hat n ω s₀) 2 S.P_H₀)
    (h_mu1_memLp : ∀ n ω, MemLp (fun h => μ₁_hat n ω h) 2 S.P_H₁)
    (h_e1_memLp  : ∀ n ω, MemLp (fun h => e₁_hat n ω h) 2 S.P_H₁)
    -- Fold-A measurability witnesses (per stage).
    (h_mu0_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ₀_hat n))
    (h_e0_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (e₀_hat n))
    (h_mu1_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ₁_hat n))
    (h_e1_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (e₁_hat n))
    -- Joint fold-A measurability on the uncurried form (per stage).
    (h_mu0_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ 0))]
          (fun (p : P.Ω × γ 0) => μ₀_hat n p.1 p.2))
    (h_e0_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ 0))]
          (fun (p : P.Ω × γ 0) => e₀_hat n p.1 p.2))
    (h_mu1_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ 1 × δ × γ 0))]
          (fun (p : P.Ω × (γ 1 × δ × γ 0)) => μ₁_hat n p.1 p.2))
    (h_e1_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ 1 × δ × γ 0))]
          (fun (p : P.Ω × (γ 1 × δ × γ 0)) => e₁_hat n p.1 p.2))
    -- Stagewise individual `o_p(1)` rates on `‖Δ·‖_{L²(P_H_k)}`.
    (h_mu0_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun s₀ => μ₀_hat n ω s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_mu1_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun h => μ₁_hat n ω h - S.μ₁_val h) 2 S.P_H₁).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_e0_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun s₀ => e₀_hat n ω s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_e1_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun h => e₁_hat n ω h - S.e₁_val h) 2 S.P_H₁).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    -- Cross-stage product rates: every `(μ_a, e_b)` pair is `o_p(n^{-1/2})`.
    (h_product_rate_00 :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun s₀ => μ₀_hat n ω s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal *
            (eLpNorm (fun s₀ => e₀_hat n ω s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (h_product_rate_11 :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun h => μ₁_hat n ω h - S.μ₁_val h) 2 S.P_H₁).toReal *
            (eLpNorm (fun h => e₁_hat n ω h - S.e₁_val h) 2 S.P_H₁).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (h_product_rate_01 :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun s₀ => μ₀_hat n ω s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal *
            (eLpNorm (fun h => e₁_hat n ω h - S.e₁_val h) 2 S.P_H₁).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (h_product_rate_10 :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun h => μ₁_hat n ω h - S.μ₁_val h) 2 S.P_H₁).toReal *
            (eLpNorm (fun s₀ => e₀_hat n ω s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (dml_DTR_estimator S sample split
        (fun n ω =>
          { μ₀_fn := μ₀_hat n ω
            e₀_fn := e₀_hat n ω
            μ₁_fn := μ₁_hat n ω
            e₁_fn := e₁_hat n ω
            μ₀_meas :=
              (h_mu0_meas n).comp
                (Measurable.prodMk measurable_const measurable_id)
            e₀_meas :=
              (h_e0_meas n).comp
                (Measurable.prodMk measurable_const measurable_id)
            μ₁_meas :=
              (h_mu1_meas n).comp
                (Measurable.prodMk measurable_const measurable_id)
            e₁_meas :=
              (h_e1_meas n).comp
                (Measurable.prodMk measurable_const measurable_id) }))
      S.θ₀
      S.ψ_seqDR
      sample
      split.foldB := by
  let η_hat : ℕ → P.Ω → DTRNuisanceVec₂ δ γ := fun n ω =>
    { μ₀_fn := μ₀_hat n ω
      e₀_fn := e₀_hat n ω
      μ₁_fn := μ₁_hat n ω
      e₁_fn := e₁_hat n ω
      μ₀_meas :=
        (h_mu0_meas n).comp
          (Measurable.prodMk measurable_const measurable_id)
      e₀_meas :=
        (h_e0_meas n).comp
          (Measurable.prodMk measurable_const measurable_id)
      μ₁_meas :=
        (h_mu1_meas n).comp
          (Measurable.prodMk measurable_const measurable_id)
      e₁_meas :=
        (h_e1_meas n).comp
          (Measurable.prodMk measurable_const measurable_id) }
  have h_in_Hε : ∀ n ω, η_hat n ω ∈ DTREstimationSystem.H_ε ε := by
    intro n ω
    exact h_e_overlap_hat n ω
  haveI : IsProbabilityMeasure S.P_H₀ := by
    unfold DTREstimationSystem.P_H₀
    exact Measure.isProbabilityMeasure_map
      (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩).aemeasurable
  haveI : IsProbabilityMeasure S.P_H₁ := by
    unfold DTREstimationSystem.P_H₁
    exact Measure.isProbabilityMeasure_map
      ((S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩).prod
        ((S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩).prod
          (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩))).aemeasurable
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold DTREstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  have hμ0_val_memLp : MemLp S.μ₀_val 2 S.P_H₀ := by
    have hYd_L2 : MemLp (S.toPODTRSystem.Y_of S.dbar) 2 P.μ :=
      (memLp_two_iff_integrable_sq
        (S.toPODTRSystem.measurable_Y_of S.dbar).aestronglyMeasurable).2
          (h_yd2 S.dbar)
    have hcond_L2 :
        MemLp ((S.toPODTRSystem.historyBundle 0 (by decide)).condExpGiven
          (S.toPODTRSystem.Y_of S.dbar) P.μ) 2 P.μ := by
      simpa [POCFBundle.condExpGiven] using hYd_L2.condExp
    have hcomp_L2 :
        MemLp (fun ω => S.μ₀_val
          (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) 2 P.μ :=
      hcond_L2.ae_eq (S.μ₀_compat hA)
    rw [DTREstimationSystem.P_H₀]
    exact (memLp_map_measure_iff S.μ₀_meas.aestronglyMeasurable
      (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩).aemeasurable).2 hcomp_L2
  have hμ1_val_memLp : MemLp S.μ₁_val 2 S.P_H₁ := by
    let H1 : P.Ω → γ 1 × δ × γ 0 := fun ω =>
      (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
       S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
       S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
    have hH1_meas : Measurable H1 := by
      dsimp [H1]
      exact (S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩).prod
        ((S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩).prod
          (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩))
    have hcomp_L2 :
        MemLp (fun ω => S.μ₁_val (H1 ω)) 2 P.μ := by
      simpa [H1] using (S.stageOneReg_memLp h_overlap h_y2).ae_eq
        (S.μ₁_val_comp_eq_stageOneReg).symm
    rw [DTREstimationSystem.P_H₁]
    exact (memLp_map_measure_iff S.μ₁_meas.aestronglyMeasurable
      hH1_meas.aemeasurable).2 hcomp_L2
  have he0_val_memLp : MemLp S.e₀_val 2 S.P_H₀ := by
    refine MemLp.of_bound S.e₀_meas.aestronglyMeasurable 1 ?_
    refine Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [S.e₀_pos s], by linarith [S.e₀_lt_one s]⟩
  have he1_val_memLp : MemLp S.e₁_val 2 S.P_H₁ := by
    refine MemLp.of_bound S.e₁_meas.aestronglyMeasurable 1 ?_
    refine Eventually.of_forall fun h => ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [S.e₁_pos h], by linarith [S.e₁_lt_one h]⟩
  have h_mu0_diff_memLp : ∀ n ω,
      MemLp (fun s₀ => (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀ := by
    intro n ω
    exact (h_mu0_memLp n ω).sub hμ0_val_memLp
  have h_mu1_diff_memLp : ∀ n ω,
      MemLp (fun h => (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁ := by
    intro n ω
    exact (h_mu1_memLp n ω).sub hμ1_val_memLp
  have h_e0_diff_memLp : ∀ n ω,
      MemLp (fun s₀ => (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀ := by
    intro n ω
    exact (h_e0_memLp n ω).sub he0_val_memLp
  have h_e1_diff_memLp : ∀ n ω,
      MemLp (fun h => (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁ := by
    intro n ω
    exact (h_e1_memLp n ω).sub he1_val_memLp
  have h_indiv_rate_ρ₁ :
      IsLittleOp
        (fun n ω =>
          (((seqDRGeneralMoment S h_e_val_pointwise).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ := by
    have hone_nonneg : ∀ᶠ _n : ℕ in atTop, 0 ≤ (1 : ℝ) := by
      filter_upwards with n
      norm_num
    simpa [seqDRGeneralMoment, DTREstimationSystem.η₀, η_hat] using
      IsLittleOp.add_eventually_nonneg_rate (μ := P.μ) hone_nonneg
        h_mu0_rate h_mu1_rate
  have h_indiv_rate_ρ₂ :
      IsLittleOp
        (fun n ω =>
          (((seqDRGeneralMoment S h_e_val_pointwise).ρ₂
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ := by
    have hone_nonneg : ∀ᶠ _n : ℕ in atTop, 0 ≤ (1 : ℝ) := by
      filter_upwards with n
      norm_num
    simpa [seqDRGeneralMoment, DTREstimationSystem.η₀, η_hat] using
      IsLittleOp.add_eventually_nonneg_rate (μ := P.μ) hone_nonneg
        h_e0_rate h_e1_rate
  have h_product_rate_abs :
      IsLittleOp
        (fun n ω =>
          (((seqDRGeneralMoment S h_e_val_pointwise).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ) *
            (((seqDRGeneralMoment S h_e_val_pointwise).ρ₂
                (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ := by
    let rn : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))
    have hrn_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ rn n := by
      filter_upwards with n
      dsimp [rn]
      positivity
    have h00_10 :
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun s₀ => μ₀_hat n ω s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal *
              (eLpNorm (fun s₀ => e₀_hat n ω s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal +
            (eLpNorm (fun h => μ₁_hat n ω h - S.μ₁_val h) 2 S.P_H₁).toReal *
              (eLpNorm (fun s₀ => e₀_hat n ω s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal)
          rn P.μ := by
      simpa [rn] using
        IsLittleOp.add_eventually_nonneg_rate (μ := P.μ) hrn_nonneg
          h_product_rate_00 h_product_rate_10
    have h01_11 :
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun s₀ => μ₀_hat n ω s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal *
              (eLpNorm (fun h => e₁_hat n ω h - S.e₁_val h) 2 S.P_H₁).toReal +
            (eLpNorm (fun h => μ₁_hat n ω h - S.μ₁_val h) 2 S.P_H₁).toReal *
              (eLpNorm (fun h => e₁_hat n ω h - S.e₁_val h) 2 S.P_H₁).toReal)
          rn P.μ := by
      simpa [rn] using
        IsLittleOp.add_eventually_nonneg_rate (μ := P.μ) hrn_nonneg
          h_product_rate_01 h_product_rate_11
    have hsum :
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun s₀ => μ₀_hat n ω s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal *
                (eLpNorm (fun s₀ => e₀_hat n ω s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal +
            ((eLpNorm (fun h => μ₁_hat n ω h - S.μ₁_val h) 2 S.P_H₁).toReal *
                (eLpNorm (fun s₀ => e₀_hat n ω s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal +
              ((eLpNorm (fun s₀ => μ₀_hat n ω s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal *
                (eLpNorm (fun h => e₁_hat n ω h - S.e₁_val h) 2 S.P_H₁).toReal +
              (eLpNorm (fun h => μ₁_hat n ω h - S.μ₁_val h) 2 S.P_H₁).toReal *
                (eLpNorm (fun h => e₁_hat n ω h - S.e₁_val h) 2 S.P_H₁).toReal)))
          rn P.μ := by
      simpa [add_assoc] using
        IsLittleOp.add_eventually_nonneg_rate (μ := P.μ) hrn_nonneg h00_10 h01_11
    simpa [seqDRGeneralMoment, DTREstimationSystem.η₀, η_hat, rn, add_mul, mul_add,
      add_assoc] using hsum
  have h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ 0 × δ × γ 1 × δ × ℝ)) =>
        S.seqDRMomentFunctional (η_hat n p.1) p.2 S.θ₀) := by
    intro n
    simpa [η_hat] using
      measurable_seqDRMomentFunctional_uncurry (S := S) (θ := S.θ₀)
        (η_fn := fun ω => η_hat n ω)
        (by simpa [η_hat] using h_mu0_meas n)
        (by simpa [η_hat] using h_e0_meas n)
        (by simpa [η_hat] using h_mu1_meas n)
        (by simpa [η_hat] using h_e1_meas n)
  have h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => S.seqDRMomentFunctional (η_hat n ω) z S.θ₀) := by
    intro n
    let mA : MeasurableSpace P.Ω :=
      MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance
    change @Measurable P.Ω ((γ 0 × δ × γ 1 × δ × ℝ) → ℝ) mA inferInstance
      (fun ω z => S.seqDRMomentFunctional (η_hat n ω) z S.θ₀)
    refine measurable_pi_lambda _ ?_
    intro z
    unfold DTREstimationSystem.seqDRMomentFunctional
    unfold Causalean.Estimation.DTR.seqDRMoment
    have hμ0 : @Measurable P.Ω ℝ mA inferInstance
        (fun ω => μ₀_hat n ω (projS₀ z)) :=
      (measurable_pi_apply (projS₀ z)).comp (h_mu0_foldA n)
    have he0 : @Measurable P.Ω ℝ mA inferInstance
        (fun ω => e₀_hat n ω (projS₀ z)) :=
      (measurable_pi_apply (projS₀ z)).comp (h_e0_foldA n)
    have hμ1 : @Measurable P.Ω ℝ mA inferInstance
        (fun ω => μ₁_hat n ω (histH₁ z)) :=
      (measurable_pi_apply (histH₁ z)).comp (h_mu1_foldA n)
    have he1 : @Measurable P.Ω ℝ mA inferInstance
        (fun ω => e₁_hat n ω (histH₁ z)) :=
      (measurable_pi_apply (histH₁ z)).comp (h_e1_foldA n)
    exact ((hμ0.add (((measurable_const).div he0).mul (hμ1.sub hμ0))).add
      ((((measurable_const).mul measurable_const).div (he0.mul he1)).mul
        (measurable_const.sub hμ1))).sub measurable_const
  have h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ 0 × δ × γ 1 × δ × ℝ))]
          (fun (p : P.Ω × (γ 0 × δ × γ 1 × δ × ℝ)) =>
            S.seqDRMomentFunctional (η_hat n p.1) p.2 S.θ₀) := by
    intro n
    let mA : MeasurableSpace P.Ω :=
      MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance
    change @Measurable (P.Ω × (γ 0 × δ × γ 1 × δ × ℝ)) ℝ
      (mA.prod (inferInstance : MeasurableSpace (γ 0 × δ × γ 1 × δ × ℝ)))
      inferInstance
      (fun p => S.seqDRMomentFunctional (η_hat n p.1) p.2 S.θ₀)
    letI : MeasurableSpace P.Ω := mA
    simpa [η_hat] using
      measurable_seqDRMomentFunctional_uncurry (S := S) (θ := S.θ₀)
        (η_fn := fun ω => η_hat n ω)
        (by simpa [η_hat] using h_mu0_uncurry_foldA n)
        (by simpa [η_hat] using h_e0_uncurry_foldA n)
        (by simpa [η_hat] using h_mu1_uncurry_foldA n)
        (by simpa [η_hat] using h_e1_uncurry_foldA n)
  have h_m_int :
      ∀ n ω, Integrable
        (fun z => S.seqDRMomentFunctional (η_hat n ω) z S.θ₀) S.P_Z := by
    intro n ω
    exact (seqDRMomentFunctional_memLp_two S h_overlap h_y2
      (η_hat n ω) (h_in_Hε n ω) (h_mu0_memLp n ω) (h_mu1_memLp n ω)).integrable
        (by norm_num : (1 : ENNReal) ≤ 2)
  have h_m_sq_int :
      ∀ n ω, Integrable
        (fun z => (S.seqDRMomentFunctional (η_hat n ω) z S.θ₀) ^ 2) S.P_Z := by
    intro n ω
    exact (seqDRMomentFunctional_memLp_two S h_overlap h_y2
      (η_hat n ω) (h_in_Hε n ω) (h_mu0_memLp n ω) (h_mu1_memLp n ω)).integrable_sq
  have hAL :=
    seqDR_dml_isAsymLinear S h_e_val_pointwise h_overlap hA h_y2 h_yd2
      sample split hc_pos hc_lt h_split_rate η_hat h_in_Hε
      h_mu0_diff_memLp h_mu1_diff_memLp h_e0_diff_memLp h_e1_diff_memLp
      h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int h_m_sq_int
      h_indiv_rate_ρ₁ h_indiv_rate_ρ₂ h_product_rate_abs
  have h_if_eq :
      (fun z => -(seqDRGeneralMoment S h_e_val_pointwise).J₀_inv *
                  S.seqDRMomentFunctional S.η₀ z S.θ₀)
      = S.ψ_seqDR := by
    funext z
    have hJ : -(seqDRGeneralMoment S h_e_val_pointwise).J₀_inv = 1 := by
      change -((seqDRGeneralMoment S h_e_val_pointwise).J₀)⁻¹ = 1
      change -((-1 : ℝ))⁻¹ = 1
      norm_num
    rw [hJ, one_mul]
    rfl
  have h_resc_eq : ∀ n ω,
      Real.sqrt ((split.foldB n).card : ℝ) *
        (Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator
          (seqDRGeneralMoment S h_e_val_pointwise) sample split η_hat n ω - S.θ₀)
      = Real.sqrt ((split.foldB n).card : ℝ) *
        (dml_DTR_estimator S sample split η_hat n ω - S.θ₀) := by
    intro n ω
    by_cases hcard : (split.foldB n).card = 0
    · have hzero : Real.sqrt ((split.foldB n).card : ℝ) = 0 := by
        rw [hcard]; simp
      rw [hzero, zero_mul, zero_mul]
    · have hcard_pos : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hcard
      have hcardR_pos : 0 < ((split.foldB n).card : ℝ) := by exact_mod_cast hcard_pos
      have h_J : (seqDRGeneralMoment S h_e_val_pointwise).J₀_inv = -1 := by
        change ((-1 : ℝ))⁻¹ = -1
        norm_num
      have hpoint : ∀ i,
          S.seqDRMomentFunctional (η_hat n ω) (sample.Z i ω) 0 =
            S.seqDRMomentFunctional (η_hat n ω) (sample.Z i ω) S.θ₀ + S.θ₀ := by
        intro i
        unfold DTREstimationSystem.seqDRMomentFunctional
        unfold Causalean.Estimation.DTR.seqDRMoment
        ring
      have hsum :
          ∑ i ∈ split.foldB n,
              S.seqDRMomentFunctional (η_hat n ω) (sample.Z i ω) 0
            = (∑ i ∈ split.foldB n,
                S.seqDRMomentFunctional (η_hat n ω) (sample.Z i ω) S.θ₀)
              + ((split.foldB n).card : ℝ) * S.θ₀ := by
        rw [Finset.sum_congr rfl (fun i _ => hpoint i),
          Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      congr 1
      simp only [Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator, dml_DTR_estimator]
      rw [h_J]
      simp only [seqDRGeneralMoment]
      change S.θ₀ -
              -1 * (((split.foldB n).card : ℝ)⁻¹ *
                ∑ x ∈ split.foldB n,
                  S.seqDRMomentFunctional (η_hat n ω) (sample.Z x ω) S.θ₀) -
              S.θ₀ =
            ((split.foldB n).card : ℝ)⁻¹ *
                ∑ i ∈ split.foldB n,
                  S.seqDRMomentFunctional (η_hat n ω) (sample.Z i ω) 0 -
              S.θ₀
      rw [hsum]
      field_simp [hcardR_pos.ne']
      ring
  refine ⟨?_, ?_, ?_⟩
  · have h := hAL.mean_zero
    rw [← h_if_eq]
    exact h
  · have h := hAL.finite_var
    rw [← h_if_eq]
    exact h
  · have h := hAL.remainder
    have hfun_eq :
        (fun n ω =>
            Real.sqrt ((split.foldB n).card : ℝ) *
              (dml_DTR_estimator S sample split η_hat n ω - S.θ₀) -
              (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
                ∑ i ∈ split.foldB n, S.ψ_seqDR (sample.Z i ω))
        = (fun n ω =>
            Real.sqrt ((split.foldB n).card : ℝ) *
              (Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator
                (seqDRGeneralMoment S h_e_val_pointwise) sample split η_hat n ω - S.θ₀) -
              (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
                ∑ i ∈ split.foldB n,
                  (-(seqDRGeneralMoment S h_e_val_pointwise).J₀_inv *
                    S.seqDRMomentFunctional S.η₀ (sample.Z i ω) S.θ₀)) := by
      funext n ω
      rw [h_resc_eq n ω]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have := congrArg (fun f => f (sample.Z i ω)) h_if_eq
      simpa using this.symm
    rw [hfun_eq]
    exact h

end DTR
end Estimation
end Causalean
