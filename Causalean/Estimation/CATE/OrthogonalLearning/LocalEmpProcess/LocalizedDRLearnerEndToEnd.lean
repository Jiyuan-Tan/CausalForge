/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# DR-Learner localized high-probability oracle inequality

This file is the localized sibling of `Estimation/CATE/OrthogonalLearning/LocalEmpProcess/DRLearnerEndToEnd.lean`.
It chains the sharp Foster-Syrgkanis localized modulus realization
`localEmpProcessModulus_localized_drLearner` with the generic
`oracle_inequality_plugin_ERM_highProb`.

The resulting rate uses the critical radius of the centred DR-loss class:

  `ρ n := if |B(n)| = 0 then √(2b)
          else (8L + 3) * criticalRadius (ψ |B(n)|)`.
-/

import Causalean.Estimation.OrthogonalLearning.OracleInequality
import Causalean.Estimation.CATE.OrthogonalLearning.LocalEmpProcess.LocalizedDRLearner

/-! # Localized DR-Learner Oracle Chain

This file composes the localized empirical-process modulus for the DR-Learner
with the generic orthogonal statistical learning oracle inequality. It provides
the high-probability CATE bound whose rate is governed by the localized critical
radius, with a separate bounded branch for an empty validation fold. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
  Causalean.PO Causalean.Estimation.ATE Causalean.Estimation.CATE
  Causalean.Stat Causalean.Stat.Concentration

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]

/-- **DR-Learner localized high-probability oracle inequality.**

Given the DR-Learner orthogonal-learning system from
`OrthogonalLearning/DRLearner.lean`, the localized critical-radius hypotheses from
`Estimation/CATE/OrthogonalLearning/LocalEmpProcess/LocalizedDRLearner.lean`, and the oracle-inequality
ingredients, conclude that with `P.μ`-probability at least `1 - δ`,

  `‖τhat n ω − τ₀‖² ≤ (4(1+σ)/σ²) · ρ²_n
                       + (4/σ) · Bias_n + (4/σ) · r_opt n`,

where `ρ n` is the sharp localized Foster-Syrgkanis rate
`(8L+3)·criticalRadius (ψ |B(n)|)` on nonempty fold-B samples, with the
same empty-fold bounded branch as the modulus theorem.
-/
theorem oracle_inequality_localized_drLearner_highProb
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [IsProbabilityMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    [Nonempty Θ_set] [Countable Θ_set]
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    (eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval)
    (S_iid : IIDSample P.Ω (γ × Bool × ℝ) P.μ
      S.toBackdoorEstimationSystem.P_Z)
    (split : OneShotSplit S_iid)
    {M_Θ M_Y M_μ ε : ℝ}
    (hM_Θ : DREvalBounded Θ_set eval M_Θ)
    (hM_Y : DROutcomeBounded S M_Y)
    (h : NuisanceVec γ)
    (hM_μ : DRNuisanceMuBounded h M_μ)
    (hOverlap : DRNuisanceOverlap S Θ_set h ε)
    (hclamp_minimizes : CenteredClampedThetaMinimizes
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      (2 * (M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2))
    (hLoss_cont : ∀ z,
      Continuous fun (θ :
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set) =>
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ.val h)
    (idx : ℕ →
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set)
    (idx_dense : DenseRange idx)
    {norm : ((γ × Bool × ℝ) → ℝ) → ℝ}
    {ψ : ℕ → ℝ → ℝ}
    (hψ : DRCriticalRadius S Θ_set eval
      (fun k => ⟨((idx k).val), (idx k).property⟩)
      h norm ψ)
    (hnorm_ae : ∀ F F' : (γ × Bool × ℝ) → ℝ,
      F =ᵐ[S.toBackdoorEstimationSystem.P_Z] F' → norm F = norm F')
    {Rmax L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hF_lip : ∀ θ ∈
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set,
      norm (fun z =>
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ h
          - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z
              (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀ h)
        ≤ L * ‖θ -
            (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀‖)
    (hF_diam : ∀ θ ∈
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set,
      norm (fun z =>
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ h
          - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z
              (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀ h)
        ≤ Rmax)
    (hRmax_lb : ∀ m : ℕ, criticalRadius (ψ m) ≤ Rmax)
    (hcrit_pos : ∀ m : ℕ, 0 < criticalRadius (ψ m))
    (hcrit_fp : ∀ m : ℕ, ψ m (criticalRadius (ψ m)) ≤ (criticalRadius (ψ m)) ^ 2)
    (hψ_ub : ∀ m : ℕ,
      RademacherUpperBound
        (fun (θ :
            (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set)
          (z : γ × Bool × ℝ) =>
          (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ.val h
            - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z
                (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀ h)
        norm S.toBackdoorEstimationSystem.P_Z
        (id : (γ × Bool × ℝ) → γ × Bool × ℝ) m (ψ m))
    (hrad_bdd : ∀ m r, ∀ S_fin : Fin m → γ × Bool × ℝ, ∀ σ : Signs m,
      BddAbove (Set.range fun p : starHullParam
            (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set =>
        |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
          starHullZeroOut
            (fun (θ :
                (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set)
              (z : γ × Bool × ℝ) =>
              (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ.val h
                - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z
                    (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀ h)
            norm r p (S_fin k)|))
    (hrad_int : ∀ m r,
      Integrable
        (fun ω : Fin m → γ × Bool × ℝ =>
          empiricalRademacherComplexity m
            (starHullZeroOut
              (fun (θ :
                  (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set)
                (z : γ × Bool × ℝ) =>
                (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ.val h
                  - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z
                      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀ h)
              norm r) ((id : (γ × Bool × ℝ) → (γ × Bool × ℝ)) ∘ ω))
        (Measure.pi (fun _ => S.toBackdoorEstimationSystem.P_Z)))
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hδ_dom : ∀ n K : ℕ, 0 < (split.foldB n).card →
      Rmax ≤ (criticalRadius (ψ (split.foldB n).card)) * (2 : ℝ) ^ K →
      2 * (M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2 *
          Real.sqrt
            (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / (split.foldB n).card)
        ≤ (criticalRadius (ψ (split.foldB n).card)) ^ 2)
    -- Oracle-inequality ingredients specialised to the DR system.
    (Dθ_truth : HasDirDerivTheta
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).g₀)
    (Dθ_at_h : HasDirDerivTheta
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes) h)
    (τhat : ℕ → P.Ω → Θ)
    (r_opt : ℕ → ℝ)
    (hPluginERM : SampleSplitPluginERM
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      S_iid split τhat (fun _ _ => h) r_opt)
    (σ : ℝ) (hσ : 0 < σ)
    (hSC : ∀ θ ∈ Θ_set,
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).L θ h
        - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).L θ₀ h
        ≥ (∫ z, Dθ_at_h.dℓ_θ θ z ∂S.toBackdoorEstimationSystem.P_Z)
          + (σ / 2) * ‖θ - θ₀‖ ^ 2)
    (hFOI : FirstOrderInequality
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes) Dθ_truth) :
    ∃ b : ℝ, 0 ≤ b ∧
      ∀ n : ℕ, ∃ E : Set P.Ω, MeasurableSet E ∧
        P.μ E ≥ 1 - ENNReal.ofReal δ ∧
        ∀ ω ∈ E,
          ‖τhat n ω - θ₀‖ ^ 2
            ≤ (4 * (1 + σ) / σ ^ 2)
                * (if (split.foldB n).card = 0 then Real.sqrt (2 * b)
                  else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card)) ^ 2
              + (4 / σ) *
                  Bias_n
                    (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
                    Dθ_truth Dθ_at_h (τhat n ω)
              + (4 / σ) * r_opt n := by
  rcases localEmpProcessModulus_localized_drLearner
      (S := S) (Θ := Θ) (Θ_set := Θ_set) (Θ_convex := Θ_convex)
      (θ₀ := θ₀) (θ₀_mem := θ₀_mem)
      (eval := eval) (eval_meas := eval_meas) (eval_θ₀ := eval_θ₀)
      (θ₀_minimizes := θ₀_minimizes)
      (S_iid := S_iid) (split := split)
      (hM_Θ := hM_Θ) (hM_Y := hM_Y) (h := h)
      (hM_μ := hM_μ) (hOverlap := hOverlap)
      (hclamp_minimizes := hclamp_minimizes)
      (_hLoss_cont := hLoss_cont) (idx := idx) (_idx_dense := idx_dense)
      (hψ := hψ) (hnorm_ae := hnorm_ae) (Rmax := Rmax) (L := L)
      (hL_nonneg := hL_nonneg) (hF_lip := hF_lip) (hF_diam := hF_diam)
      (hRmax_lb := hRmax_lb) (hcrit_pos := hcrit_pos) (hcrit_fp := hcrit_fp)
      (hψ_ub := hψ_ub) (hrad_bdd := hrad_bdd) (hrad_int := hrad_int)
      (hδ := hδ) (hδ' := hδ') (hδ_dom := hδ_dom) with
    ⟨b, hb_nonneg, hMod⟩
  refine ⟨b, hb_nonneg, ?_⟩
  exact oracle_inequality_plugin_ERM_highProb
    (S := drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
    (S_iid := S_iid) (split := split)
    (Dθ_truth := Dθ_truth) (g := h) (Dθ_at_g := Dθ_at_h)
    (θhat := τhat) (r_opt := r_opt) (hPluginERM := hPluginERM)
    (σ := σ) (hσ := hσ) (hSC := hSC) (hFOI := hFOI)
    (ρ := fun n =>
      if (split.foldB n).card = 0 then Real.sqrt (2 * b)
      else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card))
    (δ := δ) hMod

end OrthogonalLearning
end Estimation
end Causalean
