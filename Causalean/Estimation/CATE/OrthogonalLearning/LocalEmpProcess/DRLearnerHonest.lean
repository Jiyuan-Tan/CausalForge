/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Honest DR-Learner oracle inequality (explicit second-order product bias)

`oracle_inequality_drLearner_highProb` (in `DRLearnerEndToEnd.lean`) carries the
nuisance bias only symbolically, as `Bias_n`.  This file composes it with the
genuine second-order product bound `drBias_le_product` (proved in
`Estimation/CATE/OrthogonalLearning/SecondOrderBias.lean`) to obtain the
product-bias-disclosed Kennedy (2023) oracle inequality.  The word "honest" in
the theorem name refers only to this disclosure: the bias term is shown to be a
genuine **product** of the two nuisance L²-errors.

    ‖τ̂ₙ(ω) − θ₀‖²
      ≤ (4(1+σ)/σ²) · ρ²_{n,δ}                                    -- oracle / Rademacher
        + (4/σ) · (2B/ε) · Σ_a ‖ĥ.μ_fn a − μ_val a‖₂ · ‖ĥ.e_fn − e_val‖₂  -- 2nd-order bias
        + (4/σ) · r_opt n                                          -- optimisation slack

with high probability.  The middle term makes the double-robustness payoff
explicit: it vanishes when *either* nuisance is consistent, and is controlled by
the product of the two estimation errors — the whole point of Kennedy's
DR-Learner.  The directional-derivative bundles are pinned to the closed-form
`drMixedDirDeriv` family so that `Bias_n` carries the DR-Learner content.

See Kennedy (2023), "Towards optimal doubly robust estimation of heterogeneous
causal effects", and `def:est-osl-second-order-bias`.
-/

import Causalean.Estimation.CATE.OrthogonalLearning.LocalEmpProcess.DRLearnerEndToEnd
import Causalean.Estimation.CATE.OrthogonalLearning.SecondOrderBias

/-! # Product-Bias DR-Learner Oracle Bound

This file combines the doubly robust learner oracle inequality with the
second-order product-bias bound. The resulting high-probability statement makes
the error contribution from the two nuisance estimators explicit as a product
of their conditional mean and propensity-score errors. The main theorem is
`oracle_inequality_drLearner_highProb_honest`; the declaration keeps the
historical suffix `_honest`, where "honest" means that the bound exposes the
second-order product term instead of leaving it as the symbolic `Bias_n`. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Causalean.PO
  Causalean.Estimation.ATE Causalean.Estimation.CATE Causalean.Stat Causalean.Stat.Concentration

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]

/-- **Product-bias DR-Learner oracle inequality.**

Same setup as `oracle_inequality_drLearner_highProb`, but with the
directional-derivative bundles fixed to the closed-form `drMixedDirDeriv` family
and the extra bookkeeping needed by `drBias_le_product`.  The conclusion replaces
the symbolic `Bias_n` term with the explicit second-order product bound
`(2B/ε)·Σ_a ‖Δμ_a‖₂·‖Δe‖₂`, where `B` uniformly bounds `|D.dEval θ|` on `Θ_set`.
The theorem name uses the legacy suffix `_honest` for this product-bias-disclosed
version of the bound. -/
theorem oracle_inequality_drLearner_highProb_honest
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] [IsProbabilityMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    (eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval)
    (S_iid : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.toBackdoorEstimationSystem.P_Z)
    (split : OneShotSplit S_iid)
    {M_Θ M_Y M_μ ε : ℝ}
    (hM_Θ : DREvalBounded Θ_set eval M_Θ)
    (hM_Y : DROutcomeBounded S M_Y)
    (h : NuisanceVec γ)
    (hM_μ : DRNuisanceMuBounded h M_μ)
    (hOverlap : DRNuisanceOverlap S Θ_set h ε)
    (hLoss_cont : LossContinuousOnΘset
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes) h)
    (idx : ℕ →
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set)
    (idx_dense : DenseRange idx)
    (R : ℕ → ℝ)
    (hR : RademacherBound
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      S_iid split h idx R)
    (hclamp_minimizes : DRClampedThetaMinimizes S Θ_set θ₀ eval
      ((M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2))
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hε_pos : 0 < ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
      BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (h_overlap_h : h ∈ BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (D : EvalDirDeriv Θ_set θ₀ eval)
    (ND : NuisanceDirDeriv S.toBackdoorEstimationSystem.η₀)
    (τhat : ℕ → P.Ω → Θ) (hτ_mem : ∀ n ω, τhat n ω ∈ Θ_set)
    (r_opt : ℕ → ℝ)
    (hPluginERM : SampleSplitPluginERM
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      S_iid split τhat (fun _ _ => h) r_opt)
    (σ : ℝ) (hσ : 0 < σ)
    (hSC : ∀ θ ∈ Θ_set,
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).L θ h
        - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).L θ₀ h
        ≥ (∫ z, ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
            θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at h).dℓ_θ θ z
            ∂S.toBackdoorEstimationSystem.P_Z)
          + (σ / 2) * ‖θ - θ₀‖ ^ 2)
    (hFOI : FirstOrderInequality
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
        eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at S.toBackdoorEstimationSystem.η₀))
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hdEval_unif : ∀ θ ∈ Θ_set, ∀ x, |D.dEval θ x| ≤ B)
    (h_μ_h_int : ∀ a : Bool,
      Integrable (fun ω => h.μ_fn a (S.toBackdoorEstimationSystem.factualX ω)) P.μ)
    (h_phi_int :
      Integrable (fun ω => phi_eta (S.toBackdoorEstimationSystem.factualZ ω) h -
        phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)) P.μ)
    (h_phiw_int : ∀ n ω,
      Integrable (fun ω' => (phi_eta (S.toBackdoorEstimationSystem.factualZ ω') h -
        phi₀ S (S.toBackdoorEstimationSystem.factualZ ω')) *
        D.dEval (τhat n ω) (S.toBackdoorEstimationSystem.factualX ω')) P.μ)
    (hΔμ_memLp : ∀ a, MemLp
      (fun x => h.μ_fn a x - S.μ_val a x) 2 S.toBackdoorEstimationSystem.P_X)
    (hΔe_memLp : MemLp
      (fun x => h.e_fn x - S.e_val x) 2 S.toBackdoorEstimationSystem.P_X)
    (hA_int : ∀ n ω, Integrable
      (fun z => ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
        θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at
          S.toBackdoorEstimationSystem.η₀).dℓ_θ (τhat n ω) z)
      S.toBackdoorEstimationSystem.P_Z)
    (hB_int : ∀ n ω, Integrable
      (fun z => ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
        θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at h).dℓ_θ (τhat n ω) z)
      S.toBackdoorEstimationSystem.P_Z) :
    ∃ b : ℝ, 0 ≤ b ∧
      ∀ n : ℕ, ∃ E : Set P.Ω, MeasurableSet E ∧
        P.μ E ≥ 1 - ENNReal.ofReal δ ∧
        ∀ ω ∈ E,
          ‖τhat n ω - θ₀‖ ^ 2
            ≤ (4 * (1 + σ) / σ ^ 2)
                * (Real.sqrt
                    (if (split.foldB n).card = 0 then
                      2 * b
                     else
                      2 * R n
                        + 2 * b *
                          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2
              + (4 / σ) * ((2 * B / ε) *
                  ∑ a : Bool,
                    (eLpNorm (fun x => h.μ_fn a x - S.μ_val a x) 2
                      S.toBackdoorEstimationSystem.P_X).toReal *
                      (eLpNorm (fun x => h.e_fn x - S.e_val x) 2
                        S.toBackdoorEstimationSystem.P_X).toReal)
              + (4 / σ) * r_opt n := by
  obtain ⟨b, hb, hbound⟩ :=
    oracle_inequality_drLearner_highProb S Θ Θ_set Θ_convex θ₀ θ₀_mem eval
      eval_meas eval_θ₀ θ₀_minimizes S_iid split hM_Θ hM_Y h hM_μ hOverlap
      hLoss_cont idx idx_dense R hR hclamp_minimizes hδ hδ'
      ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
        eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at S.toBackdoorEstimationSystem.η₀)
      ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
        eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at h)
      τhat r_opt hPluginERM σ hσ hSC hFOI
  refine ⟨b, hb, fun n => ?_⟩
  obtain ⟨E, hEm, hEge, hE⟩ := hbound n
  refine ⟨E, hEm, hEge, fun ω hω => ?_⟩
  have hbias := drBias_le_product S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
    θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND h h_overlap_h (τhat n ω) hB_nonneg
    (fun x => hdEval_unif (τhat n ω) (hτ_mem n ω) x) h_μ_h_int h_phi_int
    (h_phiw_int n ω) hΔμ_memLp hΔe_memLp (hA_int n ω) (hB_int n ω)
  have hbias' :
      (4 / σ) *
          Bias_n (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
            ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
              eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at S.toBackdoorEstimationSystem.η₀)
            ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
              eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at h) (τhat n ω)
        ≤ (4 / σ) * ((2 * B / ε) *
            ∑ a : Bool,
              (eLpNorm (fun x => h.μ_fn a x - S.μ_val a x) 2
                S.toBackdoorEstimationSystem.P_X).toReal *
                (eLpNorm (fun x => h.e_fn x - S.e_val x) 2
                  S.toBackdoorEstimationSystem.P_X).toReal) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hbias) (by positivity)
  linarith [hE ω hω, hbias']

end OrthogonalLearning
end Estimation
end Causalean
