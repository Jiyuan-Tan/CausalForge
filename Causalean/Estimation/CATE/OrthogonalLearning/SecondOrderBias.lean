/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Second-order product bias for the DR-Learner orthogonal-learning `Bias_n`

`OrthogonalLearning.Bias_n` packages the loss-gradient nuisance bias of a `LearningSystem`.  For the
DR-Learner instantiation (`drLearningSystem`) with the closed-form mixed
directional-derivative bundle `drMixedDirDeriv`, this file proves that `Bias_n`
is genuinely *second-order*: it is bounded by the **product** of the two nuisance
L²-errors,

    |Bias_n| ≤ (2 B / ε) · Σ_a ‖ĥ.μ_fn a − μ_val a‖_{L²(P_X)} · ‖ĥ.e_fn − e_val‖_{L²(P_X)},

where `B` bounds `|D.dEval θ̂|`.  This is the quantitative double-robustness
statement that the abstract `OrthogonalLearning.Bias_taylor_form` only recorded as a trivial
existential Taylor-form witness.

Mechanism.  Both directional-derivative bundles passed to `Bias_n` come from
`drMixedDirDeriv`, whose `dℓ_θ` field is the *literal* closed form
`-2·(phi_eta z η − eval θ₀ z.1)·D.dEval θ z.1`.  The two integrands therefore
share the same `D.dEval θ̂` factor and the `eval θ₀` term cancels, so

    Bias_n = 2 · ∫ z, (phi_eta z ĥ − phi₀ S z) · D.dEval θ̂ z.1 ∂P_Z.

Applying `CATE.abs_integral_phiDiff_mul_le_product` with the bounded test
function `w := D.dEval θ̂` yields the product bound.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-second-order-bias`, and Kennedy (2023).
-/

import Causalean.Estimation.CATE.Core.SecondOrderBias
import Causalean.Estimation.CATE.OrthogonalLearning.DRLearner.Analytic
import Causalean.Estimation.OrthogonalLearning.Population.SecondOrderBias

/-! # DR-Learner Second-Order Bias

This file shows that the nuisance-induced bias in the doubly robust learner for
conditional treatment effects is bounded by the product of the outcome-regression
error and the propensity-score error. The result makes the double-robust
second-order remainder in the orthogonal statistical-learning oracle inequality
explicit. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO
  Causalean.Estimation.ATE Causalean.Estimation.CATE

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **DR-Learner second-order product bias bound.**

For the DR-Learner orthogonal-learning system with the closed-form mixed-derivative bundle
`drMixedDirDeriv`, the loss-gradient nuisance bias `Bias_n` is bounded by the
product of the two nuisance L²-errors:

    |Bias_n| ≤ (2 B / ε) · Σ_a ‖ĥ.μ_fn a − μ_val a‖₂ · ‖ĥ.e_fn − e_val‖₂,

with `B` any bound on `|D.dEval θ̂|` (available from `EvalDirDeriv.bound`).  This
makes the double-robustness content explicit: the bias vanishes to first order in
each nuisance and is controlled by their product. -/
theorem drBias_le_product
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
      BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    (eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval)
    (D : EvalDirDeriv Θ_set θ₀ eval)
    (ND : NuisanceDirDeriv S.toBackdoorEstimationSystem.η₀)
    (h : NuisanceVec γ)
    (h_overlap_h : h ∈ BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (θhat : Θ)
    {B : ℝ} (hB_nonneg : 0 ≤ B) (hdEval_bound : ∀ x, |D.dEval θhat x| ≤ B)
    (h_μ_h_int : ∀ a : Bool,
      Integrable (fun ω => h.μ_fn a (S.toBackdoorEstimationSystem.factualX ω)) P.μ)
    (h_phi_int :
      Integrable (fun ω => phi_eta (S.toBackdoorEstimationSystem.factualZ ω) h -
        phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)) P.μ)
    (h_phiw_int :
      Integrable (fun ω => (phi_eta (S.toBackdoorEstimationSystem.factualZ ω) h -
        phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)) *
        D.dEval θhat (S.toBackdoorEstimationSystem.factualX ω)) P.μ)
    (hΔμ_memLp : ∀ a, MemLp
      (fun x => h.μ_fn a x - S.μ_val a x) 2 S.toBackdoorEstimationSystem.P_X)
    (hΔe_memLp : MemLp
      (fun x => h.e_fn x - S.e_val x) 2 S.toBackdoorEstimationSystem.P_X)
    (hA_int : Integrable
      (fun z => ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
        θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at
          S.toBackdoorEstimationSystem.η₀).dℓ_θ θhat z)
      S.toBackdoorEstimationSystem.P_Z)
    (hB_int : Integrable
      (fun z => ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
        θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at h).dℓ_θ θhat z)
      S.toBackdoorEstimationSystem.P_Z) :
    |Bias_n
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
        ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
          eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at S.toBackdoorEstimationSystem.η₀)
        ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
          eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at h)
        θhat|
      ≤ (2 * B / ε) *
          ∑ a : Bool,
            (eLpNorm (fun x => h.μ_fn a x - S.μ_val a x) 2
              S.toBackdoorEstimationSystem.P_X).toReal *
              (eLpNorm (fun x => h.e_fn x - S.e_val x) 2
                S.toBackdoorEstimationSystem.P_X).toReal := by
  -- Closed forms of the two directional-derivative integrands (literal fields).
  have hAclosed : ∀ z,
      ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
        eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at
          S.toBackdoorEstimationSystem.η₀).dℓ_θ θhat z
        = -2 * (phi_eta z S.toBackdoorEstimationSystem.η₀ - eval θ₀ z.1) *
            D.dEval θhat z.1 := fun _ => rfl
  have hBclosed : ∀ z,
      ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
        eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at h).dℓ_θ θhat z
        = -2 * (phi_eta z h - eval θ₀ z.1) * D.dEval θhat z.1 := fun _ => rfl
  -- Bias_n telescopes (the `eval θ₀` term cancels) to `2 ∫ (phi_eta·h − phi₀)·dEval`.
  have hBias_eq :
      Bias_n (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
        ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
          eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at S.toBackdoorEstimationSystem.η₀)
        ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
          eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at h) θhat
        = 2 * ∫ z, (phi_eta z h - phi₀ S z) * D.dEval θhat z.1
            ∂S.toBackdoorEstimationSystem.P_Z := by
    unfold Bias_n
    rw [← integral_sub hA_int hB_int, ← integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hAclosed z, hBclosed z, phi₀]
    ring
  rw [hBias_eq, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
  calc
    2 * |∫ z, (phi_eta z h - phi₀ S z) * D.dEval θhat z.1
            ∂S.toBackdoorEstimationSystem.P_Z|
        ≤ 2 * ((B / ε) *
            ∑ a : Bool,
              (eLpNorm (fun x => h.μ_fn a x - S.μ_val a x) 2
                S.toBackdoorEstimationSystem.P_X).toReal *
                (eLpNorm (fun x => h.e_fn x - S.e_val x) 2
                  S.toBackdoorEstimationSystem.P_X).toReal) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact abs_integral_phiDiff_mul_le_product S hε_pos hA h h_overlap_h
            h_overlap_η₀ h_μ_h_int (D.dEval θhat) (D.meas θhat) hB_nonneg
            hdEval_bound h_phi_int h_phiw_int hΔμ_memLp hΔe_memLp
    _ = (2 * B / ε) *
          ∑ a : Bool,
            (eLpNorm (fun x => h.μ_fn a x - S.μ_val a x) 2
              S.toBackdoorEstimationSystem.P_X).toReal *
              (eLpNorm (fun x => h.e_fn x - S.e_val x) 2
                S.toBackdoorEstimationSystem.P_X).toReal := by ring

end OrthogonalLearning
end Estimation
end Causalean
