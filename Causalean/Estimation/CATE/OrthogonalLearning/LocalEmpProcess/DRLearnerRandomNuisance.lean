/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# DR-Learner oracle inequality at a *random* (cross-fitted) nuisance

`oracle_inequality_drLearner_highProb_honest` pins the nuisance to a fixed
deterministic `h`.  This file un-pins it: the nuisance is a fold-A-estimated
*random* `ĥ : ℕ → Ω → NuisanceVec γ`, and the bias term becomes the *random*
product of the two nuisance L²-errors evaluated at the realised `ĥ n ω`.

This is the genuinely double-robust statement: the second-order bias
`(2B/ε)·Σ_a ‖ĥ.μ_fn a − μ_val a‖₂·‖ĥ.e_fn − e_val‖₂` is a random quantity that
the analyst controls by separately estimating the two nuisances.

Two observations make this clean:

* The **deterministic** oracle inequality `oracle_inequality_plugin_ERM`
  already accepts a random `ghat : ℕ → Ω → G` together with a per-`(n,ω)`
  directional-derivative family `Dθ_hat`.  Only the *high-probability* wrapper
  and the empirical-process modulus bridge fixed `g`.
* `drBias_le_product` already holds for **any** `h ∈ H_ε`, hence for the random
  realisation `ĥ n ω` — its bias bound is already random-ready.

What this theorem still *takes as a hypothesis* is the realised empirical-process
modulus event `hMod`: a high-probability set on which the centred excess-risk
process is controlled at the realised `(τ̂ n ω, ĥ n ω)`.  Discharging `hMod`
from concentration plus the **cross-fitting independence** of fold B from the
fold-A nuisance (via `foldB_pi_law`) is the remaining frontier — it is the only
place the fixed-`g` modulus bridge needs to be lifted to the random nuisance.

See Kennedy (2023) and `def:est-osl-second-order-bias`.
-/

import Causalean.Estimation.CATE.OrthogonalLearning.LocalEmpProcess.DRLearnerHonest

/-! # Random-Nuisance DR-Learner Bound

This file extends the doubly robust learner oracle inequality from a fixed
nuisance value to a cross-fitted random nuisance estimate. The resulting bound
keeps the empirical-process control as an event and evaluates the second-order
bias at the realized nuisance estimate. The main theorem
`oracle_inequality_drLearner_random_nuisance` combines the deterministic
plug-in ERM oracle inequality with the product-bias bound applied pointwise to
the realized nuisance. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Causalean.PO
  Causalean.Estimation.ATE Causalean.Estimation.CATE Causalean.Stat Causalean.Stat.Concentration

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]

/-- **DR-Learner oracle inequality at a random cross-fitted nuisance.**

Given a random nuisance `ĥ : ℕ → Ω → NuisanceVec γ` (each `ĥ n ω` in the overlap
slice `H_ε`), the plug-in ERM target estimator, and — on a high-probability set
for each `n` — the realised empirical-process modulus inequality `hMod`, the
squared estimation error is bounded by the oracle/Rademacher term plus the
*random* second-order product bias plus the optimisation slack:

    ‖τ̂ n ω − θ₀‖²
      ≤ (4(1+σ)/σ²)·(ρ n)²
        + (4/σ)·(2B/ε)·Σ_a ‖ĥ n ω.μ_fn a − μ_val a‖₂·‖ĥ n ω.e_fn − e_val‖₂
        + (4/σ)·r_opt n.

The bias term is random (it depends on `ĥ n ω`), exposing the double-robust
product structure that the fixed-nuisance theorem hid. -/
theorem oracle_inequality_drLearner_random_nuisance
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
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
    {ε : ℝ} (hε_pos : 0 < ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
      BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (D : EvalDirDeriv Θ_set θ₀ eval)
    (ND : NuisanceDirDeriv S.toBackdoorEstimationSystem.η₀)
    (ĥ : ℕ → P.Ω → NuisanceVec γ)
    (hĥ_overlap : ∀ n ω, ĥ n ω ∈ BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (τhat : ℕ → P.Ω → Θ) (hτ_mem : ∀ n ω, τhat n ω ∈ Θ_set)
    (r_opt : ℕ → ℝ)
    (hPluginERM : SampleSplitPluginERM
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      S_iid split τhat ĥ r_opt)
    (σ : ℝ) (hσ : 0 < σ)
    (hSC : ∀ n ω, ∀ θ ∈ Θ_set,
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas
        eval_θ₀ θ₀_minimizes).L θ (ĥ n ω)
        - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas
          eval_θ₀ θ₀_minimizes).L θ₀ (ĥ n ω)
        ≥ (∫ z, ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
            θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at (ĥ n ω)).dℓ_θ θ z
            ∂S.toBackdoorEstimationSystem.P_Z)
          + (σ / 2) * ‖θ - θ₀‖ ^ 2)
    (hFOI : FirstOrderInequality
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
        eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at S.toBackdoorEstimationSystem.η₀))
    (ρ : ℕ → ℝ) {δ : ℝ}
    (hMod : ∀ n, ∃ E : Set P.Ω, MeasurableSet E ∧
      P.μ E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E,
        ((drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).L
              (τhat n ω) (ĥ n ω)
            - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).L
              θ₀ (ĥ n ω))
          - (empRiskFoldB
              (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
              S_iid split n ω (τhat n ω) (ĥ n ω)
            - empRiskFoldB
              (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
              S_iid split n ω θ₀ (ĥ n ω))
          ≤ ρ n * ‖τhat n ω - θ₀‖ + (ρ n) ^ 2)
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hdEval_unif : ∀ θ ∈ Θ_set, ∀ x, |D.dEval θ x| ≤ B)
    (h_μ_ĥ_int : ∀ n ω, ∀ a : Bool,
      Integrable (fun ω' => (ĥ n ω).μ_fn a
        (S.toBackdoorEstimationSystem.factualX ω')) P.μ)
    (h_phi_int : ∀ n ω,
      Integrable (fun ω' => phi_eta (S.toBackdoorEstimationSystem.factualZ ω') (ĥ n ω) -
        phi₀ S (S.toBackdoorEstimationSystem.factualZ ω')) P.μ)
    (h_phiw_int : ∀ n ω,
      Integrable (fun ω' => (phi_eta (S.toBackdoorEstimationSystem.factualZ ω') (ĥ n ω) -
        phi₀ S (S.toBackdoorEstimationSystem.factualZ ω')) *
        D.dEval (τhat n ω) (S.toBackdoorEstimationSystem.factualX ω')) P.μ)
    (hΔμ_memLp : ∀ n ω, ∀ a, MemLp
      (fun x => (ĥ n ω).μ_fn a x - S.μ_val a x) 2 S.toBackdoorEstimationSystem.P_X)
    (hΔe_memLp : ∀ n ω, MemLp
      (fun x => (ĥ n ω).e_fn x - S.e_val x) 2 S.toBackdoorEstimationSystem.P_X)
    (hA_int : ∀ n ω, Integrable
      (fun z => ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
        θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at
          S.toBackdoorEstimationSystem.η₀).dℓ_θ (τhat n ω) z)
      S.toBackdoorEstimationSystem.P_Z)
    (hB_int : ∀ n ω, Integrable
      (fun z => ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
        θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at (ĥ n ω)).dℓ_θ (τhat n ω) z)
      S.toBackdoorEstimationSystem.P_Z) :
    ∀ n : ℕ, ∃ E : Set P.Ω, MeasurableSet E ∧
      P.μ E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E,
        ‖τhat n ω - θ₀‖ ^ 2
          ≤ (4 * (1 + σ) / σ ^ 2) * (ρ n) ^ 2
            + (4 / σ) * ((2 * B / ε) *
                ∑ a : Bool,
                  (eLpNorm (fun x => (ĥ n ω).μ_fn a x - S.μ_val a x) 2
                    S.toBackdoorEstimationSystem.P_X).toReal *
                    (eLpNorm (fun x => (ĥ n ω).e_fn x - S.e_val x) 2
                      S.toBackdoorEstimationSystem.P_X).toReal)
            + (4 / σ) * r_opt n := by
  intro n
  obtain ⟨E, hEm, hEge, hE⟩ := hMod n
  refine ⟨E, hEm, hEge, fun ω hω => ?_⟩
  -- Deterministic oracle inequality at the realised random nuisance.
  have hdet := oracle_inequality_plugin_ERM
    (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
    S_iid split
    ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
      eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at S.toBackdoorEstimationSystem.η₀)
    ĥ
    (fun n ω => (drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
      θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at (ĥ n ω))
    τhat r_opt hPluginERM σ hσ hSC hFOI ρ n ω (hE ω hω)
  -- Random second-order product bias bound at `ĥ n ω`.
  have hbias := drBias_le_product S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀
    θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes D ND (ĥ n ω) (hĥ_overlap n ω) (τhat n ω)
    hB_nonneg (fun x => hdEval_unif (τhat n ω) (hτ_mem n ω) x) (h_μ_ĥ_int n ω)
    (h_phi_int n ω) (h_phiw_int n ω) (hΔμ_memLp n ω) (hΔe_memLp n ω)
    (hA_int n ω) (hB_int n ω)
  have hbias' :
      (4 / σ) *
          Bias_n (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
            ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
              eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at S.toBackdoorEstimationSystem.η₀)
            ((drMixedDirDeriv S hA hε_pos h_overlap_η₀ Θ Θ_set Θ_convex θ₀ θ₀_mem
              eval eval_meas eval_θ₀ θ₀_minimizes D ND).Dθ_at (ĥ n ω)) (τhat n ω)
        ≤ (4 / σ) * ((2 * B / ε) *
            ∑ a : Bool,
              (eLpNorm (fun x => (ĥ n ω).μ_fn a x - S.μ_val a x) 2
                S.toBackdoorEstimationSystem.P_X).toReal *
                (eLpNorm (fun x => (ĥ n ω).e_fn x - S.e_val x) 2
                  S.toBackdoorEstimationSystem.P_X).toReal) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hbias) (by positivity)
  have hθ₀ : (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀
      = θ₀ := rfl
  simp only [hθ₀] at hdet
  linarith [hdet, hbias']

end OrthogonalLearning
end Estimation
end Causalean
