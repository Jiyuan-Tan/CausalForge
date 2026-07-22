/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# DR-Learner end-to-end high-probability oracle inequality

This file chains `OrthogonalLearning.OracleInequality.oracle_inequality_plugin_ERM_highProb`
with `OrthogonalLearning.LocalEmpProcess.localEmpProcessModulus_drLearner` to derive an
explicit high-probability rate

  `‖τ̂_n − τ₀‖² ≤ (4(1+σ)/σ²) · ρ²_{n,δ}
                  + (4/σ) · Bias_n + (4/σ) · r_opt n`

with probability at least `1 − δ` for the DR-Learner causal instantiation,
where `ρ_{n,δ} := √(2 R n + 2b · √(2 log(1/δ)/|B(n)|))` on nonempty
estimation folds, with boundary branch `ρ_{n,δ} := √(2b)`, is the modulus
realised by `localEmpProcessModulus_drLearner`.

The rate-shape follows the orthogonal statistical-learning note's `thm:est-osl-plugin-erm-oracle` as
specialised by `prop:est-osl-dr-loss-orthogonal`.

The result composes the generic high-probability oracle inequality with the
DR-Learner empirical-process modulus realization.
-/

import Causalean.Estimation.OrthogonalLearning.OracleInequality
import Causalean.Estimation.CATE.OrthogonalLearning.DRLearner
import Causalean.Estimation.CATE.OrthogonalLearning.LocalEmpProcess.DRLearner

/-! # DR-Learner Oracle Chain

This file composes the generic plug-in oracle inequality with the global
Rademacher modulus for the doubly robust learner for conditional treatment
effects. It yields a high-probability squared-error bound whose leading term is
the empirical-process modulus and whose remaining terms are nuisance bias and
optimization slack. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
  Causalean.PO Causalean.Estimation.ATE Causalean.Estimation.CATE
  Causalean.Stat Causalean.Stat.Concentration

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]

/-- **DR-Learner end-to-end high-probability oracle inequality.**

Given the DR-Learner orthogonal-learning system from
`OrthogonalLearning/DRLearner.lean` and the bounded-loss / Rademacher-bound
hypotheses of `Estimation/CATE/OrthogonalLearning/LocalEmpProcess/DRLearner.lean`,
plus the generic oracle-inequality ingredients (strong convexity at the
realised nuisance, first-order inequality at the truth, plug-in ERM optimality
at `g := h`),
conclude:

with `P.μ`-probability at least `1 − δ`,

  `‖τhat n ω − τ₀‖² ≤ (4(1+σ)/σ²) · ρ²_{n,δ}
                       + (4/σ) · Bias_n + (4/σ) · r_opt n`

where `ρ_{n,δ} = √(2 R n + 2b · √(2 log(1/δ)/|B(n)|))` on nonempty
estimation folds, with boundary branch `ρ_{n,δ} = √(2b)`, is the modulus
realised by `localEmpProcessModulus_drLearner`.

The proof invokes `localEmpProcessModulus_drLearner` to get the
`LocalEmpProcessModulus` event, then applies
`oracle_inequality_plugin_ERM_highProb` against that event. -/
theorem oracle_inequality_drLearner_highProb
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [IsProbabilityMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
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
    -- Generic oracle-inequality ingredients specialised to the DR system.
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
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas
        eval_θ₀ θ₀_minimizes) Dθ_truth) :
    ∃ b : ℝ, 0 ≤ b ∧
      ∀ n : ℕ, ∃ E : Set P.Ω, MeasurableSet E ∧
        P.μ E ≥ 1 - ENNReal.ofReal δ ∧
        ∀ ω ∈ E,
          ‖τhat n ω - θ₀‖ ^ 2
            ≤ (4 * (1 + σ) / σ ^ 2)
                * (Real.sqrt
                    (if (split.foldB n).card = 0 then 2 * b
                     else 2 * R n + 2 * b *
                      Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2
              + (4 / σ) *
                  Bias_n
                    (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval
                      eval_meas eval_θ₀ θ₀_minimizes)
                    Dθ_truth Dθ_at_h (τhat n ω)
              + (4 / σ) * r_opt n := by
  rcases localEmpProcessModulus_drLearner
      S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀
      θ₀_minimizes
      S_iid split hM_Θ hM_Y h hM_μ hOverlap hLoss_cont idx idx_dense
      R hR hclamp_minimizes hδ hδ' with
    ⟨b, hb_nonneg, hMod⟩
  refine ⟨b, hb_nonneg, ?_⟩
  exact oracle_inequality_plugin_ERM_highProb
    (S := drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
    (S_iid := S_iid) (split := split)
    (Dθ_truth := Dθ_truth) (g := h) (Dθ_at_g := Dθ_at_h)
    (θhat := τhat) (r_opt := r_opt) (hPluginERM := hPluginERM)
    (σ := σ) (hσ := hσ) (hSC := hSC) (hFOI := hFOI)
    (ρ := fun n => Real.sqrt
      (if (split.foldB n).card = 0 then 2 * b
       else 2 * R n + 2 * b *
        Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)))
    (δ := δ) hMod

end OrthogonalLearning
end Estimation
end Causalean
