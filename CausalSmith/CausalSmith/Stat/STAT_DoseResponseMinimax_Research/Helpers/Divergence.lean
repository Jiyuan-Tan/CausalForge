/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax: divergence helpers

The symmetric two-point mean-channel KL band
(`lem:bernoulli-mean-channel-kl`) and the Le Cam estimation→testing MSE reduction
(`lem:le-cam-two-point-mse-source`).

INTERNAL REUSED INGREDIENT (kept in notes, not a one-to-one discharge):
`Causalean.Mathlib.Probability.bernoulliLaw_klDiv_le_four_sq_sub` supplies the
`{0,1}` Bernoulli KL band on `[1/4,3/4]`; F3 builds the affine `{-B,B}`
mean-channel wrapper, transports `klDiv`-invariance under the measurable affine
relabeling `x ↦ 2Bx - B`, discharges the band hypotheses, and simplifies the
constant. The Le Cam MSE form is assembled from the probability-form bound in
`Causalean.Stat.MinimaxRisk` + a Markov/Chebyshev MSE bridge + Pinsker.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Basic
import Causalean.Mathlib.Probability.SignedTwoPoint
import Causalean.Mathlib.Probability.BernoulliMeasure
import Causalean.Stat.Minimax.BretagnolleHuber
import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.LeCamTwoPoint
import Mathlib.Topology.Algebra.Field

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory

open scoped ENNReal

-- The symmetric signed two-point mean channel and its KL machinery were promoted to
-- `Causalean.Mathlib.Probability.SignedTwoPoint`; re-export them under this namespace so the
-- paper's call sites resolve unchanged.
export Causalean.Mathlib.Probability
  (twoPointMean klDiv_map_measurableEquiv twoPointMean_eq_map_bernoulli bernoulli_mean_channel_kl)

-- @node: lem:bernoulli-mean-channel-kl
/-- The signed two-point mean channel has quadratic KL divergence on the central
half of its mean range. This local wrapper links the paper lemma to the reusable
Causalean implementation. -/
lemma bernoulli_mean_channel_kl_source (B u v : ℝ) (hB : 0 < B)
    (hu : |u| ≤ B / 2) (hv : |v| ≤ B / 2) :
    InformationTheory.klDiv (twoPointMean B u) (twoPointMean B v)
      ≤ ENNReal.ofReal (2 * (u - v) ^ 2 / B ^ 2) := by
  exact bernoulli_mean_channel_kl B u v hB hu hv

-- @node: lem:le-cam-two-point-mse-source
/-- Le Cam's two-point reduction: a finite KL budget gives a positive,
budget-dependent constant multiplying the squared parameter separation. -/
lemma le_cam_two_point_mse_source (K : ℝ) :
    ∃ cK : ℝ, 0 < cK ∧
      ∀ {S : Type*} [MeasurableSpace S]
        (Q0 Q1 : Measure S) [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
        (theta0 theta1 : ℝ),
        InformationTheory.klDiv Q0 Q1 ≤ ENNReal.ofReal K →
        ∀ T : S → ℝ, Measurable T →
          Integrable (fun s => (T s - theta0) ^ 2) Q0 →
          Integrable (fun s => (T s - theta1) ^ 2) Q1 →
          cK * (theta1 - theta0) ^ 2
            ≤ max (∫ s, (T s - theta0) ^ 2 ∂Q0) (∫ s, (T s - theta1) ^ 2 ∂Q1) := by
  exact Causalean.Stat.Minimax.le_cam_two_point_mse K

end CausalSmith.Stat.DoseResponseMinimax
