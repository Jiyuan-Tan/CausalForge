/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Crux: sequential-experiment cumulative-risk engine

Infrastructure item **I-2**: the paper's core reduction turning
second-moment learning delay into cumulative Neyman loss, via sequential
Fisher-information accounting of the tilted marginals through the predictable
Bernoulli history + a Bayes-average argument through the van Trees gate +
harmonic accumulation to `log T`.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.NeymanAlgebra
import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.VanTrees
import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.SequentialRiskUniform

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory
open scoped BigOperators Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- @node: lem:local-neighborhood-cumulative-risk
/-- CRUX (I-2).  For `nu ∈ M_tan`, a feasible direction `u ∈ U_nu`, and its
linear-tilt path `h ↦ p h = nu^(u,h)`, there is a radius `bar_η > 0` such that for
every `η ∈ (0, bar_η]` there is a horizon threshold `T₀` beyond which every
adaptive design pays cumulative Neyman regret at least
`c₀ · S² · π̇_nu(u)² · J_nu(u)⁻¹ · log T` somewhere in the `η`-neighborhood, with
`c₀ > 0` a universal numerical constant.

This is an honest CONDITIONAL theorem: it assumes `LocalNeighborhoodRiskInputs`,
the disclosed sequential van Trees / DQM Fisher-tensorization bridge from the
external substrate debt.  The harmonic accumulation itself reuses
`cumulative_risk_engine_uniform_threshold`; the i.i.d.-superpopulation sampling
atom enters as `hiid`. -/
lemma local_neighborhood_cumulative_risk
    (hbridge : LocalNeighborhoodRiskInputs.{u}) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (nu : Measure (ℝ × ℝ)) (μ : Measure Ω), MTan nu → SuperpopulationIID μ nu →
        ∀ (u : ℝ × ℝ), u ∈ feasibleDirectionSet nu →
          ∀ p : ℝ → Measure (ℝ × ℝ), IsLinearTiltPath nu u p → IsLocalPath nu u p →
            ∃ barη : ℝ, 0 < barη ∧
              ∀ η : ℝ, 0 < η → η ≤ barη →
                ∃ T₀ : ℕ, ∀ (Alg : AdaptiveAlgorithm) (T : ℕ), T₀ ≤ T →
                  c₀ * (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
                      * oracleSensitivity nu u ^ 2 / localInformation nu u
                      * Real.log (T : ℝ)
                    ≤ ⨆ h ∈ Set.Icc (-η) η, cumulativeNeymanRegret Alg (p h) T := by
  refine ⟨(1 : ℝ) / 16, by norm_num, ?_⟩
  intro nu μ hnu hiid u hu p hlin hp
  rcases hbridge nu μ hnu hiid u hu p hlin hp with
    ⟨L, Iq, hL, hIq, barη, hbarη, hinputs⟩
  refine ⟨barη, hbarη, ?_⟩
  intro η hηpos hηle
  have hS : 0 < rootSecondMoment nu 0 + rootSecondMoment nu 1 :=
    add_pos (hnu.interiorMoments 0) (hnu.interiorMoments 1)
  have hJ : 0 < localInformation nu u := hu.1
  have hd : oracleSensitivity nu u ≠ 0 := hu.2
  rcases cumulative_risk_engine_uniform_threshold
      (localInformation nu u) (oracleSensitivity nu u) L Iq hJ hd hL hIq with
    ⟨T₀, hT₀⟩
  refine ⟨T₀, ?_⟩
  intro Alg T hT
  rcases hinputs η hηpos hηle Alg with ⟨b, B, RB, hB, hrec, hconv, hsup⟩
  have hBT := hT₀ b B hB hrec T hT
  have hscale_nonneg : 0 ≤ 2 * (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2 := by
    positivity
  have hscaled :
      2 * (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
          * ((oracleSensitivity nu u ^ 2 / (32 * localInformation nu u))
            * Real.log (T : ℝ))
        ≤ 2 * (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2 * B T :=
    mul_le_mul_of_nonneg_left hBT hscale_nonneg
  have hchain :
      2 * (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
          * ((oracleSensitivity nu u ^ 2 / (32 * localInformation nu u))
            * Real.log (T : ℝ))
        ≤ ⨆ h ∈ Set.Icc (-η) η, cumulativeNeymanRegret Alg (p h) T :=
    hscaled.trans ((hconv T).trans (hsup T))
  convert hchain using 1
  · field_simp [ne_of_gt hJ]
    ring

end CausalSmith.Stat.NeymanRegretMinimax
