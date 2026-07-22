/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Helpers

namespace CausalSmith.Experimentation.SaturationSkew

open MeasureTheory
open scoped BigOperators

-- @node: lem:explicit-profile-value
theorem explicit_profile_value (V1 V3 V4 pbar : ℝ) (hb : BudgetInterior pbar) :
    profileValue V1 V3 V4 pbar 0 = 0 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (pbar * (1 - pbar)),
        profileValue V1 V3 V4 pbar s
          = min
              (⨅ t ∈ Set.Icc (s / pbar - pbar) ((1 - pbar) - s / (1 - pbar)),
                V1 * s + V4 * s ^ 2 + s * (V3 * t + V4 * t ^ 2))
              (⨅ r ∈ Set.Icc (-s / (1 - pbar)) (s / pbar),
                V1 * s + V3 * (((1 - pbar) - pbar) * s + (s - pbar * (1 - pbar)) * r)
                  + V4 * ((1 - 3 * (pbar * (1 - pbar))) * s
                      + (s - pbar * (1 - pbar)) * (r ^ 2 + ((1 - pbar) - pbar) * r)))) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (pbar * (1 - pbar)),
        ∃ ν ∈ secondMomentSlice pbar s, cardSupportLe 3 ν ∧
          (∫ u, (V1 * (u - pbar) ^ 2 + V3 * (u - pbar) ^ 3 + V4 * (u - pbar) ^ 4)
              ∂(ν : Measure ℝ))
            = profileValue V1 V3 V4 pbar s) ∧
      -- Branch-attainer (first minimum `Φ₂`): the first interval minimum is attained
      -- at some `t`, realized by the two-point centered law whose support points are
      -- the roots of `x² - t x - s = 0` (equivalently `m₃ = s t`, `m₄ = s² + s t²`).
      (∀ s ∈ Set.Ioo (0 : ℝ) (pbar * (1 - pbar)),
        ∃ t ∈ Set.Icc (s / pbar - pbar) ((1 - pbar) - s / (1 - pbar)),
          (⨅ t' ∈ Set.Icc (s / pbar - pbar) ((1 - pbar) - s / (1 - pbar)),
              V1 * s + V4 * s ^ 2 + s * (V3 * t' + V4 * t' ^ 2))
            = V1 * s + V4 * s ^ 2 + s * (V3 * t + V4 * t ^ 2) ∧
          ∃ ν ∈ secondMomentSlice pbar s, cardSupportLe 2 ν ∧
            centeredMoment pbar 3 ν = s * t ∧
            centeredMoment pbar 4 ν = s ^ 2 + s * t ^ 2) ∧
      -- Branch-attainer (second minimum `Φ₃`): the second interval minimum is
      -- attained at some `r`, realized by the endpoint-interior law on the centered
      -- support `{-pbar, r, 1 - pbar}` (decentered `{0, pbar + r, 1}`) whose weights
      -- are forced by the slice (mean `pbar`, second moment `s`).
      (∀ s ∈ Set.Ioo (0 : ℝ) (pbar * (1 - pbar)),
        ∃ r ∈ Set.Icc (-s / (1 - pbar)) (s / pbar),
          (⨅ r' ∈ Set.Icc (-s / (1 - pbar)) (s / pbar),
              V1 * s + V3 * (((1 - pbar) - pbar) * s + (s - pbar * (1 - pbar)) * r')
                + V4 * ((1 - 3 * (pbar * (1 - pbar))) * s
                    + (s - pbar * (1 - pbar)) * (r' ^ 2 + ((1 - pbar) - pbar) * r')))
            = V1 * s + V3 * (((1 - pbar) - pbar) * s + (s - pbar * (1 - pbar)) * r)
                + V4 * ((1 - 3 * (pbar * (1 - pbar))) * s
                    + (s - pbar * (1 - pbar)) * (r ^ 2 + ((1 - pbar) - pbar) * r)) ∧
          ∃ ν ∈ secondMomentSlice pbar s, cardSupportLe 3 ν ∧
            (ν : Measure ℝ) ((({0, pbar + r, 1} : Finset ℝ) : Set ℝ)ᶜ) = 0 ∧
            (∫ u, (V1 * (u - pbar) ^ 2 + V3 * (u - pbar) ^ 3 + V4 * (u - pbar) ^ 4)
                ∂(ν : Measure ℝ))
              = V1 * s + V3 * (((1 - pbar) - pbar) * s + (s - pbar * (1 - pbar)) * r)
                  + V4 * ((1 - 3 * (pbar * (1 - pbar))) * s
                      + (s - pbar * (1 - pbar)) * (r ^ 2 + ((1 - pbar) - pbar) * r))) := by sorry

end CausalSmith.Experimentation.SaturationSkew
