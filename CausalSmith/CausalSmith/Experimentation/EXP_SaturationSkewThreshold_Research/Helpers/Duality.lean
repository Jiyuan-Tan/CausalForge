/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Measure.Support

namespace CausalSmith.Experimentation.SaturationSkew
open MeasureTheory
open scoped BigOperators

-- @node: lem:bounded-moment-slice-duality
/-- Optimality on a second-moment slice is equivalent to a dual residual certificate. -/
lemma bounded_moment_slice_duality (V1 V3 V4 pbar s : ℝ)
    (hne : (secondMomentSlice pbar s).Nonempty) (νs : Law)
    (hνs : νs ∈ secondMomentSlice pbar s) :
    (∀ η ∈ secondMomentSlice pbar s,
        (∫ u, (V1 * (u - pbar) ^ 2 + V3 * (u - pbar) ^ 3 + V4 * (u - pbar) ^ 4)
            ∂(νs : Measure ℝ))
          ≤ (∫ u, (V1 * (u - pbar) ^ 2 + V3 * (u - pbar) ^ 3 + V4 * (u - pbar) ^ 4)
            ∂(η : Measure ℝ))) ↔
      ∃ a b c : ℝ,
        (∀ d ∈ centeredSupportDomain pbar, 0 ≤ quarticDualResidual V1 V3 V4 a b c d) ∧
        (∀ u ∈ (νs : Measure ℝ).support,
          quarticDualResidual V1 V3 V4 a b c (u - pbar) = 0) := by sorry

end CausalSmith.Experimentation.SaturationSkew
