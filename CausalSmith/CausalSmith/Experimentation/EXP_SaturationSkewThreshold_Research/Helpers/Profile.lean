/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic

namespace CausalSmith.Experimentation.SaturationSkew

open MeasureTheory
open scoped BigOperators

-- @node: lem:profile-value-reduction
/-- Profile-value reduction: the outer certificate equals the slice infimum of the
variance functional, which decomposes into the centered quartic integrand plus the
second-moment correction. -/
lemma profile_value_reduction (V0 V1 V3 V4 pbar : ℝ) (hb : BudgetInterior pbar) :
    (∀ s : ℝ, (secondMomentSlice pbar s).Nonempty →
        outerCertificate V0 V1 V3 V4 pbar s
          = ⨅ ν : secondMomentSlice pbar s, varianceFunctional V0 V1 V3 V4 pbar (ν : Law)) ∧
      (∀ s : ℝ, ∀ ν ∈ secondMomentSlice pbar s,
        varianceFunctional V0 V1 V3 V4 pbar ν
          = V0 + (∫ u, (V1 * (u - pbar) ^ 2 + V3 * (u - pbar) ^ 3 + V4 * (u - pbar) ^ 4)
              ∂(ν : Measure ℝ)) - V4 * s ^ 2) := by sorry

end CausalSmith.Experimentation.SaturationSkew
