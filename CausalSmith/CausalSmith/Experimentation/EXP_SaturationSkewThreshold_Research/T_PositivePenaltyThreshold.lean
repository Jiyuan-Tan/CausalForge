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

-- @node: prop:positive-penalty-threshold
/-- The Dirac law minimizes iff the local quadratic penalty is nonnegative everywhere. -/
theorem positive_penalty_threshold (V0 V1 V3 V4 pbar : ℝ) (hb : BudgetInterior pbar) :
    IsMinimizer V0 V1 V3 V4 pbar (diracLaw pbar) ↔
      ∀ d ∈ centeredSupportDomain pbar, 0 ≤ V1 + V3 * d + V4 * d ^ 2 := by sorry

end CausalSmith.Experimentation.SaturationSkew
