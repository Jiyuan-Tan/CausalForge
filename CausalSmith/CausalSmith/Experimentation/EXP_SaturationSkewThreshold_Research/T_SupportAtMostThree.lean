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

-- @node: prop:support-at-most-three
/-- An optimal law exists supported on at most three points, collapsing at corners. -/
theorem support_at_most_three (V0 V1 V3 V4 pbar : ℝ)
    (hext : ExtremeMomentSliceSupport) :
    ∃ νstar : Law, IsMinimizer V0 V1 V3 V4 pbar νstar ∧ cardSupportLe 3 νstar ∧
      ((pbar = 0 ∨ pbar = 1) → νstar = diracLaw pbar) := by sorry

end CausalSmith.Experimentation.SaturationSkew
