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

-- @node: prop:explicit-two-point-cell
theorem explicit_two_point_cell (V0 V1 V3 V4 pbar : ℝ) (hb : BudgetInterior pbar) :
    IsLeast
      {v : ℝ | ∃ ν : Law, IsAdmissible pbar ν ∧ cardSupportLe 2 ν ∧
        v = varianceFunctional V0 V1 V3 V4 pbar ν - V0}
      (min 0 (min (⨅ t ∈ Set.Icc (-pbar) ((1 - pbar) - pbar),
                    pbar * (pbar + t) * (V1 + V3 * t + V4 * t ^ 2))
                  (⨅ t ∈ Set.Icc ((1 - pbar) - pbar) (1 - pbar),
                    (1 - pbar) * ((1 - pbar) - t) * (V1 + V3 * t + V4 * t ^ 2)))) := by sorry

end CausalSmith.Experimentation.SaturationSkew
