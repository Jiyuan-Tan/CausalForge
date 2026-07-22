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

-- @node: thm:constructive-optimal-design-algorithm
theorem constructive_optimal_design_algorithm (V0 V1 V3 V4 pbar : ℝ)
    (hp0 : 0 ≤ pbar) (hp1 : pbar ≤ 1)
    (hsalg : SemialgebraicOptimizationAlgorithms) :
    ∃ νalg : Law, IsMinimizer V0 V1 V3 V4 pbar νalg ∧ cardSupportLe 3 νalg ∧
      ((pbar = 0 ∨ pbar = 1) → νalg = diracLaw pbar) := by sorry

end CausalSmith.Experimentation.SaturationSkew
