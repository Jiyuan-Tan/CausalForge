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

-- @node: prop:sutva-corner
/-- Under SUTVA the functional is linear in variance with sign-determined minimizers. -/
theorem sutva_corner (V0 V1 pbar : ℝ) (M m : ℕ) :
    (∀ ν : Law, IsAdmissible pbar ν →
        varianceFunctional V0 V1 0 0 pbar ν = V0 + V1 * centeredMoment pbar 2 ν) ∧
      (0 < V1 → BudgetInterior pbar → IsMinimizer V0 V1 0 0 pbar (diracLaw pbar)) ∧
      (V1 < 0 → ∃ νB : Law, IsAdmissible pbar νB ∧
          (νB : Measure ℝ) = ENNReal.ofReal (1 - pbar) • Measure.dirac 0
              + ENNReal.ofReal pbar • Measure.dirac 1 ∧
          IsMinimizer V0 V1 0 0 pbar νB) ∧
      (V1 = 0 → ∀ ν η : Law, IsAdmissible pbar ν → IsAdmissible pbar η →
          varianceFunctional V0 V1 0 0 pbar ν = varianceFunctional V0 V1 0 0 pbar η) ∧
      ((∃ π : Fin M → ℝ, IsImplementable M m pbar π ∧
          (empiricalLaw M π : Measure ℝ)
            = ENNReal.ofReal (1 - pbar) • Measure.dirac 0 + ENNReal.ofReal pbar • Measure.dirac 1)
        ↔ ∃ z : ℤ, (M : ℝ) * pbar = z) ∧
      ((∃ π : Fin M → ℝ, IsImplementable M m pbar π ∧
          (empiricalLaw M π : Measure ℝ) = Measure.dirac pbar)
        ↔ ∃ z : ℤ, (m : ℝ) * pbar = z) := by sorry

end CausalSmith.Experimentation.SaturationSkew
