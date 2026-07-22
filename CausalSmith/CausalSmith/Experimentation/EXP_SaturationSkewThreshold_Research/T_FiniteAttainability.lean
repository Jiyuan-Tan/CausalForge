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

-- @node: thm:finite-attainability
/-- Finitely supported target laws are exactly attainable by implementable designs. -/
theorem finite_attainability (M m : ℕ) (pbar : ℝ)
    (hp0 : 0 ≤ pbar) (hp1 : pbar ≤ 1) (hM : 0 < M)
    (hEq : EqualClusterSize M m (M * m)) {K : ℕ} (w u : Fin K → ℝ)
    (hw : ∀ ℓ, 0 ≤ w ℓ) (hsum : ∑ ℓ, w ℓ = 1) (hu : ∀ ℓ, u ℓ ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∑ ℓ, w ℓ * u ℓ = pbar)
    (hMw : ∀ ℓ, ∃ z : ℤ, (M : ℝ) * w ℓ = z) (hmu : ∀ ℓ, ∃ z : ℤ, (m : ℝ) * u ℓ = z) :
    (∃ π : Fin M → ℝ, IsImplementable M m pbar π ∧
        (empiricalLaw M π : Measure ℝ) = ∑ ℓ, ENNReal.ofReal (w ℓ) • Measure.dirac (u ℓ)) ∧
      ((∃ π : Fin M → ℝ, IsImplementable M m pbar π ∧
          (empiricalLaw M π : Measure ℝ)
            = ENNReal.ofReal (1 - pbar) • Measure.dirac 0 + ENNReal.ofReal pbar • Measure.dirac 1)
        ↔ ∃ z : ℤ, (M : ℝ) * pbar = z) ∧
      ((∃ π : Fin M → ℝ, IsImplementable M m pbar π ∧
          (empiricalLaw M π : Measure ℝ) = Measure.dirac pbar)
        ↔ ∃ z : ℤ, (m : ℝ) * pbar = z) := by sorry

end CausalSmith.Experimentation.SaturationSkew
