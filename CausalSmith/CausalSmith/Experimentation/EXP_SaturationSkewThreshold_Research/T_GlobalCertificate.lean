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

-- @node: thm:global-certificate
/-- Global optimality certificate for the variance functional minimizer. -/
theorem global_certificate (V0 V1 V3 V4 pbar : ℝ) (hb : BudgetInterior pbar)
    (νstar : Law) (hν : IsAdmissible pbar νstar) :
    IsMinimizer V0 V1 V3 V4 pbar νstar ↔
      ∃ a b c : ℝ,
        (∀ d ∈ centeredSupportDomain pbar, 0 ≤ quarticDualResidual V1 V3 V4 a b c d) ∧
        (∀ u ∈ (νstar : Measure ℝ).support,
          quarticDualResidual V1 V3 V4 a b c (u - pbar) = 0) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) (pbar * (1 - pbar)),
          varianceFunctional V0 V1 V3 V4 pbar νstar
            ≤ outerCertificate V0 V1 V3 V4 pbar s) ∧
        outerCertificate V0 V1 V3 V4 pbar (centeredMoment pbar 2 νstar)
          = varianceFunctional V0 V1 V3 V4 pbar νstar := by sorry

end CausalSmith.Experimentation.SaturationSkew
