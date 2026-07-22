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

-- @node: thm:rounding-loss
theorem rounding_loss (V0 V1 V3 V4 pbar : ℝ) (hp0 : 0 ≤ pbar) (hp1 : pbar ≤ 1)
    (M m : ℕ) (hM : 0 < M) (hm : 0 < m)
    (νstar : Law) (hν : IsAdmissible pbar νstar) (h3 : cardSupportLe 3 νstar)
    (hNp : ∃ z : ℤ, ((M * m : ℕ) : ℝ) * pbar = z) :
    ∃ (πrd : Fin M → ℝ) (Crd : ℝ), IsImplementable M m pbar πrd ∧
      varianceFunctional V0 V1 V3 V4 pbar (empiricalLaw M πrd)
        ≤ varianceFunctional V0 V1 V3 V4 pbar νstar
            + Crd * ((M : ℝ)⁻¹ + (m : ℝ)⁻¹) := by sorry

end CausalSmith.Experimentation.SaturationSkew
