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

-- @node: prop:skewed-witness
/-- A skewed admissible law strictly beats the Dirac law on the variance functional. -/
theorem skewed_witness :
    ∃ νw : Law, IsAdmissible (1 / 3) νw ∧
      centeredMoment (1 / 3) 2 νw = 2 / 9 ∧
      centeredMoment (1 / 3) 3 νw = 2 / 27 ∧
      centeredMoment (1 / 3) 4 νw - (centeredMoment (1 / 3) 2 νw) ^ 2 = 2 / 81 ∧
      varianceFunctional 0 1 (-10) 1 (1 / 3) νw
          - varianceFunctional 0 1 (-10) 1 (1 / 3) (diracLaw (1 / 3)) = -40 / 81 := by sorry

end CausalSmith.Experimentation.SaturationSkew
