/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: validity of the observed cell probabilities

The attainment arguments need two facts about the observed data that are not part
of `cellProb`'s definition: the cells are nonnegative, and for each instrument
value they sum to one. Both are read off the realized latent table.
-/

import Causalean.PO.ID.Partial.BalkePearl.ClosedForm

/-! # Observed cell probabilities form a distribution per instrument value -/

namespace Causalean
namespace PO

open MeasureTheory

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-! ### Validity of the observed cell probabilities -/

/-- Observed cell probabilities are nonnegative. -/
lemma cellProb_nonneg (y d z : Bool) : 0 ≤ S.cellProb y d z :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- For each instrument value the four observed cells sum to one. -/
lemma sum_cellProb_eq_one (hA : S.BaseAssumptions) (z : Bool) :
    ∑ y : Bool, ∑ d : Bool, S.cellProb y d z = 1 := by
  have h : ∀ y d, S.cellProb y d z = _ := fun y d => S.cellProb_eq_sum_latent hA y d z
  have hs := S.latentProb_sum_eq_one
  simp only [Fintype.sum_bool] at hs
  simp only [Fintype.sum_bool, h]
  cases z <;>
    simp only [dArm, yArm, Fintype.sum_bool] <;>
    norm_num <;>
    linarith [hs]

end POBalkePearlSystem

end PO
end Causalean
