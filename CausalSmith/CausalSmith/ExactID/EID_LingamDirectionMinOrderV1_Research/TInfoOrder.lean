/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Improved real information order

The resolved information-order theorem: for `m ≥ 3`, the complete truncation
through order `2m+1` already generically separates the two arrows.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.LowerOrderApolarSeparation

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

-- @node: thm:improved-real-information-order
/-- **Improved real information order.**  For every `m ≥ 3`, generic real
opposite-arrow separation already holds at order `2m+1`.  Hence
`K^star(m) ≤ 2m+1`, and in particular it is not equal to `2m+2`. -/
theorem improvedRealInformationOrder (m : ℕ) (hm : 3 ≤ m) :
    separatesAtOrder m (2 * m + 1) ∧
    informationOrder m ≤ ((2 * m + 1 : ℕ) : ℕ∞) ∧
    informationOrder m ≠ ((2 * m + 2 : ℕ) : ℕ∞) := by
  have hsep : separatesAtOrder m (2 * m + 1) := by
    exact lowerOrderApolarSeparation m hm
  refine ⟨hsep, ?_, ?_⟩
  · apply sInf_le
    exact ⟨2 * m + 1, rfl, by omega, hsep⟩
  · intro heq
    have hle : informationOrder m ≤ ((2 * m + 1 : ℕ) : ℕ∞) := by
      apply sInf_le
      exact ⟨2 * m + 1, rfl, by omega, hsep⟩
    rw [heq] at hle
    have := ENat.coe_le_coe.mp hle
    omega

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
