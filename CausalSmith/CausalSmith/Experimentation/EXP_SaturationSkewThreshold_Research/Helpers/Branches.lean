/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic

namespace CausalSmith.Experimentation.SaturationSkew

open MeasureTheory
open scoped BigOperators

/-- Branch objective `R_k^0(θ,w,d)`. -/
def branchObjective (V1 V3 V4 : ℝ) {k : ℕ} (w d : Fin k → ℝ) : ℝ :=
  V1 * ∑ i, w i * (d i) ^ 2 + V3 * ∑ i, w i * (d i) ^ 3
    + V4 * ((∑ i, w i * (d i) ^ 4) - (∑ i, w i * (d i) ^ 2) ^ 2)

-- @node: def:branch-map-contact-handle
/-- Support-pattern contact system `E_k(θ)`: centered `k`-atom mean-zero configs. -/
def branchContactSystem (pbar : ℝ) (k : ℕ) :
    Set ((Fin k → ℝ) × (Fin k → ℝ)) :=
  {wd | (∀ i, 0 ≤ wd.1 i) ∧ (∑ i, wd.1 i = 1) ∧
    (∀ i, -pbar ≤ wd.2 i ∧ wd.2 i ≤ 1 - pbar) ∧ Monotone wd.2 ∧
    (∑ i, wd.1 i * wd.2 i = 0)}

end CausalSmith.Experimentation.SaturationSkew
