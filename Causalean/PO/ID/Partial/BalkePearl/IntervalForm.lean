/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl bounds: closed-interval (`Set.Icc`) form

`Main.lean` proves necessity as a *set membership* `ATE ∈ BPIdentifiedInterval`,
where `BPIdentifiedInterval = PartialID.IdentifiedInterval BPObjective (BPFeasible …)`
is the abstract range of the LP objective over feasible latent tables. This file
restates necessity in the closed-interval vocabulary of the partial-identification
engine: the true ATE lies between the infimum and supremum of that range,

    ATE ∈ [sInf BPIdentifiedInterval, sSup BPIdentifiedInterval],

i.e. between the Balke-Pearl LP minimum and maximum. The endpoints are the values
an analyst actually reports. The bridge `Causalean.PartialID.mem_Icc_csInf_csSup`
supplies the step once the objective is shown bounded over feasible tables.

The objective is an average of `±1`/`0` contrasts against a probability vector,
so it always lies in `[-1, 1]`; this gives the required `BddBelow`/`BddAbove`.

## Main results

* `neg_one_le_BPObjective`, `BPObjective_le_one` — `BPObjective π ∈ [-1, 1]` for
  every feasible (nonneg, sum-one) table π.
* `bddBelow_BPIdentifiedInterval`, `bddAbove_BPIdentifiedInterval` — the identified
  interval is bounded.
* `ATE_mem_Icc_csInf_csSup` — necessity in closed-interval form.
-/

import Causalean.PO.ID.Partial.BalkePearl.Main
import Causalean.PO.ID.Partial.Basic

/-! # Balke-Pearl bounds in closed-interval form

This file restates the Balke-Pearl latent-table necessity result in the
closed-interval vocabulary used by the partial-identification library. It proves
boundedness of the linear-program objective and derives membership of the true
ATE in the interval between the infimum and supremum of the feasible objective
range.
-/

namespace Causalean
namespace PO

open MeasureTheory

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-! ### Boundedness of the LP objective over feasible tables -/

/-- Per-cell coefficient bound: `boolToReal y1 - boolToReal y0 ∈ [-1, 1]`. -/
private lemma boolToReal_diff_mem_Icc (y0 y1 : Bool) :
    -1 ≤ boolToReal y1 - boolToReal y0 ∧ boolToReal y1 - boolToReal y0 ≤ 1 := by
  cases y0 <;> cases y1 <;> norm_num

/-- **Upper bound on the objective.** For a feasible (nonneg, sum-one) table π,
the LP objective `∑ (y1 - y0) · π` is at most `1`, since every contrast is `≤ 1`
and π is a probability vector. -/
lemma BPObjective_le_one {π : Bool → Bool → Bool → Bool → ℝ}
    (hnn : ∀ d0 d1 y0 y1, 0 ≤ π d0 d1 y0 y1)
    (hsum : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool, π d0 d1 y0 y1 = 1) :
    BPObjective π ≤ 1 := by
  unfold BPObjective
  refine le_of_le_of_eq
    (Finset.sum_le_sum fun d0 _ => Finset.sum_le_sum fun d1 _ =>
      Finset.sum_le_sum fun y0 _ => Finset.sum_le_sum fun y1 _ => ?_) hsum
  exact (mul_le_mul_of_nonneg_right (boolToReal_diff_mem_Icc y0 y1).2
    (hnn d0 d1 y0 y1)).trans_eq (one_mul _)

/-- **Lower bound on the objective.** Symmetrically, `-1 ≤ BPObjective π`. -/
lemma neg_one_le_BPObjective {π : Bool → Bool → Bool → Bool → ℝ}
    (hnn : ∀ d0 d1 y0 y1, 0 ≤ π d0 d1 y0 y1)
    (hsum : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool, π d0 d1 y0 y1 = 1) :
    -1 ≤ BPObjective π := by
  unfold BPObjective
  refine le_of_eq_of_le ?_
    (Finset.sum_le_sum fun d0 _ => Finset.sum_le_sum fun d1 _ =>
      Finset.sum_le_sum fun y0 _ => Finset.sum_le_sum fun y1 _ =>
        (neg_one_mul (π d0 d1 y0 y1)).symm.trans_le
          (mul_le_mul_of_nonneg_right (boolToReal_diff_mem_Icc y0 y1).1 (hnn d0 d1 y0 y1)))
  -- Remaining goal: `-1 = ∑∑∑∑ (-(π …))`.  Pull the negation out and use `hsum`.
  have hneg : (∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool, -(π d0 d1 y0 y1))
      = -(∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool, π d0 d1 y0 y1) := by
    simp only [Finset.sum_neg_distrib]
  rw [hneg, hsum]

/-! ### The identified interval is bounded -/

/-- The Balke-Pearl identified interval is bounded below (by `-1`). -/
lemma bddBelow_BPIdentifiedInterval (hA : S.BaseAssumptions) :
    BddBelow (S.BPIdentifiedInterval hA) := by
  refine ⟨-1, ?_⟩
  rintro _ ⟨⟨π, hπ⟩, rfl⟩
  exact neg_one_le_BPObjective hπ.nonneg hπ.sum_one

/-- The Balke-Pearl identified interval is bounded above (by `1`). -/
lemma bddAbove_BPIdentifiedInterval (hA : S.BaseAssumptions) :
    BddAbove (S.BPIdentifiedInterval hA) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨⟨π, hπ⟩, rfl⟩
  exact BPObjective_le_one hπ.nonneg hπ.sum_one

/-! ### Necessity in closed-interval form -/

/-- **Necessity, closed-interval form.** The true ATE lies between the infimum
and supremum of the Balke-Pearl identified interval — the LP minimum and maximum.
This is `ATE_mem_BPIdentifiedInterval` rephrased through the engine bridge
`Causalean.PartialID.mem_Icc_csInf_csSup`. -/
theorem ATE_mem_Icc_csInf_csSup (hA : S.BaseAssumptions) :
    S.ATE ∈ Set.Icc (sInf (S.BPIdentifiedInterval hA)) (sSup (S.BPIdentifiedInterval hA)) :=
  Causalean.PartialID.mem_Icc_csInf_csSup (S.bddBelow_BPIdentifiedInterval hA)
    (S.bddAbove_BPIdentifiedInterval hA) (S.ATE_mem_BPIdentifiedInterval hA)

end POBalkePearlSystem

end PO
end Causalean
