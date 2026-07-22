/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: attainment of the closed-form endpoints

`ClosedForm.lean` proves the closed-form endpoints are *valid* — every feasible
latent table has objective inside `[bpLower, bpUpper]`. This file proves they are
*attained*: some feasible table achieves each endpoint, which upgrades the
containment to an equality and makes the closed form the exact LP optimum. The
capstone is `bpLower_bpUpper_eq_csInf_csSup`.

Do not confuse this with `Sharp.lean`. That file proves a different statement, on
the model side: every feasible latent table is realized by an actual PO model, so
the identified interval is exactly the LP objective range. The present file is
purely about the linear program — that the max of eight affine expressions equals
the LP optimum. Both are needed for the closed form to be a sharp bound on the ATE.

The witnesses here are the primal optima corresponding to the eight dual vertices,
found by complementary slackness. That derivation is offline scaffolding only: no
duality theory enters the proofs, each witness is an explicit table and is checked
directly against the feasibility constraints.
-/

import Causalean.PO.ID.Partial.BalkePearl.Attainment.Lower
import Causalean.PO.ID.Partial.BalkePearl.Attainment.Upper
import Causalean.PO.ID.Partial.BalkePearl.IntervalForm

/-! # Attainment of the Balke-Pearl closed-form endpoints -/

namespace Causalean
namespace PO

open MeasureTheory

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-! ### The lower endpoint is attained -/

/-- **The closed-form lower endpoint is exactly the LP minimum.** -/
theorem csInf_BPIdentifiedInterval_eq_bpLower (hA : S.BaseAssumptions) :
    sInf (S.BPIdentifiedInterval hA) = S.bpLower := by
  refine le_antisymm ?_ ?_
  · exact csInf_le (S.bddBelow_BPIdentifiedInterval hA) (S.bpLower_mem_BPIdentifiedInterval hA)
  · refine le_csInf ⟨_, S.bpLower_mem_BPIdentifiedInterval hA⟩ ?_
    rintro b ⟨x, rfl⟩
    exact S.bpLower_le_BPObjective hA x.2

/-! ### The upper endpoint is attained -/

/-- **The closed-form upper endpoint is exactly the LP maximum.** -/
theorem csSup_BPIdentifiedInterval_eq_bpUpper (hA : S.BaseAssumptions) :
    sSup (S.BPIdentifiedInterval hA) = S.bpUpper := by
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨_, S.bpUpper_mem_BPIdentifiedInterval hA⟩ ?_
    rintro b ⟨x, rfl⟩
    exact S.BPObjective_le_bpUpper hA x.2
  · exact le_csSup (S.bddAbove_BPIdentifiedInterval hA) (S.bpUpper_mem_BPIdentifiedInterval hA)

/-! ### Sharpness of the closed form -/

/-- **The Balke-Pearl closed form is sharp.** The interval `[bpLower, bpUpper]`,
computed from the observed cell probabilities alone, has both endpoints attained
by observationally-equivalent latent tables. So no smaller interval contains
every average treatment effect compatible with the data: the bound cannot be
improved without further assumptions. -/
theorem bpLower_bpUpper_eq_csInf_csSup (hA : S.BaseAssumptions) :
    S.bpLower = sInf (S.BPIdentifiedInterval hA) ∧
      S.bpUpper = sSup (S.BPIdentifiedInterval hA) :=
  ⟨(S.csInf_BPIdentifiedInterval_eq_bpLower hA).symm,
   (S.csSup_BPIdentifiedInterval_eq_bpUpper hA).symm⟩

end POBalkePearlSystem

end PO
end Causalean
