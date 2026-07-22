/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: main theorem

This file assembles the necessity result for Balke-Pearl ATE bounds:
the true ATE always lies in the LP-identified interval.

## Main results

* `BPFeasible`                  — predicate: latent table π is nonneg, sums to 1,
                                   and reproduces observed cell probabilities.
* `BPObjective`                 — LP objective: ∑ (y1-y0) * π.
* `BPIdentifiedInterval`        — the sharp identified interval (range of BPObjective
                                   over all feasible tables).
* `latentProb_feasible`         — the realized latent table is feasible.
* `ATE_eq_BPObjective`          — ATE = BPObjective applied to the realized table.
* `ATE_mem_BPIdentifiedInterval` — NECESSITY: true ATE ∈ identified interval.

The sharpness counterpart `balkePearl_sharp` is proved in `Sharp.lean`.
-/

import Causalean.PO.ID.Partial.BalkePearl.LatentTable
import Causalean.PO.ID.Partial.Basic

/-! # Balke-Pearl latent-table necessity theorem

This file assembles the finite latent-type linear program for Balke-Pearl IV
bounds. It defines feasibility, the ATE objective, the identified objective
range, proves that the realized latent table is feasible, and shows that the
true ATE belongs to that range.
-/

namespace Causalean
namespace PO

open MeasureTheory

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-! ### Feasibility predicate -/

/-- A latent type table π is feasible for system S under assumptions hA if it is
nonneg, sums to 1, and reproduces the observed cell probabilities. -/
structure BPFeasible (S : POBalkePearlSystem P) (hA : S.BaseAssumptions)
    (π : Bool → Bool → Bool → Bool → ℝ) : Prop where
  nonneg   : ∀ d0 d1 y0 y1, 0 ≤ π d0 d1 y0 y1
  sum_one  : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
               π d0 d1 y0 y1 = 1
  marginal : ∀ (y d z : Bool),
               S.cellProb y d z
                 = ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
                     (if dArm z d0 d1 = d ∧ yArm d y0 y1 = y then 1 else 0)
                       * π d0 d1 y0 y1

/-! ### LP objective -/

/-- The LP objective: ∑ (y1-y0) * π = ATE in the latent model. -/
noncomputable def BPObjective (π : Bool → Bool → Bool → Bool → ℝ) : ℝ :=
  ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
    (boolToReal y1 - boolToReal y0) * π d0 d1 y0 y1

/-! ### Identified interval -/

/-- The Balke-Pearl sharp identified interval for ATE. -/
noncomputable def BPIdentifiedInterval (S : POBalkePearlSystem P) (hA : S.BaseAssumptions) :
    Set ℝ :=
  PartialID.IdentifiedInterval BPObjective (BPFeasible S hA)

/-! ### The realized latent table is feasible -/

/-- The actual latent type distribution latentProb is feasible. -/
theorem latentProb_feasible (hA : S.BaseAssumptions) :
    BPFeasible S hA S.latentProb where
  nonneg   := fun d0 d1 y0 y1 => S.latentProb_nonneg d0 d1 y0 y1
  sum_one  := S.latentProb_sum_eq_one
  marginal := fun y d z => S.cellProb_eq_sum_latent hA y d z

/-! ### ATE equals LP objective at the realized table -/

/-- ATE = BPObjective applied to the realized latent table. -/
theorem ATE_eq_BPObjective (_hA : S.BaseAssumptions) :
    S.ATE = BPObjective S.latentProb := by
  unfold BPObjective
  exact S.ATE_eq_sum_latent

/-! ### Necessity -/

/-- NECESSITY: The true ATE lies in the Balke-Pearl identified interval.

Every observationally-consistent model produces a feasible latent table
(latentProb) with objective equal to ATE, so ATE is attainable. -/
theorem ATE_mem_BPIdentifiedInterval (hA : S.BaseAssumptions) :
    S.ATE ∈ S.BPIdentifiedInterval hA := by
  unfold BPIdentifiedInterval
  rw [S.ATE_eq_BPObjective hA]  -- hA used here for type-checking only
  exact PartialID.mem_identifiedInterval (S.latentProb_feasible hA)

/-! ### Sharpness — see `Sharp.lean` for the proof.

The sharpness theorem `balkePearl_sharp` is stated and proved in
`Causalean/PO/ID/Partial/BalkePearl/Sharp.lean`, which constructs a
canonical PO model realising any feasible latent table. -/

end POBalkePearlSystem

end PO
end Causalean
