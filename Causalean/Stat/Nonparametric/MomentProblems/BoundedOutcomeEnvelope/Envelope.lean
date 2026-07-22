/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.Bounds
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.Attainment

/-!
# Bounded-outcome residual envelope: `IsLUB`

This file assembles the bounded-outcome moment problem. For `v ∈ (0,1)`, the measure-level residual
envelope `ρ(v) = rhoEnvelope v` is the least upper bound of the residual `l2ResidualQuadratic μ`
over all admissible laws `μ` (probability measures on `[0,1]` with second moment `v²`), and it is
*attained* by the extremal three-point law.

* `rho_envelope_isLUB` — `IsLUB (residualSet v) (rhoEnvelope v)`.
* `rho_envelope_attained` — the extremal law realizing `ρ(v)` (re-exported from `Attainment`).
* `interior_quartic_unique_root` — the unique interior root of the FOC quartic (from `QuarticRoot`).

The `IsLUB` combines the upper bound `l2ResidualQuadratic_le_rho` (every admissible residual is
`≤ ρ(v)`) with attainment (`ρ(v)` itself is a realized residual), so any upper bound of the set is
`≥ ρ(v)`.
-/

namespace Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope

open Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge (l2ResidualQuadratic)
open MeasureTheory

/-- **Measure-level sharp envelope (`IsLUB`).** For `v ∈ (0,1)`, `rhoEnvelope v` is the least upper
bound of the set of residuals `l2ResidualQuadratic μ` over admissible laws `μ`.  Equivalently: the
sup over all probability measures on `[0,1]` with `∫ y² ∂μ = v²` of the `L²` residual of `y²` on
`span{1, y}` equals the closed form `ρ(v)`, and is attained (by the extremal three-point law). -/
theorem rho_envelope_isLUB (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    IsLUB (residualSet v) (rhoEnvelope v) := by
  constructor
  · -- `rhoEnvelope v` is an upper bound of the residual set
    rintro r ⟨μ, hμ, rfl⟩
    exact l2ResidualQuadratic_le_rho v μ hμ hv0 hv1
  · -- and it is the least such: any upper bound dominates the attained value
    intro b hb
    obtain ⟨μ, hμ, hres⟩ := rho_envelope_attained v hv0 hv1
    exact hb ⟨μ, hμ, hres.symm⟩

end Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope
