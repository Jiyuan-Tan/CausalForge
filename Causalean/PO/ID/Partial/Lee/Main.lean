/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Partial.Lee.ControlMean
import Causalean.PO.ID.Partial.Lee.TrimBound

/-! # Lee Bounds

This file proves the final Lee bound for the average treatment effect among
always-selected units. Under the Lee sample-selection assumptions, it combines
the selected-control mean identity with the treated trimmed-mean bounds to
sandwich the always-selected treatment effect.

The public theorem `lee_bounds_ATT_AS` states the finite-support Lee sandwich:
`lowerTrimMean 𝒴 - m0` is a lower bound and `upperTrimMean 𝒴 - m0` is an
upper bound for the conditional mean of `Y(1) - Y(0)` on `alwaysSelected`. The
proof assembles the control mean identity, selected-treated decomposition,
latent finite-support transfer, and trim-weight sandwich developed in the
preceding Lee modules. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POLeeSystem

variable {P : POSystem} (S : POLeeSystem P)

/-- **Finite-support Lee bounds** -- prop:po-lee-bounds. Under [the baseline Lee sample-selection
assumptions](hyp:hA), [monotone sample selection](hyp:hMono), and [almost-sure finite support
`𝒴` for the factual outcome on the selected-treated cell](hyp:hSupp), [the average treatment
effect among always-selected units — those who would be selected for observation whether treated
or not — is sandwiched between the lower Lee trimmed mean minus the observable selected-control
mean `m₀`, and the upper Lee trimmed mean minus `m₀`](goal). -/
theorem lee_bounds_ATT_AS [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMono : S.MonotoneSelection)
    (𝒴 : Finset ℝ)
    (hSupp : ∀ᵐ ω ∂(P.μ.restrict S.selectedTreated), S.factualY ω ∈ 𝒴) :
    S.lowerTrimMean 𝒴 - S.m0
      ≤ eventCondExp P.μ S.alwaysSelected
          (fun ω => S.YofA true ω - S.YofA false ω)
    ∧ eventCondExp P.μ S.alwaysSelected
          (fun ω => S.YofA true ω - S.YofA false ω)
      ≤ S.upperTrimMean 𝒴 - S.m0 := by
  have hStepA := S.m0_eq_eventCondExp_Y0_alwaysSelected hA hMono
  have hStepC := S.trimmed_bounds_condExp_Y1_AS hA hMono 𝒴 hSupp
  have hSub :
      eventCondExp P.μ S.alwaysSelected
          (fun ω => S.YofA true ω - S.YofA false ω)
        = eventCondExp P.μ S.alwaysSelected (S.YofA true)
          - eventCondExp P.μ S.alwaysSelected (S.YofA false) := by
    exact
      (eventCondExp_sub P.μ S.alwaysSelected
        (g₁ := S.YofA true) (g₂ := S.YofA false)
        hA.integrableY1.integrableOn hA.integrableY0.integrableOn)
  constructor
  · rw [hSub, hStepA]
    exact sub_le_sub_right hStepC.1 _
  · rw [hSub, hStepA]
    exact sub_le_sub_right hStepC.2 _

end POLeeSystem

end PO
end Causalean
