/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Lee bounds — Step A: control-arm identification of `m₀`

`m0_eq_eventCondExp_Y0_alwaysSelected` collapses the observable
selected-control mean
  `m₀ := E[Y | A = false, Sel = true]`
to the latent always-selected mean of `Y(0)`:
  `m₀ = E[Y(0) | alwaysSelected]`.

The proof chain: consistency on `{A=false, Sel=true}` gives
`factualY = YofA false` and `factualSel = SelOfA false` pointwise; pair
random assignment `A ⫫ (Y(0), Sel(0))` drops the `{A=false}`
conditioning; monotone selection collapses `{Sel(0)=true}` to
`alwaysSelected`.
-/

import Causalean.PO.ID.Partial.Lee.Assumptions
import Causalean.PO.ID.Partial.Lee.PrincipalStrata
import Causalean.PO.ID.Partial.Lee.Trim

/-! # Lee bounds control-arm mean identity

This file proves the Lee-bounds control-arm identification step. Under
consistency, random assignment, and monotone selection, the observable selected
control mean equals the latent mean of `Y(0)` among always-selected units.

The public lemma `m0_eq_eventCondExp_Y0_alwaysSelected` rewrites the observable
selected-control mean `m0` as `eventCondExp P.μ alwaysSelected (YofA false)`.
The proof first uses consistency to replace factual outcomes and selection on
the selected-control cell, then uses pair-level random assignment to drop the
conditioning on treatment assignment, and finally uses monotone selection to
identify control selection with the always-selected stratum.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POLeeSystem

variable {P : POSystem} (S : POLeeSystem P)

/-! ### Step A. Selected-control identification of `m₀`. -/

/-- `m₀ = E[Y(0) | alwaysSelected]`. -/
lemma m0_eq_eventCondExp_Y0_alwaysSelected
    (hA : S.BaseAssumptions) (hMono : S.MonotoneSelection) :
    S.m0 = eventCondExp P.μ S.alwaysSelected (S.YofA false) := by
  have hy_on_selectedControl :
      ∀ ω ∈ S.selectedControl, S.factualY ω = S.YofA false ω := by
    intro ω hω
    have hcf : S.YofA false ω = S.factualY ω :=
      POVar.cf_eq_factual_on_event hA.consistency
        S.yVar S.aVar false S.hAY.symm hω.1
    exact hcf.symm
  have hY :
      eventCondExp P.μ S.selectedControl S.factualY
        = eventCondExp P.μ S.selectedControl (S.YofA false) :=
    eventCondExp_congr_on P.μ S.measurableSet_selectedControl hy_on_selectedControl
  have hSelectedControl :
      S.selectedControl = S.aEvent false ∩ S.selOfAFalseSet := by
    ext ω
    constructor
    · intro hω
      have hsel_cf : S.SelOfA false ω = S.factualSel ω :=
        POVar.cf_eq_factual_on_event hA.consistency
          S.selVar S.aVar false S.hASel.symm hω.1
      exact ⟨hω.1, by simpa [selOfAFalseSet, hsel_cf] using hω.2⟩
    · intro hω
      have hsel_cf : S.SelOfA false ω = S.factualSel ω :=
        POVar.cf_eq_factual_on_event hA.consistency
          S.selVar S.aVar false S.hASel.symm hω.1
      exact ⟨hω.1, by simpa [selOfAFalseSet, hsel_cf] using hω.2⟩
  have hdrop :
      eventCondExp P.μ (S.aEvent false ∩ S.selOfAFalseSet) (S.YofA false)
        = eventCondExp P.μ S.selOfAFalseSet (S.YofA false) := by
    have hpair_meas :
        Measurable (fun ω => (S.YofA false ω, S.SelOfA false ω)) :=
      Measurable.prodMk (S.measurable_YofA false) (S.measurable_SelOfA false)
    have hselSet_pair :
        MeasurableSet {p : ℝ × Bool | p.2 = true} :=
      measurable_snd (measurableSet_singleton true)
    have hφ_meas :
        Measurable (fun p : ℝ × Bool =>
          if p.2 = true then p.1 else (0 : ℝ)) := by
      exact Measurable.ite hselSet_pair measurable_fst measurable_const
    have hφ_indicator :
        (fun ω => if S.SelOfA false ω = true then S.YofA false ω else (0 : ℝ))
          = S.selOfAFalseSet.indicator (S.YofA false) := by
      funext ω
      by_cases hω : S.SelOfA false ω = true
      · simp [selOfAFalseSet, hω]
      · simp [selOfAFalseSet, hω]
    have hraw_num :
        ∫ ω in S.aEvent false,
            S.selOfAFalseSet.indicator (S.YofA false) ω ∂P.μ
          = (P.μ (S.aEvent false)).toReal *
              ∫ ω, S.selOfAFalseSet.indicator (S.YofA false) ω ∂P.μ := by
      have hraw :=
        (hA.randAssign false).integral_restrict_preimage_eq_mul
          S.measurable_factualA hpair_meas
          (measurableSet_singleton false) hφ_meas
      simpa [aEvent, factualA, POVar.event, hφ_indicator] using hraw
    have hnum :
        ∫ ω in S.aEvent false ∩ S.selOfAFalseSet, S.YofA false ω ∂P.μ
          = (P.μ (S.aEvent false)).toReal *
              ∫ ω in S.selOfAFalseSet, S.YofA false ω ∂P.μ := by
      rw [← MeasureTheory.setIntegral_indicator S.measurableSet_selOfAFalseSet,
        ← MeasureTheory.integral_indicator S.measurableSet_selOfAFalseSet]
      exact hraw_num
    have hden_enn :
        P.μ (S.aEvent false ∩ S.selOfAFalseSet)
          = P.μ (S.aEvent false) * P.μ S.selOfAFalseSet := by
      have hraw :=
        (hA.randAssign false).measure_inter_preimage_eq_mul
          {false} {p : ℝ × Bool | p.2 = true}
          (measurableSet_singleton false) hselSet_pair
      simpa [aEvent, factualA, selOfAFalseSet, POVar.event] using hraw
    have hden :
        (P.μ (S.aEvent false ∩ S.selOfAFalseSet)).toReal
          = (P.μ (S.aEvent false)).toReal * (P.μ S.selOfAFalseSet).toReal := by
      rw [hden_enn, ENNReal.toReal_mul]
    have hAfalse_ne_zero : (P.μ (S.aEvent false)).toReal ≠ 0 := by
      rw [ENNReal.toReal_ne_zero]
      exact ⟨hA.posAFalse, measure_ne_top _ _⟩
    unfold eventCondExp
    rw [hnum, hden]
    exact mul_div_mul_left _ _ hAfalse_ne_zero
  have hAS :
      eventCondExp P.μ S.selOfAFalseSet (S.YofA false)
        = eventCondExp P.μ S.alwaysSelected (S.YofA false) := by
    unfold eventCondExp
    have hset := S.selOfAFalseSet_ae_eq_alwaysSelected hMono.monotone
    rw [MeasureTheory.setIntegral_congr_set hset, measure_congr hset]
  unfold m0
  rw [hY, hSelectedControl, hdrop, hAS]

end POLeeSystem

end PO
end Causalean
