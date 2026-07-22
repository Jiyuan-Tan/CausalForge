/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Manski bounds: MTR-sharpened (prop:po-iv-mtr)

Under consistency, bounded outcomes, and MTR (`Y(0) ≤ Y(1)` a.s.), the
ATE is nonnegative and sharper bounds hold.  No instrument stratification
is used in this file — `Z` does not appear.  The key inputs are:

* consistency on the events `{D = 1}` and `{D = 0}` (via
  `factualY_mul_indD_eq`),
* MTR (`hMTR.monotone`),
* almost-sure outcome bounds (`hA.bounded_one`, `hA.bounded_zero`),
* the total-law decomposition over the binary partition
  `{D = 1} ⊔ {D = 0}` (proved inline as `integral_YofD_eq_bool_decomposition`).

We write
    p := (P.μ (S.dEvent true)).toReal,
so that `1 - p = (P.μ (S.dEvent false)).toReal` (since `P.μ` is a
probability measure) and conditional means are expressed via
`eventCondExp P.μ (S.dEvent d) f`.
-/

import Causalean.PO.ID.Partial.Manski.Helpers

/-! # Manski bounds under monotone treatment response

This file proves the monotone-treatment-response sharpening of Manski bounds.
Consistency, binary-treatment event decompositions, bounded outcomes, and the
almost-sure inequality `Y(0) <= Y(1)` imply a nonnegative ATE and tighter
arm-wise and ATE sandwiches.

The main public conclusions are the arm comparisons `mtr_E_Y_le_E_Y1` and
`mtr_E_Y0_le_E_Y`, the bounded-arm inequalities `mtr_E_Y1_le_upper` and
`mtr_lower_le_E_Y0`, the nonnegativity theorem `mtr_nonneg_ATE`, and the final
two-sided ATE statement `mtr_bounds_ATE`.
-/

namespace Causalean
namespace PO

open MeasureTheory

namespace POManskiIVSystem

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (S : POManskiIVSystem P α)

/-! ### Bool-indexed total-law decomposition over the `D` partition

Specialisations of the generic `integral_eq_sum_measure_mul_eventCondExp`
(and `POVar.eventCondExp_cfUnder_eq_factual_on_event`) to the binary
partition `{D = true} ⊔ {D = false}`. -/

/-- The two treatment events cover `P.Ω`. -/
private lemma iUnion_dEvent : (⋃ d, S.dEvent d) = Set.univ := by
  refine Set.eq_univ_of_forall (fun ω => ?_)
  refine Set.mem_iUnion.mpr ⟨S.factualD ω, ?_⟩
  rfl

/-- The two treatment events are pairwise disjoint. -/
private lemma pairwise_disjoint_dEvent :
    Pairwise (Function.onFun Disjoint S.dEvent) := by
  rintro d₁ d₂ hne
  refine Set.disjoint_left.mpr (fun ω hω₁ hω₂ => ?_)
  have h₁ : S.factualD ω = d₁ := hω₁
  have h₂ : S.factualD ω = d₂ := hω₂
  exact hne (h₁.symm.trans h₂)

/-- Total-law decomposition: for an integrable `f`,
`∫ f = p·E[f|D=1] + (1-p)·E[f|D=0]`, via the generic Fintype total law. -/
private lemma integral_eq_sum_eventCondExp_dEvent
    (f : P.Ω → ℝ) (hf : Integrable f P.μ) :
    ∫ ω, f ω ∂P.μ
      = eventCondExp P.μ (S.dEvent true) f * (P.μ (S.dEvent true)).toReal
        + eventCondExp P.μ (S.dEvent false) f * (P.μ (S.dEvent false)).toReal := by
  have h := integral_eq_sum_measure_mul_eventCondExp (μ := P.μ)
    (A := S.dEvent) S.measurableSet_dEvent S.pairwise_disjoint_dEvent
    S.iUnion_dEvent f hf
  simpa [Fintype.sum_bool, mul_comm] using h

/-- Consistency on `{D = d}`: `E[Y(d) | D = d] = E[Y | D = d]`. -/
private lemma eventCondExp_YofD_eq_factualY_on_dEvent
    (hA : S.BaseAssumptions) (d : Bool) :
    eventCondExp P.μ (S.dEvent d) (S.YofD d)
      = eventCondExp P.μ (S.dEvent d) S.factualY :=
  POVar.eventCondExp_cfUnder_eq_factual_on_event hA.consistency
    S.yVar S.dVar d (Ne.symm S.hDY) P.μ

/-! ### Core pointwise a.s. inequalities -/

/-- Under consistency + MTR, `Y ≤ Y(1)` almost surely. -/
private lemma factualY_le_YofD_true
    (hA : S.BaseAssumptions) (hMTR : S.MTR) :
    S.factualY ≤ᵐ[P.μ] S.YofD true := by
  -- Pointwise: on `{D = 1}`, `Y = Y(1) ≤ Y(1)`; on `{D = 0}`, `Y = Y(0) ≤ Y(1)`
  -- (the latter from MTR).  We express this using `cf_eq_factual_on_event` +
  -- `hMTR.monotone`.
  have hvw : S.yVar.v ≠ S.dVar.v := Ne.symm S.hDY
  refine hMTR.monotone.mono (fun ω hmono => ?_)
  cases hD : S.factualD ω
  · -- D = false: Y = Y(0) ≤ Y(1).
    have hω : ω ∈ S.dEvent false := hD
    have hY0 : S.YofD false ω = S.factualY ω := by
      simpa [POManskiIVSystem.YofD, POManskiIVSystem.factualY] using
        POVar.cf_eq_factual_on_event hA.consistency S.yVar S.dVar false hvw hω
    linarith [hY0 ▸ hmono]
  · -- D = true: Y = Y(1), done.
    have hω : ω ∈ S.dEvent true := hD
    have hY1 : S.YofD true ω = S.factualY ω := by
      simpa [POManskiIVSystem.YofD, POManskiIVSystem.factualY] using
        POVar.cf_eq_factual_on_event hA.consistency S.yVar S.dVar true hvw hω
    linarith

/-- Under consistency + MTR, `Y(0) ≤ Y` almost surely. -/
private lemma YofD_false_le_factualY
    (hA : S.BaseAssumptions) (hMTR : S.MTR) :
    S.YofD false ≤ᵐ[P.μ] S.factualY := by
  have hvw : S.yVar.v ≠ S.dVar.v := Ne.symm S.hDY
  refine hMTR.monotone.mono (fun ω hmono => ?_)
  cases hD : S.factualD ω
  · -- D = false: Y(0) = Y.
    have hω : ω ∈ S.dEvent false := hD
    have hY0 : S.YofD false ω = S.factualY ω := by
      simpa [POManskiIVSystem.YofD, POManskiIVSystem.factualY] using
        POVar.cf_eq_factual_on_event hA.consistency S.yVar S.dVar false hvw hω
    linarith
  · -- D = true: Y(0) ≤ Y(1) = Y.
    have hω : ω ∈ S.dEvent true := hD
    have hY1 : S.YofD true ω = S.factualY ω := by
      simpa [POManskiIVSystem.YofD, POManskiIVSystem.factualY] using
        POVar.cf_eq_factual_on_event hA.consistency S.yVar S.dVar true hvw hω
    linarith [hY1 ▸ hmono]

/-! ### Main MTR bounds -/

/-- Step 1 of prop:po-iv-mtr: `E[Y] ≤ E[Y(1)]`. -/
theorem mtr_E_Y_le_E_Y1 (hA : S.BaseAssumptions) (hMTR : S.MTR) :
    ∫ ω, S.factualY ω ∂P.μ ≤ ∫ ω, S.YofD true ω ∂P.μ :=
  integral_mono_ae hA.integrable_factualY hA.integrable_Y1
    (S.factualY_le_YofD_true hA hMTR)

/-- Step 4 of prop:po-iv-mtr: `E[Y(0)] ≤ E[Y]`. -/
theorem mtr_E_Y0_le_E_Y (hA : S.BaseAssumptions) (hMTR : S.MTR) :
    ∫ ω, S.YofD false ω ∂P.μ ≤ ∫ ω, S.factualY ω ∂P.μ :=
  integral_mono_ae hA.integrable_Y0 hA.integrable_factualY
    (S.YofD_false_le_factualY hA hMTR)

/-- Step 2 of prop:po-iv-mtr:
`E[Y(1)] ≤ p·E[Y|D=1] + (1-p)·b`. -/
theorem mtr_E_Y1_le_upper (hA : S.BaseAssumptions) :
    ∫ ω, S.YofD true ω ∂P.μ
      ≤ (P.μ (S.dEvent true)).toReal
          * eventCondExp P.μ (S.dEvent true) S.factualY
        + (P.μ (S.dEvent false)).toReal * hA.hi := by
  -- Decompose: E[Y(1)] = p·E[Y(1)|D=1] + (1-p)·E[Y(1)|D=0].
  have hdecomp := S.integral_eq_sum_eventCondExp_dEvent (S.YofD true) hA.integrable_Y1
  -- Rewrite both summands as set integrals.
  have h1 := eventCondExp_mul_measure_toReal P.μ (S.dEvent true) (S.YofD true)
  have h0 := eventCondExp_mul_measure_toReal P.μ (S.dEvent false) (S.YofD true)
  rw [h1, h0] at hdecomp
  -- First set integral: use consistency to swap Y(1) ↔ Y on {D=1}.
  have hset_true : ∫ ω in S.dEvent true, S.YofD true ω ∂P.μ
                 = ∫ ω in S.dEvent true, S.factualY ω ∂P.μ := by
    refine setIntegral_congr_fun (S.measurableSet_dEvent true) ?_
    intro ω hω
    have hvw : S.yVar.v ≠ S.dVar.v := Ne.symm S.hDY
    have := POVar.cf_eq_factual_on_event hA.consistency S.yVar S.dVar true hvw hω
    simpa [POManskiIVSystem.YofD, POManskiIVSystem.factualY] using this
  -- Rewrite the first summand as p · E[Y|D=1].
  have hfirst : ∫ ω in S.dEvent true, S.YofD true ω ∂P.μ
              = (P.μ (S.dEvent true)).toReal
                  * eventCondExp P.μ (S.dEvent true) S.factualY := by
    rw [hset_true, ← eventCondExp_mul_measure_toReal P.μ (S.dEvent true) S.factualY, mul_comm]
  -- Bound the second summand: ∫_{D=0} Y(1) ≤ hi · (μ(D=0)).toReal.
  have hbd_ae : S.YofD true ≤ᵐ[P.μ] (fun _ => hA.hi) :=
    hA.bounded_one.mono (fun _ h => h.2)
  have hsecond_le :
      ∫ ω in S.dEvent false, S.YofD true ω ∂P.μ
        ≤ (P.μ (S.dEvent false)).toReal * hA.hi := by
    have hconst_int :
        ∫ _ω in S.dEvent false, hA.hi ∂P.μ
          = (P.μ (S.dEvent false)).toReal * hA.hi := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
          smul_eq_mul, mul_comm]
    calc ∫ ω in S.dEvent false, S.YofD true ω ∂P.μ
        ≤ ∫ _ω in S.dEvent false, hA.hi ∂P.μ := by
          exact setIntegral_mono_ae hA.integrable_Y1.integrableOn
            (integrable_const hA.hi).integrableOn hbd_ae
      _ = (P.μ (S.dEvent false)).toReal * hA.hi := hconst_int
  -- Combine.
  rw [hdecomp, hfirst]
  linarith [hsecond_le]

/-- Step 3 of prop:po-iv-mtr:
`(1-p)·E[Y|D=0] + p·a ≤ E[Y(0)]`. -/
theorem mtr_lower_le_E_Y0 (hA : S.BaseAssumptions) :
    (P.μ (S.dEvent false)).toReal
        * eventCondExp P.μ (S.dEvent false) S.factualY
      + (P.μ (S.dEvent true)).toReal * hA.lo
    ≤ ∫ ω, S.YofD false ω ∂P.μ := by
  -- Decompose: E[Y(0)] = p·E[Y(0)|D=1] + (1-p)·E[Y(0)|D=0].
  have hdecomp := S.integral_eq_sum_eventCondExp_dEvent (S.YofD false) hA.integrable_Y0
  have h1 := eventCondExp_mul_measure_toReal P.μ (S.dEvent true) (S.YofD false)
  have h0 := eventCondExp_mul_measure_toReal P.μ (S.dEvent false) (S.YofD false)
  rw [h1, h0] at hdecomp
  -- On {D = 0}: consistency gives ∫_{D=0} Y(0) = ∫_{D=0} Y.
  have hset_false : ∫ ω in S.dEvent false, S.YofD false ω ∂P.μ
                  = ∫ ω in S.dEvent false, S.factualY ω ∂P.μ := by
    refine setIntegral_congr_fun (S.measurableSet_dEvent false) ?_
    intro ω hω
    have hvw : S.yVar.v ≠ S.dVar.v := Ne.symm S.hDY
    have := POVar.cf_eq_factual_on_event hA.consistency S.yVar S.dVar false hvw hω
    simpa [POManskiIVSystem.YofD, POManskiIVSystem.factualY] using this
  have hsecond : ∫ ω in S.dEvent false, S.YofD false ω ∂P.μ
               = (P.μ (S.dEvent false)).toReal
                   * eventCondExp P.μ (S.dEvent false) S.factualY := by
    rw [hset_false, ← eventCondExp_mul_measure_toReal P.μ (S.dEvent false) S.factualY, mul_comm]
  -- Bound the first summand below: lo · (μ(D=1)).toReal ≤ ∫_{D=1} Y(0).
  have hbd_ae : (fun _ : P.Ω => hA.lo) ≤ᵐ[P.μ] S.YofD false :=
    hA.bounded_zero.mono (fun _ h => h.1)
  have hfirst_ge :
      (P.μ (S.dEvent true)).toReal * hA.lo
        ≤ ∫ ω in S.dEvent true, S.YofD false ω ∂P.μ := by
    have hconst_int :
        ∫ _ω in S.dEvent true, hA.lo ∂P.μ
          = (P.μ (S.dEvent true)).toReal * hA.lo := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
          smul_eq_mul, mul_comm]
    calc (P.μ (S.dEvent true)).toReal * hA.lo
        = ∫ _ω in S.dEvent true, hA.lo ∂P.μ := hconst_int.symm
      _ ≤ ∫ ω in S.dEvent true, S.YofD false ω ∂P.μ := by
          exact setIntegral_mono_ae (integrable_const hA.lo).integrableOn
            hA.integrable_Y0.integrableOn hbd_ae
  rw [hdecomp, hsecond]
  linarith [hfirst_ge]

/-- Step 5 (ATE nonnegativity) of prop:po-iv-mtr: `0 ≤ ATE`. -/
theorem mtr_nonneg_ATE (hA : S.BaseAssumptions) (hMTR : S.MTR) : 0 ≤ S.ATE := by
  have hdiff : (0 : P.Ω → ℝ) ≤ᵐ[P.μ] (fun ω => S.YofD true ω - S.YofD false ω) := by
    refine hMTR.monotone.mono (fun ω h => ?_)
    simpa using sub_nonneg.mpr h
  have hint : Integrable (fun ω => S.YofD true ω - S.YofD false ω) P.μ :=
    hA.integrable_Y1.sub hA.integrable_Y0
  have h := integral_mono_ae (integrable_const 0) hint hdiff
  simpa [ATE, integral_zero] using h

/-- The two-sided ATE sandwich from prop:po-iv-mtr. -/
theorem mtr_bounds_ATE (hA : S.BaseAssumptions) (hMTR : S.MTR) :
    0 ≤ S.ATE ∧
    S.ATE ≤ ((P.μ (S.dEvent true)).toReal
                * eventCondExp P.μ (S.dEvent true) S.factualY
              + (P.μ (S.dEvent false)).toReal * hA.hi)
           - ((P.μ (S.dEvent false)).toReal
                * eventCondExp P.μ (S.dEvent false) S.factualY
              + (P.μ (S.dEvent true)).toReal * hA.lo) := by
  refine ⟨S.mtr_nonneg_ATE hA hMTR, ?_⟩
  -- ATE = E[Y(1)] - E[Y(0)].
  have hATE_eq :
      S.ATE = ∫ ω, S.YofD true ω ∂P.μ - ∫ ω, S.YofD false ω ∂P.μ := by
    unfold ATE
    exact integral_sub hA.integrable_Y1 hA.integrable_Y0
  have hU := S.mtr_E_Y1_le_upper hA
  have hL := S.mtr_lower_le_E_Y0 hA
  rw [hATE_eq]; linarith

end POManskiIVSystem

end PO
end Causalean
