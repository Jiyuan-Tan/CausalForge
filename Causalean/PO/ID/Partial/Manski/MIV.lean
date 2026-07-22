/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Manski bounds under Monotone Instrumental Variable (MIV)

Proves prop:po-iv-miv: envelope bounds on the conditional arm means

    mLower_d z ≤ E[Y(d) | Z=z] ≤ mUpper_d z

where

    mLower_d z := sSup { L_{d,u} | u ∈ supp Z, u ≤ z }
    mUpper_d z := sInf { U_{d,u} | u ∈ supp Z, z ≤ u }

and `L_{d,·}, U_{d,·}` are the Manski stratum bound functionals from
`Setup.lean`.  The proof chains the stratum-level conditional bounds from
`Helpers.lean` with the MIV monotonicity of `u ↦ E[Y(d) | Z=u]`.

The integrated forms `E[mLower_d(Z)] ≤ E[Y(d)] ≤ E[mUpper_d(Z)]` yield the
corresponding ATE bounds by applying the arm-wise envelope inequalities.
-/

import Causalean.PO.ID.Partial.Manski.Helpers

/-! # Manski bounds under monotone instrumental variables

This file proves envelope bounds for treatment-arm conditional means under the
monotone instrumental variable assumption. The stratum-level Manski bounds are
combined with monotonicity in the instrument and then integrated to obtain the
corresponding ATE bounds.

It defines the lower and upper monotone-instrument envelopes `mLower1`,
`mUpper1`, `mLower0`, and `mUpper0`, proves their conditional and integrated
arm-wise bounds, and concludes with `miv_bounds_ATE`.
-/

set_option linter.unusedFintypeInType false

namespace Causalean
namespace PO

open MeasureTheory

namespace POManskiIVSystem

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (S : POManskiIVSystem P α)

/-! ### Envelope functions

The four envelopes are parameterized by the outcome bounds `lo, hi` and
take a linear order on `α` as an explicit instance argument; downstream
callers supply it via `letI := hMIV.inst`. -/

/-- Lower envelope for arm `d = 1`:
    `sSup { L_{1,u} | u ∈ supp, u ≤ z }`. -/
noncomputable def mLower1 (hA : S.BaseAssumptions) [LinearOrder α] (z : α) : ℝ :=
  sSup {val : ℝ | ∃ u ∈ S.support, u ≤ z ∧ val = S.lowerBound1 hA.lo u}

/-- Upper envelope for arm `d = 1`:
    `sInf { U_{1,u} | u ∈ supp, z ≤ u }`. -/
noncomputable def mUpper1 (hA : S.BaseAssumptions) [LinearOrder α] (z : α) : ℝ :=
  sInf {val : ℝ | ∃ u ∈ S.support, z ≤ u ∧ val = S.upperBound1 hA.hi u}

/-- Lower envelope for arm `d = 0`:
    `sSup { L_{0,u} | u ∈ supp, u ≤ z }`. -/
noncomputable def mLower0 (hA : S.BaseAssumptions) [LinearOrder α] (z : α) : ℝ :=
  sSup {val : ℝ | ∃ u ∈ S.support, u ≤ z ∧ val = S.lowerBound0 hA.lo u}

/-- Upper envelope for arm `d = 0`:
    `sInf { U_{0,u} | u ∈ supp, z ≤ u }`. -/
noncomputable def mUpper0 (hA : S.BaseAssumptions) [LinearOrder α] (z : α) : ℝ :=
  sInf {val : ℝ | ∃ u ∈ S.support, z ≤ u ∧ val = S.upperBound0 hA.hi u}

/-! ### Conditional envelope bounds (prop:po-iv-miv, conditional part) -/

/-- `mLower1 z ≤ E[Y(1) | Z = z]` for every `z ∈ supp Z`.

Proof: for every `u ∈ supp Z` with `u ≤ z`,
    `L_{1,u} ≤ E[Y(1) | Z=u] ≤ E[Y(1) | Z=z]`
by the stratum bound from `Helpers.lean` chained with MIV monotonicity.
Taking `sSup` over `u` gives the claim via `csSup_le`. -/
theorem miv_mLower1_le_cond_Y1 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMIV : S.MIV) {z : α} (hz : z ∈ S.support) :
    letI := hMIV.inst
    S.mLower1 hA z ≤ eventCondExp P.μ (S.zEvent z) (S.YofD true) := by
  letI := hMIV.inst
  -- The set whose sSup we take.
  set T : Set ℝ :=
    {val : ℝ | ∃ u ∈ S.support, u ≤ z ∧ val = S.lowerBound1 hA.lo u} with hT
  -- Every element of `T` is ≤ the target.
  have hle_all : ∀ v ∈ T, v ≤ eventCondExp P.μ (S.zEvent z) (S.YofD true) := by
    rintro v ⟨u, hu, hule, rfl⟩
    have h1 : S.lowerBound1 hA.lo u ≤
        eventCondExp P.μ (S.zEvent u) (S.YofD true) :=
      S.lowerBound1_le_cond_Y1 hA hu
    have h2 : eventCondExp P.μ (S.zEvent u) (S.YofD true) ≤
        eventCondExp P.μ (S.zEvent z) (S.YofD true) :=
      hMIV.monotone true u z hu hz hule
    exact le_trans h1 h2
  -- Nonempty (take `u = z`).
  have hne : T.Nonempty := ⟨S.lowerBound1 hA.lo z, z, hz, le_refl z, rfl⟩
  change sSup T ≤ _
  exact csSup_le hne hle_all

/-- `E[Y(1) | Z = z] ≤ mUpper1 z` for every `z ∈ supp Z`. -/
theorem miv_cond_Y1_le_mUpper1 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMIV : S.MIV) {z : α} (hz : z ∈ S.support) :
    letI := hMIV.inst
    eventCondExp P.μ (S.zEvent z) (S.YofD true) ≤ S.mUpper1 hA z := by
  letI := hMIV.inst
  set T : Set ℝ :=
    {val : ℝ | ∃ u ∈ S.support, z ≤ u ∧ val = S.upperBound1 hA.hi u} with hT
  have hge_all : ∀ v ∈ T, eventCondExp P.μ (S.zEvent z) (S.YofD true) ≤ v := by
    rintro v ⟨u, hu, hleu, rfl⟩
    have h1 : eventCondExp P.μ (S.zEvent z) (S.YofD true) ≤
        eventCondExp P.μ (S.zEvent u) (S.YofD true) :=
      hMIV.monotone true z u hz hu hleu
    have h2 : eventCondExp P.μ (S.zEvent u) (S.YofD true) ≤
        S.upperBound1 hA.hi u :=
      S.cond_Y1_le_upperBound1 hA hu
    exact le_trans h1 h2
  have hne : T.Nonempty := ⟨S.upperBound1 hA.hi z, z, hz, le_refl z, rfl⟩
  change _ ≤ sInf T
  exact le_csInf hne hge_all

/-- `mLower0 z ≤ E[Y(0) | Z = z]` for every `z ∈ supp Z`. -/
theorem miv_mLower0_le_cond_Y0 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMIV : S.MIV) {z : α} (hz : z ∈ S.support) :
    letI := hMIV.inst
    S.mLower0 hA z ≤ eventCondExp P.μ (S.zEvent z) (S.YofD false) := by
  letI := hMIV.inst
  set T : Set ℝ :=
    {val : ℝ | ∃ u ∈ S.support, u ≤ z ∧ val = S.lowerBound0 hA.lo u} with hT
  have hle_all : ∀ v ∈ T, v ≤ eventCondExp P.μ (S.zEvent z) (S.YofD false) := by
    rintro v ⟨u, hu, hule, rfl⟩
    have h1 : S.lowerBound0 hA.lo u ≤
        eventCondExp P.μ (S.zEvent u) (S.YofD false) :=
      S.lowerBound0_le_cond_Y0 hA hu
    have h2 : eventCondExp P.μ (S.zEvent u) (S.YofD false) ≤
        eventCondExp P.μ (S.zEvent z) (S.YofD false) :=
      hMIV.monotone false u z hu hz hule
    exact le_trans h1 h2
  have hne : T.Nonempty := ⟨S.lowerBound0 hA.lo z, z, hz, le_refl z, rfl⟩
  change sSup T ≤ _
  exact csSup_le hne hle_all

/-- `E[Y(0) | Z = z] ≤ mUpper0 z` for every `z ∈ supp Z`. -/
theorem miv_cond_Y0_le_mUpper0 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (hMIV : S.MIV) {z : α} (hz : z ∈ S.support) :
    letI := hMIV.inst
    eventCondExp P.μ (S.zEvent z) (S.YofD false) ≤ S.mUpper0 hA z := by
  letI := hMIV.inst
  set T : Set ℝ :=
    {val : ℝ | ∃ u ∈ S.support, z ≤ u ∧ val = S.upperBound0 hA.hi u} with hT
  have hge_all : ∀ v ∈ T, eventCondExp P.μ (S.zEvent z) (S.YofD false) ≤ v := by
    rintro v ⟨u, hu, hleu, rfl⟩
    have h1 : eventCondExp P.μ (S.zEvent z) (S.YofD false) ≤
        eventCondExp P.μ (S.zEvent u) (S.YofD false) :=
      hMIV.monotone false z u hz hu hleu
    have h2 : eventCondExp P.μ (S.zEvent u) (S.YofD false) ≤
        S.upperBound0 hA.hi u :=
      S.cond_Y0_le_upperBound0 hA hu
    exact le_trans h1 h2
  have hne : T.Nonempty := ⟨S.upperBound0 hA.hi z, z, hz, le_refl z, rfl⟩
  change _ ≤ sInf T
  exact le_csInf hne hge_all

/-! ### Integrated envelope bounds and ATE bound

Under a `Fintype` hypothesis on the instrument value space `α`, the
integrated bounds follow from the stratum-level bounds by the
finite-partition total law
`integral_eq_sum_measure_mul_eventCondExp` (sections 8h of the API),
combined with the pointwise-on-stratum identity
`∫_{Z=z} g(factualZ ω) ∂μ = (μ (Z=z)).toReal * g z`. -/

/-- The `Z`-stratum events cover `P.Ω`. -/
private lemma iUnion_zEvent : (⋃ z, S.zEvent z) = Set.univ := by
  refine Set.eq_univ_of_forall (fun ω => ?_)
  exact Set.mem_iUnion.mpr ⟨S.factualZ ω, rfl⟩

/-- The `Z`-stratum events are pairwise disjoint. -/
private lemma pairwise_disjoint_zEvent :
    Pairwise (Function.onFun Disjoint S.zEvent) := by
  rintro z₁ z₂ hne
  refine Set.disjoint_left.mpr (fun ω hω₁ hω₂ => ?_)
  have h₁ : S.factualZ ω = z₁ := hω₁
  have h₂ : S.factualZ ω = z₂ := hω₂
  exact hne (h₁.symm.trans h₂)

/-- Pointwise-on-stratum identity:
`(μ(Z=z)).toReal * eventCondExp μ (Z=z) (g ∘ factualZ) = (μ(Z=z)).toReal * g z`.

Works without any `Fintype`/discreteness hypothesis on `α`; the zero-
measure case is handled uniformly by `eventCondExp_mul_measure_toReal`. -/
private lemma measure_mul_eventCondExp_of_factualZ_const
    (g : α → ℝ) (z : α) :
    (P.μ (S.zEvent z)).toReal
      * eventCondExp P.μ (S.zEvent z) (fun ω => g (S.factualZ ω))
      = (P.μ (S.zEvent z)).toReal * g z := by
  rw [mul_comm, eventCondExp_mul_measure_toReal]
  have hset : ∫ ω in S.zEvent z, g (S.factualZ ω) ∂P.μ
            = ∫ _ω in S.zEvent z, g z ∂P.μ := by
    refine MeasureTheory.setIntegral_congr_fun (S.measurableSet_zEvent z) ?_
    intro ω hω
    change g (S.factualZ ω) = g z
    have : S.factualZ ω = z := hω
    rw [this]
  rw [hset, MeasureTheory.setIntegral_const, smul_eq_mul,
    MeasureTheory.measureReal_def, mul_comm]

/-- Integral of `g ∘ factualZ` under a `Fintype` instrument support:
`∫ g(factualZ ω) ∂μ = ∑ z, (μ(Z=z)).toReal * g z`. -/
private lemma integral_comp_factualZ_eq_sum [Fintype α] [IsFiniteMeasure P.μ]
    (g : α → ℝ) :
    ∫ ω, g (S.factualZ ω) ∂P.μ
      = ∑ z : α, (P.μ (S.zEvent z)).toReal * g z := by
  have hmeas_g : Measurable g := measurable_of_finite g
  have hmeas_comp : Measurable (fun ω => g (S.factualZ ω)) :=
    hmeas_g.comp S.measurable_factualZ
  have hint : Integrable (fun ω => g (S.factualZ ω)) P.μ := by
    refine MeasureTheory.Integrable.of_bound hmeas_comp.aestronglyMeasurable
      (∑ z : α, |g z|) (Filter.Eventually.of_forall (fun ω => ?_))
    have hle : |g (S.factualZ ω)| ≤ ∑ z : α, |g z| :=
      Finset.single_le_sum (f := fun z => |g z|)
        (fun z _ => abs_nonneg _) (Finset.mem_univ _)
    simpa using hle
  have h := integral_eq_sum_measure_mul_eventCondExp (μ := P.μ)
    (A := S.zEvent) S.measurableSet_zEvent S.pairwise_disjoint_zEvent
    S.iUnion_zEvent (fun ω => g (S.factualZ ω)) hint
  rw [h]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  exact S.measure_mul_eventCondExp_of_factualZ_const g z

/-- Integral of `S.YofD d` decomposed via the `Fintype` total law:
`∫ YofD d = ∑ z, (μ(Z=z)).toReal * eventCondExp μ (Z=z) (YofD d)`. -/
private lemma integral_YofD_eq_sum_over_zEvent [Fintype α] [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (d : Bool) :
    ∫ ω, S.YofD d ω ∂P.μ
      = ∑ z : α, (P.μ (S.zEvent z)).toReal
          * eventCondExp P.μ (S.zEvent z) (S.YofD d) := by
  have hint : Integrable (S.YofD d) P.μ := by
    cases d
    · exact hA.integrable_Y0
    · exact hA.integrable_Y1
  exact integral_eq_sum_measure_mul_eventCondExp (μ := P.μ)
    (A := S.zEvent) S.measurableSet_zEvent S.pairwise_disjoint_zEvent
    S.iUnion_zEvent (S.YofD d) hint

/-- Helper: pointwise comparison `c * a ≤ c * b` with `c = (μ(Z=z)).toReal`,
splitting on whether `z ∈ support`.  On `support` the stratum bound applies;
off `support` `μ(Z=z) = 0` makes both sides vanish. -/
private lemma mul_zEvent_measure_mono_of_stratum_le
    (a b : α → ℝ)
    (hstratum : ∀ {z : α}, z ∈ S.support → a z ≤ b z)
    (z : α) :
    (P.μ (S.zEvent z)).toReal * a z ≤ (P.μ (S.zEvent z)).toReal * b z := by
  by_cases hz : z ∈ S.support
  · exact mul_le_mul_of_nonneg_left (hstratum hz) ENNReal.toReal_nonneg
  · have hμ : P.μ (S.zEvent z) = 0 := by
      by_contra hne; exact hz hne
    simp [hμ]

/-- Integrated envelope bound for arm `d = 1` (lower):
`∫ mLower1(Z) ≤ ∫ Y(1)`. -/
theorem miv_integral_mLower1_le_integral_Y1 [IsFiniteMeasure P.μ] [Fintype α]
    (hA : S.BaseAssumptions) (hMIV : S.MIV) :
    letI := hMIV.inst
    (∫ ω, S.mLower1 hA (S.factualZ ω) ∂P.μ) ≤ ∫ ω, S.YofD true ω ∂P.μ := by
  letI := hMIV.inst
  rw [S.integral_comp_factualZ_eq_sum (S.mLower1 hA),
    S.integral_YofD_eq_sum_over_zEvent hA true]
  refine Finset.sum_le_sum (fun z _ => ?_)
  exact S.mul_zEvent_measure_mono_of_stratum_le
    (a := fun z => S.mLower1 hA z)
    (b := fun z => eventCondExp P.μ (S.zEvent z) (S.YofD true))
    (fun {z} hz => S.miv_mLower1_le_cond_Y1 hA hMIV hz) z

/-- Integrated envelope bound for arm `d = 1` (upper):
`∫ Y(1) ≤ ∫ mUpper1(Z)`. -/
theorem miv_integral_Y1_le_integral_mUpper1 [IsFiniteMeasure P.μ] [Fintype α]
    (hA : S.BaseAssumptions) (hMIV : S.MIV) :
    letI := hMIV.inst
    (∫ ω, S.YofD true ω ∂P.μ) ≤ ∫ ω, S.mUpper1 hA (S.factualZ ω) ∂P.μ := by
  letI := hMIV.inst
  rw [S.integral_YofD_eq_sum_over_zEvent hA true,
    S.integral_comp_factualZ_eq_sum (S.mUpper1 hA)]
  refine Finset.sum_le_sum (fun z _ => ?_)
  exact S.mul_zEvent_measure_mono_of_stratum_le
    (a := fun z => eventCondExp P.μ (S.zEvent z) (S.YofD true))
    (b := fun z => S.mUpper1 hA z)
    (fun {z} hz => S.miv_cond_Y1_le_mUpper1 hA hMIV hz) z

/-- Integrated envelope bound for arm `d = 0` (lower):
`∫ mLower0(Z) ≤ ∫ Y(0)`. -/
theorem miv_integral_mLower0_le_integral_Y0 [IsFiniteMeasure P.μ] [Fintype α]
    (hA : S.BaseAssumptions) (hMIV : S.MIV) :
    letI := hMIV.inst
    (∫ ω, S.mLower0 hA (S.factualZ ω) ∂P.μ) ≤ ∫ ω, S.YofD false ω ∂P.μ := by
  letI := hMIV.inst
  rw [S.integral_comp_factualZ_eq_sum (S.mLower0 hA),
    S.integral_YofD_eq_sum_over_zEvent hA false]
  refine Finset.sum_le_sum (fun z _ => ?_)
  exact S.mul_zEvent_measure_mono_of_stratum_le
    (a := fun z => S.mLower0 hA z)
    (b := fun z => eventCondExp P.μ (S.zEvent z) (S.YofD false))
    (fun {z} hz => S.miv_mLower0_le_cond_Y0 hA hMIV hz) z

/-- Integrated envelope bound for arm `d = 0` (upper):
`∫ Y(0) ≤ ∫ mUpper0(Z)`. -/
theorem miv_integral_Y0_le_integral_mUpper0 [IsFiniteMeasure P.μ] [Fintype α]
    (hA : S.BaseAssumptions) (hMIV : S.MIV) :
    letI := hMIV.inst
    (∫ ω, S.YofD false ω ∂P.μ) ≤ ∫ ω, S.mUpper0 hA (S.factualZ ω) ∂P.μ := by
  letI := hMIV.inst
  rw [S.integral_YofD_eq_sum_over_zEvent hA false,
    S.integral_comp_factualZ_eq_sum (S.mUpper0 hA)]
  refine Finset.sum_le_sum (fun z _ => ?_)
  exact S.mul_zEvent_measure_mono_of_stratum_le
    (a := fun z => eventCondExp P.μ (S.zEvent z) (S.YofD false))
    (b := fun z => S.mUpper0 hA z)
    (fun {z} hz => S.miv_cond_Y0_le_mUpper0 hA hMIV hz) z

/-- MIV ATE envelope bounds (prop:po-iv-miv, integrated form):

    `∫ (mLower1(Z) - mUpper0(Z)) ≤ ATE ≤ ∫ (mUpper1(Z) - mLower0(Z))`.

Follows from the four integrated envelope bounds above plus linearity. -/
theorem miv_bounds_ATE [IsFiniteMeasure P.μ] [Fintype α]
    (hA : S.BaseAssumptions) (hMIV : S.MIV) :
    letI := hMIV.inst
    (∫ ω, S.mLower1 hA (S.factualZ ω) - S.mUpper0 hA (S.factualZ ω) ∂P.μ)
      ≤ S.ATE
    ∧ S.ATE ≤
      (∫ ω, S.mUpper1 hA (S.factualZ ω) - S.mLower0 hA (S.factualZ ω) ∂P.μ) := by
  letI := hMIV.inst
  -- Integrability of the envelope composites (bounded on a Fintype support).
  have hmeas_mL1 : Measurable (S.mLower1 hA) := measurable_of_finite _
  have hmeas_mU1 : Measurable (S.mUpper1 hA) := measurable_of_finite _
  have hmeas_mL0 : Measurable (S.mLower0 hA) := measurable_of_finite _
  have hmeas_mU0 : Measurable (S.mUpper0 hA) := measurable_of_finite _
  have hint_mL1 : Integrable (fun ω => S.mLower1 hA (S.factualZ ω)) P.μ := by
    refine MeasureTheory.Integrable.of_bound
      (hmeas_mL1.comp S.measurable_factualZ).aestronglyMeasurable
      (∑ z : α, |S.mLower1 hA z|) (Filter.Eventually.of_forall (fun ω => ?_))
    have : |S.mLower1 hA (S.factualZ ω)| ≤ ∑ z : α, |S.mLower1 hA z| :=
      Finset.single_le_sum (f := fun z => |S.mLower1 hA z|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    simpa using this
  have hint_mU1 : Integrable (fun ω => S.mUpper1 hA (S.factualZ ω)) P.μ := by
    refine MeasureTheory.Integrable.of_bound
      (hmeas_mU1.comp S.measurable_factualZ).aestronglyMeasurable
      (∑ z : α, |S.mUpper1 hA z|) (Filter.Eventually.of_forall (fun ω => ?_))
    have : |S.mUpper1 hA (S.factualZ ω)| ≤ ∑ z : α, |S.mUpper1 hA z| :=
      Finset.single_le_sum (f := fun z => |S.mUpper1 hA z|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    simpa using this
  have hint_mL0 : Integrable (fun ω => S.mLower0 hA (S.factualZ ω)) P.μ := by
    refine MeasureTheory.Integrable.of_bound
      (hmeas_mL0.comp S.measurable_factualZ).aestronglyMeasurable
      (∑ z : α, |S.mLower0 hA z|) (Filter.Eventually.of_forall (fun ω => ?_))
    have : |S.mLower0 hA (S.factualZ ω)| ≤ ∑ z : α, |S.mLower0 hA z| :=
      Finset.single_le_sum (f := fun z => |S.mLower0 hA z|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    simpa using this
  have hint_mU0 : Integrable (fun ω => S.mUpper0 hA (S.factualZ ω)) P.μ := by
    refine MeasureTheory.Integrable.of_bound
      (hmeas_mU0.comp S.measurable_factualZ).aestronglyMeasurable
      (∑ z : α, |S.mUpper0 hA z|) (Filter.Eventually.of_forall (fun ω => ?_))
    have : |S.mUpper0 hA (S.factualZ ω)| ≤ ∑ z : α, |S.mUpper0 hA z| :=
      Finset.single_le_sum (f := fun z => |S.mUpper0 hA z|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    simpa using this
  have hATE_eq :
      S.ATE = ∫ ω, S.YofD true ω ∂P.μ - ∫ ω, S.YofD false ω ∂P.μ := by
    unfold ATE
    exact integral_sub hA.integrable_Y1 hA.integrable_Y0
  have hL1 := S.miv_integral_mLower1_le_integral_Y1 hA hMIV
  have hU1 := S.miv_integral_Y1_le_integral_mUpper1 hA hMIV
  have hL0 := S.miv_integral_mLower0_le_integral_Y0 hA hMIV
  have hU0 := S.miv_integral_Y0_le_integral_mUpper0 hA hMIV
  refine ⟨?_, ?_⟩
  · have hsub_lhs := integral_sub hint_mL1 hint_mU0
    rw [hsub_lhs, hATE_eq]
    linarith
  · have hsub_rhs := integral_sub hint_mU1 hint_mL0
    rw [hsub_rhs, hATE_eq]
    linarith

end POManskiIVSystem

end PO
end Causalean
