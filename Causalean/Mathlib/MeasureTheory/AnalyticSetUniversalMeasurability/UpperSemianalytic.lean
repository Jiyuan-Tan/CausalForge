/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module

public import Causalean.Mathlib.MeasureTheory.AnalyticSetUniversalMeasurability.UniversalMeasurability
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Completed measurability of upper-semi-analytic losses

This file provides only the function-level compatibility needed by downstream statistical
applications: an extended-nonnegative function whose strict superlevel sets are analytic is
measurable on the completion of every finite Borel measure, and its completed lower integral agrees
with the lower integral computed against the original measure.
-/

@[expose] public section

open Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]

/-- The outer integral of an extended-nonnegative function is the infimum of the lower
integrals of all measurable pointwise majorants. -/
noncomputable def outerLIntegral (μ : Measure Ω) (f : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ g), ∫⁻ ω, g ω ∂μ

/-- Outer integration is monotone in its extended-nonnegative integrand. -/
theorem outerLIntegral_mono {μ : Measure Ω} {f g : Ω → ℝ≥0∞} (hfg : f ≤ g) :
    outerLIntegral μ f ≤ outerLIntegral μ g := by
  unfold outerLIntegral
  refine le_iInf fun h => le_iInf fun hh => le_iInf fun hgh => ?_
  exact iInf₂_le_of_le h hh (iInf_le_of_le (hfg.trans hgh) le_rfl)

/-- The lower Lebesgue integral is bounded by the outer integral. -/
theorem lintegral_le_outerLIntegral (μ : Measure Ω) (f : Ω → ℝ≥0∞) :
    (∫⁻ ω, f ω ∂μ) ≤ outerLIntegral μ f := by
  unfold outerLIntegral
  refine le_iInf fun g => le_iInf fun _ => le_iInf fun hfg => ?_
  exact lintegral_mono hfg

/-- A pointwise lower bound may be integrated before comparison with an
outer integral, without measurability of either function. -/
theorem lintegral_le_outerLIntegral_of_measurable_le
    {μ : Measure Ω} {f g : Ω → ℝ≥0∞} (hfg : f ≤ g) :
    (∫⁻ ω, f ω ∂μ) ≤ outerLIntegral μ g :=
  (lintegral_le_outerLIntegral μ f).trans (outerLIntegral_mono hfg)

/-- Outer integration agrees with Lebesgue integration for measurable functions. -/
theorem outerLIntegral_eq_lintegral_of_measurable
    {μ : Measure Ω} {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    outerLIntegral μ f = ∫⁻ ω, f ω ∂μ := by
  apply le_antisymm
  · unfold outerLIntegral
    exact iInf₂_le_of_le f hf (iInf_le_of_le le_rfl le_rfl)
  · exact lintegral_le_outerLIntegral μ f

/-- Completing a measure can only increase the lower integral of an arbitrary
extended-nonnegative function. -/
theorem lintegral_le_lintegral_completion (μ : Measure Ω) (f : Ω → ℝ≥0∞) :
    (∫⁻ ω, f ω ∂μ) ≤ ∫⁻ ω, f ω ∂μ.completion := by
  let m₀ : MeasurableSpace (NullMeasurableSpace Ω μ) := ‹MeasurableSpace Ω›
  change @lintegral Ω ‹MeasurableSpace Ω› μ f ≤
    @lintegral (NullMeasurableSpace Ω μ)
      (@NullMeasurableSpace.instMeasurableSpace Ω ‹MeasurableSpace Ω› μ)
      μ.completion f
  conv_lhs => rw [lintegral]
  refine iSup₂_le fun h hh => ?_
  have hid : @Measurable (NullMeasurableSpace Ω μ) Ω
      (@NullMeasurableSpace.instMeasurableSpace Ω ‹MeasurableSpace Ω› μ) m₀ id := by
    intro s hs
    exact hs.nullMeasurableSet
  let h' := @SimpleFunc.comp (NullMeasurableSpace Ω μ) Ω ℝ≥0∞
    (@NullMeasurableSpace.instMeasurableSpace Ω ‹MeasurableSpace Ω› μ) m₀ h id hid
  have hh' : ⇑h' ≤ f := by
    intro x
    exact hh x
  have hpre : h.lintegral μ = h'.lintegral μ.completion := by
    refine @SimpleFunc.lintegral_eq_of_measure_preimage Ω
      (NullMeasurableSpace Ω μ) m₀ μ
      (@NullMeasurableSpace.instMeasurableSpace Ω ‹MeasurableSpace Ω› μ)
      h h' μ.completion ?_
    intro y
    rfl
  calc h.lintegral μ
      = h'.lintegral μ.completion := hpre
    _ = ∫⁻ ω, h' ω ∂μ.completion := (h'.lintegral_eq_lintegral μ.completion).symm
    _ ≤ ∫⁻ ω, f ω ∂μ.completion := lintegral_mono hh'

/-- A measurable extended-nonnegative function has the same integral before
and after completion of the measure. -/
theorem lintegral_completion_eq_of_measurable
    (μ : Measure Ω) {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ω, f ω ∂μ.completion) = ∫⁻ ω, f ω ∂μ := by
  let m₀ : MeasurableSpace (NullMeasurableSpace Ω μ) := ‹MeasurableSpace Ω›
  have hm : m₀ ≤
      (@NullMeasurableSpace.instMeasurableSpace Ω ‹MeasurableSpace Ω› μ) := by
    intro s hs
    exact hs.nullMeasurableSet
  let μ' : @Measure (NullMeasurableSpace Ω μ) m₀ := by
    unfold m₀ NullMeasurableSpace
    exact μ
  have htrim : μ.completion.trim hm = μ' := by
    apply @Measure.ext (NullMeasurableSpace Ω μ) m₀
    intro s hs
    rw [trim_measurableSet_eq hm hs]
    rfl
  have hf' : @Measurable (NullMeasurableSpace Ω μ) ℝ≥0∞ m₀ _ f := by
    unfold m₀ NullMeasurableSpace
    exact hf
  have h := @lintegral_trim (NullMeasurableSpace Ω μ) m₀
    (@NullMeasurableSpace.instMeasurableSpace Ω ‹MeasurableSpace Ω› μ)
    μ.completion hm f hf'
  rw [htrim] at h
  exact h.symm

/-- An extended-nonnegative function is upper-semi-analytic when every strict superlevel set is
analytic. -/
def UpperSemianalytic (f : Ω → ℝ≥0∞) : Prop :=
  ∀ a : ℝ≥0∞, AnalyticSet {ω | a < f ω}

namespace UpperSemianalytic

/-- An upper-semi-analytic extended-nonnegative function is null-measurable for every finite Borel
measure. -/
theorem nullMeasurable [PolishSpace Ω] [BorelSpace Ω] {f : Ω → ℝ≥0∞}
    (hf : UpperSemianalytic f) (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurable f μ := by
  change @Measurable (NullMeasurableSpace Ω μ) ℝ≥0∞ _ _ f
  apply measurable_of_Ioi
  intro a
  exact (hf a).nullMeasurableSet μ

/-- An upper-semi-analytic extended-nonnegative loss is measurable once a finite Borel sampling
measure is completed, so it is available to ordinary completed-measure integration. -/
theorem measurable_completion [PolishSpace Ω] [BorelSpace Ω] {f : Ω → ℝ≥0∞}
    (hf : UpperSemianalytic f) (μ : Measure Ω) [IsFiniteMeasure μ] :
    @Measurable (NullMeasurableSpace Ω μ) ℝ≥0∞ _ _ f := by
  exact (hf.nullMeasurable μ).measurable'

/-- On a Polish sample space equipped with its Borel σ-algebra and a finite measure `μ`, if
[`f` is upper-semi-analytic — every strict superlevel set `{ω | a < f ω}` is
analytic](hyp:hf), then [the lower Lebesgue integral of `f` against the completion of `μ`
equals the outer integral of `f` with respect to `μ`, i.e. the infimum of the lower integrals
of all measurable pointwise majorants of `f`](goal). -/
theorem lintegral_completion_eq_outerLIntegral [PolishSpace Ω] [BorelSpace Ω]
    {f : Ω → ℝ≥0∞}
    (hf : UpperSemianalytic f) (μ : Measure Ω) [IsFiniteMeasure μ] :
    (∫⁻ ω, f ω ∂μ.completion) = outerLIntegral μ f := by
  classical
  let m₀ : MeasurableSpace (NullMeasurableSpace Ω μ) := ‹MeasurableSpace Ω›
  have hm : m₀ ≤
      (@NullMeasurableSpace.instMeasurableSpace Ω ‹MeasurableSpace Ω› μ) := by
    intro s hs
    change NullMeasurableSet s μ
    exact hs.nullMeasurableSet
  let μ' : @Measure (NullMeasurableSpace Ω μ) m₀ := by
    unfold m₀ NullMeasurableSpace
    exact μ
  have htrim : μ.completion.trim hm = μ' := by
    apply @Measure.ext (NullMeasurableSpace Ω μ) m₀
    intro s hs
    rw [trim_measurableSet_eq hm hs]
    rfl
  have h_lintegral (g : Ω → ℝ≥0∞) (hg : Measurable g) :
      (∫⁻ ω, g ω ∂μ.completion) = ∫⁻ ω, g ω ∂μ := by
    have hμ' : (∫⁻ ω, g ω ∂μ') = ∫⁻ ω, g ω ∂μ := by
      unfold μ' m₀ NullMeasurableSpace
      rfl
    have hg' : @Measurable (NullMeasurableSpace Ω μ) ℝ≥0∞ m₀ _ g := by
      unfold m₀ NullMeasurableSpace
      exact hg
    have ht := @lintegral_trim (NullMeasurableSpace Ω μ) m₀
      (@NullMeasurableSpace.instMeasurableSpace Ω ‹MeasurableSpace Ω› μ)
      μ.completion hm g hg'
    rw [← hμ', ← htrim]
    exact ht.symm
  rw [outerLIntegral]
  apply le_antisymm
  · refine le_iInf fun g ↦ le_iInf fun hg ↦ le_iInf fun hfg ↦ ?_
    calc
      (∫⁻ ω, f ω ∂μ.completion) ≤ ∫⁻ ω, g ω ∂μ.completion :=
        lintegral_mono hfg
      _ = ∫⁻ ω, g ω ∂μ := h_lintegral g hg
  · let hfm : AEMeasurable f μ := (hf.nullMeasurable μ).aemeasurable
    let g : Ω → ℝ≥0∞ := hfm.mk f
    have hgm : Measurable g := hfm.measurable_mk
    have hfg : f =ᵐ[μ] g := hfm.ae_eq_mk
    have hDnull : μ {ω | f ω ≠ g ω} = 0 := by
      rw [← compl_mem_ae_iff]
      have hfg' : {ω | f ω = g ω} ∈ ae μ := hfg
      simpa only [compl_setOf, Classical.not_not] using hfg'
    obtain ⟨N, hDN, hNm, hNnull⟩ :=
      exists_measurable_superset_of_null hDnull
    let G : Ω → ℝ≥0∞ := N.piecewise (fun _ ↦ ⊤) g
    have hGm : Measurable G := measurable_const.piecewise hNm hgm
    have hfG : f ≤ G := by
      intro ω
      by_cases hω : ω ∈ N
      · simp [G, hω]
      · have hEq : f ω = g ω := by
          by_contra hne
          exact hω (hDN hne)
        simp [G, hω, hEq]
    have hGg : G =ᵐ[μ] g := by
      filter_upwards [compl_mem_ae_iff.2 hNnull] with ω hω
      have hωN : ω ∉ N := by simpa using hω
      simp [G, hωN]
    have hGf : G =ᵐ[μ.completion] f := by
      rw [μ.ae_completion]
      exact hGg.trans hfg.symm
    have houter :
        (⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ g), ∫⁻ ω, g ω ∂μ) ≤
          ∫⁻ ω, G ω ∂μ :=
      iInf₂_le_of_le G hGm (iInf_le_of_le hfG le_rfl)
    calc
      (⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ g), ∫⁻ ω, g ω ∂μ) ≤
          ∫⁻ ω, G ω ∂μ := houter
      _ = ∫⁻ ω, G ω ∂μ.completion := (h_lintegral G hGm).symm
      _ = ∫⁻ ω, f ω ∂μ.completion := lintegral_congr_ae hGf

end UpperSemianalytic

end MeasureTheory
