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

/-- For an upper-semi-analytic extended-nonnegative function, integration on the completed space
agrees with the outer integral against the original measure. -/
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
    rw [trim_measurableSet_eq hm hs, Measure.completion_apply]
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
      simpa only [compl_setOf, Classical.not_not] using hfg
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
