/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module

public import Causalean.Mathlib.MeasureTheory.AnalyticSetUniversalMeasurability.Capacity
public import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Universal measurability of analytic sets

This file converts Choquet capacitability for the outer measure of a finite Borel measure into
membership in the completed sigma-algebra.  Its main declaration is the public universal
measurability theorem for Mathlib's `MeasureTheory.AnalyticSet`.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]

/-- A set capacitable for the outer measure of a finite measure is null-measurable for that
measure. -/
theorem ChoquetCapacity.IsCapacitable.nullMeasurableSet [PolishSpace Ω]
    [BorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω}
    (hs : μ.toChoquetCapacity.IsCapacitable s) : NullMeasurableSet s μ := by
  by_cases hzero : μ s = 0
  · exact NullMeasurableSet.of_null hzero
  have hlt (n : ℕ) : μ s * (1 - (n + 1 : ℝ≥0∞)⁻¹) < μ s := by
    nth_rw 2 [← mul_one (μ s)]
    refine (ENNReal.mul_lt_mul_iff_right hzero (by finiteness)).2 ?_
    refine ENNReal.sub_lt_of_lt_add (by simp) ?_
    exact ENNReal.lt_add_right (by simp) (by simp)
  have hex (n : ℕ) : ∃ K : Set Ω, K ⊆ s ∧ IsCompact K ∧
      μ s * (1 - (n + 1 : ℝ≥0∞)⁻¹) < μ K := by
    rw [ChoquetCapacity.IsCapacitable] at hs
    have hsc : μ s = ⨆ (K : Set Ω) (_ : K ⊆ s) (_ : IsCompact K), μ K := by
      simpa only [Measure.toChoquetCapacity_apply] using hs
    have h : μ s * (1 - (n + 1 : ℝ≥0∞)⁻¹) <
        ⨆ (K : Set Ω) (_ : K ⊆ s) (_ : IsCompact K), μ K :=
      (hlt n).trans_eq hsc
    simpa only [lt_iSup_iff, exists_prop] using h
  choose K hKsub hKcompact hKgt using hex
  let B : Set Ω := ⋃ n, K n
  have hBsub : B ⊆ s := iUnion_subset hKsub
  have hBmeas : MeasurableSet B :=
    MeasurableSet.iUnion fun n ↦ (hKcompact n).isClosed.measurableSet
  have hBmeasure : μ B = μ s := by
    refine le_antisymm (μ.mono hBsub) ?_
    have htend : Tendsto (fun n : ℕ ↦ μ s * (1 - (n + 1 : ℝ≥0∞)⁻¹))
        atTop (𝓝 (μ s)) := by
      nth_rw 2 [← mul_one (μ s)]
      refine ENNReal.Tendsto.const_mul ?_ (by simp)
      nth_rw 3 [← tsub_zero 1]
      refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (by simp)
      convert ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1) with n
      simp
    refine le_of_tendsto_of_tendsto' htend tendsto_const_nhds fun n ↦ (hKgt n).le.trans ?_
    exact μ.mono (Set.subset_iUnion K n)
  have hnull : μ (s \ B) = 0 := by
    rw [measure_diff hBsub hBmeas.nullMeasurableSet (by finiteness), hBmeasure, tsub_self]
  rw [← union_diff_cancel hBsub]
  exact hBmeas.nullMeasurableSet.union (NullMeasurableSet.of_null hnull)

/-- An analytic subset of a Polish sample space is measurable after completing any finite Borel
measure, so it differs from an ordinary measurable event only on a zero-probability set. -/
theorem AnalyticSet.nullMeasurableSet [PolishSpace Ω] [BorelSpace Ω]
    {s : Set Ω} (hs : AnalyticSet s) (μ : Measure Ω) [IsFiniteMeasure μ] :
    NullMeasurableSet s μ := by
  exact (hs.isCapacitable (c := μ.toChoquetCapacity)).nullMeasurableSet

end MeasureTheory

