/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Słoczyński (2022): cell integral helpers

Integral identities for finite cells used by the saturated bridge.
-/

import Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition.Support.Basic
/-! # Słoczyński cell integral identities

This file proves reusable integral identities for finite covariate cells in
the Słoczyński bridge. The results convert indicator-weighted integrals into
cell masses and cell means, provide integrability facts for products with
treatment and cell indicators, and reduce saturated linear-combination
orthogonality to per-cell orthogonality. The central declarations are
`indicator_cell_memLp`, `integral_cell_indicator_one_eq_cellMass`,
`cell_integral_div_mul_cellMass`, `cellTau_mul_cellMass`,
`integrable_mul_indicator_D_G`, `propensity_eq_cellShare_of_mem`,
`meanReg_eq_cellMean_of_mem`, `integral_mul_saturated_eq_zero_of_cell`, and
`integral_eq_sum_cell`. -/

namespace Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

section CellHelpers

/-- Indicator helper: `Set.indicator {G = g} 1` is in `MemLp 2 μ` for a
finite measure (it is bounded by `1` and finite measure ⇒ MemLp `p`
for every `p`). Stated as a separate lemma because it appears repeatedly
in orthogonality and per-cell calculations. -/
theorem indicator_cell_memLp {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (G : Ω → 𝒢) (G_meas : Measurable G) (g : 𝒢) :
    MemLp (fun ω => Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω) 2 μ := by
  exact CellBridge.indicator_cell_memLp μ G G_meas g

/-- Cell indicators integrate to the corresponding real cell mass. -/
theorem integral_cell_indicator_one_eq_cellMass {Ω 𝒢 : Type*}
    [MeasurableSpace Ω] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) (G : Ω → 𝒢) (G_meas : Measurable G) (g : 𝒢) :
    ∫ ω, Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ =
      cellMass μ G g := by
  simpa [cellMass] using
    (CellBridge.integral_cell_indicator_one_eq_cellMass μ G G_meas g)

/-- Dividing an indicator-weighted cell integral by a nonzero cell mass and
multiplying back recovers the numerator; on zero-mass cells the numerator is
zero because the indicator is a.e. zero. -/
theorem cell_integral_div_mul_cellMass {Ω 𝒢 : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Ω → ℝ) (G : Ω → 𝒢) (g : 𝒢) :
    ((∫ ω, F ω * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ)
        / cellMass μ G g)
      * cellMass μ G g =
      ∫ ω, F ω * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ := by
  simpa [cellMass] using
    (CellBridge.cell_integral_div_mul_cellMass μ F G g)

/-- Cell-effect numerator divided by cell mass and multiplied back recovers
the raw effect numerator. -/
theorem cellTau_mul_cellMass {Ω 𝒢 : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y0 Y1 : Ω → ℝ) (G : Ω → 𝒢) (g : 𝒢) :
    cellTau μ Y0 Y1 G g * cellMass μ G g =
      ∫ ω, (Y1 ω - Y0 ω)
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ := by
  simpa [cellTau, cellMass] using
    (CellBridge.cellMean_mul_cellMass μ (fun ω => Y1 ω - Y0 ω) G g)

/-- Product of two singleton indicators against an `L²` function is
integrable under a finite measure. -/
theorem integrable_mul_indicator_D_G {Ω 𝒢 : Type*}
    [MeasurableSpace Ω] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F D : Ω → ℝ) (G : Ω → 𝒢)
    (D_meas : Measurable D) (G_meas : Measurable G)
    (F_memLp : MemLp F 2 μ) (d : ℝ) (g : 𝒢) :
    Integrable
      (fun ω => F ω
        * Set.indicator {ω' | D ω' = d} (fun _ => (1 : ℝ)) ω
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω) μ := by
  let sD : Set Ω := {ω | D ω = d}
  let sG : Set Ω := {ω | G ω = g}
  have hsD : MeasurableSet sD := D_meas (measurableSet_singleton d)
  have hsG : MeasurableSet sG := G_meas (measurableSet_singleton g)
  have hmem :
      MemLp (fun ω => Set.indicator sG (Set.indicator sD F) ω) 2 μ :=
    (F_memLp.indicator hsD).indicator hsG
  have hEq :
      (fun ω => Set.indicator sG (Set.indicator sD F) ω) =
        (fun ω => F ω
          * Set.indicator sD (fun _ => (1 : ℝ)) ω
          * Set.indicator sG (fun _ => (1 : ℝ)) ω) := by
    funext ω
    by_cases hG : ω ∈ sG
    · by_cases hD : ω ∈ sD
      · simp [sD, sG, Set.indicator, hD, hG]
      · simp [sD, sG, Set.indicator, hD, hG]
    · simp [sD, sG, Set.indicator, hG]
  rw [← hEq]
  exact hmem.integrable (by norm_num : (1 : ENNReal) ≤ 2)

/-- On its own cell, the saturated propensity representative equals the
corresponding cell share. -/
theorem propensity_eq_cellShare_of_mem {Ω 𝒢 : Type*}
    [MeasurableSpace Ω] [Fintype 𝒢]
    (μ : Measure Ω)
    (D : Ω → ℝ) (G : Ω → 𝒢) {g : 𝒢} {ω : Ω} (hG : G ω = g) :
    propensity μ D G ω = cellShare μ D G g := by
  classical
  unfold propensity
  rw [Finset.sum_eq_single g]
  · simp [hG]
  · intro b _ hbg
    simp [Set.indicator, hG, hbg.symm]
  · intro hg
    simp at hg

/-- On its own cell, the saturated mean-regression representative equals the
corresponding cell mean. -/
theorem meanReg_eq_cellMean_of_mem {Ω 𝒢 : Type*}
    [MeasurableSpace Ω] [Fintype 𝒢]
    (μ : Measure Ω)
    (Y : Ω → ℝ) (G : Ω → 𝒢) {g : 𝒢} {ω : Ω} (hG : G ω = g) :
    meanReg μ Y G ω =
      (∫ ω', Y ω'
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω' ∂μ)
        / cellMass μ G g := by
  classical
  unfold meanReg
  rw [Finset.sum_eq_single g]
  · simp [hG]
  · intro b _ hbg
    simp [Set.indicator, hG, hbg.symm]
  · intro hg
    simp at hg

/-- If a square-integrable residual is orthogonal to every cell indicator, it
is orthogonal to every saturated finite linear combination. -/
theorem integral_mul_saturated_eq_zero_of_cell {Ω 𝒢 : Type*}
    [MeasurableSpace Ω] [Fintype 𝒢]
    [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (V : Ω → ℝ) (G : Ω → 𝒢) (G_meas : Measurable G)
    (V_memLp : MemLp V 2 μ) (c : 𝒢 → ℝ)
    (hcell : ∀ g,
      ∫ ω, V ω
          * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ = 0) :
    ∫ ω, V ω
        * (∑ g, c g
          * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω) ∂μ = 0 := by
  classical
  exact CellBridge.integral_mul_indicatorSpan_eq_zero_of_cell μ V G G_meas
    V_memLp c hcell

/-- For [an ambient probability space and finite covariate space](hyp:Ω,𝒢), [a measure
`μ`](hyp:μ), [a measurable covariate map `G`](hyp:G,G_meas), and [an integrable function
`F`](hyp:F,F_int), [the integral of `F` against `μ` equals the sum, over covariate cells `g`, of
the integral of `F` restricted to the cell `{G = g}`](goal). -/
theorem integral_eq_sum_cell {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [Fintype 𝒢] [MeasurableSpace 𝒢]
    [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) (F : Ω → ℝ) (G : Ω → 𝒢)
    (G_meas : Measurable G) (F_int : Integrable F μ) :
    ∫ ω, F ω ∂μ =
      ∑ g, ∫ ω, F ω
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ := by
  classical
  exact CellBridge.integral_eq_sum_cell μ F G G_meas F_int


end CellHelpers

end Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition
