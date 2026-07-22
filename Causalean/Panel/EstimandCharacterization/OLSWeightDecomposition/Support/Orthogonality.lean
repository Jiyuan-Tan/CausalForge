/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Słoczyński (2022): orthogonality helpers

Per-cell orthogonality facts and the observed-outcome L² bridge.
-/

import Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition.Support.Integrals
/-! # Słoczyński orthogonality helpers

This file proves the cell-level orthogonality statements needed for the
Słoczyński finite-cell bridge. It shows that treatment and outcome residuals
are orthogonal to saturated cell indicators through
`residD_cell_orthogonal` and `residY_cell_orthogonal`. It also proves
`Y_memLp_of_consistency`, deriving observed-outcome square-integrability from
binary treatment, consistency, and square-integrability of the two potential
outcomes. -/

namespace Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

section CellHelpers

/-- The treatment residual is orthogonal to each saturated cell indicator. -/
theorem residD_cell_orthogonal {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [Fintype 𝒢] [DecidableEq 𝒢] [MeasurableSpace 𝒢]
    [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (G : Ω → 𝒢)
    (G_meas : Measurable G) (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) (g : 𝒢) :
    ∫ ω, (D ω - propensity μ D G ω)
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ = 0 := by
  let s : Set Ω := {ω | G ω = g}
  let I : Ω → ℝ := fun ω => Set.indicator s (fun _ => (1 : ℝ)) ω
  let p : ℝ := cellShare μ D G g
  have hD_mem : MemLp D 2 μ := by
    have hD_bounded : ∀ᵐ ω ∂μ, D ω ∈ Set.Icc (-1 : ℝ) 1 := by
      filter_upwards [D_binary] with ω hD
      rcases hD with hD0 | hD1
      · simp [hD0]
      · simp [hD1]
    exact memLp_of_bounded (f := D) hD_bounded
      (D_meas.aestronglyMeasurable) (2 : ENNReal)
  have hI_mem : MemLp I 2 μ := by
    simpa [I, s] using indicator_cell_memLp μ G G_meas g
  have hDInt : Integrable (fun ω => D ω * I ω) μ :=
    hD_mem.integrable_mul hI_mem
  have hpIInt : Integrable (fun ω => p * I ω) μ :=
    (hI_mem.const_mul p).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have h_ae :
      (fun ω => (D ω - propensity μ D G ω) * I ω) =ᵐ[μ]
        (fun ω => D ω * I ω - p * I ω) := by
    filter_upwards [] with ω
    by_cases hω : ω ∈ s
    · have hp : propensity μ D G ω = p :=
        propensity_eq_cellShare_of_mem μ D G hω
      simp [I, Set.indicator, hω, hp, p]
    · simp [I, Set.indicator, hω]
  have hInt :
      ∫ ω, (D ω - propensity μ D G ω) * I ω ∂μ =
        ∫ ω, D ω * I ω ∂μ - ∫ ω, p * I ω ∂μ := by
    calc
      ∫ ω, (D ω - propensity μ D G ω) * I ω ∂μ =
          ∫ ω, D ω * I ω - p * I ω ∂μ := integral_congr_ae h_ae
      _ = ∫ ω, D ω * I ω ∂μ - ∫ ω, p * I ω ∂μ :=
          integral_sub hDInt hpIInt
  have hIint : ∫ ω, I ω ∂μ = cellMass μ G g := by
    simpa [I, s] using integral_cell_indicator_one_eq_cellMass μ G G_meas g
  have hpInt : ∫ ω, p * I ω ∂μ = p * cellMass μ G g := by
    calc
      ∫ ω, p * I ω ∂μ = p * ∫ ω, I ω ∂μ := integral_const_mul p I
      _ = p * cellMass μ G g := by rw [hIint]
  have hshare : p * cellMass μ G g = ∫ ω, D ω * I ω ∂μ := by
    simpa [p, I, s, cellShare, cellMass] using
      (CellBridge.cellMean_mul_cellMass μ D G G_meas g)
  change ∫ ω, (D ω - propensity μ D G ω) * I ω ∂μ = 0
  rw [hInt, hpInt, hshare]
  ring

/-- The outcome residual is orthogonal to each cell indicator. -/
theorem residY_cell_orthogonal {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [Fintype 𝒢] [DecidableEq 𝒢] [MeasurableSpace 𝒢]
    [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (G : Ω → 𝒢)
    (G_meas : Measurable G) (Y_memLp : MemLp Y 2 μ) (g : 𝒢) :
    ∫ ω, (Y ω - meanReg μ Y G ω)
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ = 0 := by
  let s : Set Ω := {ω | G ω = g}
  let I : Ω → ℝ := fun ω => Set.indicator s (fun _ => (1 : ℝ)) ω
  let m : ℝ := (∫ ω, Y ω * I ω ∂μ) / cellMass μ G g
  have hI_mem : MemLp I 2 μ := by
    simpa [I, s] using indicator_cell_memLp μ G G_meas g
  have hYInt : Integrable (fun ω => Y ω * I ω) μ :=
    Y_memLp.integrable_mul hI_mem
  have hmIInt : Integrable (fun ω => m * I ω) μ :=
    (hI_mem.const_mul m).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have h_ae :
      (fun ω => (Y ω - meanReg μ Y G ω) * I ω) =ᵐ[μ]
        (fun ω => Y ω * I ω - m * I ω) := by
    filter_upwards [] with ω
    by_cases hω : ω ∈ s
    · have hm : meanReg μ Y G ω = m := by
        simpa [m, I, s] using meanReg_eq_cellMean_of_mem μ Y G hω
      simp [I, Set.indicator, hω, hm, m]
    · simp [I, Set.indicator, hω]
  have hInt :
      ∫ ω, (Y ω - meanReg μ Y G ω) * I ω ∂μ =
        ∫ ω, Y ω * I ω ∂μ - ∫ ω, m * I ω ∂μ := by
    calc
      ∫ ω, (Y ω - meanReg μ Y G ω) * I ω ∂μ =
          ∫ ω, Y ω * I ω - m * I ω ∂μ := integral_congr_ae h_ae
      _ = ∫ ω, Y ω * I ω ∂μ - ∫ ω, m * I ω ∂μ :=
          integral_sub hYInt hmIInt
  have hIint : ∫ ω, I ω ∂μ = cellMass μ G g := by
    simpa [I, s] using integral_cell_indicator_one_eq_cellMass μ G G_meas g
  have hmInt : ∫ ω, m * I ω ∂μ = m * cellMass μ G g := by
    calc
      ∫ ω, m * I ω ∂μ = m * ∫ ω, I ω ∂μ := integral_const_mul m I
      _ = m * cellMass μ G g := by rw [hIint]
  have hmean : m * cellMass μ G g = ∫ ω, Y ω * I ω ∂μ := by
    simpa [m, I, s, cellMass, CellBridge.cellMean] using
      (CellBridge.cellMean_mul_cellMass μ Y G G_meas g)
  change ∫ ω, (Y ω - meanReg μ Y G ω) * I ω ∂μ = 0
  rw [hInt, hmInt, hmean]
  ring

/-- The observed outcome `Y = D · Y1 + (1 − D) · Y0` is in `MemLp 2 μ`
under consistency, binary treatment, and `MemLp 2 μ` assumptions for both
potential outcomes. The pointwise bound
`|Y| ≤ |Y0| + |Y1|` (a.e.) plus closure of `MemLp 2` under sums gives
the result. Stated separately because the bridge theorem takes
`Y_memLp` as a hypothesis but downstream consumers (e.g. tests) may
need to derive it. -/
theorem Y_memLp_of_consistency {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    {D Y Y0 Y1 : Ω → ℝ}
    (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (Y0_memLp : MemLp Y0 2 μ) (Y1_memLp : MemLp Y1 2 μ)
  (consis : Y =ᵐ[μ] fun ω => D ω * Y1 ω + (1 - D ω) * Y0 ω) :
    MemLp Y 2 μ := by
  let s1 : Set Ω := D ⁻¹' ({(1 : ℝ)} : Set ℝ)
  let s0 : Set Ω := D ⁻¹' ({(0 : ℝ)} : Set ℝ)
  have hYeq :
      (fun ω => Set.indicator s1 Y1 ω + Set.indicator s0 Y0 ω)
        =ᵐ[μ] (fun ω => D ω * Y1 ω + (1 - D ω) * Y0 ω) := by
    filter_upwards [D_binary] with ω hD
    rcases hD with hD0 | hD1
    · simp [s1, s0, hD0]
    · simp [s1, s0, hD1]
  have h_mem :
      MemLp (fun ω => Set.indicator s1 Y1 ω + Set.indicator s0 Y0 ω) 2 μ := by
    have hD1_meas : MeasurableSet s1 := by
      simpa [s1] using D_meas (measurableSet_singleton (1 : ℝ))
    have hD0_meas : MeasurableSet s0 := by
      simpa [s0] using D_meas (measurableSet_singleton (0 : ℝ))
    exact (Y1_memLp.indicator hD1_meas).add (Y0_memLp.indicator hD0_meas)
  have h_mem' : MemLp (fun ω => D ω * Y1 ω + (1 - D ω) * Y0 ω) 2 μ := by
    exact (memLp_congr_ae hYeq).1 h_mem
  exact (memLp_congr_ae consis).2 h_mem'


end CellHelpers

end Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition
