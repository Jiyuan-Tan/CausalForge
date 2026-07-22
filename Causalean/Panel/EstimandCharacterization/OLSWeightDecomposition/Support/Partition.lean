/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Słoczyński (2022): partition and residualization witnesses

Builds the finite partition and residualization witnesses for the
saturated-control probability-space bridge.
-/

import Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition.FinitePartition
import Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition.Support.Orthogonality

/-! # Słoczyński partition bridge

This file constructs the finite partition and residualization witnesses used to
connect saturated-control population objects with Słoczyński's finite-partition
OLS weight algebra. The definition `partitionOf` packages measurable binary
treatment and a finite cell classifier into the `FinitePartition` consumed by
the algebraic theorems, while `partitionOf_p_eq_eventCondExp` and
`partitionOf_tau_eq_eventCondExp` certify that its treated shares and
treatment effects are shared population cell means. The definitions
`residWitnessD` and `residWitnessY` build the residualization witnesses for the
treatment and observed outcome variables against the saturated control class. -/

namespace Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

/-- Measurable binary treatment data with a finite cell classifier and positive
saturated-overlap denominator determine the finite Słoczyński partition of cell
masses, treated shares, and within-cell treatment effects.

The resulting partition uses the classifier's cell masses, within-cell treated
shares, and within-cell averages of the treated-minus-control potential-outcome
contrast. -/
noncomputable def partitionOf {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢]
    [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D Y0 Y1 : Ω → ℝ) (G : Ω → 𝒢)
    (G_meas : Measurable G)
    (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (overlap : 0 < ∑ g, cellMass μ G g
                  * (cellShare μ D G g * (1 - cellShare μ D G g))) :
    FinitePartition 𝒢 :=
  ⟨ cellMass μ G
  , cellShare μ D G
  , cellTau μ Y0 Y1 G
  , fun g => cellMass_nonneg μ G g
  , cellMass_sum_eq_one μ G G_meas
  , fun g => cellShare_nonneg μ D G D_meas D_binary g
  , fun g => cellShare_le_one μ D G G_meas D_meas D_binary g
  , overlap ⟩

/-- **Population-cell certificate for `partitionOf`.** The treated share `p_g` of
the Słoczyński partition is the shared population cell mean `E[D | G = g]` (via
`eventCondExp`). -/
theorem partitionOf_p_eq_eventCondExp {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [Fintype 𝒢] [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D Y0 Y1 : Ω → ℝ) (G : Ω → 𝒢) (G_meas : Measurable G) (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (overlap : 0 < ∑ g, cellMass μ G g
                  * (cellShare μ D G g * (1 - cellShare μ D G g))) (g : 𝒢) :
    (partitionOf μ D Y0 Y1 G G_meas D_meas D_binary overlap).p g
      = Causalean.PO.eventCondExp μ {ω | G ω = g} D :=
  cellShare_eq_eventCondExp μ D G G_meas g

/-- **Population-cell certificate for `partitionOf`.** The cell treatment effect
`τ_g` of the Słoczyński partition is the shared population potential-outcome
contrast `E[Y(1) − Y(0) | G = g]` (via `eventCondExp`), so the overlap-weighted
estimand is built from genuine potential-outcome cell means. -/
theorem partitionOf_tau_eq_eventCondExp {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [Fintype 𝒢] [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D Y0 Y1 : Ω → ℝ) (G : Ω → 𝒢) (G_meas : Measurable G) (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (overlap : 0 < ∑ g, cellMass μ G g
                  * (cellShare μ D G g * (1 - cellShare μ D G g))) (g : 𝒢) :
    (partitionOf μ D Y0 Y1 G G_meas D_meas D_binary overlap).τ g
      = Causalean.PO.eventCondExp μ {ω | G ω = g} (fun ω => Y1 ω - Y0 ω) :=
  cellTau_eq_eventCondExp μ Y0 Y1 G G_meas g

/-- Residualization witness for the treatment variable `D`.

With `VH := propensity μ D G` and
`Vtilde ω := D ω − propensity μ D G ω`, this packages the four
witness obligations:

* `VH_mem` — `propensity μ D G ∈ saturatedClass μ G` (by
  `propensity_mem_saturatedClass`).
* `Vtilde_memLp` — `D − propensity` is in `MemLp 2 μ` (boundedness +
  finite measure).
* `decomp` — `D = propensity + (D − propensity)` pointwise.
* `orthogonal` — `∫ (D − propensity) · h dμ = 0` for every
  `h ∈ saturatedClass μ G`. Reduces per cell to the defining identity
  of `cellShare`. -/
noncomputable def residWitnessD {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢]
    [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (G : Ω → 𝒢)
    (G_meas : Measurable G) (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) :
    ResidualizationWitness μ (saturatedClass μ G G_meas) D := by
  refine
    { VH := propensity μ D G
    , Vtilde := fun ω => D ω - propensity μ D G ω
    , VH_mem := propensity_mem_saturatedClass μ D G G_meas
    , Vtilde_memLp := by
        have hD_mem : MemLp D 2 μ := by
          have hD_bounded : ∀ᵐ ω ∂μ, D ω ∈ Set.Icc (-1 : ℝ) 1 := by
            filter_upwards [D_binary] with ω hD
            rcases hD with hD0 | hD1
            · simp [hD0]
            · simp [hD1]
          exact memLp_of_bounded (f := D) hD_bounded (D_meas.aestronglyMeasurable) (2 : ENNReal)
        exact hD_mem.sub ((saturatedClass μ G G_meas).memLp (propensity_mem_saturatedClass μ D G G_meas))
      , decomp := by
          filter_upwards [] with ω
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      , orthogonal := by
          intro h hh
          rcases hh with ⟨c, hc⟩
          have hD_mem : MemLp D 2 μ := by
            have hD_bounded : ∀ᵐ ω ∂μ, D ω ∈ Set.Icc (-1 : ℝ) 1 := by
              filter_upwards [D_binary] with ω hD
              rcases hD with hD0 | hD1
              · simp [hD0]
              · simp [hD1]
            exact memLp_of_bounded (f := D) hD_bounded
              (D_meas.aestronglyMeasurable) (2 : ENNReal)
          have hV_mem : MemLp (fun ω => D ω - propensity μ D G ω) 2 μ :=
            hD_mem.sub
              ((saturatedClass μ G G_meas).memLp
                (propensity_mem_saturatedClass μ D G G_meas))
          calc
            ∫ ω, (D ω - propensity μ D G ω) * h ω ∂μ =
                ∫ ω, (D ω - propensity μ D G ω)
                  * (∑ g, c g
                    * Set.indicator {ω' | G ω' = g}
                      (fun _ => (1 : ℝ)) ω) ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards [hc] with ω hω
              rw [hω]
            _ = 0 :=
              integral_mul_saturated_eq_zero_of_cell μ
                (fun ω => D ω - propensity μ D G ω) G G_meas hV_mem c
                (fun g => residD_cell_orthogonal μ D G G_meas D_meas D_binary g)
      }

/-- Residualization witness for the outcome variable `Y`.

With `VH := meanReg μ Y G`
and `Vtilde ω := Y ω − meanReg μ Y G ω`, the witness obligations are as for
`residWitnessD`, with `meanReg_mem_saturatedClass` discharging
`VH_mem` and the per-cell mean identity discharging orthogonality. -/
noncomputable def residWitnessY {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢]
    [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (G : Ω → 𝒢)
    (G_meas : Measurable G) (Y_memLp : MemLp Y 2 μ) :
    ResidualizationWitness μ (saturatedClass μ G G_meas) Y := by
  refine
    { VH := meanReg μ Y G
    , Vtilde := fun ω => Y ω - meanReg μ Y G ω
    , VH_mem := meanReg_mem_saturatedClass μ Y G G_meas
    , Vtilde_memLp := by
        exact Y_memLp.sub ((saturatedClass μ G G_meas).memLp (meanReg_mem_saturatedClass μ Y G G_meas))
      , decomp := by
          filter_upwards [] with ω
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      , orthogonal := by
          intro h hh
          rcases hh with ⟨c, hc⟩
          have hV_mem : MemLp (fun ω => Y ω - meanReg μ Y G ω) 2 μ :=
            Y_memLp.sub
              ((saturatedClass μ G G_meas).memLp
                (meanReg_mem_saturatedClass μ Y G G_meas))
          calc
            ∫ ω, (Y ω - meanReg μ Y G ω) * h ω ∂μ =
                ∫ ω, (Y ω - meanReg μ Y G ω)
                  * (∑ g, c g
                    * Set.indicator {ω' | G ω' = g}
                      (fun _ => (1 : ℝ)) ω) ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards [hc] with ω hω
              rw [hω]
            _ = 0 :=
              integral_mul_saturated_eq_zero_of_cell μ
                (fun ω => Y ω - meanReg μ Y G ω) G G_meas hV_mem c
                (fun g => residY_cell_orthogonal μ Y G G_meas Y_memLp g)
      }

end Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition
