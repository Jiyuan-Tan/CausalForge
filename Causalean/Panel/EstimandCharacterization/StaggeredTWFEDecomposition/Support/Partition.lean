/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021) Layer B: residualization witnesses

Builds the cohort + period residualization witnesses for `D` and `Y`
against `panelClass`. The orthogonality field is discharged by combining
per-axis orthogonality (`Support/Orthogonality.lean`) with the
`integral_mul_panelClass_eq_zero_of_axes` lemma in `Support/Integrals.lean`.
-/

import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.Support.Orthogonality
/-! # Goodman-Bacon Residualization Witnesses

This file constructs the residualization witnesses for treatment and outcome
after projecting on cohort and period cells in a balanced panel. These
witnesses package the fitted component, the residual component, square
integrability, decomposition, and orthogonality conditions used by the
Goodman-Bacon bridge. -/

namespace Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

variable {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢] [DecidableEq 𝒢]
  [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢] {T : ℕ}

/-- **B3. Residualization witness for `D`** against `panelClass`. With
`VH := panelPropensity μ D G T_rv` and `Vtilde ω := D ω - panelPropensity ω`,
this packages the four witness obligations:

* `VH_mem` — `panelPropensity` lies in `panelClass` (by
  `panelPropensity_mem_panelClass`).
* `Vtilde_memLp` — `D - panelPropensity ∈ MemLp 2 μ` (D is bounded; class
  members are in `MemLp 2`).
* `decomp` — `D = panelPropensity + (D - panelPropensity)` pointwise.
* `orthogonal` — `∫ (D - panelPropensity) · h dμ = 0` for every
  `h ∈ panelClass`. Discharged by combining
  `residD_cohort_orthogonal` and `residD_period_orthogonal` via
  `integral_mul_panelClass_eq_zero_of_axes`. **Requires the balanced-cell
  hypothesis `B_balanced`.** -/
noncomputable def residWitnessD_panel
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (B_balanced : IsBalancedPanelLaw μ G T_rv) :
    ResidualizationWitness μ (panelClass μ G T_rv G_meas T_meas) D := by
  let H := panelClass μ G T_rv G_meas T_meas
  have hVH_mem : H.mem (panelPropensity μ D G T_rv) :=
    panelPropensity_mem_panelClass μ D G T_rv G_meas T_meas
  have hD_mem : MemLp D 2 μ := by
    have hD_bounded : ∀ᵐ ω ∂μ, D ω ∈ Set.Icc (-1 : ℝ) 1 := by
      filter_upwards [D_binary] with ω hD
      rcases hD with hD0 | hD1
      · simp [hD0]
      · simp [hD1]
    exact memLp_of_bounded (f := D) hD_bounded
      (D_meas.aestronglyMeasurable) (2 : ENNReal)
  have hVtilde_memLp : MemLp (fun ω => D ω - panelPropensity μ D G T_rv ω) 2 μ :=
    hD_mem.sub (H.memLp hVH_mem)
  refine
    { VH := panelPropensity μ D G T_rv
    , Vtilde := fun ω => D ω - panelPropensity μ D G T_rv ω
    , VH_mem := hVH_mem
    , Vtilde_memLp := hVtilde_memLp
    , decomp := by
        filter_upwards [] with ω
        change D ω = panelPropensity μ D G T_rv ω
          + (D ω - panelPropensity μ D G T_rv ω)
        ring
    , orthogonal := by
        intro h hh
        rcases hh with ⟨cG, cT, hh_eq⟩
        have hVtilde := hVtilde_memLp
        calc
          ∫ ω, (D ω - panelPropensity μ D G T_rv ω) * h ω ∂μ
              = ∫ ω, (D ω - panelPropensity μ D G T_rv ω)
                * ((∑ g, cG g
                  * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω)
                  + (∑ t, cT t
                    * Set.indicator {ω' | T_rv ω' = t}
                        (fun _ => (1 : ℝ)) ω)) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [hh_eq] with ω hω
            rw [hω]
          _ = 0 :=
            integral_mul_panelClass_eq_zero_of_axes μ
              (fun ω => D ω - panelPropensity μ D G T_rv ω)
              G T_rv G_meas T_meas hVtilde cG cT
              (fun g => residD_cohort_orthogonal μ D G T_rv G_meas T_meas
                D_meas D_binary B_balanced g)
              (fun t => residD_period_orthogonal μ D G T_rv G_meas T_meas
                D_meas D_binary B_balanced t)
    }

/-- **B3. Residualization witness for `Y`** against `panelClass`. -/
noncomputable def residWitnessY_panel
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (Y_memLp : MemLp Y 2 μ)
    (B_balanced : IsBalancedPanelLaw μ G T_rv) :
    ResidualizationWitness μ (panelClass μ G T_rv G_meas T_meas) Y := by
  let H := panelClass μ G T_rv G_meas T_meas
  have hVH_mem : H.mem (panelMeanReg μ Y G T_rv) :=
    panelMeanReg_mem_panelClass μ Y G T_rv G_meas T_meas
  have hVtilde_memLp : MemLp (fun ω => Y ω - panelMeanReg μ Y G T_rv ω) 2 μ :=
    Y_memLp.sub (H.memLp hVH_mem)
  refine
    { VH := panelMeanReg μ Y G T_rv
    , Vtilde := fun ω => Y ω - panelMeanReg μ Y G T_rv ω
    , VH_mem := hVH_mem
    , Vtilde_memLp := hVtilde_memLp
    , decomp := by
        filter_upwards [] with ω
        change Y ω = panelMeanReg μ Y G T_rv ω
          + (Y ω - panelMeanReg μ Y G T_rv ω)
        ring
    , orthogonal := by
        intro h hh
        rcases hh with ⟨cG, cT, hh_eq⟩
        have hVtilde := hVtilde_memLp
        calc
          ∫ ω, (Y ω - panelMeanReg μ Y G T_rv ω) * h ω ∂μ
              = ∫ ω, (Y ω - panelMeanReg μ Y G T_rv ω)
                * ((∑ g, cG g
                  * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω)
                  + (∑ t, cT t
                    * Set.indicator {ω' | T_rv ω' = t}
                        (fun _ => (1 : ℝ)) ω)) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [hh_eq] with ω hω
            rw [hω]
          _ = 0 :=
            integral_mul_panelClass_eq_zero_of_axes μ
              (fun ω => Y ω - panelMeanReg μ Y G T_rv ω)
              G T_rv G_meas T_meas hVtilde cG cT
              (fun g => residY_cohort_orthogonal μ Y G T_rv G_meas T_meas
                Y_memLp B_balanced g)
              (fun t => residY_period_orthogonal μ Y G T_rv G_meas T_meas
                Y_memLp B_balanced t)
    }

end Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition
