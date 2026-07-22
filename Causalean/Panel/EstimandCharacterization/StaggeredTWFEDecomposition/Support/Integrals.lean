/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021) Layer B: cell integral helpers

Integral identities for cohort and period cells used by the saturated
cohort-plus-period bridge. Mirrors `OLSWeightDecomposition/Support/Integrals.lean` but
with two axes (cohort and period).

The headline identity here is `integral_mul_panelClass_eq_zero_of_axes`:
if a square-integrable residual is orthogonal to every cohort indicator
*and* to every period indicator, it is orthogonal to every member of
`panelClass`. This decouples per-axis orthogonality (proved in
`Support/Orthogonality.lean`) from the witness-level orthogonality
obligation.
-/

import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.Support.Basic

/-!
Proves integral identities for the staggered-TWFE bridge. The module supplies
MemLp, indicator, and orthogonality facts used to transport finite weighted
decompositions into the population setting.
-/

namespace Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

variable {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢] [DecidableEq 𝒢]
  [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢] {T : ℕ}

section CellHelpers

/-! #### Indicator `MemLp 2` lemmas -/

/-- Cohort indicator `𝟙{G = g}` is in `MemLp 2 μ` (bounded + finite measure). -/
theorem indicator_cohort_memLp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → 𝒢) (G_meas : Measurable G) (g : 𝒢) :
    MemLp (fun ω => Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω) 2 μ := by
  exact CellBridge.indicator_cell_memLp μ G G_meas g

/-- Period indicator `𝟙{T_rv = t}` is in `MemLp 2 μ`. -/
theorem indicator_period_memLp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T_rv : Ω → Fin T) (T_meas : Measurable T_rv) (t : Fin T) :
    MemLp (fun ω => Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω) 2 μ := by
  exact CellBridge.indicator_cell_memLp μ T_rv T_meas t

/-- Joint cell indicator `𝟙{G=g ∧ T_rv=t}` is in `MemLp 2 μ`. -/
theorem indicator_panel_cell_memLp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv) (g : 𝒢) (t : Fin T) :
    MemLp (fun ω => Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
            (fun _ => (1 : ℝ)) ω) 2 μ := by
  -- The cell `{G = g ∧ T_rv = t}` is the intersection of two measurable sets.
  let sG : Set Ω := {ω | G ω = g}
  let sT : Set Ω := {ω | T_rv ω = t}
  have hG : MeasurableSet sG := G_meas (measurableSet_singleton g)
  have hT : MeasurableSet sT := T_meas (measurableSet_singleton t)
  have hcell : MeasurableSet (sG ∩ sT) := hG.inter hT
  have hEq : ({ω | G ω = g ∧ T_rv ω = t} : Set Ω) = sG ∩ sT := by
    ext ω; simp [sG, sT]
  rw [hEq]
  exact (memLp_const (μ := μ) (1 : ℝ)).indicator hcell

/-! #### Integral-of-indicator-equals-mass lemmas -/

/-- `∫ 𝟙{G = g} dμ = cohortMass μ G g`. -/
theorem integral_cohort_indicator_one_eq_cohortMass
    (μ : Measure Ω) (G : Ω → 𝒢) (G_meas : Measurable G) (g : 𝒢) :
    ∫ ω, Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ =
      cohortMass μ G g := by
  simpa [cohortMass] using
    (CellBridge.integral_cell_indicator_one_eq_cellMass μ G G_meas g)

/-- `∫ 𝟙{T_rv = t} dμ = periodMass μ T_rv t`. -/
theorem integral_period_indicator_one_eq_periodMass
    (μ : Measure Ω) (T_rv : Ω → Fin T) (T_meas : Measurable T_rv) (t : Fin T) :
    ∫ ω, Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ =
      periodMass μ T_rv t := by
  simpa [periodMass] using
    (CellBridge.integral_cell_indicator_one_eq_cellMass μ T_rv T_meas t)

/-- `∫ 𝟙{G = g ∧ T_rv = t} dμ = cellMass μ G T_rv g t`. -/
theorem integral_panel_cell_indicator_one_eq_cellMass
    (μ : Measure Ω) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv) (g : 𝒢) (t : Fin T) :
    ∫ ω, Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
            (fun _ => (1 : ℝ)) ω ∂μ =
      cellMass μ G T_rv g t := by
  let sG : Set Ω := {ω | G ω = g}
  let sT : Set Ω := {ω | T_rv ω = t}
  have hG : MeasurableSet sG := G_meas (measurableSet_singleton g)
  have hT : MeasurableSet sT := T_meas (measurableSet_singleton t)
  have hcell : MeasurableSet (sG ∩ sT) := hG.inter hT
  have hEq : ({ω | G ω = g ∧ T_rv ω = t} : Set Ω) = sG ∩ sT := by
    ext ω; simp [sG, sT]
  change (∫ ω, Set.indicator (sG ∩ sT) (1 : Ω → ℝ) ω ∂μ) = cellMass μ G T_rv g t
  rw [MeasureTheory.integral_indicator_one hcell]
  rw [← hEq]
  simp [Measure.real, cellMass, CellBridge.jointCellMass]

/-! #### div–mul–mass lemmas -/

/-- Defining identity for `cohortBarD`: dividing by cohort mass and
multiplying back recovers the cohort-indicator-weighted integral.
On zero-mass cohorts both sides are zero (a.e.-vanishing indicator). -/
theorem cohort_integral_div_mul_cohortMass
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (G : Ω → 𝒢) (G_meas : Measurable G) (g : 𝒢) :
    ((∫ ω, F ω * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ)
        / cohortMass μ G g) * cohortMass μ G g =
      ∫ ω, F ω * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ := by
  simpa [cohortMass] using
    (CellBridge.cell_integral_div_mul_cellMass μ F G G_meas g)

/-- Period analogue. -/
theorem period_integral_div_mul_periodMass
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (T_rv : Ω → Fin T) (T_meas : Measurable T_rv) (t : Fin T) :
    ((∫ ω, F ω * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ)
        / periodMass μ T_rv t) * periodMass μ T_rv t =
      ∫ ω, F ω * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ := by
  simpa [periodMass] using
    (CellBridge.cell_integral_div_mul_cellMass μ F T_rv T_meas t)

/-- Cell analogue (joint cohort × period cell). -/
theorem panel_cell_integral_div_mul_cellMass
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv) (g : 𝒢) (t : Fin T) :
    ((∫ ω, F ω * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
              (fun _ => (1 : ℝ)) ω ∂μ)
        / cellMass μ G T_rv g t) * cellMass μ G T_rv g t =
      ∫ ω, F ω * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
              (fun _ => (1 : ℝ)) ω ∂μ := by
  let s : Set Ω := {ω | G ω = g ∧ T_rv ω = t}
  let A : ℝ := ∫ ω, F ω * Set.indicator s (fun _ => (1 : ℝ)) ω ∂μ
  have _hs_meas : MeasurableSet s := by
    have hG : MeasurableSet {ω : Ω | G ω = g} :=
      G_meas (measurableSet_singleton g)
    have hT : MeasurableSet {ω : Ω | T_rv ω = t} :=
      T_meas (measurableSet_singleton t)
    simpa [s, Set.inter_def] using hG.inter hT
  have hs_top : μ s ≠ ⊤ := by
    exact ne_of_lt <| lt_of_le_of_lt (measure_mono (Set.subset_univ s))
      (by simp [IsProbabilityMeasure.measure_univ])
  by_cases hmass : cellMass μ G T_rv g t = 0
  · have hs_zero : μ s = 0 := by
      have hzero : (μ s).toReal = 0 := by simpa [cellMass, s] using hmass
      rcases (ENNReal.toReal_eq_zero_iff (μ s)).1 hzero with h0 | htop
      · exact h0
      · exact False.elim (hs_top htop)
    have h_not_mem : ∀ᵐ ω ∂μ, ω ∉ s := by
      rw [MeasureTheory.ae_iff]
      simpa using hs_zero
    have h_ae :
        (fun ω => F ω * Set.indicator s (fun _ => (1 : ℝ)) ω) =ᵐ[μ] 0 := by
      filter_upwards [h_not_mem] with ω hω
      simp [Set.indicator, hω]
    have hA : A = 0 := by
      simpa [A] using (integral_eq_zero_of_ae h_ae)
    simp [cellMass, s, A, hA]
  · have hAdef :
        A = ∫ ω, F ω
          * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
              (fun _ => (1 : ℝ)) ω ∂μ := by
      simp [A, s]
    rw [hAdef.symm]
    field_simp [hmass]

/-! #### `cohortBarD` defining identity (cleanup form) -/

/-- `cohortBarD g · cohortMass g = ∫ D · 𝟙{G=g} dμ`. -/
theorem cohortBarD_mul_cohortMass
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (G : Ω → 𝒢) (G_meas : Measurable G) (g : 𝒢) :
    cohortBarD μ D G g * cohortMass μ G g =
      ∫ ω, D ω * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ := by
  simpa [cohortBarD] using
    (cohort_integral_div_mul_cohortMass μ D G G_meas g)

/-! #### Constant-on-cell identities for `panelPropensity` and `panelMeanReg`

On a cohort-period cell `{G = g ∧ T_rv = t}`, the propensity and the
mean-regression evaluate to a single closed-form constant. These are the
`propensity_eq_cellShare_of_mem` / `meanReg_eq_cellMean_of_mem` analogues
for the two-axis case. -/

/-- The "panel-propensity hat" `pHat g t = cohortBarD g + cT t` where
`cT t := (∫ D · 𝟙{T_rv=t} dμ) / periodMass t - ∫ D dμ`. -/
noncomputable def panelPropensityHat
    (μ : Measure Ω) (D : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (g : 𝒢) (t : Fin T) : ℝ :=
  cohortBarD μ D G g
    + ((∫ ω', D ω' * Set.indicator {ω' | T_rv ω' = t}
              (fun _ => (1 : ℝ)) ω' ∂μ)
        / periodMass μ T_rv t
        - ∫ ω', D ω' ∂μ)

/-- "panel-meanReg hat" analogue for `Y`. -/
noncomputable def panelMeanRegHat
    (μ : Measure Ω) (Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (g : 𝒢) (t : Fin T) : ℝ :=
  ((∫ ω', Y ω' * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω' ∂μ)
      / cohortMass μ G g)
    + ((∫ ω', Y ω' * Set.indicator {ω' | T_rv ω' = t}
            (fun _ => (1 : ℝ)) ω' ∂μ)
        / periodMass μ T_rv t
        - ∫ ω', Y ω' ∂μ)

/-- On the cell `{G = g ∧ T_rv = t}`, `panelPropensity` evaluates to
`panelPropensityHat g t`. Pointwise (no a.e. needed) by single-cell
membership selecting one term in each finite sum. -/
theorem panelPropensity_eq_hat_of_mem
    (μ : Measure Ω) (D : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    {g : 𝒢} {t : Fin T} {ω : Ω} (hG : G ω = g) (hT : T_rv ω = t) :
    panelPropensity μ D G T_rv ω = panelPropensityHat μ D G T_rv g t := by
  unfold panelPropensity panelPropensityHat
  rw [Finset.sum_eq_single g]
  · rw [Finset.sum_eq_single t]
    · simp [hG, hT]
    · intro b _ hbt
      simp [Set.indicator, hT, hbt.symm]
    · intro ht
      simp at ht
  · intro b _ hbg
    simp [Set.indicator, hG, hbg.symm]
  · intro hg
    simp at hg

/-- On the cell `{G = g ∧ T_rv = t}`, `panelMeanReg` evaluates to
`panelMeanRegHat g t`. -/
theorem panelMeanReg_eq_hat_of_mem
    (μ : Measure Ω) (Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    {g : 𝒢} {t : Fin T} {ω : Ω} (hG : G ω = g) (hT : T_rv ω = t) :
    panelMeanReg μ Y G T_rv ω = panelMeanRegHat μ Y G T_rv g t := by
  unfold panelMeanReg panelMeanRegHat
  rw [Finset.sum_eq_single g]
  · rw [Finset.sum_eq_single t]
    · simp [hG, hT]
    · intro b _ hbt
      simp [Set.indicator, hT, hbt.symm]
    · intro ht
      simp at ht
  · intro b _ hbg
    simp [Set.indicator, hG, hbg.symm]
  · intro hg
    simp at hg

/-! #### Per-axis to whole-class orthogonality -/

/-- If a square-integrable residual `V` is orthogonal to every cohort
indicator and to every period indicator, then it is orthogonal to every
member of `panelClass`. -/
theorem integral_mul_panelClass_eq_zero_of_axes
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (V_memLp : MemLp V 2 μ)
    (cG : 𝒢 → ℝ) (cT : Fin T → ℝ)
    (hCohort : ∀ g,
      ∫ ω, V ω * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ = 0)
    (hPeriod : ∀ t,
      ∫ ω, V ω * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ = 0) :
    ∫ ω, V ω
        * ((∑ g, cG g
            * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω)
            + (∑ t, cT t
              * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω)) ∂μ
      = 0 := by
  exact CellBridge.integral_mul_twoAxisIndicatorSpan_eq_zero_of_axes
    μ V G T_rv G_meas T_meas V_memLp cG cT hCohort hPeriod

/-! #### Integral-as-sum-over-cells identities -/

/-- Integrate by summing over cohort cells:
`∫ F dμ = ∑_g ∫ F · 𝟙{G = g} dμ`. -/
theorem integral_eq_sum_cohort
    (μ : Measure Ω) (F : Ω → ℝ) (G : Ω → 𝒢)
    (G_meas : Measurable G) (F_int : Integrable F μ) :
    ∫ ω, F ω ∂μ =
      ∑ g, ∫ ω, F ω
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ := by
  exact CellBridge.integral_eq_sum_cell μ F G G_meas F_int

/-- Integrate by summing over period cells. -/
theorem integral_eq_sum_period
    (μ : Measure Ω) (F : Ω → ℝ) (T_rv : Ω → Fin T)
    (T_meas : Measurable T_rv) (F_int : Integrable F μ) :
    ∫ ω, F ω ∂μ =
      ∑ t, ∫ ω, F ω
        * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ := by
  exact CellBridge.integral_eq_sum_cell μ F T_rv T_meas F_int

/-- Integrate by summing over cohort × period cells. -/
theorem integral_eq_sum_panel_cell
    (μ : Measure Ω) (F : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (F_int : Integrable F μ) :
    ∫ ω, F ω ∂μ =
      ∑ g, ∑ t, ∫ ω, F ω
        * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
            (fun _ => (1 : ℝ)) ω ∂μ := by
  let term : 𝒢 × Fin T → Ω → ℝ := fun gt ω =>
    F ω * Set.indicator {ω' | G ω' = gt.1 ∧ T_rv ω' = gt.2}
      (fun _ => (1 : ℝ)) ω
  have hterm_int :
      ∀ gt ∈ ((Finset.univ : Finset 𝒢).product (Finset.univ : Finset (Fin T))),
        Integrable (term gt) μ := by
    intro gt _
    have hG : MeasurableSet {ω : Ω | G ω = gt.1} :=
      G_meas (measurableSet_singleton gt.1)
    have hT : MeasurableSet {ω : Ω | T_rv ω = gt.2} :=
      T_meas (measurableSet_singleton gt.2)
    have hcell : MeasurableSet ({ω : Ω | G ω = gt.1} ∩ {ω : Ω | T_rv ω = gt.2}) :=
      hG.inter hT
    have hEq :
        term gt = fun ω =>
          Set.indicator {ω' | G ω' = gt.1 ∧ T_rv ω' = gt.2} F ω := by
      funext ω
      by_cases hω : G ω = gt.1 ∧ T_rv ω = gt.2
      · simp [term, Set.indicator, hω]
      · simp [term, Set.indicator, hω]
    rw [hEq]
    have hcellSet : MeasurableSet {ω : Ω | G ω = gt.1 ∧ T_rv ω = gt.2} := by
      simpa [Set.inter_def] using hcell
    exact F_int.indicator hcellSet
  have hsum_ind : ∀ ω, (∑ g, ∑ t,
      Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
        (fun _ => (1 : ℝ)) ω) = 1 := by
    intro ω
    rw [Finset.sum_eq_single (G ω)]
    · rw [Finset.sum_eq_single (T_rv ω)]
      · simp
      · intro b _ hb
        have hne : ¬ T_rv ω = b := fun h => hb h.symm
        simp [Set.indicator, hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    · intro b _ hb
      have hne : ¬ G ω = b := fun h => hb h.symm
      simp [Set.indicator, hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  have hsum_product : ∀ ω,
      ((Finset.univ : Finset 𝒢).product (Finset.univ : Finset (Fin T))).sum
        (fun gt => term gt ω) =
      ∑ g, ∑ t, F ω
        * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
            (fun _ => (1 : ℝ)) ω := by
    intro ω
    simpa [term] using
      (Finset.sum_product'
        (Finset.univ : Finset 𝒢) (Finset.univ : Finset (Fin T))
        (fun g t => F ω
          * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
              (fun _ => (1 : ℝ)) ω))
  calc
    ∫ ω, F ω ∂μ =
        ∫ ω, F ω
          * (∑ g, ∑ t,
              Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
                (fun _ => (1 : ℝ)) ω) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [] with ω
      simp [hsum_ind ω]
    _ = ∫ ω, ((Finset.univ : Finset 𝒢).product (Finset.univ : Finset (Fin T))).sum
          (fun gt => term gt ω) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [] with ω
      rw [hsum_product]
      simp [Finset.mul_sum]
    _ = ((Finset.univ : Finset 𝒢).product (Finset.univ : Finset (Fin T))).sum
          (fun gt => ∫ ω, term gt ω ∂μ) := by
      simpa using
        (MeasureTheory.integral_finset_sum
          ((Finset.univ : Finset 𝒢).product (Finset.univ : Finset (Fin T)))
          (f := term) hterm_int)
    _ = ∑ g, ∑ t, ∫ ω, F ω
        * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
            (fun _ => (1 : ℝ)) ω ∂μ := by
      simpa [term] using
        (Finset.sum_product'
          (Finset.univ : Finset 𝒢) (Finset.univ : Finset (Fin T))
          (fun g t => ∫ ω, F ω
            * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
                (fun _ => (1 : ℝ)) ω ∂μ))

end CellHelpers

end Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition
