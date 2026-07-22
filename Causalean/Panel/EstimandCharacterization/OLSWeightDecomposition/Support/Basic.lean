/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Słoczyński (2022): saturated finite-cell bridge basics

Basic saturated-control class, cell statistics, and elementary bounds for
the finite-cell probability-space bridge.
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Causalean.Panel.CellBridge
import Causalean.Panel.PO.PopulationCells
/-! # Słoczyński bridge basics

This file sets up the saturated finite-cell control class and the basic cell
statistics for Słoczyński's probability-space bridge. It defines
`saturatedClass`, `cellMass`, `cellShare`, `cellTau`, `propensity`, and
`meanReg`; relates `cellShare` and `cellTau` to the shared
`eventCondExp` population-cell operator; and proves the elementary bounds
`cellMass_nonneg`, `cellMass_sum_eq_one`, `cellShare_nonneg`, and
`cellShare_le_one`. The membership lemmas `propensity_mem_saturatedClass` and
`meanReg_mem_saturatedClass` supply the saturated-control pieces used by the
residualization witnesses. -/

namespace Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

/-- Linear `L²` control class spanned, up to almost-everywhere equality, by the
finite family of cell indicators `𝟙{G = g}` for `g : 𝒢`.

Membership predicate (predicate-style, residualization_core D1 option (b)):

    f ∈ saturatedClass μ G  ↔  ∃ c : 𝒢 → ℝ,
        f =ᵐ[μ] (fun ω => ∑ g, c g · 𝟙{G ω = g}).

Closed under addition (sum the coefficient maps), scalar multiplication
(scale the coefficient map), and contains zero (take `c = 0`). Every member
is square-integrable on the finite measure `μ` because each indicator is
bounded. -/
noncomputable def saturatedClass {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢]
    [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → 𝒢) (G_meas : Measurable G) : LinearL2Class μ :=
  CellBridge.indicatorSpan μ G G_meas

/-- Cell mass `(μ {G = g}).toReal`, the probability weight of covariate cell `g`. -/
def cellMass {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : Ω → 𝒢) (g : 𝒢) : ℝ :=
  CellBridge.cellMass μ G g

/-- Cell-wise treated share, defined as the indicator-weighted integral of `D`
on covariate cell `g`, divided by `cellMass μ G g`. On zero-mass cells, the
value is `0` by Mathlib's `0/0 = 0` convention. -/
noncomputable def cellShare {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : Ω → ℝ) (G : Ω → 𝒢) (g : 𝒢) : ℝ :=
  CellBridge.cellMean μ D G g

/-- Cell-wise treatment effect `E[Y(1) − Y(0) | G = g]` in the shared
indicator-weighted cell-mean convention. Like `cellShare`, zero-mass cells
collapse to `0`. -/
noncomputable def cellTau {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) (G : Ω → 𝒢) (g : 𝒢) : ℝ :=
  CellBridge.cellMean μ (fun ω => Y1 ω - Y0 ω) G g

/-! ### Bridge to the shared population cell-mean operator

The Słoczyński bridge computes cell means with `CellBridge.cellMean` (an
indicator-weighted integral over `{G = g}` divided by the cell mass). These
lemmas identify that operator with the shared `Causalean.PO.eventCondExp`
underlying `Panel.PO.CellPartition.mean`, so the OLS cell statistics
`cellShare` / `cellTau` are the same population cell means used by the other
panel population bridges. A full `CellPartition` cannot be formed here because
the Słoczyński estimand tolerates zero-mass cells, whereas `CellPartition`
requires strictly positive cells; the identity is therefore stated at the
operator level, which needs no positivity. -/

/-- The `CellBridge` indicator-weighted cell mean equals the shared event-level
conditional expectation on the cohort cell `{G = g}`. -/
theorem cellMean_eq_eventCondExp {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) (F : Ω → ℝ) (G : Ω → 𝒢) (G_meas : Measurable G) (g : 𝒢) :
    CellBridge.cellMean μ F G g
      = Causalean.PO.eventCondExp μ {ω | G ω = g} F := by
  have hA : MeasurableSet {ω | G ω = g} := G_meas (measurableSet_singleton g)
  unfold CellBridge.cellMean Causalean.PO.eventCondExp CellBridge.cellMass
  congr 1
  rw [← MeasureTheory.integral_indicator hA]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  by_cases hω : ω ∈ {ω | G ω = g}
  · simp [Set.indicator_of_mem hω]
  · simp [Set.indicator_of_notMem hω]

/-- **OLS treated share is a shared population cell mean.**
`cellShare μ D G g = E[D | G = g]` in the shared `eventCondExp` operator. -/
theorem cellShare_eq_eventCondExp {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) (D : Ω → ℝ) (G : Ω → 𝒢) (G_meas : Measurable G) (g : 𝒢) :
    cellShare μ D G g = Causalean.PO.eventCondExp μ {ω | G ω = g} D :=
  cellMean_eq_eventCondExp μ D G G_meas g

/-- **OLS cell treatment effect is a shared population cell mean.**
`cellTau μ Y0 Y1 G g = E[Y(1) − Y(0) | G = g]` in the shared `eventCondExp`
operator — a genuine potential-outcome contrast. -/
theorem cellTau_eq_eventCondExp {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) (G : Ω → 𝒢) (G_meas : Measurable G) (g : 𝒢) :
    cellTau μ Y0 Y1 G g
      = Causalean.PO.eventCondExp μ {ω | G ω = g} (fun ω => Y1 ω - Y0 ω) :=
  cellMean_eq_eventCondExp μ (fun ω => Y1 ω - Y0 ω) G G_meas g

/-- Saturated propensity `propensity μ D G ω = cellShare μ D G (G ω)`
(pointwise, by disjointness of the `{G = g}` family). Plays the role of
`p(G(·))` and lies in `saturatedClass μ G G_meas`. -/
noncomputable def propensity {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢]
    (μ : Measure Ω) (D : Ω → ℝ) (G : Ω → 𝒢) : Ω → ℝ :=
  fun ω => ∑ g, cellShare μ D G g
    * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω

/-- Saturated mean regression `meanReg μ Y G ω` is the cell-wise
average of `Y`, evaluated at `G ω`. Plays the role of `m(G(·))` for the
outcome `Y`. Lies in `saturatedClass μ G G_meas`. -/
noncomputable def meanReg {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢]
    (μ : Measure Ω) (Y : Ω → ℝ) (G : Ω → 𝒢) : Ω → ℝ :=
  fun ω => ∑ g,
    ((∫ ω', Y ω'
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω' ∂μ)
       / cellMass μ G g)
    * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω

section CellHelpers

/-- Cell mass is nonnegative — `(μ S).toReal ≥ 0`. -/
theorem cellMass_nonneg {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : Ω → 𝒢) (g : 𝒢) :
    0 ≤ cellMass μ G g := by
  exact ENNReal.toReal_nonneg

/-- Cell masses sum to `1` under `IsProbabilityMeasure μ` and a measurable
`G` valued in a finite type with `MeasurableSingletonClass`. The `{G = g}`
family partitions `Ω` (up to `μ`-null sets) and the `μ`-mass of each is
finite. This supplies the `π_sum_one` field for the finite-partition algebra. -/
theorem cellMass_sum_eq_one {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢]
    [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (G : Ω → 𝒢) (G_meas : Measurable G) :
  ∑ g, cellMass μ G g = 1 := by
  have hsum :
      (Finset.univ).sum (fun g => (μ (G ⁻¹' ({g} : Set 𝒢))).toReal) =
        (μ (G ⁻¹' (Set.univ : Set 𝒢))).toReal := by
    simpa [Measure.real] using
      (MeasureTheory.sum_measureReal_preimage_singleton
        (μ := μ) (s := (Finset.univ : Finset 𝒢)) (f := G)
        (hf := by
          intro g hg
          exact G_meas (measurableSet_singleton g))
        (h := by
          intro g hg
          exact ne_of_lt <| lt_of_le_of_lt (measure_mono (Set.subset_univ _))
            (by simpa [IsProbabilityMeasure.measure_univ])))
  simpa [cellMass, preimage_univ] using hsum

/-- Cell-wise treated share is nonnegative under `D_binary`. The integrand
`D · 𝟙{G = g}` is a.e. nonnegative because `D ∈ {0, 1}` a.e. -/
theorem cellShare_nonneg {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) (D : Ω → ℝ) (G : Ω → 𝒢)
    (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) (g : 𝒢) :
    0 ≤ cellShare μ D G g := by
  have h_num_nonneg :
      0 ≤ ∫ ω, D ω * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [D_binary] with ω hD
    rcases hD with hD0 | hD1
    · simp [hD0]
    · by_cases hG : G ω = g
      · simp [hD1, hG]
      · simp [hD1, hG]
  have h_den_nonneg : 0 ≤ cellMass μ G g := cellMass_nonneg (μ := μ) G g
  exact div_nonneg h_num_nonneg h_den_nonneg

/-- Cell-wise treated share is at most `1` under `D_binary`. The integrand
`D · 𝟙{G = g} ≤ 𝟙{G = g}` a.e., so the numerator is at most
`cellMass μ G g`. -/
theorem cellShare_le_one {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢]
    [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (D : Ω → ℝ) (G : Ω → 𝒢)
  (G_meas : Measurable G) (D_meas : Measurable D)
  (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) (g : 𝒢) :
  cellShare μ D G g ≤ 1 := by
  let s : Set Ω := {ω | G ω = g}
  let I : Ω → ℝ := fun ω => Set.indicator s (1 : Ω → ℝ) ω
  have hI_meas : MeasurableSet s := by
    exact G_meas (measurableSet_singleton g)
  have hI_top : μ s ≠ ⊤ := by
    refine ne_of_lt <| lt_of_le_of_lt (measure_mono (Set.subset_univ s))
      (by simpa [IsProbabilityMeasure.measure_univ])
  have h_num_le_den :
      ∫ ω, D ω * I ω ∂μ ≤ ∫ ω, I ω ∂μ := by
    have hI_integrable : Integrable I μ := by
      unfold I
      exact (integrable_indicator_iff hI_meas).2
        (integrableOn_const (s := s) (μ := μ) (hs := hI_top))
    have hI_nonneg : 0 ≤ᵐ[μ] I := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      exact Set.indicator_nonneg (fun _ _ => (show 0 ≤ (1 : ℝ) by norm_num)) ω
    have h_nonneg : 0 ≤ᵐ[μ] fun ω => D ω * I ω := by
      filter_upwards [D_binary, hI_nonneg] with ω hD hI
      rcases hD with hD0 | hD1
      · simpa [I, hD0] using hI
      · simpa [I, hD1] using mul_nonneg (by norm_num : (0:ℝ) ≤ 1) hI
    have h_le : (fun ω => D ω * I ω) ≤ᵐ[μ] I := by
      filter_upwards [D_binary, hI_nonneg] with ω hD hI
      rcases hD with hD0 | hD1
      · simpa [I, hD0] using hI
      · simpa [I, hD1] using (le_rfl : I ω ≤ I ω)
    exact integral_mono_of_nonneg h_nonneg hI_integrable h_le
  have hI_int : (∫ ω, I ω ∂μ) = cellMass μ G g := by
    change (∫ ω, Set.indicator s (1 : Ω → ℝ) ω ∂μ) = (μ s).toReal
    rw [MeasureTheory.integral_indicator_one hI_meas]
    simp [Measure.real, cellMass, s]
  have h_num_le_cellmass : ∫ ω, D ω * I ω ∂μ ≤ cellMass μ G g := by
    simpa [hI_int] using h_num_le_den
  exact div_le_one_of_le₀ h_num_le_cellmass (cellMass_nonneg (μ := μ) G g)

/-- The pointwise representative `propensity μ D G` lies in
`saturatedClass μ G G_meas`. Take the coefficient map
`c g := cellShare μ D G g`; equality holds pointwise (and so a.e.). -/
theorem propensity_mem_saturatedClass {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [Fintype 𝒢] [DecidableEq 𝒢] [MeasurableSpace 𝒢]
    [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (G : Ω → 𝒢)
    (G_meas : Measurable G) :
    (saturatedClass μ G G_meas).mem (propensity μ D G) := by
  exact ⟨fun g => cellShare μ D G g, Filter.EventuallyEq.rfl⟩

/-- The mean-regression `meanReg μ Y G` lies in `saturatedClass μ G G_meas`.
Take the coefficient map `c g := (∫ Y · 𝟙{G = g} dμ) / cellMass μ G g`. -/
theorem meanReg_mem_saturatedClass {Ω 𝒢 : Type*} [MeasurableSpace Ω]
    [Fintype 𝒢] [DecidableEq 𝒢] [MeasurableSpace 𝒢]
    [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (G : Ω → 𝒢)
    (G_meas : Measurable G) :
    (saturatedClass μ G G_meas).mem (meanReg μ Y G) := by
  refine ⟨fun g => (∫ ω', Y ω' * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω' ∂μ)
    / cellMass μ G g, ?_⟩
  exact Filter.EventuallyEq.rfl

end CellHelpers

end Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition
