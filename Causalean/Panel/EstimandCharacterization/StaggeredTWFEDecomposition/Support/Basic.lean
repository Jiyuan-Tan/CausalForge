/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021) Layer B: panel class, cell statistics, and projections

Holds the saturated cohort + period nuisance class `panelClass`, the
cohort/period/cell statistics extracted from the joint law, the in-class
projections `panelPropensity` / `panelMeanReg`, the elementary cell-mass
positivity bounds, and the membership lemmas
`panelPropensity_mem_panelClass` / `panelMeanReg_mem_panelClass`.

Intended to be a pure-definitions + light-bound layer; integral identities
go in `Support/Integrals.lean`, per-cell orthogonality in
`Support/Orthogonality.lean`, residualization witnesses in
`Support/Partition.lean`, and per-cell denominator/numerator identities in
`Support/PerCell.lean`.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.md`
("Layer B" section).
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Causalean.Panel.Analysis.Residualization
import Causalean.Panel.CellBridge
import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.FinitePanel

/-!
Defines basic bridge objects for the staggered-TWFE decomposition. The module
packages saturated cohort-period classes and finite panel support used to
connect algebraic weighted panels to population integrals.
-/

namespace Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

variable {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢] [DecidableEq 𝒢]
  [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢] {T : ℕ}

/-! ### B1. Saturated cohort + period class -/

/-- **B1. Saturated cohort + period class.** Linear `L²` class spanned (a.e.)
by the family of cohort indicators `𝟙{G = g}` (for `g : 𝒢`) and period
indicators `𝟙{T_rv = t}` (for `t : Fin T`).

Membership predicate (predicate-style, residualization_core D1 option (b)):

    f ∈ panelClass μ G T_rv  ↔  ∃ (cG : 𝒢 → ℝ) (cT : Fin T → ℝ),
        f =ᵐ[μ] (fun ω => ∑ g, cG g · 𝟙{G ω = g}
                        + ∑ t, cT t · 𝟙{T_rv ω = t}). -/
noncomputable def panelClass
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv) : LinearL2Class μ :=
  CellBridge.twoAxisIndicatorSpan μ G T_rv G_meas T_meas

/-! ### B2. Cell statistics -/

/-- **B2. Cell mass.** `cellMass μ G T_rv g t = (μ {G = g ∧ T_rv = t}).toReal`.
Plays the role of `ℙ(G = g, T = t) = p_g / |𝒯|` in
`def:po-estimand-goodman-bacon-panel`. -/
def cellMass (μ : Measure Ω) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (g : 𝒢) (t : Fin T) : ℝ :=
  CellBridge.jointCellMass μ G T_rv g t

/-- **B2. Cohort mass.** `cohortMass μ G g = (μ {G = g}).toReal`. Plays the
role of `p_g`. Equals `∑ t, cellMass μ G T_rv g t` under the balanced-law
hypothesis. -/
def cohortMass (μ : Measure Ω) (G : Ω → 𝒢) (g : 𝒢) : ℝ :=
  CellBridge.cellMass μ G g

/-- **B2. Period mass.** `periodMass μ T_rv t = (μ {T_rv = t}).toReal`.
Plays the role of `1/|𝒯|` under the balanced-law hypothesis. -/
def periodMass (μ : Measure Ω) (T_rv : Ω → Fin T) (t : Fin T) : ℝ :=
  CellBridge.cellMass μ T_rv t

/-- **B2. Cell mean.** `cellMean μ Y G T_rv g t` plays the role of
`Y_{gt} = E[Y | G = g, T = t]` from the LaTeX panel definition.
On zero-mass cells the value is `0` by Mathlib's `0/0 = 0` convention. -/
noncomputable def cellMean (μ : Measure Ω) (Y : Ω → ℝ) (G : Ω → 𝒢)
    (T_rv : Ω → Fin T) (g : 𝒢) (t : Fin T) : ℝ :=
  (∫ ω, Y ω
    * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ)
    / cellMass μ G T_rv g t

private theorem cellMean_eq_cellBridge (μ : Measure Ω) (Y : Ω → ℝ) (G : Ω → 𝒢)
    (T_rv : Ω → Fin T) (g : 𝒢) (t : Fin T) :
    cellMean μ Y G T_rv g t =
      CellBridge.cellMean μ Y (fun ω => (G ω, T_rv ω)) (g, t) := by
  unfold cellMean CellBridge.cellMean cellMass CellBridge.jointCellMass CellBridge.cellMass
  congr 2
  · ext ω
    simp
  · congr 1
    ext ω
    simp

/-- **B2. Cohort mean treatment share.** `cohortBarD μ D G g` plays the role
of `\overline{D}_g = E[D | G = g]`. -/
noncomputable def cohortBarD (μ : Measure Ω) (D : Ω → ℝ) (G : Ω → 𝒢)
    (g : 𝒢) : ℝ :=
  (∫ ω, D ω * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ)
    / cohortMass μ G g

/-! ### B2. `panelOf` — Layer A panel built from the law -/

/-- **B2. Bridge to Layer A.** Constructs a `CohortPanel 𝒢 T` from a
probability space carrying the cell-level data plus an explicit adoption
date `A : 𝒢 → WithTop (Fin T)`. -/
noncomputable def panelOf
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (A : 𝒢 → WithTop (Fin T))
    (hT_pos : 0 < T)
    (hp_pos : ∀ g, 0 < cohortMass μ G g)
    (hp_sum : ∑ g, cohortMass μ G g = 1) :
    CohortPanel 𝒢 T :=
  { p := cohortMass μ G
  , A := A
  , Y := cellMean μ Y G T_rv
  , T_pos := hT_pos
  , p_pos := hp_pos
  , p_sum_one := hp_sum }

/-! ### B3. In-class projections for `D` and `Y` -/

/-- **B3. Saturated cohort+period propensity for `D`.** The pointwise
representative

    panelPropensity μ D G T_rv ω
      := \overline{D}_{G ω} + (E[D | T = T_rv ω] - E[D])

decomposes the projection of `D` on `H_gt` as the sum of a cohort-indicator
expansion and a period-indicator expansion (centred to ensure
identifiability). Lies in `panelClass μ G T_rv G_meas T_meas`. -/
noncomputable def panelPropensity
    (μ : Measure Ω) (D : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T) : Ω → ℝ :=
  fun ω =>
    (∑ g, cohortBarD μ D G g
      * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω)
    + (∑ t, ((∫ ω', D ω'
        * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω' ∂μ)
        / periodMass μ T_rv t
        - ∫ ω', D ω' ∂μ)
      * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω)

/-- **B3. Saturated cohort+period mean regression for `Y`.** Analogous to
`panelPropensity`, with `Y` in place of `D`. -/
noncomputable def panelMeanReg
    (μ : Measure Ω) (Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T) : Ω → ℝ :=
  fun ω =>
    (∑ g, ((∫ ω', Y ω'
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω' ∂μ)
        / cohortMass μ G g)
      * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω)
    + (∑ t, ((∫ ω', Y ω'
        * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω' ∂μ)
        / periodMass μ T_rv t
        - ∫ ω', Y ω' ∂μ)
      * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω)

/-! ### B3. Membership lemmas -/

/-- The pointwise representative `panelPropensity μ D G T_rv` lies in
`panelClass μ G T_rv G_meas T_meas`. Coefficient maps:
`cG g := cohortBarD μ D G g`, `cT t := (∫ D · 𝟙{T=t} dμ) / periodMass t - ∫ D dμ`. -/
theorem panelPropensity_mem_panelClass
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv) :
    (panelClass μ G T_rv G_meas T_meas).mem (panelPropensity μ D G T_rv) := by
  unfold panelClass CellBridge.twoAxisIndicatorSpan
  refine ⟨fun g => cohortBarD μ D G g,
    fun t => (∫ ω', D ω'
      * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω' ∂μ)
      / periodMass μ T_rv t
      - ∫ ω', D ω' ∂μ, ?_⟩
  filter_upwards [] with ω
  rfl

/-- The pointwise representative `panelMeanReg μ Y G T_rv` lies in
`panelClass μ G T_rv G_meas T_meas`. -/
theorem panelMeanReg_mem_panelClass
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv) :
    (panelClass μ G T_rv G_meas T_meas).mem (panelMeanReg μ Y G T_rv) := by
  unfold panelClass CellBridge.twoAxisIndicatorSpan
  refine ⟨fun g => (∫ ω', Y ω'
      * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω' ∂μ)
      / cohortMass μ G g,
    fun t => (∫ ω', Y ω'
      * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω' ∂μ)
      / periodMass μ T_rv t
      - ∫ ω', Y ω' ∂μ, ?_⟩
  filter_upwards [] with ω
  rfl

/-! ### B2. Elementary cell-mass bounds -/

/-- Cell mass is nonnegative. -/
theorem cellMass_nonneg (μ : Measure Ω) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (g : 𝒢) (t : Fin T) : 0 ≤ cellMass μ G T_rv g t := ENNReal.toReal_nonneg

/-- Cohort mass is nonnegative. -/
theorem cohortMass_nonneg (μ : Measure Ω) (G : Ω → 𝒢) (g : 𝒢) :
    0 ≤ cohortMass μ G g := ENNReal.toReal_nonneg

/-- Period mass is nonnegative. -/
theorem periodMass_nonneg (μ : Measure Ω) (T_rv : Ω → Fin T) (t : Fin T) :
    0 ≤ periodMass μ T_rv t := ENNReal.toReal_nonneg

end Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition
