/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Borusyak-Jaravel-Spiess (2024): population bridge to the finite BJS panel

Anchors the abstract `BJSPanel` (whose mean fields are free reals) to a genuine
probability space carrying potential outcomes. A `BJSPopulation` bundles
`(Ω, μ)`, a treated/untreated cell classifier `cellOf : Ω → Treated ⊕ Untreated`,
and potential outcomes `Y0` (untreated), `Y1` (treated), and observed `Yobs`.
Its `toPanel` fills every mean field of `BJSPanel` with a cell-conditional mean
of a potential-outcome slice; in particular the treated-cell effect `tau c`
becomes the genuine population contrast `E[Y(1) − Y(0) ∣ cell c]`.

The `TreatmentEffectFixed` restriction and the observed-equals-untreated clause
of `UntreatedOutcomeModel` are **derived** from cell-level consistency (the
observed outcome is the treated/untreated potential outcome on treated/untreated
cells). Only the additive untreated-outcome model `E[Y(0) ∣ cell] = q · β₀` — the
paper's fixed-effect / parallel-trends restriction — remains a modeling
hypothesis, supplied to the discharge lemma.

Source spec: `doc/basic_concepts/po/estimand_characterization/bjs_imputation.md`.
-/

import Causalean.Panel.EstimandCharacterization.ImputationEventStudy.Imputation
import Causalean.Panel.PO.PopulationCells

/-! # Borusyak-Jaravel-Spiess imputation population bridge

This file constructs a finite `BJSPanel` from a probability space with treated
and untreated potential outcomes, defining its mean fields as treated/untreated
cell conditional means and deriving the untreated-consistency and fixed-effect
restrictions from cell-level potential-outcome consistency. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace ImputationEventStudy

open MeasureTheory
open Causalean.Panel.PO

noncomputable section

variable {Treated Untreated Regressor : Type*}
  [Fintype Treated] [Fintype Untreated] [Fintype Regressor]

/-- A **population** for the BJS imputation design: a probability space with a
treated/untreated cell classifier and potential outcomes `Y0` (untreated),
`Y1` (treated), and observed `Yobs`, related by cell-level consistency. The
design rows `qT`, `qU`, target weights `a`, and nuisance vector `beta0` are
carried through to the induced panel unchanged. -/
structure BJSPopulation (Treated Untreated Regressor : Type*)
    [Fintype Treated] [Fintype Untreated] [Fintype Regressor] where
  /-- Unit sample space. -/
  Ω : Type*
  /-- Measurable-space structure on `Ω`. -/
  [measΩ : MeasurableSpace Ω]
  /-- Population measure. -/
  μ : Measure Ω
  /-- `μ` is a probability measure. -/
  [probμ : IsProbabilityMeasure μ]
  /-- Treated/untreated cell classifier. -/
  cellOf : Ω → Treated ⊕ Untreated
  /-- Each cell is measurable. -/
  cell_meas : ∀ i, MeasurableSet (cellOf ⁻¹' {i})
  /-- Each cell has positive mass. -/
  cell_pos : ∀ i, 0 < (μ (cellOf ⁻¹' {i})).toReal
  /-- Untreated potential outcome. -/
  Y0 : Ω → ℝ
  /-- Treated potential outcome. -/
  Y1 : Ω → ℝ
  /-- Observed outcome. -/
  Yobs : Ω → ℝ
  /-- Consistency on treated cells: the observed outcome is the treated
  potential outcome. -/
  hTreatedCons : ∀ (c : Treated) (ω : Ω),
    cellOf ω = Sum.inl c → Yobs ω = Y1 ω
  /-- Consistency on untreated cells: the observed outcome is the untreated
  potential outcome. -/
  hUntreatedCons : ∀ (u : Untreated) (ω : Ω),
    cellOf ω = Sum.inr u → Yobs ω = Y0 ω
  /-- Regressor row for a treated cell. -/
  qT : Treated → Regressor → ℝ
  /-- Regressor row for an untreated cell. -/
  qU : Untreated → Regressor → ℝ
  /-- Target weight on treated cells. -/
  a : Treated → ℝ
  /-- Nuisance vector in the untreated outcome model. -/
  beta0 : Regressor → ℝ

namespace BJSPopulation

variable (E : BJSPopulation Treated Untreated Regressor)

attribute [instance] BJSPopulation.measΩ BJSPopulation.probμ

/-- The treated/untreated cell partition induced by the classifier. -/
noncomputable def cells : CellPartition E.μ (Treated ⊕ Untreated) :=
  cellPartitionOfClassifier E.μ E.cellOf E.cell_meas E.cell_pos

/-- The BJS panel induced by a population: every mean field is a treated/untreated
cell conditional mean of the appropriate potential-outcome slice, and the
treated effect `tau c` is the genuine population contrast
`E[Y(1) ∣ cell c] − E[Y(0) ∣ cell c]`. -/
noncomputable def toPanel : BJSPanel Treated Untreated Regressor where
  qT := E.qT
  qU := E.qU
  a := E.a
  beta0 := E.beta0
  EY_T c := E.cells.mean E.Yobs (Sum.inl c)
  EY_U u := E.cells.mean E.Yobs (Sum.inr u)
  EY0_T c := E.cells.mean E.Y0 (Sum.inl c)
  EY0_U u := E.cells.mean E.Y0 (Sum.inr u)
  tau c := E.cells.mean E.Y1 (Sum.inl c) - E.cells.mean E.Y0 (Sum.inl c)

/-- On a treated cell the observed mean equals the treated potential-outcome
mean. -/
theorem toPanel_EY_T_eq_mean_Y1 (c : Treated) :
    (E.toPanel).EY_T c = E.cells.mean E.Y1 (Sum.inl c) := by
  refine (E.cells).mean_congr_on (Sum.inl c) ?_
  intro ω hω
  have hcell : E.cellOf ω = Sum.inl c := by simpa [cells] using hω
  exact E.hTreatedCons c ω hcell

/-- On an untreated cell the observed mean equals the untreated potential-outcome
mean. -/
theorem toPanel_EY_U_eq_mean_Y0 (u : Untreated) :
    (E.toPanel).EY_U u = E.cells.mean E.Y0 (Sum.inr u) := by
  refine (E.cells).mean_congr_on (Sum.inr u) ?_
  intro ω hω
  have hcell : E.cellOf ω = Sum.inr u := by simpa [cells] using hω
  exact E.hUntreatedCons u ω hcell

/-- **Causal-meaning certificate.** In the induced panel, `tau c` is literally
the population treatment-effect contrast `E[Y(1) ∣ cell c] − E[Y(0) ∣ cell c]`,
so the estimand carries genuine causal content. -/
theorem toPanel_tau_eq_po_contrast (c : Treated) :
    (E.toPanel).tau c =
      E.cells.mean E.Y1 (Sum.inl c) - E.cells.mean E.Y0 (Sum.inl c) := rfl

/-- **Treatment-effect-fixed is derived.** `EY_T = EY0_T + tau` holds because on
treated cells the observed mean is the treated potential-outcome mean and `tau`
is the treated-minus-untreated contrast. -/
theorem toPanel_treatmentEffectFixed : (E.toPanel).TreatmentEffectFixed := by
  intro c
  have h := E.toPanel_EY_T_eq_mean_Y1 c
  simp only [toPanel] at h ⊢
  rw [h]; ring

/-- **Untreated-outcome model is derived from the linear untreated-mean
hypotheses plus consistency.** The two linear-model conjuncts
`E[Y(0) ∣ cell] = q · β₀` are the genuine modeling hypotheses `hLinT`/`hLinU`
(additive fixed-effect / parallel-trends form); the observed-equals-untreated
conjunct is derived from untreated-cell consistency. -/
theorem toPanel_untreatedModel
    (hLinT : ∀ c : Treated, E.cells.mean E.Y0 (Sum.inl c) = dot (E.qT c) E.beta0)
    (hLinU : ∀ u : Untreated, E.cells.mean E.Y0 (Sum.inr u) = dot (E.qU u) E.beta0) :
    (E.toPanel).UntreatedOutcomeModel := by
  refine ⟨?_, ?_, ?_⟩
  · intro c; simpa [toPanel] using hLinT c
  · intro u; simpa [toPanel] using hLinU u
  · intro u
    rw [E.toPanel_EY_U_eq_mean_Y0 u]
    simp [toPanel]

/-- **Population BJS imputation identification (headline).** For a population
BJS design, the observed-law imputation functional identifies the target
`∑ a_c · E[Y(1) − Y(0) ∣ cell c]`, under the additive untreated-outcome model
`hLinT`/`hLinU` and the (design-side) prediction-span condition. The
treatment-effect-fixed restriction and untreated consistency are derived, and
`tau c` is the genuine population contrast. -/
theorem bjs_imputation_identification_population
    (hLinT : ∀ c : Treated, E.cells.mean E.Y0 (Sum.inl c) = dot (E.qT c) E.beta0)
    (hLinU : ∀ u : Untreated, E.cells.mean E.Y0 (Sum.inr u) = dot (E.qU u) E.beta0)
    (hPred : (E.toPanel).PredictionIdentified) :
    ∃ h : (E.toPanel).ImputationWeights,
      (E.toPanel).psiImp h.weight = (E.toPanel).theta :=
  (E.toPanel).bjs_imputation_identification
    (E.toPanel_untreatedModel hLinT hLinU) hPred E.toPanel_treatmentEffectFixed

end BJSPopulation

end

end ImputationEventStudy
end Panel.EstimandCharacterization
end Causalean
