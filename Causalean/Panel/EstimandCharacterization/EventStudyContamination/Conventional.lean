/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sun-Abraham (2021): conventional event-study contamination

Finite-cell contamination algebra for the conventional TWFE event-study
coefficient. The orthogonality conditions (`ConventionalResidualization`) and
the FWL ratio (`D.mu = conventionalMuRatio`) are consumed here as hypotheses.
Both are derived from a weighted cell-grid projection in `CellGrid.lean`, with
public entry points in `Contamination.lean`.
-/

import Causalean.Panel.EstimandCharacterization.EventStudyContamination.Setup

/-! # Sun-Abraham Conventional Event Study

This file formalizes the finite-cell algebra for the conventional two-way fixed
effects event-study coefficient in the Sun-Abraham setting. It expresses the
coefficient as a weighted average of cohort-relative-time treatment effects
under supplied residualization, support, and integrability conditions. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace EventStudyContamination

open Finset

namespace EventStudySystem

variable {T : ℕ}

/-- Included-event-time indicator on a cohort-relative-time cell. -/
noncomputable def eventIndicator (_P : EventStudySystem T) (k e : ℤ) : ℝ :=
  if e = k then 1 else 0

/-- Conventional event-study finite design for the coefficient on
`displayedEvent`. -/
structure ConventionalDesign (P : EventStudySystem T) where
  /-- Finite support of relative times used in the cell expansion. -/
  eventSupport : Finset ℤ
  /-- Included relative-time indicators in the conventional TWFE regression. -/
  includedEvents : Finset ℤ
  /-- Omitted reference relative time. -/
  omittedEvent : ℤ
  /-- Displayed event time `l` whose coefficient is characterized. -/
  displayedEvent : ℤ
  /-- Residualized relative-time indicator `Rdot^l`, constant on cells. -/
  Rdot : Fin T → ℤ → ℝ
  /-- Conventional population TWFE event-study coefficient `mu_l`. -/
  mu : ℝ

/-- Finite-span nuisance class for the coefficient on `R^l`: cohort effects,
period effects, and other included relative-time indicators. -/
def IsEventStudyNuisance (P : EventStudySystem T) (D : P.ConventionalDesign)
    (h : Fin T → Fin T → ℝ) : Prop :=
  ∃ hAdd : Fin T → Fin T → ℝ, Causalean.Panel.Weighted.IsUnitTimeAdditive hAdd ∧
    ∃ gamma : ℤ → ℝ,
      ∀ g ∈ P.cohorts, ∀ t,
        h g t = hAdd g t +
          ∑ k ∈ D.includedEvents.filter (fun k => k ≠ D.displayedEvent),
            gamma k * P.eventIndicator k (P.relTime g t)

/-- Average of a cohort-period nuisance function over the finite periods that
realize cell `(g,e)`. -/
noncomputable def cellAverage (P : EventStudySystem T)
    (h : Fin T → Fin T → ℝ) (g : Fin T) (e : ℤ) : ℝ :=
  ((P.targetPeriods g e).card : ℝ)⁻¹ *
    ∑ t ∈ P.targetPeriods g e, h g t

/-- Finite-cell residualization record for the conventional coefficient.

The fields are the finite-cell consequences of `Rdot^l` being the residual of
the displayed relative-time indicator `R^l` against the event-study nuisance
class: orthogonality to nuisance functions, the displayed-event expansion of
the denominator, and zero weights for other included event-time indicators.
This file consumes the record as a hypothesis for the algebraic contamination
proofs; `CellGrid.lean` derives the record from a weighted projection on the
admissible cohort-relative-time grid. -/
structure ConventionalResidualization (P : EventStudySystem T)
    (D : P.ConventionalDesign) : Prop where
  hResidualization :
    ∀ h : Fin T → Fin T → ℝ, P.IsEventStudyNuisance D h →
      ∑ ge ∈ P.admissibleCells D.eventSupport,
        P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
          P.cellAverage h ge.1 ge.2 = 0
  hDisplayedExpansion :
    ∑ ge ∈ P.admissibleCells D.eventSupport,
      P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
        P.eventIndicator D.displayedEvent ge.2 =
      ∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
        P.cellMassAtEvent g D.displayedEvent * D.Rdot g D.displayedEvent
  hOtherIncludedOrthogonal :
    ∀ e ∈ D.includedEvents, e ≠ D.displayedEvent →
      ∑ g ∈ P.cohortsAtEvent D.eventSupport e,
        P.cellMassAtEvent g e * D.Rdot g e = 0

/-- Finite residualized denominator `E[Rdot^l R^l]`. -/
noncomputable def residualDenom (P : EventStudySystem T)
    (D : P.ConventionalDesign) : ℝ :=
  ∑ ge ∈ P.admissibleCells D.eventSupport,
    P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
      P.eventIndicator D.displayedEvent ge.2

/-- Finite residualized numerator `E[Rdot^l Y]`. -/
noncomputable def residualNumerator (P : EventStudySystem T)
    (D : P.ConventionalDesign) : ℝ :=
  ∑ ge ∈ P.admissibleCells D.eventSupport,
    P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
      P.observedCellMean ge.1 ge.2

/-- Residualized-ratio form of the conventional event-study coefficient. -/
noncomputable def conventionalMuRatio (P : EventStudySystem T)
    (D : P.ConventionalDesign) : ℝ :=
  P.residualNumerator D / P.residualDenom D

/-- Transparent finite support bookkeeping for the conventional cell expansion.
It records that the explicit event-time support is the finite universe over
which the displayed theorem is expanded, without asserting the headline
contamination formula itself. -/
structure ConventionalFiniteSupport (P : EventStudySystem T)
    (D : P.ConventionalDesign) : Prop where
  hIncludedInSupport : ∀ e ∈ D.includedEvents, e ∈ D.eventSupport
  hDisplayedInSupport : D.displayedEvent ∈ D.eventSupport
  hCellsSupported :
    ∀ ge ∈ P.admissibleCells D.eventSupport, ge.1 ∈ P.cohorts ∧ ge.2 ∈ D.eventSupport

/-- Sun-Abraham contamination weight for the conventional event-study
coefficient. -/
noncomputable def omega (P : EventStudySystem T) (D : P.ConventionalDesign)
    (g : Fin T) (e : ℤ) : ℝ :=
  (P.cellMassAtEvent g e * D.Rdot g e) / P.residualDenom D

/-- Desired-event-time weights sum to one. -/
theorem desired_event_weights_sum_one (P : EventStudySystem T)
    (D : P.ConventionalDesign)
    (hResidualization : P.ConventionalResidualization D)
    (hDenomPos : 0 < P.residualDenom D) :
    ∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
      P.omega D g D.displayedEvent = 1 := by
  have hDenom_ne : P.residualDenom D ≠ 0 := ne_of_gt hDenomPos
  calc
    ∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
        P.omega D g D.displayedEvent =
        (∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
          P.cellMassAtEvent g D.displayedEvent * D.Rdot g D.displayedEvent) /
          P.residualDenom D := by
      simp [omega, Finset.sum_div]
    _ = P.residualDenom D / P.residualDenom D := by
      rw [← hResidualization.hDisplayedExpansion]
      rfl
    _ = 1 := div_self hDenom_ne

/-- Other included-event-time weights sum to zero. -/
theorem other_included_event_weights_sum_zero (P : EventStudySystem T)
    (D : P.ConventionalDesign) {e : ℤ}
    (hDisplayedIncluded : D.displayedEvent ∈ D.includedEvents)
    (hOtherIncluded : e ∈ D.includedEvents)
    (hOther : e ≠ D.displayedEvent)
    (hResidualization : P.ConventionalResidualization D)
    (hDenomPos : 0 < P.residualDenom D) :
    ∑ g ∈ P.cohortsAtEvent D.eventSupport e, P.omega D g e = 0 := by
  have _ := hDisplayedIncluded
  have _ : P.residualDenom D ≠ 0 := ne_of_gt hDenomPos
  calc
    ∑ g ∈ P.cohortsAtEvent D.eventSupport e, P.omega D g e =
        (∑ g ∈ P.cohortsAtEvent D.eventSupport e,
          P.cellMassAtEvent g e * D.Rdot g e) / P.residualDenom D := by
      simp [omega, Finset.sum_div]
    _ = 0 / P.residualDenom D := by
      rw [hResidualization.hOtherIncludedOrthogonal e hOtherIncluded hOther]
    _ = 0 := zero_div _

/-- Conventional Sun-Abraham contamination representation.

Takes the FWL ratio identity `D.mu = conventionalMuRatio D` and the finite-cell
orthogonality conditions `ConventionalResidualization` as hypotheses. See
`cellGrid_mu_eq_conventionalMuRatio`, `cellGrid_provides_residualization`, and
the public wrappers in `Contamination.lean` for the projection-derived entry
points. -/
theorem contamination_representation (P : EventStudySystem T)
    (D : P.ConventionalDesign)
    (hCausal : P.EventStudyCausalRestrictions)
    (hResidualization : P.ConventionalResidualization D)
    (hDenomPos : 0 < P.residualDenom D)
    (hMuRatio : D.mu = P.conventionalMuRatio D)
    (hSupport : P.ConventionalFiniteSupport D) :
    D.mu =
      ∑ ge ∈ P.admissibleCells D.eventSupport,
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 := by
  have _ : P.residualDenom D ≠ 0 := ne_of_gt hDenomPos
  rcases hCausal.hMeanParallelUntreated with ⟨hAdd, ⟨alpha, lambda, hAdd_eq⟩, hUntreated⟩
  let hFE : Fin T → Fin T → ℝ := fun g t => alpha g + lambda t
  have hNuisance : P.IsEventStudyNuisance D hFE := by
    refine ⟨hFE, ⟨alpha, lambda, ?_⟩, fun _ => 0, ?_⟩
    · intro g t
      rfl
    intro g hg t
    simp [hFE]
  have hFE_zero :
      ∑ ge ∈ P.admissibleCells D.eventSupport,
        P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
          P.cellAverage hFE ge.1 ge.2 = 0 :=
    hResidualization.hResidualization hFE hNuisance
  have hObs :
      ∀ ge ∈ P.admissibleCells D.eventSupport,
        P.observedCellMean ge.1 ge.2 =
          P.cellAverage hFE ge.1 ge.2 + P.CATT ge.1 ge.2 := by
    intro ge hge
    have hg : ge.1 ∈ P.cohorts := (hSupport.hCellsSupported ge hge).1
    unfold observedCellMean cellAverage hFE
    change
      ((P.targetPeriods ge.1 ge.2).card : ℝ)⁻¹ *
          ∑ t ∈ P.targetPeriods ge.1 ge.2, P.observedMean ge.1 t =
        ((P.targetPeriods ge.1 ge.2).card : ℝ)⁻¹ *
            ∑ t ∈ P.targetPeriods ge.1 ge.2, (alpha ge.1 + lambda t) +
          ((P.targetPeriods ge.1 ge.2).card : ℝ)⁻¹ *
            ∑ t ∈ P.targetPeriods ge.1 ge.2,
              (P.treatedMean ge.1 t - P.untreatedMean ge.1 t)
    have hsum :
        (∑ t ∈ P.targetPeriods ge.1 ge.2, P.observedMean ge.1 t) =
          (∑ t ∈ P.targetPeriods ge.1 ge.2, (alpha ge.1 + lambda t)) +
            ∑ t ∈ P.targetPeriods ge.1 ge.2,
              (P.treatedMean ge.1 t - P.untreatedMean ge.1 t) := by
      calc
        (∑ t ∈ P.targetPeriods ge.1 ge.2, P.observedMean ge.1 t) =
            ∑ t ∈ P.targetPeriods ge.1 ge.2,
              ((alpha ge.1 + lambda t) +
                (P.treatedMean ge.1 t - P.untreatedMean ge.1 t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hCausal.hConsistency ge.1 hg t, hUntreated ge.1 hg t, hAdd_eq ge.1 t]
          ring
        _ = (∑ t ∈ P.targetPeriods ge.1 ge.2, (alpha ge.1 + lambda t)) +
            ∑ t ∈ P.targetPeriods ge.1 ge.2,
              (P.treatedMean ge.1 t - P.untreatedMean ge.1 t) := by
          rw [Finset.sum_add_distrib]
    rw [hsum, mul_add]
  have hNumerator :
      P.residualNumerator D =
        ∑ ge ∈ P.admissibleCells D.eventSupport,
          P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
            P.CATT ge.1 ge.2 := by
    unfold residualNumerator
    calc
      ∑ ge ∈ P.admissibleCells D.eventSupport,
          P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
            P.observedCellMean ge.1 ge.2 =
          ∑ ge ∈ P.admissibleCells D.eventSupport,
            P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
              (P.cellAverage hFE ge.1 ge.2 + P.CATT ge.1 ge.2) := by
        apply Finset.sum_congr rfl
        intro ge hge
        rw [hObs ge hge]
      _ =
          (∑ ge ∈ P.admissibleCells D.eventSupport,
            P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
              P.cellAverage hFE ge.1 ge.2) +
          ∑ ge ∈ P.admissibleCells D.eventSupport,
            P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
              P.CATT ge.1 ge.2 := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
      _ =
          ∑ ge ∈ P.admissibleCells D.eventSupport,
            P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
              P.CATT ge.1 ge.2 := by
        rw [hFE_zero, zero_add]
  calc
    D.mu = P.residualNumerator D / P.residualDenom D := hMuRatio
    _ =
        (∑ ge ∈ P.admissibleCells D.eventSupport,
          P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
            P.CATT ge.1 ge.2) / P.residualDenom D := by
      rw [hNumerator]
    _ =
        ∑ ge ∈ P.admissibleCells D.eventSupport,
          P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ge hge
      simp [omega]
      ring

set_option linter.flexible false in
/-- Equivalent split of the contamination formula into the displayed
event-time component and all other admissible event times. -/
theorem contamination_representation_split (P : EventStudySystem T)
    (D : P.ConventionalDesign)
    (hCausal : P.EventStudyCausalRestrictions)
    (hResidualization : P.ConventionalResidualization D)
    (hDenomPos : 0 < P.residualDenom D)
    (hMuRatio : D.mu = P.conventionalMuRatio D)
    (hSupport : P.ConventionalFiniteSupport D) :
    D.mu =
      (∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
        P.omega D g D.displayedEvent * P.CATT g D.displayedEvent) +
      (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 ≠ D.displayedEvent),
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2) := by
  let F : Fin T × ℤ → ℝ := fun ge => P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2
  have hMain :
      D.mu = ∑ ge ∈ P.admissibleCells D.eventSupport, F ge := by
    simpa [F] using
      contamination_representation P D hCausal hResidualization hDenomPos
        hMuRatio hSupport
  have hDisplayedCells :
      (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 = D.displayedEvent) =
        (P.cohortsAtEvent D.eventSupport D.displayedEvent).map
          ⟨fun g => (g, D.displayedEvent),
            by
              intro a b h
              exact congrArg Prod.fst h⟩ := by
    ext ge
    rcases ge with ⟨g, e⟩
    simp [admissibleCells, cohortsAtEvent]
    constructor
    · intro h
      have hg : g ∈ P.cohorts := h.1.1.1
      have heSupport : e ∈ D.eventSupport := h.1.1.2
      have hAdm : P.AdmissibleCell g e := h.1.2
      have heq : e = D.displayedEvent := h.2
      exact ⟨⟨hg, ⟨by simpa [← heq] using heSupport,
        by simpa [← heq] using hAdm⟩⟩, heq.symm⟩
    · rintro ⟨⟨hg, hDisplayedSupport, hAdm⟩, heq⟩
      exact ⟨⟨⟨hg, by simpa [heq] using hDisplayedSupport⟩,
        by simpa [heq] using hAdm⟩, heq.symm⟩
  calc
    D.mu = ∑ ge ∈ P.admissibleCells D.eventSupport, F ge := hMain
    _ =
        (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 = D.displayedEvent), F ge) +
        (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 ≠ D.displayedEvent), F ge) := by
      exact (Finset.sum_filter_add_sum_filter_not
        (P.admissibleCells D.eventSupport)
        (fun ge : Fin T × ℤ => ge.2 = D.displayedEvent) F).symm
    _ =
        (∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
          P.omega D g D.displayedEvent * P.CATT g D.displayedEvent) +
        (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 ≠ D.displayedEvent),
          P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2) := by
      rw [hDisplayedCells, Finset.sum_map]
      rfl

/-- Apparent pretrends: a displayed lead can equal a weighted sum of
post-treatment effects once all negative-event-time CATTs vanish. -/
theorem apparent_pretrends_from_post_treatment (P : EventStudySystem T)
    (D : P.ConventionalDesign)
    (hCausal : P.EventStudyCausalRestrictions)
    (hResidualization : P.ConventionalResidualization D)
    (hDenomPos : 0 < P.residualDenom D)
    (hMuRatio : D.mu = P.conventionalMuRatio D)
    (hSupport : P.ConventionalFiniteSupport D)
    (hLead : D.displayedEvent < 0) :
    D.mu =
      ∑ ge ∈ (P.admissibleCells D.eventSupport).filter (fun ge => 0 ≤ ge.2),
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 := by
  have _ := hLead
  let F : Fin T × ℤ → ℝ := fun ge => P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2
  have hMain :
      D.mu = ∑ ge ∈ P.admissibleCells D.eventSupport, F ge := by
    simpa [F] using
      contamination_representation P D hCausal hResidualization hDenomPos
        hMuRatio hSupport
  have hNegZero :
      ∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ¬ 0 ≤ ge.2), F ge = 0 := by
    apply Finset.sum_eq_zero
    intro ge hge
    have hmem : ge ∈ P.admissibleCells D.eventSupport := (Finset.mem_filter.mp hge).1
    have hneg : ¬ 0 ≤ ge.2 := (Finset.mem_filter.mp hge).2
    have hlt : ge.2 < 0 := not_le.mp hneg
    have hg : ge.1 ∈ P.cohorts := (hSupport.hCellsSupported ge hmem).1
    simp [F, P.CATT_eq_zero_of_noAnticipation hCausal.hNoAnticipation hg hlt]
  calc
    D.mu = ∑ ge ∈ P.admissibleCells D.eventSupport, F ge := hMain
    _ =
        (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => 0 ≤ ge.2), F ge) +
        (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ¬ 0 ≤ ge.2), F ge) := by
      exact (Finset.sum_filter_add_sum_filter_not
        (P.admissibleCells D.eventSupport)
        (fun ge : Fin T × ℤ => 0 ≤ ge.2) F).symm
    _ = ∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => 0 ≤ ge.2), F ge := by
      rw [hNegZero, add_zero]

end EventStudySystem

end EventStudyContamination
end Panel.EstimandCharacterization
end Causalean
