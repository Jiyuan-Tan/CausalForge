/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sun-Abraham (2021): finite event-study setup

Finite-cell formalization of the staggered-adoption event-study objects used by
the conventional TWFE contamination theorem and the interaction-weighted
event-study characterization.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/sun_abraham_event_study.md`.
-/

import Causalean.Panel.Weighted.AdditiveSpan
import Causalean.Panel.AdoptionPath
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Order.WithBot

/-! # Sun-Abraham Event-Study Setup

This file provides the finite staggered-adoption event-study system used by the
Sun-Abraham characterization modules. It defines the cohort, period,
relative-time, potential-outcome, and comparison-path primitives on which the
conventional and interaction-weighted estimands are built. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace EventStudyContamination

open Finset

/-- Finite staggered-adoption event-study system.

Periods are `Fin T`, adoption paths are `WithTop (Fin T)`, and `⊤` is the
never-treated path. The finite-cohort set `cohorts` records the adopted cohorts
used in event-study sums; potential-outcome and observed mean fields are finite
cell-level primitives. -/
structure EventStudySystem (T : ℕ) where
  /-- Integer-valued period map used to form relative event times. -/
  time : Fin T → ℤ
  /-- Finite adoption cohorts included in the event-study support. -/
  cohorts : Finset (Fin T)
  /-- Population share of each adoption path, including `⊤` for never treated. -/
  cohortShare : WithTop (Fin T) → ℝ
  /-- Balanced cohort-period cell mass. -/
  cellMass : Fin T → Fin T → ℝ
  /-- Factual observed outcome mean by adoption path and period. -/
  observedPathMean : WithTop (Fin T) → Fin T → ℝ
  /-- Factual observed outcome mean by finite cohort and period. -/
  observedMean : Fin T → Fin T → ℝ
  /-- Mean potential outcome under the cohort's own treatment path. -/
  treatedMean : Fin T → Fin T → ℝ
  /-- Mean never-treated potential outcome for each finite cohort. -/
  untreatedMean : Fin T → Fin T → ℝ
  /-- Mean never-treated potential outcome for any comparison adoption path. -/
  untreatedPathMean : WithTop (Fin T) → Fin T → ℝ

namespace EventStudySystem

variable {T : ℕ}

/-- A finite adoption path, embedded in `WithTop (Fin T)`. -/
def finitePath (g : Fin T) : WithTop (Fin T) := AdoptionPath.finite g

/-- `h = ∞`, the never-treated adoption path. -/
def isNeverTreated (h : WithTop (Fin T)) : Prop := AdoptionPath.isNeverTreated h

/-- `h < ∞`, the path is eventually treated. -/
def isEventuallyTreated (h : WithTop (Fin T)) : Prop := AdoptionPath.isEventuallyTreated h

/-- Relative event time `t - g` under the system's integer-valued period map. -/
def relTime (P : EventStudySystem T) (g t : Fin T) : ℤ :=
  P.time t - P.time g

open Classical in
/-- Absorbing treatment path `1{h < ∞ and h ≤ t}`. Since `⊤ ≤ t` is false,
the never-treated path is untreated in every finite period. -/
noncomputable def absorbingTreatment (h : WithTop (Fin T)) (t : Fin T) : ℝ :=
  AdoptionPath.absorbingTreatment h t

open Classical in
/-- The target periods for finite cohort `g` at relative time `e`. -/
noncomputable def targetPeriods (P : EventStudySystem T) (g : Fin T) (e : ℤ) :
    Finset (Fin T) :=
  Finset.univ.filter (fun t => P.relTime g t = e)

open Classical in
/-- Baseline periods with relative time `-1` for finite cohort `g`. -/
noncomputable def baselinePeriods (P : EventStudySystem T) (g : Fin T) :
    Finset (Fin T) :=
  P.targetPeriods g (-1)

/-- A finite cohort-relative-time cell is admissible when the cohort is in
support and at least one finite period realizes that relative time. -/
def AdmissibleCell (P : EventStudySystem T) (g : Fin T) (e : ℤ) : Prop :=
  g ∈ P.cohorts ∧ (P.targetPeriods g e).Nonempty

open Classical in
/-- Finite support of admissible cells, filtered through an explicit finite
relative-time support `E`. -/
noncomputable def admissibleCells (P : EventStudySystem T) (E : Finset ℤ) :
    Finset (Fin T × ℤ) :=
  (P.cohorts.product E).filter (fun ge => P.AdmissibleCell ge.1 ge.2)

open Classical in
/-- Cohorts observed at relative time `e`, with membership checked against an
explicit finite relative-time support. -/
noncomputable def cohortsAtEvent (P : EventStudySystem T) (E : Finset ℤ)
    (e : ℤ) : Finset (Fin T) :=
  P.cohorts.filter (fun g => e ∈ E ∧ P.AdmissibleCell g e)

/-- Balanced finite-cell mass for cohort-relative-time cell `(g,e)`. -/
noncomputable def cellMassAtEvent (P : EventStudySystem T) (g : Fin T)
    (e : ℤ) : ℝ :=
  ∑ t ∈ P.targetPeriods g e, P.cellMass g t

/-- Average factual observed outcome over the periods realizing `(g,e)`. -/
noncomputable def observedCellMean (P : EventStudySystem T) (g : Fin T)
    (e : ℤ) : ℝ :=
  ((P.targetPeriods g e).card : ℝ)⁻¹ *
    ∑ t ∈ P.targetPeriods g e, P.observedMean g t

/-- Average treated-minus-never potential-outcome contrast over `(g,e)`. -/
noncomputable def meanCellContrast (P : EventStudySystem T) (g : Fin T)
    (e : ℤ) : ℝ :=
  ((P.targetPeriods g e).card : ℝ)⁻¹ *
    ∑ t ∈ P.targetPeriods g e, (P.treatedMean g t - P.untreatedMean g t)

/-- Cohort average treatment effect on the treated for the finite
cohort-relative-time cell `(g,e)`.

This definition averages the treated-minus-never potential-outcome contrast over
all finite periods in `targetPeriods g e`. It therefore matches the source
point-period `CATT_{g,e}` at period `g+e` when that target-period set is a
singleton, as in the usual injective calendar-time encoding. -/
noncomputable def CATT (P : EventStudySystem T) (g : Fin T) (e : ℤ) : ℝ :=
  P.meanCellContrast g e

/-- Target-period observed mean for an arbitrary adoption path, used by the
IW comparison-group DID contrast. -/
noncomputable def pathTargetMean (P : EventStudySystem T)
    (h : WithTop (Fin T)) (g : Fin T) (e : ℤ) : ℝ :=
  ((P.targetPeriods g e).card : ℝ)⁻¹ *
    ∑ t ∈ P.targetPeriods g e, P.observedPathMean h t

/-- Baseline observed mean for an arbitrary adoption path, using relative
time `-1` for treated cohort `g`. -/
noncomputable def pathBaselineMean (P : EventStudySystem T)
    (h : WithTop (Fin T)) (g : Fin T) : ℝ :=
  ((P.baselinePeriods g).card : ℝ)⁻¹ *
    ∑ t ∈ P.baselinePeriods g, P.observedPathMean h t

/-- Consistency for observed finite-cohort outcome means. -/
def Consistency (P : EventStudySystem T) : Prop :=
  ∀ g ∈ P.cohorts, ∀ t, P.observedMean g t = P.treatedMean g t

/-- Path-level consistency for comparison-group adoption paths.

This is the path-level analogue of `Consistency` for arbitrary adoption
paths `h : WithTop (Fin T)`: in any finite period `t` where path `h` is
untreated (`absorbingTreatment h t = 0`), the factual observed path mean equals
the never-treated potential-outcome path mean. It is the honest causal primitive
the source uses to convert a comparison group's *observed* trend into an
*untreated potential-outcome* trend. -/
def PathConsistency (P : EventStudySystem T) : Prop :=
  ∀ (h : WithTop (Fin T)) (t : Fin T),
    absorbingTreatment h t = 0 → P.observedPathMean h t = P.untreatedPathMean h t

/-- Path-consistency, applied to an untreated comparison period, yields the
observed-equals-untreated path-mean bridge used by the IW comparison-group
argument. -/
theorem pathConsistency_observed_eq_untreated (P : EventStudySystem T)
    (hPathConsistency : P.PathConsistency) {h : WithTop (Fin T)} {t : Fin T}
    (hUntreated : absorbingTreatment h t = 0) :
    P.observedPathMean h t = P.untreatedPathMean h t :=
  hPathConsistency h t hUntreated

/-- No anticipation in mean potential outcomes. -/
def NoAnticipation (P : EventStudySystem T) : Prop :=
  ∀ g ∈ P.cohorts, ∀ t, P.time t < P.time g →
    P.treatedMean g t = P.untreatedMean g t

/-- Additive mean parallel untreated paths. -/
def MeanParallelUntreated (P : EventStudySystem T) : Prop :=
  ∃ h : Fin T → Fin T → ℝ, Causalean.Panel.Weighted.IsUnitTimeAdditive h ∧
    ∀ g ∈ P.cohorts, ∀ t, P.untreatedMean g t = h g t

/-- Sun-Abraham event-study causal restrictions. Field names mirror the NL
artifact's assumption names. -/
structure EventStudyCausalRestrictions (P : EventStudySystem T) : Prop where
  hConsistency : P.Consistency
  hNoAnticipation : P.NoAnticipation
  hMeanParallelUntreated : P.MeanParallelUntreated

/-- No anticipation implies zero CATT on pre-treatment relative-time cells. -/
theorem CATT_eq_zero_of_noAnticipation (P : EventStudySystem T)
    (hNoAnticipation : P.NoAnticipation) {g : Fin T} {e : ℤ}
    (hg : g ∈ P.cohorts) (he : e < 0) :
    P.CATT g e = 0 := by
  unfold CATT meanCellContrast
  rw [Finset.sum_eq_zero]
  · simp
  · intro t ht
    have hrel : P.relTime g t = e := by
      simpa [targetPeriods] using ht
    have hpre : P.time t < P.time g := by
      have hneg : P.relTime g t < 0 := by
        simpa [hrel] using he
      simpa [relTime] using (sub_neg.mp hneg)
    have hmean := hNoAnticipation g hg t hpre
    simp [hmean]

/-- Cell-mean decomposition into additive untreated fixed effects and CATT. -/
theorem observedCellMean_eq_fixedEffects_add_CATT (P : EventStudySystem T)
    (hCausal : P.EventStudyCausalRestrictions) {g : Fin T} {e : ℤ}
    (hg : g ∈ P.cohorts) :
    ∃ alpha : Fin T → ℝ, ∃ lambda : Fin T → ℝ,
      P.observedCellMean g e =
        ((P.targetPeriods g e).card : ℝ)⁻¹ *
          ∑ t ∈ P.targetPeriods g e, (alpha g + lambda t) +
        P.CATT g e := by
  rcases hCausal.hMeanParallelUntreated with ⟨hFE, ⟨alpha, lambda, hFE_add⟩, hUntreated⟩
  refine ⟨alpha, lambda, ?_⟩
  unfold observedCellMean CATT meanCellContrast
  have hsum :
      (∑ t ∈ P.targetPeriods g e, P.observedMean g t) =
        (∑ t ∈ P.targetPeriods g e, (alpha g + lambda t)) +
          ∑ t ∈ P.targetPeriods g e, (P.treatedMean g t - P.untreatedMean g t) := by
    calc
      (∑ t ∈ P.targetPeriods g e, P.observedMean g t) =
          ∑ t ∈ P.targetPeriods g e,
            ((alpha g + lambda t) + (P.treatedMean g t - P.untreatedMean g t)) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [hCausal.hConsistency g hg t, hUntreated g hg t, hFE_add g t]
        calc
          P.treatedMean g t =
              P.treatedMean g t - (alpha g + lambda t) + (alpha g + lambda t) := by
            exact (sub_add_cancel (P.treatedMean g t) (alpha g + lambda t)).symm
          _ = alpha g + lambda t + (P.treatedMean g t - (alpha g + lambda t)) := by
            rw [add_comm]
      _ = (∑ t ∈ P.targetPeriods g e, (alpha g + lambda t)) +
          ∑ t ∈ P.targetPeriods g e, (P.treatedMean g t - P.untreatedMean g t) := by
        rw [Finset.sum_add_distrib]
  rw [hsum, mul_add]

/-- Under an injective calendar-time encoding, at most one finite period can
realize a given relative time, so the target-period set of any cell is a
subsingleton. -/
theorem targetPeriods_subsingleton_of_injective (P : EventStudySystem T)
    (hInj : Function.Injective P.time) (g : Fin T) (e : ℤ) :
    (P.targetPeriods g e : Set (Fin T)).Subsingleton := by
  intro a ha b hb
  simp only [Finset.coe_filter, Set.mem_setOf_eq, targetPeriods, relTime] at ha hb
  have hab : P.time a = P.time b := by
    have := ha.2.trans hb.2.symm
    linarith [this]
  exact hInj hab

/-- **G1 faithfulness corollary.** When the calendar-time map `time` is
injective (the usual one-period-per-relative-time encoding), the cell-averaged
`CATT g e` collapses to the source's *point* `CATT_{g,e}` at the unique period
`t` realizing relative time `e`, i.e. `treatedMean g t - untreatedMean g t`.

This certifies that the cell-averaged `CATT` equals the source's
point-period object exactly in the injective setting the paper assumes; the
main theorems hold for the (wider) cell-averaged class and specialize here. -/
theorem CATT_eq_sourceCATT_of_injective (P : EventStudySystem T)
    (hInj : Function.Injective P.time) {g : Fin T} {e : ℤ} {t : Fin T}
    (ht : t ∈ P.targetPeriods g e) :
    P.CATT g e = P.treatedMean g t - P.untreatedMean g t := by
  have hsub := P.targetPeriods_subsingleton_of_injective hInj g e
  have hsingleton : P.targetPeriods g e = {t} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨ht, ?_⟩
    intro x hx
    exact hsub (by simpa using hx) (by simpa using ht)
  unfold CATT meanCellContrast
  rw [hsingleton]
  simp

end EventStudySystem

end EventStudyContamination
end Panel.EstimandCharacterization
end Causalean
