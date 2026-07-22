/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sun-Abraham (2021): population bridge to the finite event-study system

Anchors the abstract `EventStudySystem` (whose mean fields are free reals) to a
genuine probability space carrying adoption-path–indexed potential outcomes.
An `EventStudyPopulation` bundles `(Ω, μ)`, a realized adoption cohort
`G : Ω → WithTop (Fin T)`, a calendar-time map, and the potential-outcome family
`Ypath t h ω = Y_{ωt}(h)`. Its `toSystem` fills every mean field of
`EventStudySystem` with an event-level conditional mean of a potential-outcome
slice (via `eventCondExp`); in particular the estimand
`CATT g e` becomes the genuine population contrast
`E[Y_{·t}(g) − Y_{·t}(∞) ∣ G = g]`.

The three Sun-Abraham causal restrictions
(`Consistency`, `NoAnticipation`, `PathConsistency`) are then **derived** from
Ω-level potential-outcome facts (the observed outcome is the PO under the
realized path — consistency is definitional — and structural no-anticipation),
not assumed on the abstract reals. Only `MeanParallelUntreated` — the additive
fixed-effect parallel-trends restriction on the never-treated potential outcome —
remains a genuine modeling hypothesis, supplied to the discharge lemma.

Source spec:
`doc/basic_concepts/po/estimand_characterization/sun_abraham_event_study.tex`,
Definition `def:po-estimand-sa-system` and Assumption `ass:po-estimand-sa-causal`.
-/

import Causalean.Panel.EstimandCharacterization.EventStudyContamination.Contamination
import Causalean.Panel.EstimandCharacterization.EventStudyContamination.InteractionWeighted
import Causalean.Panel.PO.PopulationCells

/-! # Sun-Abraham event-study population bridge

This file constructs a finite `EventStudySystem` from a probability space with
adoption-path potential outcomes, defining its mean fields as cohort-cell
conditional means and deriving the Sun-Abraham causal restrictions from the
underlying potential-outcome structure. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace EventStudyContamination

open MeasureTheory
open Causalean.PO
open Causalean.Panel.PO

/-- A staggered-adoption event-study **population**: a probability space with a
realized adoption cohort `G`, a calendar-time map, and adoption-path–indexed
potential outcomes `Ypath t h ω = Y_{ωt}(h)`.

The cohort cells `{ω | G ω = h}` (over all paths `h : WithTop (Fin T)`,
including `⊤` = never-treated) are measurable events on which the event-study
means are computed. They are not required to have positive mass globally:
zero-mass paths are allowed, and support/positivity is imposed only by the
downstream event-level design hypotheses that need it. `time` is required
strictly monotone so that the calendar order used by `NoAnticipation` agrees
with the adoption-date order used by `absorbingTreatment`. -/
structure EventStudyPopulation (T : ℕ) where
  /-- Unit sample space. -/
  Ω : Type*
  /-- Measurable-space structure on `Ω`. -/
  [measΩ : MeasurableSpace Ω]
  /-- Population measure. -/
  μ : Measure Ω
  /-- `μ` is a probability measure. -/
  [probμ : IsProbabilityMeasure μ]
  /-- Realized adoption cohort of each unit (`⊤` = never treated). -/
  G : Ω → WithTop (Fin T)
  /-- Each cohort cell `{G = h}` is measurable. -/
  Gcell_meas : ∀ h, MeasurableSet (G ⁻¹' {h})
  /-- Calendar-time map on periods. -/
  time : Fin T → ℤ
  /-- Calendar time is strictly increasing in the period index, so the calendar
  order matches the adoption-date order. -/
  time_strictMono : StrictMono time
  /-- Finite adoption cohorts included in the event-study support. -/
  cohorts : Finset (Fin T)
  /-- Potential-outcome family: `Ypath t h ω` is the outcome of unit `ω` at
  period `t` under adoption path `h`. -/
  Ypath : Fin T → WithTop (Fin T) → Ω → ℝ
  /-- **Structural no-anticipation.** In any period where path `h` is untreated
  (`absorbingTreatment h t = 0`, i.e. `h = ⊤` or the period precedes adoption),
  the outcome under `h` equals the never-treated outcome, for every unit. -/
  hNoAnt : ∀ (h : WithTop (Fin T)) (t : Fin T) (ω : Ω),
    EventStudySystem.absorbingTreatment (T := T) h t = 0 →
    Ypath t h ω = Ypath t ⊤ ω

namespace EventStudyPopulation

variable {T : ℕ}

attribute [instance] EventStudyPopulation.measΩ EventStudyPopulation.probμ

/-- The event `{ω | G ω = h}` for an adoption path. -/
def cell (E : EventStudyPopulation T) (h : WithTop (Fin T)) : Set E.Ω :=
  E.G ⁻¹' {h}

/-- The population mass of an adoption-path event, as a real number. -/
def cellMass (E : EventStudyPopulation T) (h : WithTop (Fin T)) : ℝ :=
  (E.μ (E.cell h)).toReal

/-- Event-level conditional mean on an adoption-path cell. This is totalized by
`eventCondExp`, so zero-mass paths are allowed at the population-bridge layer. -/
noncomputable def cellMean (E : EventStudyPopulation T) (f : E.Ω → ℝ)
    (h : WithTop (Fin T)) : ℝ :=
  eventCondExp E.μ (E.cell h) f

/-- Event-level means agree when the integrands agree pointwise on the
adoption-path cell. -/
theorem cellMean_congr_on (E : EventStudyPopulation T) {f g : E.Ω → ℝ}
    (h : WithTop (Fin T)) (heq : ∀ ω ∈ E.cell h, f ω = g ω) :
    E.cellMean f h = E.cellMean g h :=
  eventCondExp_congr_on E.μ (E.Gcell_meas h) heq

/-- Event-level means are additive over subtraction of integrable integrands. -/
theorem cellMean_sub (E : EventStudyPopulation T) {f g : E.Ω → ℝ}
    (h : WithTop (Fin T))
    (hf : IntegrableOn f (E.cell h) E.μ) (hg : IntegrableOn g (E.cell h) E.μ) :
    E.cellMean (f - g) h = E.cellMean f h - E.cellMean g h :=
  eventCondExp_sub E.μ (E.cell h) hf hg

/-- The observed outcome at period `t`: the potential outcome under the unit's
realized adoption path. Consistency is thus definitional. -/
def observed (E : EventStudyPopulation T) (t : Fin T) (ω : E.Ω) : ℝ :=
  E.Ypath t (E.G ω) ω

/-- The event-study system induced by a population: every mean field is the
cohort-cell conditional mean of the appropriate potential-outcome slice.

`cellMass g t` is period-independent, equal to the cross-sectional cohort mass
`ℙ(G = g)`: in the balanced unit-period population the abstract system targets,
cohort `g`'s cell at every period `t` is the cohort-`g` units, of mass `ℙ(G = g)`.
This is faithful because `cellMass` enters the downstream objects only through the
normalized contamination weight `omega = cellMassAtEvent · Rdot / residualDenom`
and the cell-grid weight `cellMassAtEvent / cellTotalMass`, both of which are
ratios in which any uniform rescaling of `cellMass` cancels; the absolute value
never matters. (It would be wrong for an *unbalanced* panel, which is out of the
system's balanced scope.) -/
noncomputable def toSystem (E : EventStudyPopulation T) : EventStudySystem T where
  time := E.time
  cohorts := E.cohorts
  cohortShare h := E.cellMass h
  cellMass g _t := E.cellMass (EventStudySystem.finitePath g)
  observedPathMean h t := E.cellMean (E.observed t) h
  observedMean g t := E.cellMean (E.observed t) (EventStudySystem.finitePath g)
  treatedMean g t :=
    E.cellMean (E.Ypath t (EventStudySystem.finitePath g))
      (EventStudySystem.finitePath g)
  untreatedMean g t :=
    E.cellMean (E.Ypath t ⊤) (EventStudySystem.finitePath g)
  untreatedPathMean h t := E.cellMean (E.Ypath t ⊤) h

/-- On the cohort cell `{G = finitePath g}`, the observed outcome equals the
own-path potential outcome — the pointwise content of consistency. -/
theorem observed_eqOn_cell (E : EventStudyPopulation T) (g : Fin T) (t : Fin T) :
    ∀ ω ∈ E.cell (EventStudySystem.finitePath g),
      E.observed t ω = E.Ypath t (EventStudySystem.finitePath g) ω := by
  intro ω hω
  have hG : E.G ω = EventStudySystem.finitePath g := by
    simpa [cell] using hω
  simp [observed, hG]

/-- **Consistency is derived.** The observed cohort mean equals the own-path
potential-outcome mean, because the observed outcome is the potential outcome
under the realized path. -/
theorem toSystem_consistency (E : EventStudyPopulation T) :
    (E.toSystem).Consistency := by
  intro g _hg t
  simpa [toSystem] using
    E.cellMean_congr_on (EventStudySystem.finitePath g)
      (E.observed_eqOn_cell g t)

/-- **No-anticipation is derived** from structural no-anticipation: on a
pre-adoption period the own-path and never-treated potential-outcome means
coincide, so their cohort means do. -/
theorem toSystem_noAnticipation (E : EventStudyPopulation T) :
    (E.toSystem).NoAnticipation := by
  intro g _hg t hlt
  have htg : t < g := E.time_strictMono.lt_iff_lt.mp hlt
  have habs : EventStudySystem.absorbingTreatment (T := T)
      (EventStudySystem.finitePath g) t = 0 := by
    have hnotle : ¬ (EventStudySystem.finitePath g) ≤ (t : WithTop (Fin T)) := by
      simp only [EventStudySystem.finitePath, AdoptionPath.finite, not_le]
      exact_mod_cast htg
    simp [EventStudySystem.absorbingTreatment, AdoptionPath.absorbingTreatment_eq,
      hnotle]
  simpa [toSystem] using
    E.cellMean_congr_on (EventStudySystem.finitePath g)
      (fun ω _ => E.hNoAnt (EventStudySystem.finitePath g) t ω habs)

/-- **Path-consistency is derived**: on a period where comparison path `h` is
untreated, the observed path mean equals the never-treated path mean. -/
theorem toSystem_pathConsistency (E : EventStudyPopulation T) :
    (E.toSystem).PathConsistency := by
  intro h t huntreated
  simpa [toSystem] using
    E.cellMean_congr_on h
      (fun ω hω => by
        have hG : E.G ω = h := by simpa [cell] using hω
        have h1 : E.observed t ω = E.Ypath t h ω := by simp [observed, hG]
        rw [h1]
        exact E.hNoAnt h t ω huntreated)

/-- **Outcome integrability (Sun-Abraham assumption H5).** Every
potential-outcome slice `Ypath t h` is `μ`-integrable. This is the population
content of the source theorem's integrability hypothesis: it is exactly the
condition under which each cohort-cell mean
`E.cellMean (Ypath t h) · = E[Y_{·t}(h) ∣ G = ·]` is a genuine finite expectation
rather than only a totalized value. Not every population satisfies it; for
example, heavy-tailed potential outcomes can fail this condition. -/
def OutcomesIntegrable (E : EventStudyPopulation T) : Prop :=
  ∀ (t : Fin T) (h : WithTop (Fin T)), Integrable (E.Ypath t h) E.μ

/-- **Bundle: the induced system satisfies the Sun-Abraham causal
restrictions**, given the additive parallel-trends hypothesis. Consistency and
no-anticipation are derived; only parallel trends is assumed. -/
theorem toSystem_causalRestrictions (E : EventStudyPopulation T)
    (hPar : (E.toSystem).MeanParallelUntreated) :
    (E.toSystem).EventStudyCausalRestrictions where
  hConsistency := E.toSystem_consistency
  hNoAnticipation := E.toSystem_noAnticipation
  hMeanParallelUntreated := hPar

/-- **Causal-meaning certificate.** In the induced system, `CATT g e` is
literally the cohort-cell average of the population potential-outcome contrast
`E[Y_{·t}(g) ∣ G = g] − E[Y_{·t}(∞) ∣ G = g]`, so the estimand carries genuine
causal content rather than a docstring assertion on free reals. -/
theorem toSystem_CATT_eq_po_contrast (E : EventStudyPopulation T)
    (g : Fin T) (e : ℤ) :
    (E.toSystem).CATT g e =
      (((E.toSystem).targetPeriods g e).card : ℝ)⁻¹ *
        ∑ t ∈ (E.toSystem).targetPeriods g e,
          (E.cellMean (E.Ypath t (EventStudySystem.finitePath g))
              (EventStudySystem.finitePath g)
            - E.cellMean (E.Ypath t ⊤) (EventStudySystem.finitePath g)) := by
  rfl

/-- **Integrability makes `CATT` a genuine expected contrast.** Under outcome
integrability (assumption H5), the two cohort-cell means combine into a single
cell mean of the potential-outcome difference: each summand is
`E[Y_{·t}(g) − Y_{·t}(∞) ∣ G = g]`, a genuine expectation of the individual
treatment-effect random variable. This is where the integrability hypothesis
does real work — `cellMean_sub` requires each slice to be integrable
on the cell, so without H5 the two means could not be merged. -/
theorem toSystem_CATT_eq_meanDiff (E : EventStudyPopulation T)
    (hInt : E.OutcomesIntegrable) (g : Fin T) (e : ℤ) :
    (E.toSystem).CATT g e =
      (((E.toSystem).targetPeriods g e).card : ℝ)⁻¹ *
        ∑ t ∈ (E.toSystem).targetPeriods g e,
          E.cellMean
            (E.Ypath t (EventStudySystem.finitePath g) - E.Ypath t ⊤)
            (EventStudySystem.finitePath g) := by
  rw [toSystem_CATT_eq_po_contrast]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [E.cellMean_sub (EventStudySystem.finitePath g)
      (hInt t (EventStudySystem.finitePath g)).integrableOn (hInt t ⊤).integrableOn]

/-- **Population contamination representation (headline).** For a population
event-study system, the conventional TWFE event-study coefficient `D.mu` equals
the contamination-weighted sum of genuine population cohort-relative-time
effects `CATT g e = E[Y_{·t}(g) − Y_{·t}(∞) ∣ G = g]`. Consistency and
no-anticipation are derived from the potential-outcome structure; only the
additive parallel-trends restriction `hPar`, the outcome-integrability
assumption `hIntegrable` (source H5), and the design-side projection witnesses
are assumed. This is the Sun-Abraham contamination theorem stated over a
genuinely potential-outcome-anchored system.

Integrability certifies that each `CATT g e` is the genuine expected
treatment-effect contrast `E[Y_{·t}(g) − Y_{·t}(∞) ∣ G = g]` (see
`toSystem_CATT_eq_meanDiff`); the contamination identity itself is an algebraic
FWL rearrangement that holds for the total cell means regardless. -/
theorem contamination_representation_population (E : EventStudyPopulation T)
    (D : (E.toSystem).ConventionalDesign)
    (hPar : (E.toSystem).MeanParallelUntreated)
    (hSupport : (E.toSystem).ConventionalFiniteSupport D)
    (hIntegrable : E.OutcomesIntegrable)
    (hCell : (E.toSystem).CellGridResidualization D) :
    D.mu =
      ∑ ge ∈ (E.toSystem).admissibleCells D.eventSupport,
        (E.toSystem).omega D ge.1 ge.2 * (E.toSystem).CATT ge.1 ge.2 := by
  have _ := hIntegrable
  exact (E.toSystem).contamination_representation_of_cellGrid
    (E.toSystem_causalRestrictions hPar) hSupport hCell

/-- **Population interaction-weighted characterization (headline).** For a
population event-study system, the interaction-weighted estimand `nuIW` is a
convex cohort-share average of genuine population effects `CATT g ℓ`, with no
contamination from other event times. Consistency, no-anticipation, and
path-consistency are derived; only the comparison-group parallel-trends
restriction, the outcome-integrability assumption `hIntegrable` (source H5), and
the design-side support/weight conditions are assumed. Integrability certifies
that each `CATT g ℓ` is a genuine expected treatment-effect contrast (see
`toSystem_CATT_eq_meanDiff`). -/
theorem IW_convex_characterization_population (E : EventStudyPopulation T)
    (I : (E.toSystem).IWDesign)
    (hEventTime_nonneg : 0 ≤ I.eventTime)
    (hIWParallelTrends : (E.toSystem).IWComparisonParallelTrends I)
    (hSupport : (E.toSystem).IWSupport I)
    (hRhoNonneg : ∀ g ∈ I.cohortsIW, 0 ≤ I.rho g)
    (hRhoSumOne : ∑ g ∈ I.cohortsIW, I.rho g = 1)
    (hIntegrable : E.OutcomesIntegrable)
    {lo hi : ℝ}
    (hLo : ∀ g ∈ I.cohortsIW, lo ≤ (E.toSystem).CATT g I.eventTime)
    (hHi : ∀ g ∈ I.cohortsIW, (E.toSystem).CATT g I.eventTime ≤ hi) :
    (∀ g ∈ I.cohortsIW, (E.toSystem).Delta I g = (E.toSystem).CATT g I.eventTime) ∧
      (E.toSystem).nuIW I =
        ∑ g ∈ I.cohortsIW, I.rho g * (E.toSystem).CATT g I.eventTime ∧
      lo ≤ (E.toSystem).nuIW I ∧ (E.toSystem).nuIW I ≤ hi := by
  have _ := hIntegrable
  exact (E.toSystem).IW_convex_characterization I
    hEventTime_nonneg
    E.toSystem_consistency E.toSystem_noAnticipation E.toSystem_pathConsistency
    hIWParallelTrends hSupport hRhoNonneg hRhoSumOne hLo hHi

end EventStudyPopulation

end EventStudyContamination
end Panel.EstimandCharacterization
end Causalean
