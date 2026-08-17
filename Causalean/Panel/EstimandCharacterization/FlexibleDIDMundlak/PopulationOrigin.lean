/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Wooldridge population origin of staggered-DID cell means

Makes the conditional-expectation origin of the staggered-DID cell means
definitional rather than an assumed identification hypothesis.

`StaggeredATTCells.ofPopulation` builds a `StaggeredATTCells` out of a probability
model `(μ, cellEvent, Y0pop, Ygpop, Yobspop)` by *defining* each cell mean as the
event-level conditional expectation `eventCondExp μ (cellEvent g t c) ·` of the
corresponding population outcome. The constructor assumes positive cell mass and
cell-level integrability for the untreated, cohort-specific, and observed
outcomes, so the resulting means have the intended population interpretation.
With this definition:

* `consistency_treated` / `consistency_untreated` are **derived** from pointwise
  potential-outcome consistency on each cell (`eventCondExp_congr_on`), exactly as
  DCDH's `cellMean_consistency` derives the DCDH consistency identity;
* the identification hypothesis `hY0` of `PopulationBridge.m0_eq_eventCondExp_*`
  holds by `rfl`, since `Y0Mean` is now *defined* as that `eventCondExp`.

The payoff corollaries `m0_eq_eventCondExp_treated_ofPopulation` /
`_untreated_ofPopulation` show that on the relevant cell the saturated
untreated regression's fitted value equals the population conditional expectation
`E[Y_t(∞) | G = g, t, C = c]`, with the *causal* content carried entirely by
`recovers_target_Y0` / `untreatedFit`.  No paper assumption is strengthened: the
covariate-weight witness (`cohortShare`, `covarWeight`) is passed in exactly as
DCDH passes the FWL residual `Dtilde`, and the pointwise consistency inputs are
exactly the paper's consistency axiom restricted to each cell.
-/

import Causalean.Panel.EstimandCharacterization.FlexibleDIDMundlak.PopulationBridge
import Causalean.PO.Conditioning.EventCondExp

/-! # Wooldridge Population Origin

This file constructs the finite staggered-DID cell system from an underlying
probability model.  `StaggeredATTCells.ofPopulation` defines the cell means as
raw event-level quotients of population outcomes and derives the consistency
fields from pointwise potential-outcome consistency on the corresponding cells.
The corollaries `m0_eq_eventCondExp_treated_ofPopulation` and
`m0_eq_eventCondExp_untreated_ofPopulation` specialize the population bridge for
systems built by this constructor, so the untreated-fit identification
hypothesis is definitional. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace FlexibleDIDMundlak

open MeasureTheory Causalean.PO

variable {Cohort Time Covar : Type*}
  [Fintype Cohort] [Fintype Time] [Fintype Covar]

/-- Builds a finite staggered-DID cell system from a population model.

The probability model has a sample space `Ω` with cell
events `cellEvent g t c` and population potential / factual outcomes
`Y0pop`, `Ygpop`, `Yobspop`.  The cell means are *defined* as the population
event-level conditional expectations

* `Y0Mean g t c     = E[Y(0)  | cell g t c]`,
* `YgMean g t c      = E[Y(g)  | cell g t c]`,
* `observedMean g t c = E[Y_obs | cell g t c]`.

The two consistency fields are **derived** from pointwise potential-outcome
consistency on each cell (`hcons_tr` / `hcons_ut`) via `eventCondExp_congr_on`:
on a treated cell the observed factual equals the cohort-`g` outcome pointwise,
on an untreated cell it equals the untreated outcome pointwise.

As in `DCDHPanel.ofPopulation`, the cell-weight data (`cohortShare`,
`covarWeight`) and their side conditions (`cohortShare_pos_on_treated`,
`covarWeight_nonneg`, `covarWeight_sum_one`) are supplied as witnesses — the
weight construction is separate from the population cell-mean definitions. -/
noncomputable def StaggeredATTCells.ofMeasure
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (cellEvent : Cohort → Time → Covar → Set Ω)
    (Y0pop Ygpop Yobspop : Ω → ℝ)
    (treatedCell untreatedCell : Cohort → Time → Prop)
    (cohortShare : Cohort → ℝ) (covarWeight : Cohort → Covar → ℝ)
    (hmeas : ∀ g t c, MeasurableSet (cellEvent g t c))
    (hcell_pos : ∀ g t c, 0 < (μ (cellEvent g t c)).toReal)
    (hY0_int : ∀ g t c, IntegrableOn Y0pop (cellEvent g t c) μ)
    (hYg_int : ∀ g t c, IntegrableOn Ygpop (cellEvent g t c) μ)
    (hYobs_int : ∀ g t c, IntegrableOn Yobspop (cellEvent g t c) μ)
    (cohortShare_pos_on_treated :
      ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t → 0 < cohortShare g)
    (covarWeight_nonneg : ∀ g c, 0 ≤ covarWeight g c)
    (covarWeight_sum_one : ∀ g, ∑ c, covarWeight g c = 1)
    (hcons_tr : ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t →
        ∀ c, ∀ ω ∈ cellEvent g t c, Yobspop ω = Ygpop ω)
    (hcons_ut : ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, untreatedCell g t →
        ∀ c, ∀ ω ∈ cellEvent g t c, Yobspop ω = Y0pop ω) :
    StaggeredATTCells Cohort Time Covar where
  cohortShare := cohortShare
  covarWeight := covarWeight
  treatedCell := treatedCell
  untreatedCell := untreatedCell
  Y0Mean g t c := eventCondExp μ (cellEvent g t c) Y0pop
  YgMean g t c := eventCondExp μ (cellEvent g t c) Ygpop
  observedMean g t c := eventCondExp μ (cellEvent g t c) Yobspop
  cohortShare_pos_on_treated := cohortShare_pos_on_treated
  covarWeight_nonneg := covarWeight_nonneg
  covarWeight_sum_one := covarWeight_sum_one
  consistency_treated g t hgt c :=
    have _ := hcell_pos g t c
    have _ := hYg_int g t c
    have _ := hYobs_int g t c
    eventCondExp_congr_on μ (hmeas g t c) (hcons_tr hgt c)
  consistency_untreated g t hut c :=
    have _ := hcell_pos g t c
    have _ := hY0_int g t c
    have _ := hYobs_int g t c
    eventCondExp_congr_on μ (hmeas g t c) (hcons_ut hut c)

/-- Probability-measure specialization of `StaggeredATTCells.ofMeasure`. -/
noncomputable def StaggeredATTCells.ofPopulation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (cellEvent : Cohort → Time → Covar → Set Ω)
    (Y0pop Ygpop Yobspop : Ω → ℝ)
    (treatedCell untreatedCell : Cohort → Time → Prop)
    (cohortShare : Cohort → ℝ) (covarWeight : Cohort → Covar → ℝ)
    (hmeas : ∀ g t c, MeasurableSet (cellEvent g t c))
    (hcell_pos : ∀ g t c, 0 < (μ (cellEvent g t c)).toReal)
    (hY0_int : ∀ g t c, IntegrableOn Y0pop (cellEvent g t c) μ)
    (hYg_int : ∀ g t c, IntegrableOn Ygpop (cellEvent g t c) μ)
    (hYobs_int : ∀ g t c, IntegrableOn Yobspop (cellEvent g t c) μ)
    (cohortShare_pos_on_treated :
      ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t → 0 < cohortShare g)
    (covarWeight_nonneg : ∀ g c, 0 ≤ covarWeight g c)
    (covarWeight_sum_one : ∀ g, ∑ c, covarWeight g c = 1)
    (hcons_tr : ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t →
        ∀ c, ∀ ω ∈ cellEvent g t c, Yobspop ω = Ygpop ω)
    (hcons_ut : ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, untreatedCell g t →
        ∀ c, ∀ ω ∈ cellEvent g t c, Yobspop ω = Y0pop ω) :
    StaggeredATTCells Cohort Time Covar :=
  StaggeredATTCells.ofMeasure μ cellEvent Y0pop Ygpop Yobspop treatedCell untreatedCell
    cohortShare covarWeight hmeas hcell_pos hY0_int hYg_int hYobs_int
    cohortShare_pos_on_treated covarWeight_nonneg covarWeight_sum_one hcons_tr hcons_ut

/-- **On a treated cell in a population-built system, the fitted untreated mean
equals the population conditional mean of the untreated potential outcome.**
Fix a population model on a sample space `Ω`, with population outcomes
`Y0pop`, `Ygpop`, `Yobspop`; suppose [every cell event `cellEvent g t c` is
measurable](hyp:hmeas), [every cell has strictly positive probability
mass](hyp:hcell_pos), and [the three population outcomes are each integrable on
every cell](hyp:hY0_int,hYg_int,hYobs_int). Suppose also [the cohort share is
strictly positive on every treated cell](hyp:cohortShare_pos_on_treated), [the
covariate weights are nonnegative](hyp:covarWeight_nonneg) and [sum to one
within each cohort](hyp:covarWeight_sum_one), and [the observed outcome agrees
pointwise with the cohort-`g` outcome on treated cells and with the untreated
outcome on untreated cells (pointwise consistency)](hyp:hcons_tr,hcons_ut). If
[the finite cell system `P` is exactly the one built from this population data
by `StaggeredATTCells.ofPopulation`](hyp:hP) and, for a saturated untreated
regression `S` on `P`, [no anticipation holds](hyp:hNA) and [conditional
parallel trends holds](hyp:hCPT), then on [any treated cell `(g,t)`](hyp:hgt),
[the saturated regression's fitted value `S.m0 g t c` equals the population
conditional mean `E[Y0pop | cellEvent g t c]`, for every covariate cell
`c`](goal).

Because `P.Y0Mean g t c` is defined as
`eventCondExp μ (cellEvent g t c) Y0pop`, the population-identification
hypothesis used by `m0_eq_eventCondExp_treated` holds by `rfl`. The causal
content (additive extrapolation via conditional parallel trends) is carried by
`recovers_target_Y0`. -/
theorem m0_eq_eventCondExp_treated_ofPopulation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (cellEvent : Cohort → Time → Covar → Set Ω)
    (Y0pop Ygpop Yobspop : Ω → ℝ)
    (treatedCell untreatedCell : Cohort → Time → Prop)
    (cohortShare : Cohort → ℝ) (covarWeight : Cohort → Covar → ℝ)
    (hmeas : ∀ g t c, MeasurableSet (cellEvent g t c))
    (hcell_pos : ∀ g t c, 0 < (μ (cellEvent g t c)).toReal)
    (hY0_int : ∀ g t c, IntegrableOn Y0pop (cellEvent g t c) μ)
    (hYg_int : ∀ g t c, IntegrableOn Ygpop (cellEvent g t c) μ)
    (hYobs_int : ∀ g t c, IntegrableOn Yobspop (cellEvent g t c) μ)
    (cohortShare_pos_on_treated :
      ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t → 0 < cohortShare g)
    (covarWeight_nonneg : ∀ g c, 0 ≤ covarWeight g c)
    (covarWeight_sum_one : ∀ g, ∑ c, covarWeight g c = 1)
    (hcons_tr : ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t →
        ∀ c, ∀ ω ∈ cellEvent g t c, Yobspop ω = Ygpop ω)
    (hcons_ut : ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, untreatedCell g t →
        ∀ c, ∀ ω ∈ cellEvent g t c, Yobspop ω = Y0pop ω)
    {P : StaggeredATTCells Cohort Time Covar}
    (hP : P = StaggeredATTCells.ofPopulation μ cellEvent Y0pop Ygpop Yobspop
          treatedCell untreatedCell cohortShare covarWeight hmeas
          hcell_pos hY0_int hYg_int hYobs_int
          cohortShare_pos_on_treated covarWeight_nonneg covarWeight_sum_one
          hcons_tr hcons_ut)
    (S : SaturatedUntreatedRegression P)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) (c : Covar) :
    S.m0 g t c = eventCondExp μ (cellEvent g t c) Y0pop :=
  have _ := hcell_pos g t c
  have _ := hY0_int g t c
  have _ := hYg_int g t c
  have _ := hYobs_int g t c
  m0_eq_eventCondExp_treated μ S hNA hCPT hgt c cellEvent Y0pop (by subst hP; rfl)

/-- **On an untreated cell in a population-built system, the fitted untreated
mean equals the population conditional mean of the untreated potential
outcome.** Fix a population model on a sample space `Ω`, with population
outcomes `Y0pop`, `Ygpop`, `Yobspop`; suppose [every cell event
`cellEvent g t c` is measurable](hyp:hmeas), [every cell has strictly positive
probability mass](hyp:hcell_pos), and [the three population outcomes are each
integrable on every cell](hyp:hY0_int,hYg_int,hYobs_int). Suppose also [the
cohort share is strictly positive on every treated cell](hyp:cohortShare_pos_on_treated),
[the covariate weights are nonnegative](hyp:covarWeight_nonneg) and [sum to one
within each cohort](hyp:covarWeight_sum_one), and [the observed outcome agrees
pointwise with the cohort-`g` outcome on treated cells and with the untreated
outcome on untreated cells (pointwise consistency)](hyp:hcons_tr,hcons_ut). If
[the finite cell system `P` is exactly the one built from this population data
by `StaggeredATTCells.ofPopulation`](hyp:hP) and, for a saturated untreated
regression `S` on `P`, [no anticipation holds](hyp:hNA) and [conditional
parallel trends holds](hyp:hCPT), then on [any untreated cell `(g,t)`](hyp:hut),
[the saturated regression's fitted value `S.m0 g t c` equals the population
conditional mean `E[Y0pop | cellEvent g t c]`, for every covariate cell
`c`](goal). -/
theorem m0_eq_eventCondExp_untreated_ofPopulation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (cellEvent : Cohort → Time → Covar → Set Ω)
    (Y0pop Ygpop Yobspop : Ω → ℝ)
    (treatedCell untreatedCell : Cohort → Time → Prop)
    (cohortShare : Cohort → ℝ) (covarWeight : Cohort → Covar → ℝ)
    (hmeas : ∀ g t c, MeasurableSet (cellEvent g t c))
    (hcell_pos : ∀ g t c, 0 < (μ (cellEvent g t c)).toReal)
    (hY0_int : ∀ g t c, IntegrableOn Y0pop (cellEvent g t c) μ)
    (hYg_int : ∀ g t c, IntegrableOn Ygpop (cellEvent g t c) μ)
    (hYobs_int : ∀ g t c, IntegrableOn Yobspop (cellEvent g t c) μ)
    (cohortShare_pos_on_treated :
      ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t → 0 < cohortShare g)
    (covarWeight_nonneg : ∀ g c, 0 ≤ covarWeight g c)
    (covarWeight_sum_one : ∀ g, ∑ c, covarWeight g c = 1)
    (hcons_tr : ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t →
        ∀ c, ∀ ω ∈ cellEvent g t c, Yobspop ω = Ygpop ω)
    (hcons_ut : ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, untreatedCell g t →
        ∀ c, ∀ ω ∈ cellEvent g t c, Yobspop ω = Y0pop ω)
    {P : StaggeredATTCells Cohort Time Covar}
    (hP : P = StaggeredATTCells.ofPopulation μ cellEvent Y0pop Ygpop Yobspop
          treatedCell untreatedCell cohortShare covarWeight hmeas
          hcell_pos hY0_int hYg_int hYobs_int
          cohortShare_pos_on_treated covarWeight_nonneg covarWeight_sum_one
          hcons_tr hcons_ut)
    (S : SaturatedUntreatedRegression P)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    {g : Cohort} {t : Time} (hut : P.untreatedCell g t) (c : Covar) :
    S.m0 g t c = eventCondExp μ (cellEvent g t c) Y0pop :=
  have _ := hcell_pos g t c
  have _ := hY0_int g t c
  have _ := hYg_int g t c
  have _ := hYobs_int g t c
  m0_eq_eventCondExp_untreated μ S hNA hCPT hut c cellEvent Y0pop (by subst hP; rfl)

end FlexibleDIDMundlak
end Panel.EstimandCharacterization
end Causalean
