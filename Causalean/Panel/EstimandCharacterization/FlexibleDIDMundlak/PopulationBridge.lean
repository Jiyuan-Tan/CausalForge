/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Wooldridge finite imputation estimand to population conditional expectation

Bridges the finite-cell imputation residual mean `imputationTheta` to the
population conditional expectation `eventCondExp μ cohortEvent Δ`, via the law of iterated expectations
over the finite covariate partition
(`Causalean.PO.eventCondExp_eq_sum_condProb_mul_eventCondExp`).

The bridge is *hypothesis-driven*: it takes a probability model `(μ, cohortEvent,
covarCell, Δ)` together with two identification hypotheses that connect the
finite-cell construction's primitive means to that model — the covariate weights are the
conditional cell probabilities, and each finite cell residual is the within-cell
conditional mean of the treatment-effect integrand `Δ`.  Those hypotheses are
exactly the paper's *definition* of `θ^imp` as `E[Δ | G = g]` together with the
finite cell-average representation; the bridge is the total-expectation identity
connecting them.  No paper assumption is strengthened.
-/

import Causalean.Panel.EstimandCharacterization.FlexibleDIDMundlak.DID
import Causalean.PO.Conditioning.EventCondExp

/-! # Wooldridge Population Bridge

This file connects Wooldridge's finite imputation estimands to population
conditional expectations.  The main bridges are
`imputationTheta_eq_eventCondExp` and `thetaImp_eq_eventCondExp`, which apply the
finite-partition law of iterated expectations to identify covariate-weighted
finite residual means with event-level conditional expectations.  The companion
lemmas `m0_eq_eventCondExp_treated` and `m0_eq_eventCondExp_untreated` state the
population conditional-expectation origin of the saturated untreated fit on
treated and untreated cells. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace FlexibleDIDMundlak

open MeasureTheory Causalean.PO

variable {Cohort Time Covar : Type*}
  [Fintype Cohort] [Fintype Time] [Fintype Covar]

/-- The finite imputation residual mean equals a population conditional
expectation.

`imputationTheta P S g t = ∑_c covarWeight(g,c)·(observedMean − m0)` equals the
population conditional expectation `E[Δ | G = g]` of the treatment-effect
integrand `Δ` on the cohort event `cohortEvent`, under the identification
hypotheses:

* `hweight`: each covariate weight is the conditional cell probability
  `P(C = c | G = g) = μ(cohortEvent ∩ covarCell c) / μ(cohortEvent)`;
* `hcell`: each finite cell residual `observedMean − m0` is the within-cell
  conditional mean `E[Δ | G = g, C = c] = eventCondExp μ (cohortEvent ∩ covarCell c) Δ`.

This is a direct application of the conditional finite-partition total law
(law of iterated expectations) to the covariate partition `covarCell`. -/
theorem imputationTheta_eq_eventCondExp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : StaggeredATTCells Cohort Time Covar) (S : SaturatedUntreatedRegression P)
    (g : Cohort) (t : Time)
    (cohortEvent : Set Ω) (covarCell : Covar → Set Ω) (Δ : Ω → ℝ)
    (hG : MeasurableSet cohortEvent)
    (hC : ∀ c, MeasurableSet (covarCell c))
    (hdisj : Pairwise (Function.onFun Disjoint covarCell))
    (hcov : (⋃ c, covarCell c) = Set.univ)
    (hΔ : Integrable Δ μ)
    (hweight : ∀ c, P.covarWeight g c
        = (μ (cohortEvent ∩ covarCell c)).toReal / (μ cohortEvent).toReal)
    (hcell : ∀ c, P.observedMean g t c - S.m0 g t c
        = eventCondExp μ (cohortEvent ∩ covarCell c) Δ) :
    imputationTheta P S g t = eventCondExp μ cohortEvent Δ := by
  unfold imputationTheta
  rw [eventCondExp_eq_sum_condProb_mul_eventCondExp μ cohortEvent covarCell hG hC
    hdisj hcov Δ hΔ]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [hweight c, hcell c]

/-- The imputation estimand equals a population conditional expectation.

The imputation cell estimand `thetaImp` of a `FlexibleDIDEstimands` equals the
population conditional expectation `E[Δ | G = g]` on each treated cell, under the
same identification hypotheses.  Combines `FlexibleDIDEstimands.thetaImp_eq_imputation`
with `imputationTheta_eq_eventCondExp`. -/
theorem thetaImp_eq_eventCondExp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : StaggeredATTCells Cohort Time Covar) (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t)
    (cohortEvent : Set Ω) (covarCell : Covar → Set Ω) (Δ : Ω → ℝ)
    (hG : MeasurableSet cohortEvent)
    (hC : ∀ c, MeasurableSet (covarCell c))
    (hdisj : Pairwise (Function.onFun Disjoint covarCell))
    (hcov : (⋃ c, covarCell c) = Set.univ)
    (hΔ : Integrable Δ μ)
    (hweight : ∀ c, P.covarWeight g c
        = (μ (cohortEvent ∩ covarCell c)).toReal / (μ cohortEvent).toReal)
    (hcell : ∀ c, P.observedMean g t c - S.m0 g t c
        = eventCondExp μ (cohortEvent ∩ covarCell c) Δ) :
    E.thetaImp g t = eventCondExp μ cohortEvent Δ := by
  rw [E.thetaImp_eq_imputation hgt]
  exact imputationTheta_eq_eventCondExp μ P S g t cohortEvent covarCell Δ
    hG hC hdisj hcov hΔ hweight hcell

/-! ### Population Origin of `m0`

The finite-cell projection origin of `m0` (`SaturatedUntreatedRegression.untreatedNormalEq`)
is already in `DID.lean`, and `recovers_target_Y0` / `untreatedFit` derive the
exact untreated-mean recovery from no-anticipation + conditional parallel trends.
The population bridge reads the finite untreated-outcome cell mean `Y0Mean` as
the population conditional expectation
`E[Y_t(∞) | G = g, t, C = c]` of the untreated potential outcome, so that the
saturated projection `m0` equals that conditional expectation cellwise.  The
identification hypothesis `hY0` is exactly the statement that the finite
primitive `Y0Mean` *is* that conditional mean — it is definitional, not a
strengthening; all causal content lives in `recovers_target_Y0` / `untreatedFit`. -/

/-- On a treated cell, the fitted untreated mean equals the population
conditional mean of the untreated potential outcome.

The saturated untreated regression's fitted value equals the population
conditional expectation of the untreated potential outcome
`E[Y_t(∞) | G = g, t, C = c]`,
given the identification `hY0 : Y0Mean g t c = eventCondExp μ (cellEvent g t c) Y0pop`.
The causal content (additive extrapolation from untreated to treated cells via
conditional parallel trends) is carried by `recovers_target_Y0`. -/
theorem m0_eq_eventCondExp_treated
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {P : StaggeredATTCells Cohort Time Covar} (S : SaturatedUntreatedRegression P)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) (c : Covar)
    (cellEvent : Cohort → Time → Covar → Set Ω) (Y0pop : Ω → ℝ)
    (hY0 : P.Y0Mean g t c = eventCondExp μ (cellEvent g t c) Y0pop) :
    S.m0 g t c = eventCondExp μ (cellEvent g t c) Y0pop := by
  rw [S.recovers_target_Y0 hNA hCPT hgt c, hY0]

/-- On an untreated cell, the fitted untreated mean equals the population
conditional mean of the untreated potential outcome.

On an untreated cell, the fitted value likewise equals
`E[Y_t(∞) | G = g, t, C = c]`: `untreatedFit`
gives `m0 = YgMean`, no-anticipation turns that into `Y0Mean`, and `hY0` reads
`Y0Mean` as the population conditional mean. -/
theorem m0_eq_eventCondExp_untreated
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {P : StaggeredATTCells Cohort Time Covar} (S : SaturatedUntreatedRegression P)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    {g : Cohort} {t : Time} (hut : P.untreatedCell g t) (c : Covar)
    (cellEvent : Cohort → Time → Covar → Set Ω) (Y0pop : Ω → ℝ)
    (hY0 : P.Y0Mean g t c = eventCondExp μ (cellEvent g t c) Y0pop) :
    S.m0 g t c = eventCondExp μ (cellEvent g t c) Y0pop := by
  rw [S.untreatedFit hNA hCPT hut c, hNA hut c, hY0]

end FlexibleDIDMundlak
end Panel.EstimandCharacterization
end Causalean
