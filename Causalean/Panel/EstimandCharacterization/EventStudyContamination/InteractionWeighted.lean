/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sun-Abraham (2021): interaction-weighted event-study characterization
-/

import Causalean.Panel.EstimandCharacterization.EventStudyContamination.Setup

/-! # Sun-Abraham Interaction-Weighted Event Study

This file develops the finite-cell interaction-weighted event-study estimand for
the Sun-Abraham framework. It records the comparison-group contrasts and
aggregation weights that make the interaction-weighted coefficient a convex
average of target cohort-specific effects, proving `IW_Delta_eq_CATT` and
`IW_convex_characterization`. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace EventStudyContamination

open Finset

/-- Finite convex-combination bound. If the weights `w` are nonnegative and sum
to one, then any nonnegative-weighted average of values lying in `[lo, hi]`
again lies in `[lo, hi]`. This is the algebraic content of "convex combination"
used to certify that the IW estimand is a genuine convex average of the target
CATTs (no contamination). -/
theorem sum_convex_mem_Icc {ι : Type*} (s : Finset ι) (w f : ι → ℝ)
    {lo hi : ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hlo : ∀ i ∈ s, lo ≤ f i) (hhi : ∀ i ∈ s, f i ≤ hi) :
    lo ≤ ∑ i ∈ s, w i * f i ∧ ∑ i ∈ s, w i * f i ≤ hi := by
  constructor
  · calc
      lo = ∑ i ∈ s, w i * lo := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ i ∈ s, w i * f i := by
        apply Finset.sum_le_sum
        intro i hi'
        exact mul_le_mul_of_nonneg_left (hlo i hi') (hw i hi')
  · calc
      ∑ i ∈ s, w i * f i ≤ ∑ i ∈ s, w i * hi := by
        apply Finset.sum_le_sum
        intro i hi'
        exact mul_le_mul_of_nonneg_left (hhi i hi') (hw i hi')
      _ = hi := by rw [← Finset.sum_mul, hsum, one_mul]

namespace EventStudySystem

variable {T : ℕ}

/-- Interaction-weighted finite DID design for a fixed event time. -/
structure IWDesign (P : EventStudySystem T) where
  /-- Fixed event time `l`, intended to be nonnegative in the theorem. -/
  eventTime : ℤ
  /-- Eligible IW cohorts `G_l^IW`. -/
  cohortsIW : Finset (Fin T)
  /-- Comparison group `C^0_{g,l}` for each eligible cohort. -/
  comparisonGroup : Fin T → Finset (WithTop (Fin T))
  /-- Aggregation weights `rho(g,l)`. -/
  rho : Fin T → ℝ

/-- Observed treated-cohort target mean from the finite-cohort factual means. -/
noncomputable def observedTargetMean (P : EventStudySystem T)
    (I : P.IWDesign) (g : Fin T) : ℝ :=
  ((P.targetPeriods g I.eventTime).card : ℝ)⁻¹ *
    ∑ t ∈ P.targetPeriods g I.eventTime, P.observedMean g t

/-- Observed treated-cohort baseline mean from the finite-cohort factual
means, using relative time `-1`. -/
noncomputable def observedBaselineMean (P : EventStudySystem T)
    (_I : P.IWDesign) (g : Fin T) : ℝ :=
  ((P.baselinePeriods g).card : ℝ)⁻¹ *
    ∑ t ∈ P.baselinePeriods g, P.observedMean g t

/-- Total comparison-group population mass for cohort `g`'s IW contrast. -/
noncomputable def comparisonMass (P : EventStudySystem T)
    (I : P.IWDesign) (g : Fin T) : ℝ :=
  ∑ h ∈ I.comparisonGroup g, P.cohortShare h

/-- Population-share weighted comparison-group mean change from baseline
`g-1` to target `g+l`. -/
noncomputable def comparisonMeanChange (P : EventStudySystem T)
    (I : P.IWDesign) (g : Fin T) : ℝ :=
  (P.comparisonMass I g)⁻¹ *
    ∑ h ∈ I.comparisonGroup g,
      P.cohortShare h * (P.pathTargetMean h g I.eventTime - P.pathBaselineMean h g)

/-- Cohort-specific DID contrast using the treated cohort and its comparison
group. -/
noncomputable def DIDContrast (P : EventStudySystem T)
    (I : P.IWDesign) (g : Fin T) : ℝ :=
  (P.observedTargetMean I g - P.observedBaselineMean I g) -
    P.comparisonMeanChange I g

/-- Cohort-specific IW DID contrast `Delta(g,l)`. It is definitional rather
than stored separately, so the IW theorem identifies the actual DID contrast. -/
noncomputable def Delta (P : EventStudySystem T) (I : P.IWDesign)
    (g : Fin T) : ℝ :=
  P.DIDContrast I g

/-- Interaction-weighted event-study estimand. -/
noncomputable def nuIW (P : EventStudySystem T) (I : P.IWDesign) : ℝ :=
  ∑ g ∈ I.cohortsIW, I.rho g * P.Delta I g

/-- IW support restrictions for eligible cohorts and their comparison groups.

The support record supplies nonempty baseline/target periods, positive cohort
and comparison mass, and untreated-status facts for each comparison path. The
observed-equals-untreated bridge for comparison groups is derived separately
from `PathConsistency` and these untreated-status fields via
`pathConsistency_observed_eq_untreated`. -/
structure IWSupport (P : EventStudySystem T) (I : P.IWDesign) : Prop where
  hBaselineValid :
    ∀ g ∈ I.cohortsIW, (P.baselinePeriods g).Nonempty
  hTargetValid :
    ∀ g ∈ I.cohortsIW, g ∈ P.cohorts ∧ (P.targetPeriods g I.eventTime).Nonempty
  hCohortSharePos :
    ∀ g ∈ I.cohortsIW, 0 < P.cohortShare (finitePath g)
  hComparisonNonempty :
    ∀ g ∈ I.cohortsIW, (I.comparisonGroup g).Nonempty
  hComparisonPositive :
    ∀ g ∈ I.cohortsIW, 0 < P.comparisonMass I g
  hComparisonUntreatedBaseline :
    ∀ g ∈ I.cohortsIW, ∀ h ∈ I.comparisonGroup g,
      ∀ t ∈ P.baselinePeriods g, absorbingTreatment h t = 0
  hComparisonUntreatedTarget :
    ∀ g ∈ I.cohortsIW, ∀ h ∈ I.comparisonGroup g,
      ∀ t ∈ P.targetPeriods g I.eventTime, absorbingTreatment h t = 0

/-- Comparison-group parallel trends for the IW DID contrast. -/
structure IWComparisonParallelTrends (P : EventStudySystem T)
    (I : P.IWDesign) : Prop where
  hComparisonPositive :
    ∀ g ∈ I.cohortsIW, 0 < P.comparisonMass I g
  hComparisonUntreated :
    ∀ g ∈ I.cohortsIW, ∀ h ∈ I.comparisonGroup g,
      (∀ t ∈ P.baselinePeriods g, absorbingTreatment h t = 0) ∧
      (∀ t ∈ P.targetPeriods g I.eventTime, absorbingTreatment h t = 0)
  hComparisonParallelTrends :
    ∀ g ∈ I.cohortsIW,
      ((P.targetPeriods g I.eventTime).card : ℝ)⁻¹ *
          ∑ t ∈ P.targetPeriods g I.eventTime,
            (P.untreatedMean g t) -
        ((P.baselinePeriods g).card : ℝ)⁻¹ *
          ∑ t ∈ P.baselinePeriods g, (P.untreatedMean g t)
      =
      (P.comparisonMass I g)⁻¹ *
        ∑ h ∈ I.comparisonGroup g,
          P.cohortShare h *
          (((P.targetPeriods g I.eventTime).card : ℝ)⁻¹ *
              ∑ t ∈ P.targetPeriods g I.eventTime, P.untreatedPathMean h t -
            ((P.baselinePeriods g).card : ℝ)⁻¹ *
              ∑ t ∈ P.baselinePeriods g, P.untreatedPathMean h t)

/-- Each IW DID contrast equals the cohort-relative-time CATT. -/
theorem IW_Delta_eq_CATT (P : EventStudySystem T) (I : P.IWDesign)
    (hConsistency : P.Consistency)
    (hNoAnticipation : P.NoAnticipation)
    (hPathConsistency : P.PathConsistency)
    (hIWParallelTrends : P.IWComparisonParallelTrends I)
    (hSupport : P.IWSupport I)
    {g : Fin T} (hg : g ∈ I.cohortsIW) :
    P.Delta I g = P.CATT g I.eventTime := by
  have hgCohort : g ∈ P.cohorts := (hSupport.hTargetValid g hg).1
  have hObsTarget :
      P.observedTargetMean I g =
        ((P.targetPeriods g I.eventTime).card : ℝ)⁻¹ *
          ∑ t ∈ P.targetPeriods g I.eventTime, P.treatedMean g t := by
    unfold observedTargetMean
    have hsum :
        (∑ t ∈ P.targetPeriods g I.eventTime, P.observedMean g t) =
          ∑ t ∈ P.targetPeriods g I.eventTime, P.treatedMean g t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hConsistency g hgCohort t
    rw [hsum]
  have hObsBaseline :
      P.observedBaselineMean I g =
        ((P.baselinePeriods g).card : ℝ)⁻¹ *
          ∑ t ∈ P.baselinePeriods g, P.untreatedMean g t := by
    unfold observedBaselineMean
    have hsum :
        (∑ t ∈ P.baselinePeriods g, P.observedMean g t) =
          ∑ t ∈ P.baselinePeriods g, P.untreatedMean g t := by
      apply Finset.sum_congr rfl
      intro t ht
      have hrel : P.relTime g t = -1 := by
        simpa [baselinePeriods, targetPeriods] using ht
      have hpre : P.time t < P.time g := by
        have hneg : P.relTime g t < 0 := by
          rw [hrel]
          norm_num
        simpa [relTime] using (sub_neg.mp hneg)
      rw [hConsistency g hgCohort t, hNoAnticipation g hgCohort t hpre]
    rw [hsum]
  have hPathTarget : ∀ h ∈ I.comparisonGroup g,
      P.pathTargetMean h g I.eventTime =
        ((P.targetPeriods g I.eventTime).card : ℝ)⁻¹ *
          ∑ t ∈ P.targetPeriods g I.eventTime, P.untreatedPathMean h t := by
    intro h hh
    unfold pathTargetMean
    have hsum :
        (∑ t ∈ P.targetPeriods g I.eventTime, P.observedPathMean h t) =
          ∑ t ∈ P.targetPeriods g I.eventTime, P.untreatedPathMean h t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact P.pathConsistency_observed_eq_untreated hPathConsistency
        (hSupport.hComparisonUntreatedTarget g hg h hh t ht)
    rw [hsum]
  have hPathBaseline : ∀ h ∈ I.comparisonGroup g,
      P.pathBaselineMean h g =
        ((P.baselinePeriods g).card : ℝ)⁻¹ *
          ∑ t ∈ P.baselinePeriods g, P.untreatedPathMean h t := by
    intro h hh
    unfold pathBaselineMean
    have hsum :
        (∑ t ∈ P.baselinePeriods g, P.observedPathMean h t) =
          ∑ t ∈ P.baselinePeriods g, P.untreatedPathMean h t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact P.pathConsistency_observed_eq_untreated hPathConsistency
        (hSupport.hComparisonUntreatedBaseline g hg h hh t ht)
    rw [hsum]
  have hComparison :
      P.comparisonMeanChange I g =
        (P.comparisonMass I g)⁻¹ *
          ∑ h ∈ I.comparisonGroup g,
            P.cohortShare h *
            (((P.targetPeriods g I.eventTime).card : ℝ)⁻¹ *
                ∑ t ∈ P.targetPeriods g I.eventTime, P.untreatedPathMean h t -
              ((P.baselinePeriods g).card : ℝ)⁻¹ *
                ∑ t ∈ P.baselinePeriods g, P.untreatedPathMean h t) := by
    unfold comparisonMeanChange
    have hsum :
        (∑ h ∈ I.comparisonGroup g,
          P.cohortShare h *
            (P.pathTargetMean h g I.eventTime - P.pathBaselineMean h g)) =
          ∑ h ∈ I.comparisonGroup g,
            P.cohortShare h *
            (((P.targetPeriods g I.eventTime).card : ℝ)⁻¹ *
                ∑ t ∈ P.targetPeriods g I.eventTime, P.untreatedPathMean h t -
              ((P.baselinePeriods g).card : ℝ)⁻¹ *
                ∑ t ∈ P.baselinePeriods g, P.untreatedPathMean h t) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [hPathTarget h hh, hPathBaseline h hh]
    rw [hsum]
  have hParallel := hIWParallelTrends.hComparisonParallelTrends g hg
  unfold Delta DIDContrast CATT meanCellContrast
  rw [hObsTarget, hObsBaseline, hComparison, ← hParallel]
  rw [Finset.sum_sub_distrib]
  rw [mul_sub]
  rw [sub_sub_sub_cancel_right]

/-- Interaction-weighted event-study characterization: at a nonnegative event
time, the IW estimand is a convex cohort-share weighted average of the desired
event-time CATTs, with no contamination from other relative times.

The third conjunct is the paper's selling point made into a *conclusion*: the
nonnegativity (`hRhoNonneg`) and sum-to-one (`hRhoSumOne`) of the aggregation
weights are genuinely consumed (via `sum_convex_mem_Icc`) to certify that
`nuIW` lies in the convex hull `[lo, hi]` of the target CATTs whenever the
per-cohort `CATT(g,l)` are bounded by `lo`/`hi`. Taking `lo := ⨅ g, CATT(g,l)`
and `hi := ⨆ g, CATT(g,l)` recovers `min_g CATT ≤ nuIW ≤ max_g CATT`; we state
the bound parametrically in `lo`/`hi` to avoid `Finset.min'`/`max'`
nonemptiness side goals. The explicit `0 ≤ I.eventTime` hypothesis matches the
source restriction for the interaction-weighted event-study estimand. -/
theorem IW_convex_characterization (P : EventStudySystem T) (I : P.IWDesign)
    (hEventTime_nonneg : 0 ≤ I.eventTime)
    (hConsistency : P.Consistency)
    (hNoAnticipation : P.NoAnticipation)
    (hPathConsistency : P.PathConsistency)
    (hIWParallelTrends : P.IWComparisonParallelTrends I)
    (hSupport : P.IWSupport I)
    (hRhoNonneg : ∀ g ∈ I.cohortsIW, 0 ≤ I.rho g)
    (hRhoSumOne : ∑ g ∈ I.cohortsIW, I.rho g = 1)
    {lo hi : ℝ}
    (hLo : ∀ g ∈ I.cohortsIW, lo ≤ P.CATT g I.eventTime)
    (hHi : ∀ g ∈ I.cohortsIW, P.CATT g I.eventTime ≤ hi) :
    (∀ g ∈ I.cohortsIW, P.Delta I g = P.CATT g I.eventTime) ∧
      P.nuIW I = ∑ g ∈ I.cohortsIW, I.rho g * P.CATT g I.eventTime ∧
      lo ≤ P.nuIW I ∧ P.nuIW I ≤ hi := by
  have _ := hEventTime_nonneg
  have hDelta : ∀ g ∈ I.cohortsIW, P.Delta I g = P.CATT g I.eventTime := by
    intro g hg
    exact P.IW_Delta_eq_CATT I hConsistency hNoAnticipation hPathConsistency
      hIWParallelTrends hSupport hg
  have hAgg : P.nuIW I = ∑ g ∈ I.cohortsIW, I.rho g * P.CATT g I.eventTime := by
    unfold nuIW
    apply Finset.sum_congr rfl
    intro g hg
    rw [hDelta g hg]
  refine ⟨hDelta, hAgg, ?_, ?_⟩ <;>
    rw [hAgg]
  · exact (sum_convex_mem_Icc I.cohortsIW I.rho
      (fun g => P.CATT g I.eventTime) hRhoNonneg hRhoSumOne hLo hHi).1
  · exact (sum_convex_mem_Icc I.cohortsIW I.rho
      (fun g => P.CATT g I.eventTime) hRhoNonneg hRhoSumOne hLo hHi).2

end EventStudySystem

end EventStudyContamination
end Panel.EstimandCharacterization
end Causalean
