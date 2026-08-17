import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.FiniteMaxRisk

/-!
# Retention and de-Poissonization for the finite packing maximum

This file transfers the canonical marked-Poisson maximum loss to the retained
fixed-size sample and controls the failed-count event.
-/

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Mapping a canonical marked configuration to distances before taking its
successful prefix is the same as taking the observation prefix first. -/
-- @node: canonicalPrefix_finiteSampleMap_packingMarkedDistance
lemma canonicalPrefix_finiteSampleMap_packingMarkedDistance {n : ℕ}
    (x : Score) (s : FiniteSample (Observation × ℝ)) (h : n ≤ s.count) :
    canonicalPrefixObservations (0, 0) n
        (finiteSampleMap (packingMarkedDistance x) s) =
      distanceData n (canonicalPrefixObservations (0, 0) n s) x := by
  unfold canonicalPrefixObservations
  have hmap : n ≤ (finiteSampleMap (packingMarkedDistance x) s).count := by
    exact h
  rw [dif_pos hmap, dif_pos h]
  rfl

/-- On the successful count event, the global Poisson loss is exactly the
finite packing loss of the retained fixed-size sample. -/
-- @node: globalPackingPoissonLoss_eq_finitePackingLoss
lemma globalPackingPoissonLoss_eq_finitePackingLoss {M n : ℕ}
    (T : PIRule n) (rho : RuleFun n) (P : CtyLaw)
    (centers : Fin M → Score) (values : Fin M → Bool → ℝ)
    (omega : Fin M → Bool)
    (hsection : ∀ w j, rho w (centers j) =
      T.map (centers j) (distanceData n w (centers j)))
    (hvalues : ∀ j, P.mu (centers j) = values j (omega j))
    (s : FiniteSample (Observation × ℝ)) (hs : n ≤ s.count) :
    globalPackingPoissonLoss T centers values omega s =
      finitePackingLoss rho P centers
        (canonicalPrefixObservations (0, 0) n s) := by
  unfold globalPackingPoissonLoss finitePackingLoss
  congr 1
  funext j
  congr 2
  rw [hvalues j, hsection]
  unfold globalPackingPoissonValue
  rw [if_pos hs, canonicalPrefix_finiteSampleMap_packingMarkedDistance _ _ hs]

/-- The count of a canonical marked-Poisson configuration is Poisson. -/
-- @node: canonicalMarkedPoissonSampleLaw_map_count
-- @node: globalPackingPoissonLoss_le_on_count_lt
lemma globalPackingPoissonLoss_le_on_count_lt {M n : ℕ}
    (T : PIRule n) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool)
    (B : ℝ) (hB : ∀ j, |values j (omega j)| ≤ B)
    (s : FiniteSample (Observation × ℝ)) (hs : s.count < n) :
    globalPackingPoissonLoss T centers values omega s ≤ ENNReal.ofReal B := by
  unfold globalPackingPoissonLoss
  apply iSup_le
  intro j
  apply ENNReal.ofReal_le_ofReal
  unfold globalPackingPoissonValue
  rw [if_neg (Nat.not_le_of_lt hs)]
  simpa only [zero_sub, abs_neg] using hB j

/-- The Poissonized risk is at most the retained fixed-size risk plus the
failed-count probability times a uniform zero-default bound. -/
-- @node: globalPackingPoissonRisk_le_fixedRisk_add_tail
lemma globalPackingPoissonRisk_le_fixedRisk_add_tail {M n : ℕ}
    (T : PIRule n) (rho : RuleFun n) (P : CtyLaw)
    (centers : Fin M → Score) (values : Fin M → Bool → ℝ)
    (omega : Fin M → Bool)
    (hsection : ∀ w j, rho w (centers j) =
      T.map (centers j) (distanceData n w (centers j)))
    (hvalues : ∀ j, P.mu (centers j) = values j (omega j))
    (hfiniteMeas : Measurable (finitePackingLoss rho P centers))
    (B : ℝ) (hB : ∀ j, |values j (omega j)| ≤ B) :
    (letI : IsProbabilityMeasure P.law := P.law_isProbability
     ∫⁻ s, globalPackingPoissonLoss T centers values omega s
          ∂canonicalMarkedPoissonSampleLaw P.law packingMarkLaw (2 * n)) ≤
      (∫⁻ w, finitePackingLoss rho P centers w ∂sampleLaw P n) +
        ENNReal.ofReal B *
          ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  let μ := canonicalMarkedPoissonSampleLaw P.law packingMarkLaw (2 * n)
  let success : Set (FiniteSample (Observation × ℝ)) :=
    FiniteSample.count ⁻¹' Ici n
  have hsuccess : MeasurableSet success :=
    measurable_finiteSample_count measurableSet_Ici
  have hsplit := lintegral_add_compl
    (globalPackingPoissonLoss T centers values omega) (μ := μ) hsuccess
  rw [← hsplit]
  apply add_le_add
  · have hmap := map_canonicalPrefixObservations_restrict_count_ge
      P.law packingMarkLaw (2 * n) (0, 0) n
    have heq : ∫⁻ s in success,
          globalPackingPoissonLoss T centers values omega s ∂μ =
        ∫⁻ s in success,
          finitePackingLoss rho P centers
            (canonicalPrefixObservations (0, 0) n s) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hsuccess] with s hs
      exact globalPackingPoissonLoss_eq_finitePackingLoss T rho P centers
        values omega hsection hvalues s hs
    rw [heq]
    change (∫⁻ s, finitePackingLoss rho P centers
        (canonicalPrefixObservations (0, 0) n s) ∂μ.restrict success) ≤ _
    rw [← lintegral_map'
      hfiniteMeas.aemeasurable
      (measurable_canonicalPrefixObservations (0, 0) n).aemeasurable]
    rw [hmap, lintegral_smul_measure]
    change (poissonMeasure (2 * n)) (Ici n) *
      (∫⁻ w, finitePackingLoss rho P centers w ∂sampleLaw P n) ≤
        ∫⁻ w, finitePackingLoss rho P centers w ∂sampleLaw P n
    exact mul_le_of_le_one_left (by positivity) prob_le_one
  · calc
      (∫⁻ s in successᶜ, globalPackingPoissonLoss T centers values omega s ∂μ) ≤
          ∫⁻ _s in successᶜ, ENNReal.ofReal B ∂μ := by
        apply setLIntegral_mono measurable_const
        intro s hs
        apply globalPackingPoissonLoss_le_on_count_lt T centers values omega B hB s
        simpa [success] using hs
      _ = ENNReal.ofReal B * μ successᶜ := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal B *
          ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) := by
        gcongr
        have hcount := canonicalMarkedPoissonSampleLaw_map_count
          P.law packingMarkLaw (2 * n)
        have hfail : μ successᶜ = (poissonMeasure (2 * n)) {k | k < n} := by
          rw [← hcount]
          rw [Measure.map_apply measurable_finiteSample_count (by measurability)]
          congr 1
          ext s
          simp [success]
        rw [hfail]
        exact poisson_two_n_lower_tail n

end CausalSmith.Stat.BddUniformLogPenalty
