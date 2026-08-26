import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization

/-!
# Fixed-prefix de-Poissonization for the one-arm lower bound

This file isolates the sample-size transfer used in Appendix D.2.  A loss on a
canonical marked-Poisson sample is compared with the same loss on a retained
fixed-size prefix, with the failed-count event paid separately.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Mix a conditional risk bound over a Poisson total count.  Counts at least
`n` pay the common core risk; smaller counts pay the explicit failure bound. -/
lemma poissonBindLintegral_le_core_add_tail
    {X : Type*} [MeasurableSpace X]
    (K : ℕ → Measure X) (hK : Measurable K)
    (lam : ℝ≥0) (n : ℕ) (loss : X → ℝ≥0∞) (hloss : Measurable loss)
    (core fail : ℝ≥0∞)
    (hsuccess : ∀ k, n ≤ k → (∫⁻ x, loss x ∂K k) ≤ core)
    (hfail : ∀ k, k < n → (∫⁻ x, loss x ∂K k) ≤ fail) :
    (∫⁻ x, loss x ∂(poissonMeasure lam).bind K) ≤
      core + fail * (poissonMeasure lam) {k | k < n} := by
  rw [Measure.lintegral_bind hK.aemeasurable hloss.aemeasurable]
  let success : Set ℕ := Set.Ici n
  have hsuccessMeas : MeasurableSet success := measurableSet_Ici
  rw [← lintegral_add_compl
    (fun k => ∫⁻ x, loss x ∂K k) hsuccessMeas]
  apply add_le_add
  · calc
      (∫⁻ k in success, ∫⁻ x, loss x ∂K k ∂poissonMeasure lam) ≤
          ∫⁻ _k in success, core ∂poissonMeasure lam := by
        apply setLIntegral_mono measurable_const
        intro k hk
        exact hsuccess k hk
      _ = core * (poissonMeasure lam) success := setLIntegral_const _ _
      _ = (poissonMeasure lam) success * core := mul_comm _ _
      _ ≤ core := mul_le_of_le_one_left (by positivity) prob_le_one
  · calc
      (∫⁻ k in successᶜ, ∫⁻ x, loss x ∂K k ∂poissonMeasure lam) ≤
          ∫⁻ _k in successᶜ, fail ∂poissonMeasure lam := by
        apply setLIntegral_mono measurable_const
        intro k hk
        apply hfail k
        simpa [success] using hk
      _ = fail * (poissonMeasure lam) successᶜ := setLIntegral_const _ _
      _ = fail * (poissonMeasure lam) {k | k < n} := by
        have hset : successᶜ = {k | k < n} := by
          ext k
          simp [success]
        rw [hset]

/-- A canonical marked-Poisson loss that agrees with a fixed-prefix loss when
the count reaches `n`, and is bounded by `B` otherwise, is at most the
fixed-sample risk plus `B` times the Poisson lower-tail probability. -/
lemma canonicalMarkedPoissonRisk_le_fixedRisk_add_tail
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R]
    (lam : ℝ≥0) (x₀ : X) (n : ℕ)
    (poissonLoss : FiniteSample (X × ℝ) → ℝ≥0∞)
    (fixedLoss : (Fin n → X) → ℝ≥0∞)
    (hfixed : Measurable fixedLoss)
    (hsuccess : ∀ s, n ≤ s.count →
      poissonLoss s = fixedLoss (canonicalPrefixObservations x₀ n s))
    (B : ℝ≥0∞) (hfail : ∀ s, s.count < n → poissonLoss s ≤ B) :
    (∫⁻ s, poissonLoss s ∂canonicalMarkedPoissonSampleLaw P R lam) ≤
      (∫⁻ w, fixedLoss w ∂Measure.pi (fun _ : Fin n => P)) +
        B * (poissonMeasure lam) {k | k < n} := by
  let μ := canonicalMarkedPoissonSampleLaw P R lam
  let success : Set (FiniteSample (X × ℝ)) :=
    FiniteSample.count ⁻¹' Ici n
  have hsuccessMeas : MeasurableSet success :=
    measurable_finiteSample_count measurableSet_Ici
  have hsplit := lintegral_add_compl poissonLoss (μ := μ) hsuccessMeas
  rw [← hsplit]
  apply add_le_add
  · have hmap := map_canonicalPrefixObservations_restrict_count_ge
      P R lam x₀ n
    have heq :
        ∫⁻ s in success, poissonLoss s ∂μ =
          ∫⁻ s in success,
            fixedLoss (canonicalPrefixObservations x₀ n s) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hsuccessMeas] with s hs
      exact hsuccess s hs
    rw [heq]
    change (∫⁻ s, fixedLoss (canonicalPrefixObservations x₀ n s)
      ∂μ.restrict success) ≤ _
    rw [← lintegral_map' hfixed.aemeasurable
      (measurable_canonicalPrefixObservations x₀ n).aemeasurable]
    rw [hmap, lintegral_smul_measure]
    exact mul_le_of_le_one_left (by positivity) prob_le_one
  · calc
      (∫⁻ s in successᶜ, poissonLoss s ∂μ) ≤
          ∫⁻ _s in successᶜ, B ∂μ := by
        apply setLIntegral_mono measurable_const
        intro s hs
        apply hfail s
        simpa [success] using hs
      _ = B * μ successᶜ := setLIntegral_const _ _
      _ = B * (poissonMeasure lam) {k | k < n} := by
        congr 1
        have hcount := canonicalMarkedPoissonSampleLaw_map_count P R lam
        rw [← hcount]
        rw [Measure.map_apply measurable_finiteSample_count (by measurability)]
        congr 1
        ext s
        simp [success]

/-- The generic transfer for a finite, not necessarily normalized intensity
measure.  Its fixed-prefix law uses the normalized intensity, while its count
mean is `lam` times the original total mass. -/
lemma finiteMeasureMarkedPoissonRisk_le_normalizedFixedRisk_add_tail
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν]
    (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R]
    (lam : ℝ≥0) (x₀ : X) (n : ℕ)
    (poissonLoss : FiniteSample (X × ℝ) → ℝ≥0∞)
    (fixedLoss : (Fin n → X) → ℝ≥0∞)
    (hfixed : Measurable fixedLoss)
    (hsuccess : ∀ s, n ≤ s.count →
      poissonLoss s = fixedLoss (canonicalPrefixObservations x₀ n s))
    (B : ℝ≥0∞) (hfail : ∀ s, s.count < n → poissonLoss s ≤ B) :
    (∫⁻ s, poissonLoss s
        ∂Measure.map orderByMarks
          (finiteMeasureMarkedPoissonLaw ν P₀ R lam)) ≤
      (∫⁻ w, fixedLoss w
        ∂Measure.pi (fun _ : Fin n => normalizedFiniteMeasure ν P₀)) +
      B * (poissonMeasure (lam * finiteMeasureMass ν)) {k | k < n} := by
  simpa [finiteMeasureMarkedPoissonLaw, canonicalMarkedPoissonSampleLaw] using
    canonicalMarkedPoissonRisk_le_fixedRisk_add_tail
      (normalizedFiniteMeasure ν P₀) R (lam * finiteMeasureMass ν)
        x₀ n poissonLoss fixedLoss hfixed hsuccess B hfail

/-- At Poisson mean `2n`, the generic retained-prefix comparison has the
explicit exponential lower-tail bound used in fixed-sample transfers. -/
lemma canonicalMarkedPoissonRisk_le_fixedRisk_add_exp_tail
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R]
    (x₀ : X) (n : ℕ)
    (poissonLoss : FiniteSample (X × ℝ) → ℝ≥0∞)
    (fixedLoss : (Fin n → X) → ℝ≥0∞)
    (hfixed : Measurable fixedLoss)
    (hsuccess : ∀ s, n ≤ s.count →
      poissonLoss s = fixedLoss (canonicalPrefixObservations x₀ n s))
    (B : ℝ≥0∞) (hfail : ∀ s, s.count < n → poissonLoss s ≤ B) :
    (∫⁻ s, poissonLoss s
        ∂canonicalMarkedPoissonSampleLaw P R (2 * n)) ≤
      (∫⁻ w, fixedLoss w ∂Measure.pi (fun _ : Fin n => P)) +
        B * ENNReal.ofReal
          (Real.exp (-(n : ℝ) * (1 - Real.log 2))) := by
  refine (canonicalMarkedPoissonRisk_le_fixedRisk_add_tail
    P R (2 * n) x₀ n poissonLoss fixedLoss hfixed hsuccess B hfail).trans ?_
  gcongr
  exact poisson_two_n_lower_tail n

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
