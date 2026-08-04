import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.DimensionWitness.Envelope

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal Topology

lemma dw_policyKL_reference (d : ℕ) (hd : 4 ≤ d) (x : Fin d) :
    policyKL (dwExperiment d hd).reference
        (gibbsPolicy (dwExperiment d hd) (dwLaw d hd)) x =
      Real.log (4 / 3) / 2 := by
  unfold policyKL
  rw [Fin.sum_univ_two, dw_gibbsPolicy, dw_gibbsPolicy]
  simp [dwExperiment]
  have hlog :
      Real.log (2 / 3) + Real.log 2 = Real.log (4 / 3) := by
    rw [← Real.log_mul (by norm_num : (2 / 3 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    norm_num
  norm_num
  rw [← hlog]
  ring_nf
  rfl

lemma dw_reference_regret (d : ℕ) (hd : 4 ≤ d) :
    regularizedWelfare (dwExperiment d hd) (dwLaw d hd)
        (gibbsPolicy (dwExperiment d hd) (dwLaw d hd)) -
      regularizedWelfare (dwExperiment d hd) (dwLaw d hd)
        (dwExperiment d hd).reference =
      Real.log (4 / 3) / (8 * Real.log 3) := by
  rw [gibbs_regret_identity (dwExperiment d hd) (dwLaw d hd)
    dwCoverageC dwCoverageD (dw_exactShell d hd)
    (dwExperiment d hd).reference
    (dwExperiment d hd).reference_isPolicy (fun _ _ h => h)]
  simp_rw [dw_contextMass, dw_policyKL_reference]
  simp
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  simp [dwExperiment, dwEta]
  field_simp
  ring

lemma dw_reference_regret_nonneg (d : ℕ) (hd : 4 ≤ d) :
    0 ≤ Real.log (4 / 3) / (8 * Real.log 3) := by
  exact div_nonneg
    (Real.log_nonneg (by norm_num))
    (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))

lemma dw_lowerPolicy_regret_nonneg (d : ℕ) (hd : 4 ≤ d)
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2)) :
    0 ≤ regularizedWelfare (dwExperiment d hd) (dwLaw d hd)
          (gibbsPolicy (dwExperiment d hd) (dwLaw d hd)) -
        regularizedWelfare (dwExperiment d hd) (dwLaw d hd)
          (lowerEnvelopePolicy (dwExperiment d hd) 64 sample) := by
  let g := lowerEnvelope (dwExperiment d hd) 64 sample
  have hpolicy :
      IsPolicy (lowerEnvelopePolicy (dwExperiment d hd) 64 sample) := by
    simpa [lowerEnvelopePolicy, gibbsFromPotential, g] using
      gibbsFromPotential_isPolicy (dwExperiment d hd) g
  have hsupp :
      SupportedOnReference (dwExperiment d hd)
        (lowerEnvelopePolicy (dwExperiment d hd) 64 sample) := by
    simpa [lowerEnvelopePolicy, gibbsFromPotential, g] using
      gibbsFromPotential_supported (dwExperiment d hd) g
  rw [gibbs_regret_identity (dwExperiment d hd) (dwLaw d hd)
    dwCoverageC dwCoverageD (dw_exactShell d hd)
    (lowerEnvelopePolicy (dwExperiment d hd) 64 sample) hpolicy hsupp]
  apply mul_nonneg
  · exact inv_nonneg.mpr (dwExperiment d hd).eta_pos.le
  · apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg ENNReal.toReal_nonneg
    simpa [lowerEnvelopePolicy, gibbsFromPotential, g, gibbsPolicy,
      gibbsNormalizer] using
      policyKL_gibbsPotentials_nonneg (dwExperiment d hd)
        (linearReward (dwLaw d hd)) g x

noncomputable def dwSampleEmbedding (d : ℕ)
    (source : Fin (d ^ 2) → Fin d × Fin 2) :
    LoggedSample (d ^ 2) (Fin d) (Fin 2) :=
  fun i => dwObservation d (source i)

def dwSampleSupport (d : ℕ) :
    Set (LoggedSample (d ^ 2) (Fin d) (Fin 2)) :=
  Set.range (dwSampleEmbedding d)

lemma dwSampleSupport_finite (d : ℕ) :
    (dwSampleSupport d).Finite :=
  Set.finite_range _

lemma dw_sample_mem_support_ae (d : ℕ) (hd : 4 ≤ d) :
    ∀ᵐ sample ∂productLaw (dwExperiment d hd) (dwLaw d hd) (d ^ 2),
      sample ∈ dwSampleSupport d := by
  filter_upwards [dw_rewardGood_ae d hd] with sample hr
  refine ⟨fun i => ((sample i).context, (sample i).action), ?_⟩
  funext i
  cases hzi : sample i with
  | mk x a r =>
      have hri := hr i
      simp only [hzi] at hri
      simp [dwSampleEmbedding, dwObservation, hzi]
      rw [hri, dw_linearReward]

instance dwMeasurableSingletonObservation (d : ℕ) :
    MeasurableSingletonClass (BanditObservation (Fin d) (Fin 2)) where
  measurableSet_singleton z := by
    change ∃ s : Set (Fin d × Fin 2 × ℝ), MeasurableSet s ∧
      (fun w : BanditObservation (Fin d) (Fin 2) =>
        (w.context, w.action, w.reward)) ⁻¹' s = {z}
    refine ⟨{(z.context, z.action, z.reward)}, MeasurableSet.singleton _, ?_⟩
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases w with ⟨wc, wa, wr⟩
      rcases z with ⟨zc, za, zr⟩
      simp only at h ⊢
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl
    · intro h
      subst w
      rfl

lemma integrable_of_ae_mem_finite
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Set Ω) (hs : s.Finite)
    (hmem : ∀ᵐ x ∂μ, x ∈ s) (f : Ω → ℝ) :
    Integrable f μ := by
  classical
  let g : Ω → ℝ :=
    fun x => ∑ y ∈ hs.toFinset, if x = y then f y else 0
  have hg : Measurable g := by
    apply Finset.measurable_sum
    intro y _
    exact Measurable.ite (MeasurableSet.singleton y)
      measurable_const measurable_const
  have hfg : f =ᵐ[μ] g := by
    filter_upwards [hmem] with x hx
    dsimp only [g]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y hy hne
      simp [Ne.symm hne]
    · intro hxnot
      exact (hxnot (hs.mem_toFinset.mpr hx)).elim
  have hbound : ∀ x, ‖g x‖ ≤ ∑ y ∈ hs.toFinset, ‖f y‖ := by
    intro x
    calc
      ‖g x‖ ≤ ∑ y ∈ hs.toFinset,
          ‖if x = y then f y else 0‖ := norm_sum_le _ _
      _ ≤ ∑ y ∈ hs.toFinset, ‖f y‖ := by
        gcongr with y hy
        split_ifs <;> simp
  exact (Integrable.of_bound hg.aestronglyMeasurable
    (∑ y ∈ hs.toFinset, ‖f y‖) (ae_of_all μ hbound)).congr hfg.symm

noncomputable def dwLearner (d : ℕ) (hd : 4 ≤ d) :
    Learner (d ^ 2) (𝒳 := Fin d) (𝒜 := Fin 2) :=
  fun sample _ => lowerEnvelopePolicy (dwExperiment d hd) 64 sample

noncomputable def dwRegretIntegrand (d : ℕ) (hd : 4 ≤ d)
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2)) : ℝ :=
  regularizedWelfare (dwExperiment d hd) (dwLaw d hd)
      (gibbsPolicy (dwExperiment d hd) (dwLaw d hd)) -
    regularizedWelfare (dwExperiment d hd) (dwLaw d hd)
      (learnerPolicyOnSample (dwExperiment d hd) (dwLearner d hd) sample)

lemma dwRegretIntegrand_integrable (d : ℕ) (hd : 4 ≤ d) :
    Integrable (dwRegretIntegrand d hd)
      (productLaw (dwExperiment d hd) (dwLaw d hd) (d ^ 2)) := by
  letI : IsProbabilityMeasure (dwLaw d hd).dataMeasure :=
    (dwLaw d hd).isProbability
  letI : IsProbabilityMeasure
      (productLaw (dwExperiment d hd) (dwLaw d hd) (d ^ 2)) := by
    unfold productLaw
    infer_instance
  exact integrable_of_ae_mem_finite
    (productLaw (dwExperiment d hd) (dwLaw d hd) (d ^ 2))
    (dwSampleSupport d) (dwSampleSupport_finite d)
    (dw_sample_mem_support_ae d hd) (dwRegretIntegrand d hd)

lemma dwRegretIntegrand_nonneg (d : ℕ) (hd : 4 ≤ d)
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2)) :
    0 ≤ dwRegretIntegrand d hd sample := by
  unfold dwRegretIntegrand learnerPolicyOnSample
  split_ifs with hbounded
  · exact dw_lowerPolicy_regret_nonneg d hd sample
  · rw [dw_reference_regret]
    exact dw_reference_regret_nonneg d hd

lemma dwRegretIntegrand_on_good (d : ℕ) (hd : 4 ≤ d)
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2))
    (hgood : sample ∈ dwGoodEvent d hd) :
    dwRegretIntegrand d hd sample =
      Real.log (4 / 3) / (8 * Real.log 3) := by
  have hbounded : BoundedLoggedSample sample := by
    intro i
    rw [hgood.2 i]
    exact (dw_exactShell d hd).linearRealizability.1
      (sample i).context (sample i).action
  unfold dwRegretIntegrand learnerPolicyOnSample
  rw [dif_pos hbounded]
  change regularizedWelfare (dwExperiment d hd) (dwLaw d hd)
      (gibbsPolicy (dwExperiment d hd) (dwLaw d hd)) -
    regularizedWelfare (dwExperiment d hd) (dwLaw d hd)
      (lowerEnvelopePolicy (dwExperiment d hd) 64 sample) =
        Real.log (4 / 3) / (8 * Real.log 3)
  rw [dw_lowerEnvelopePolicy_eq_reference d hd sample hgood,
    dw_reference_regret]

lemma dw_learnerRisk_lower (d : ℕ) (hd : 4 ≤ d) :
    learnerRisk (dwExperiment d hd) (dwLaw d hd) (d ^ 2)
        (dwLearner d hd) ≥
      Real.log (4 / 3) / (8 * Real.log 3) *
        (1 - d * Real.exp (-(d : ℝ) * (3 * Real.log 3 - 2))) := by
  let μ := productLaw (dwExperiment d hd) (dwLaw d hd) (d ^ 2)
  letI : IsProbabilityMeasure (dwLaw d hd).dataMeasure :=
    (dwLaw d hd).isProbability
  letI : IsProbabilityMeasure μ := by
    dsimp only [μ, productLaw]
    infer_instance
  let c := Real.log (4 / 3) / (8 * Real.log 3)
  have hc : 0 ≤ c := dw_reference_regret_nonneg d hd
  have hindicator :
      Integrable ((dwGoodEvent d hd).indicator (fun _ => c)) μ := by
    exact (integrable_const c).indicator (dw_goodEvent_measurable d hd)
  have hmono :
      ∫ sample, (dwGoodEvent d hd).indicator (fun _ => c) sample ∂μ ≤
        ∫ sample, dwRegretIntegrand d hd sample ∂μ := by
    apply integral_mono hindicator (dwRegretIntegrand_integrable d hd)
    intro sample
    by_cases hgood : sample ∈ dwGoodEvent d hd
    · rw [Set.indicator_of_mem hgood, dwRegretIntegrand_on_good d hd sample hgood]
    · rw [Set.indicator_of_notMem hgood]
      exact dwRegretIntegrand_nonneg d hd sample
  have hevent :
      c * μ.real (dwGoodEvent d hd) ≤
        ∫ sample, dwRegretIntegrand d hd sample ∂μ := by
    calc
      c * μ.real (dwGoodEvent d hd) =
          ∫ sample, (dwGoodEvent d hd).indicator (fun _ => c) sample ∂μ := by
            rw [integral_indicator_const _ (dw_goodEvent_measurable d hd)]
            simp [smul_eq_mul, mul_comm]
      _ ≤ _ := hmono
  have hprob := dw_goodEvent_probability d hd
  have hscaled :
      c * (1 - d * Real.exp (-(d : ℝ) * (3 * Real.log 3 - 2))) ≤
        c * μ.real (dwGoodEvent d hd) :=
    mul_le_mul_of_nonneg_left hprob hc
  unfold learnerRisk
  change c * (1 - d * Real.exp (-(d : ℝ) * (3 * Real.log 3 - 2))) ≤
    ∫ sample, dwRegretIntegrand d hd sample ∂μ
  exact hscaled.trans hevent

end CausalSmith.Stat.ReverseKLTwoCoverage
