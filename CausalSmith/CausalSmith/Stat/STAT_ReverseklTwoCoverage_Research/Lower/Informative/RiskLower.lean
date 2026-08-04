import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.Assouad

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def informativeObserveSample {n d : ℕ}
    (sample : Fin n → (Fin (d + 1) × (Fin 2 × Bool))) :
    LoggedSample n (Fin (d + 1)) (Fin 2) :=
  fun i => ibObservation (sample i)

lemma informativeObserveSample_measurable {n d : ℕ} :
    Measurable
      (informativeObserveSample :
        (Fin n → (Fin (d + 1) × (Fin 2 × Bool))) →
          LoggedSample n (Fin (d + 1)) (Fin 2)) :=
  measurable_of_finite _

noncomputable def informativeSourceDecoder
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (L : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2))
    (sample : Fin n → (Fin (d + 1) × (Fin 2 × Bool)))
    (j : Fin (d - 1)) : Bool :=
  informativeDecoder hd eta C D gamma heta hD hDC hCexp
    L (informativeObserveSample sample) j

lemma informativeSourceDecoder_measurable
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (L : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2)) :
    ∀ j b, MeasurableSet
      {sample | informativeSourceDecoder hd eta C D gamma heta hD hDC
        hCexp L sample j = b} := by
  intro j b
  exact (Set.toFinite _).measurableSet

lemma informative_productLaw_eq_map_source
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    productLaw
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp)
        (informativeLaw d hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgamma) n =
      Measure.map informativeObserveSample
        (informativeSourceProduct n d hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgamma) := by
  unfold productLaw informativeSourceProduct
  rw [informativeLaw_dataMeasure_eq_map_source]
  symm
  exact Measure.pi_map_pi
    (fun _ => ibObservation_measurable.aemeasurable)

lemma measurable_policyKL_learner
    {d n : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜)
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hL : IsMeasurableLearner E L)
    (q : Policy 𝒳 𝒜) (x : 𝒳) :
    Measurable (fun sample => policyKL
      (learnerPolicyOnSample E L sample) q x) := by
  unfold policyKL
  apply Finset.measurable_sum Finset.univ
  intro a _
  have hf : Measurable (fun sample =>
      learnerPolicyOnSample E L sample x a) := hL.1 x a
  apply Measurable.ite
  · simpa only [Set.preimage, Set.mem_singleton_iff] using
      hf (MeasurableSet.singleton 0)
  · exact measurable_const
  · exact hf.mul
      (Real.measurable_log.comp (hf.div measurable_const))

lemma informative_regret_measurable
    {d n : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (L : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2))
    (hL : IsMeasurableLearner
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp) L) :
    Measurable (fun sample =>
      regularizedWelfare
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp)
          (informativeLaw d hd eta C D gamma heta hD hDC hCexp
            v hgamma0 hgamma)
          (gibbsPolicy
            (informativeExperiment d hd eta C D heta
              (lt_of_lt_of_le hD hDC) hCexp)
            (informativeLaw d hd eta C D gamma heta hD hDC hCexp
              v hgamma0 hgamma)) -
        regularizedWelfare
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp)
          (informativeLaw d hd eta C D gamma heta hD hDC hCexp
            v hgamma0 hgamma)
          (learnerPolicyOnSample
            (informativeExperiment d hd eta C D heta
              (lt_of_lt_of_le hD hDC) hCexp) L sample)) := by
  unfold regularizedWelfare
  apply measurable_const.sub
  apply Measurable.sub
  · apply Finset.measurable_sum Finset.univ
    intro x _
    apply measurable_const.mul
    apply Finset.measurable_sum Finset.univ
    intro a _
    exact (hL.1 x a).mul measurable_const
  · apply measurable_const.mul
    apply Finset.measurable_sum Finset.univ
    intro x _
    apply measurable_const.mul
    exact measurable_policyKL_learner
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp) L hL
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).reference x

lemma integral_decode_count_eq_hammingRisk
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (L : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2)) :
    (∫ sample,
        (∑ j : Fin (d - 1),
          if informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp
              L sample j ≠ v j then (1 : ℝ) else 0)
      ∂informativeSourceProduct n d hd eta C D gamma heta hD hDC hCexp
        v hgamma0 hgamma) =
      Causalean.Stat.hammingRisk
        (fun u => informativeSourceProduct n d hd eta C D gamma heta hD hDC
          hCexp u hgamma0 hgamma)
        (informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp L)
        v := by
  rw [integral_finset_sum Finset.univ
    (fun _ _ => Integrable.of_finite)]
  unfold Causalean.Stat.hammingRisk
  apply Finset.sum_congr rfl
  intro j _
  let s := {sample |
    informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp
      L sample j ≠ v j}
  have hs : MeasurableSet s := (Set.toFinite s).measurableSet
  have hfun :
      (fun sample =>
        if informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp
            L sample j ≠ v j then (1 : ℝ) else 0) =
      s.indicator (fun _ => (1 : ℝ)) := by
    funext sample
    by_cases h :
        informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp
          L sample j = v j
    · simp [s, h]
    · simp [s, h]
  rw [hfun, integral_indicator_const 1 hs]
  simp only [smul_eq_mul, mul_one]
  unfold s
  rfl

lemma informative_learnerRisk_ge_hamming
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (L : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2))
    (hL : IsMeasurableLearner
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp) L) :
    eta⁻¹ * (1 / informativeTotal d eta C D) *
        ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
        Causalean.Stat.hammingRisk
          (fun u => informativeSourceProduct n d hd eta C D gamma heta hD hDC
            hCexp u hgamma0 hgamma)
          (informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp L)
          v ≤
      learnerRisk
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp)
        (informativeLaw d hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgamma) n L := by
  let μ := informativeSourceProduct n d hd eta C D gamma heta hD hDC hCexp
    v hgamma0 hgamma
  let count := fun sample =>
    ∑ j : Fin (d - 1),
      if informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp
          L sample j ≠ v j then (1 : ℝ) else 0
  let loss := fun sample =>
    regularizedWelfare
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp)
        (informativeLaw d hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgamma)
        (gibbsPolicy
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp)
          (informativeLaw d hd eta C D gamma heta hD hDC hCexp
            v hgamma0 hgamma)) -
      regularizedWelfare
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp)
        (informativeLaw d hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgamma)
        (learnerPolicyOnSample
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp) L
          (informativeObserveSample sample))
  have hmono : ∀ sample,
      eta⁻¹ * (1 / informativeTotal d eta C D) *
          ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
          count sample ≤ loss sample := by
    intro sample
    exact informative_pointwise_regret_ge_decode hd eta C D gamma heta hD
      hDC hCexp v hgamma0 hgamma L hL (informativeObserveSample sample)
  have hint :
      (∫ sample,
        eta⁻¹ * (1 / informativeTotal d eta C D) *
          ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
          count sample ∂μ) ≤
        ∫ sample, loss sample ∂μ :=
    integral_mono Integrable.of_finite Integrable.of_finite hmono
  rw [show (∫ sample,
      eta⁻¹ * (1 / informativeTotal d eta C D) *
        ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
        count sample ∂μ) =
      eta⁻¹ * (1 / informativeTotal d eta C D) *
        ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
        (∫ sample, count sample ∂μ) by
    rw [show (fun sample =>
        eta⁻¹ * (1 / informativeTotal d eta C D) *
          ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
          count sample) =
        fun sample =>
          (eta⁻¹ * (1 / informativeTotal d eta C D) *
            ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2)) *
            count sample by rfl,
      integral_const_mul]] at hint
  rw [show (∫ sample, count sample ∂μ) =
      Causalean.Stat.hammingRisk
        (fun u => informativeSourceProduct n d hd eta C D gamma heta hD hDC
          hCexp u hgamma0 hgamma)
        (informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp L)
        v by
    exact integral_decode_count_eq_hammingRisk hd eta C D gamma heta hD hDC
      hCexp v hgamma0 hgamma L] at hint
  unfold learnerRisk
  rw [informative_productLaw_eq_map_source hd eta C D gamma heta hD hDC
    hCexp v hgamma0 hgamma]
  rw [integral_map informativeObserveSample_measurable.aemeasurable
    ((informative_regret_measurable hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hgamma L hL).aestronglyMeasurable)]
  exact hint

lemma informative_exists_learnerRisk_lower
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (hbudget :
      (n : ℝ) *
        (4 * gamma ^ 2 / informativeTotal d eta C D *
          (1 / informativeBeta eta D +
            1 / (1 - informativeBeta eta D))) ≤ 1)
    (L : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2))
    (hL : IsMeasurableLearner
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp) L) :
    ∃ v : Fin (d - 1) → Bool,
      eta⁻¹ * (1 / informativeTotal d eta C D) *
          ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
          ((d - 1 : ℕ) : ℝ) / 8 ≤
        learnerRisk
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp)
          (informativeLaw d hd eta C D gamma heta hD hDC hCexp
            v hgamma0 hgamma) n L := by
  have htv : ∀ j (v : Fin (d - 1) → Bool),
      Causalean.Stat.tvDist
          (informativeSourceProduct n d hd eta C D gamma heta hD hDC hCexp
            v hgamma0 hgamma)
          (informativeSourceProduct n d hd eta C D gamma heta hD hDC hCexp
            (Causalean.Stat.flipBit j v) hgamma0 hgamma) ≤ 3 / 4 :=
    fun j v => informativeSourceProduct_neighbor_tv hd eta C D gamma heta hD
      hDC hCexp v hgamma0 hgamma j hbudget
  obtain ⟨v, hv⟩ := Causalean.Stat.assouad_exists
    (fun u => informativeSourceProduct n d hd eta C D gamma heta hD hDC
      hCexp u hgamma0 hgamma)
    (informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp L)
    (informativeSourceDecoder_measurable hd eta C D gamma heta hD hDC hCexp L)
    htv
  refine ⟨v, ?_⟩
  have hrisk := informative_learnerRisk_ge_hamming hd eta C D gamma heta hD
    hDC hCexp v hgamma0 hgamma L hL
  have hk :
      0 ≤ eta⁻¹ * (1 / informativeTotal d eta C D) *
        ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) := by
    have hT := informativeTotal_pos hd heta hD hDC hCexp
    positivity
  have hham :
      (((d - 1 : ℕ) : ℝ) / 8) ≤
        Causalean.Stat.hammingRisk
          (fun u => informativeSourceProduct n d hd eta C D gamma heta hD hDC
            hCexp u hgamma0 hgamma)
          (informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp L)
          v := by
    have hv' :
        (((d - 1 : ℕ) : ℝ) / 2) * (1 - 3 / 4) ≤
          Causalean.Stat.hammingRisk
            (fun u => informativeSourceProduct n d hd eta C D gamma heta hD hDC
              hCexp u hgamma0 hgamma)
            (informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp L)
            v := hv
    norm_num at hv' ⊢
    linarith
  calc
    eta⁻¹ * (1 / informativeTotal d eta C D) *
          ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
          ((d - 1 : ℕ) : ℝ) / 8 =
        (eta⁻¹ * (1 / informativeTotal d eta C D) *
          ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2)) *
          (((d - 1 : ℕ) : ℝ) / 8) := by ring
    _ ≤ (eta⁻¹ * (1 / informativeTotal d eta C D) *
          ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2)) *
        Causalean.Stat.hammingRisk
          (fun u => informativeSourceProduct n d hd eta C D gamma heta hD hDC
            hCexp u hgamma0 hgamma)
          (informativeSourceDecoder hd eta C D gamma heta hD hDC hCexp L)
          v := mul_le_mul_of_nonneg_left hham hk
    _ ≤ learnerRisk
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp)
          (informativeLaw d hd eta C D gamma heta hD hDC hCexp
            v hgamma0 hgamma) n L := hrisk

end

end CausalSmith.Stat.ReverseKLTwoCoverage
