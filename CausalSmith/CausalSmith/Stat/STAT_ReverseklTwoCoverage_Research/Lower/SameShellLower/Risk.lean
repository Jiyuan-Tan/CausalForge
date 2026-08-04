import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.RiskBridge

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def hardObserveSample {n d : ℕ} {C D : ℝ}
    (sample : Fin n →
      (Fin (hardContextCard d C D) × (Fin 3 × Bool))) :
    LoggedSample n (Fin (hardContextCard d C D)) (Fin 3) :=
  fun i => ibObservation (sample i)

lemma hardObserveSample_measurable {n d : ℕ} {C D : ℝ} :
    Measurable
      (hardObserveSample :
        (Fin n → (Fin (hardContextCard d C D) × (Fin 3 × Bool))) →
          LoggedSample n (Fin (hardContextCard d C D)) (Fin 3)) :=
  measurable_of_finite _

noncomputable def hardSourceDecoder
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (L : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3))
    (sample : Fin n →
      (Fin (hardContextCard d C D) × (Fin 3 × Bool)))
    (j : Fin (hardCoordinateCount d)) : Bool :=
  hardDecoder hd eta C D gamma heta hD hDC hCexp
    L (hardObserveSample sample) j

lemma hardSourceDecoder_measurable
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (L : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3)) :
    ∀ j b, MeasurableSet
      {sample | hardSourceDecoder hd eta C D gamma heta hD hDC hCexp
        L sample j = b} := by
  intro j b
  exact (Set.toFinite _).measurableSet

lemma hard_productLaw_eq_map_source
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2) :
    productLaw
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardLaw hd eta C D gamma heta hD hDC hCexp v
        hgamma0 (hgammaBeta.trans (by linarith))
        (hgammaOne.trans (by linarith))) n =
      Measure.map hardObserveSample
        (hardSourceProduct n hd eta C D gamma heta hD hDC hCexp v
          hgamma0 hgammaBeta hgammaOne) := by
  unfold productLaw hardSourceProduct
  rw [hardLaw_dataMeasure_eq_map_source]
  symm
  exact Measure.pi_map_pi
    (fun _ => ibObservation_measurable.aemeasurable)

lemma hard_pointwise_regret_ge_decode
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma : 0 < gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hpert : gamma ≤
      min (hardScale D eta)
        (min (1 / 4)
          (min (hardBeta D eta gamma)
            (1 - hardBeta D eta gamma))))
    (L : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3))
    (hL : IsMeasurableLearner
      (hardExperiment d hd eta C D heta hD hDC hCexp) L)
    (sample : LoggedSample n (Fin (hardContextCard d C D)) (Fin 3)) :
    eta⁻¹ *
        ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
        ((((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2) *
        (∑ j : Fin (hardCoordinateCount d),
          if hardDecoder hd eta C D gamma heta hD hDC hCexp
              L sample j ≠ v j then (1 : ℝ) else 0) ≤
      regularizedWelfare
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardLaw hd eta C D gamma heta hD hDC hCexp v
          hgamma.le (hgammaBeta.trans (by linarith))
          (hgammaOne.trans (by linarith)))
        (gibbsPolicy
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardLaw hd eta C D gamma heta hD hDC hCexp v
            hgamma.le (hgammaBeta.trans (by linarith))
            (hgammaOne.trans (by linarith)))) -
      regularizedWelfare
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardLaw hd eta C D gamma heta hD hDC hCexp v
          hgamma.le (hgammaBeta.trans (by linarith))
          (hgammaOne.trans (by linarith)))
        (learnerPolicyOnSample
          (hardExperiment d hd eta C D heta hD hDC hCexp) L sample) := by
  let hgb : gamma ≤ hardBeta D eta gamma :=
    hgammaBeta.trans (by linarith)
  let hgo : gamma ≤ 1 - hardBeta D eta gamma :=
    hgammaOne.trans (by linarith)
  let E := hardExperiment d hd eta C D heta hD hDC hCexp
  let P := hardLaw hd eta C D gamma heta hD hDC hCexp v
    hgamma.le hgb hgo
  let p := learnerPolicyOnSample E L sample
  let q := gibbsPolicy E P
  obtain ⟨hp, hsupp⟩ := learnerPolicyOnSample_valid E L hL sample
  have hq := gibbsPolicy_isPolicy E P
  have hqpos : ∀ x a, 0 < q x a := by
    intro x a
    dsimp [q]
    exact div_pos
      (mul_pos
        (hardExperiment_reference_pos hd heta hD hDC hCexp x a)
        (Real.exp_pos _))
      (gibbsNormalizer_pos E P x)
  have hkl0 : ∀ x, 0 ≤ policyKL p q x :=
    fun x => policyKL_nonneg_of_isPolicy p q hp hq
      (fun x a hzero => False.elim ((hqpos x a).ne' hzero)) x
  have hloss0 : ∀ x, 0 ≤ contextMass P x * policyKL p q x :=
    fun x => mul_nonneg ENNReal.toReal_nonneg (hkl0 x)
  have hinj : Set.InjOn (hardContext C D)
      (↑(Finset.univ : Finset (Fin (hardCoordinateCount d))) :
        Set (Fin (hardCoordinateCount d))) :=
    fun _ _ _ _ hij => hardContext_injective C D hij
  have himage :
      (∑ j : Fin (hardCoordinateCount d),
          contextMass P (hardContext C D j) *
            policyKL p q (hardContext C D j)) ≤
        ∑ x, contextMass P x * policyKL p q x := by
    calc
      _ = ∑ x ∈ Finset.image (hardContext C D)
              (Finset.univ : Finset (Fin (hardCoordinateCount d))),
            contextMass P x * policyKL p q x := by
          symm
          exact Finset.sum_image hinj
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg hloss0
  let rhoHard := (hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta
  let delta := ((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2
  have hbits :
      (∑ j : Fin (hardCoordinateCount d),
          rhoHard * (delta ^ 2 / 2) *
            (if hardDecoder hd eta C D gamma heta hD hDC hCexp
                L sample j ≠ v j then (1 : ℝ) else 0)) ≤
        ∑ j : Fin (hardCoordinateCount d),
          contextMass P (hardContext C D j) *
            policyKL p q (hardContext C D j) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases herr : hardDecoder hd eta C D gamma heta hD hDC hCexp
        L sample j ≠ v j
    · rw [if_pos herr, mul_one]
      have hmass : contextMass P (hardContext C D j) = rhoHard := by
        dsimp [P, rhoHard]
        rw [hardLaw_contextMass]
        simp [hardContext, hardRho, hardContextRawMass]
      rw [hmass]
      exact mul_le_mul_of_nonneg_left
        (hardDecoder_error_policyKL hd eta C D gamma heta hD hDC hCexp
          v hgamma hgb hgo hden L hL sample j herr)
        (div_nonneg (inv_nonneg.mpr
          (Nat.cast_nonneg (hardCoordinateCount d)))
          (hardTotal_pos (d := d) heta hD hDC hCexp).le)
    · rw [if_neg herr]
      simp
      exact hloss0 (hardContext C D j)
  have hselected :
      rhoHard * (delta ^ 2 / 2) *
          (∑ j : Fin (hardCoordinateCount d),
            if hardDecoder hd eta C D gamma heta hD hDC hCexp
                L sample j ≠ v j then (1 : ℝ) else 0) ≤
        ∑ x, contextMass P x * policyKL p q x := by
    calc
      _ = ∑ j : Fin (hardCoordinateCount d),
          rhoHard * (delta ^ 2 / 2) *
            (if hardDecoder hd eta C D gamma heta hD hDC hCexp
                L sample j ≠ v j then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
      _ ≤ _ := hbits.trans himage
  rw [gibbs_regret_identity E P C D
    (hard_exactShell hd heta hD hDC hCexp hgamma.le hden hgb hgo v)
    p hp (fun x a hp0 => by
      by_contra href
      exact hp0 (hsupp x a href))]
  change eta⁻¹ * rhoHard * (delta ^ 2 / 2) * _ ≤
    eta⁻¹ * ∑ x, contextMass P x * policyKL p q x
  calc
    _ = eta⁻¹ * (rhoHard * (delta ^ 2 / 2) * _) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hselected (inv_nonneg.mpr heta.le)

lemma hard_measurable_policyKL_learner
    {d n : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜)
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hL : IsMeasurableLearner E L)
    (q : Policy 𝒳 𝒜) (x : 𝒳) :
    Measurable (fun sample =>
      policyKL (learnerPolicyOnSample E L sample) q x) := by
  unfold policyKL
  apply Finset.measurable_sum Finset.univ
  intro a _
  have hf : Measurable (fun sample =>
      learnerPolicyOnSample E L sample x a) := hL.1 x a
  apply Measurable.ite
  · simpa only [Set.preimage, Set.mem_singleton_iff] using
      hf (MeasurableSet.singleton 0)
  · exact measurable_const
  · exact hf.mul (Real.measurable_log.comp (hf.div measurable_const))

lemma hard_regret_measurable
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma)
    (L : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3))
    (hL : IsMeasurableLearner
      (hardExperiment d hd eta C D heta hD hDC hCexp) L) :
    Measurable (fun sample =>
      regularizedWelfare
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardLaw hd eta C D gamma heta hD hDC hCexp v
          hgamma0 hgammaBeta hgammaOne)
        (gibbsPolicy
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardLaw hd eta C D gamma heta hD hDC hCexp v
            hgamma0 hgammaBeta hgammaOne)) -
      regularizedWelfare
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardLaw hd eta C D gamma heta hD hDC hCexp v
          hgamma0 hgammaBeta hgammaOne)
        (learnerPolicyOnSample
          (hardExperiment d hd eta C D heta hD hDC hCexp) L sample)) := by
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
    exact hard_measurable_policyKL_learner
      (hardExperiment d hd eta C D heta hD hDC hCexp) L hL
      (hardExperiment d hd eta C D heta hD hDC hCexp).reference x

lemma hard_integral_decode_count_eq_hammingRisk
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2)
    (L : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3)) :
    (∫ sample,
        (∑ j : Fin (hardCoordinateCount d),
          if hardSourceDecoder hd eta C D gamma heta hD hDC hCexp
              L sample j ≠ v j then (1 : ℝ) else 0)
      ∂hardSourceProduct n hd eta C D gamma heta hD hDC hCexp v
        hgamma0 hgammaBeta hgammaOne) =
      Causalean.Stat.hammingRisk
        (fun u => hardSourceProduct n hd eta C D gamma heta hD hDC
          hCexp u hgamma0 hgammaBeta hgammaOne)
        (hardSourceDecoder hd eta C D gamma heta hD hDC hCexp L) v := by
  rw [integral_finset_sum Finset.univ (fun _ _ => Integrable.of_finite)]
  unfold Causalean.Stat.hammingRisk
  apply Finset.sum_congr rfl
  intro j _
  let s := {sample |
    hardSourceDecoder hd eta C D gamma heta hD hDC hCexp
      L sample j ≠ v j}
  have hs : MeasurableSet s := (Set.toFinite s).measurableSet
  have hfun :
      (fun sample =>
        if hardSourceDecoder hd eta C D gamma heta hD hDC hCexp
            L sample j ≠ v j then (1 : ℝ) else 0) =
      s.indicator (fun _ => (1 : ℝ)) := by
    funext sample
    by_cases h : hardSourceDecoder hd eta C D gamma heta hD hDC hCexp
        L sample j = v j <;> simp [s, h]
  rw [hfun, integral_indicator_const 1 hs]
  simp only [smul_eq_mul, mul_one]
  unfold s
  rfl

lemma hard_learnerRisk_ge_hamming
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma : 0 < gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hpert : gamma ≤
      min (hardScale D eta)
        (min (1 / 4)
          (min (hardBeta D eta gamma)
            (1 - hardBeta D eta gamma))))
    (L : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3))
    (hL : IsMeasurableLearner
      (hardExperiment d hd eta C D heta hD hDC hCexp) L) :
    eta⁻¹ *
        ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
        ((((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2) *
        Causalean.Stat.hammingRisk
          (fun u => hardSourceProduct n hd eta C D gamma heta hD hDC
            hCexp u hgamma.le hgammaBeta hgammaOne)
          (hardSourceDecoder hd eta C D gamma heta hD hDC hCexp L) v ≤
      learnerRisk
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardLaw hd eta C D gamma heta hD hDC hCexp v
          hgamma.le (hgammaBeta.trans (by linarith))
          (hgammaOne.trans (by linarith))) n L := by
  let μ := hardSourceProduct n hd eta C D gamma heta hD hDC hCexp v
    hgamma.le hgammaBeta hgammaOne
  let count := fun sample =>
    ∑ j : Fin (hardCoordinateCount d),
      if hardSourceDecoder hd eta C D gamma heta hD hDC hCexp
          L sample j ≠ v j then (1 : ℝ) else 0
  let loss := fun sample =>
    regularizedWelfare
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardLaw hd eta C D gamma heta hD hDC hCexp v
        hgamma.le (hgammaBeta.trans (by linarith))
        (hgammaOne.trans (by linarith)))
      (gibbsPolicy
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardLaw hd eta C D gamma heta hD hDC hCexp v
          hgamma.le (hgammaBeta.trans (by linarith))
          (hgammaOne.trans (by linarith)))) -
    regularizedWelfare
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardLaw hd eta C D gamma heta hD hDC hCexp v
        hgamma.le (hgammaBeta.trans (by linarith))
        (hgammaOne.trans (by linarith)))
      (learnerPolicyOnSample
        (hardExperiment d hd eta C D heta hD hDC hCexp) L
        (hardObserveSample sample))
  let coeff := eta⁻¹ *
    ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
    ((((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2)
  have hmono : ∀ sample, coeff * count sample ≤ loss sample := by
    intro sample
    exact hard_pointwise_regret_ge_decode hd eta C D gamma heta hD hDC
      hCexp v hgamma hgammaBeta hgammaOne hden hpert L hL
      (hardObserveSample sample)
  have hint :
      (∫ sample, coeff * count sample ∂μ) ≤
        ∫ sample, loss sample ∂μ :=
    integral_mono Integrable.of_finite Integrable.of_finite hmono
  rw [show (∫ sample, coeff * count sample ∂μ) =
      coeff * (∫ sample, count sample ∂μ) by rw [integral_const_mul]] at hint
  rw [show (∫ sample, count sample ∂μ) =
      Causalean.Stat.hammingRisk
        (fun u => hardSourceProduct n hd eta C D gamma heta hD hDC
          hCexp u hgamma.le hgammaBeta hgammaOne)
        (hardSourceDecoder hd eta C D gamma heta hD hDC hCexp L) v by
    exact hard_integral_decode_count_eq_hammingRisk hd eta C D gamma heta
      hD hDC hCexp v hgamma.le hgammaBeta hgammaOne L] at hint
  unfold learnerRisk
  rw [hard_productLaw_eq_map_source hd eta C D gamma heta hD hDC hCexp
    v hgamma.le hgammaBeta hgammaOne]
  rw [integral_map hardObserveSample_measurable.aemeasurable
    ((hard_regret_measurable hd eta C D gamma heta hD hDC hCexp v
      hgamma.le (hgammaBeta.trans (by linarith))
      (hgammaOne.trans (by linarith)) L hL).aestronglyMeasurable)]
  exact hint

lemma hard_exists_learnerRisk_lower
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hgamma : 0 < gamma)
    (hbeta : 0 < hardBeta D eta gamma)
    (hbeta1 : hardBeta D eta gamma < 1)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hpert : gamma ≤
      min (hardScale D eta)
        (min (1 / 4)
          (min (hardBeta D eta gamma)
            (1 - hardBeta D eta gamma))))
    (hbudget : (n : ℝ) * hardNeighborChiBound d eta C D gamma ≤
      Real.log (17 / 16))
    (L : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3))
    (hL : IsMeasurableLearner
      (hardExperiment d hd eta C D heta hD hDC hCexp) L) :
    ∃ v : Fin (hardCoordinateCount d) → Bool,
      eta⁻¹ *
          ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
          ((((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2) *
          (hardCoordinateCount d : ℝ) * 7 / 16 ≤
        learnerRisk
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardLaw hd eta C D gamma heta hD hDC hCexp v
            hgamma.le (hgammaBeta.trans (by linarith))
            (hgammaOne.trans (by linarith))) n L := by
  have htv : ∀ j (v : Fin (hardCoordinateCount d) → Bool),
      Causalean.Stat.tvDist
        (hardSourceProduct n hd eta C D gamma heta hD hDC hCexp v
          hgamma.le hgammaBeta hgammaOne)
        (hardSourceProduct n hd eta C D gamma heta hD hDC hCexp
          (Causalean.Stat.flipBit j v)
          hgamma.le hgammaBeta hgammaOne) ≤ 1 / 8 :=
    fun j v => hardSourceProduct_neighbor_tv_eighth hd eta C D gamma heta hD hDC
      hCexp v hgamma.le hbeta hbeta1 hgammaBeta hgammaOne j hbudget
  obtain ⟨v, hv⟩ := Causalean.Stat.assouad_exists
    (fun u => hardSourceProduct n hd eta C D gamma heta hD hDC
      hCexp u hgamma.le hgammaBeta hgammaOne)
    (hardSourceDecoder hd eta C D gamma heta hD hDC hCexp L)
    (hardSourceDecoder_measurable hd eta C D gamma heta hD hDC hCexp L)
    htv
  refine ⟨v, ?_⟩
  have hrisk := hard_learnerRisk_ge_hamming hd eta C D gamma heta hD hDC
    hCexp v hgamma hgammaBeta hgammaOne hden hpert L hL
  have hcoeff : 0 ≤ eta⁻¹ *
      ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
      ((((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2) := by
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr heta.le)
        (div_nonneg
          (inv_nonneg.mpr
            (Nat.cast_nonneg (hardCoordinateCount d)))
          (hardTotal_pos (d := d) heta hD hDC hCexp).le))
      (div_nonneg (sq_nonneg _) (by norm_num))
  have hham : (hardCoordinateCount d : ℝ) * 7 / 16 ≤
      Causalean.Stat.hammingRisk
        (fun u => hardSourceProduct n hd eta C D gamma heta hD hDC
          hCexp u hgamma.le hgammaBeta hgammaOne)
        (hardSourceDecoder hd eta C D gamma heta hD hDC hCexp L) v := by
    norm_num at hv ⊢
    linarith
  calc
    eta⁻¹ * ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
          ((((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2) *
          (hardCoordinateCount d : ℝ) * 7 / 16 =
        (eta⁻¹ * ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
          ((((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2)) *
          ((hardCoordinateCount d : ℝ) * 7 / 16) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hham hcoeff).trans hrisk

end

end CausalSmith.Stat.ReverseKLTwoCoverage
