import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.DimensionWitness.Construction
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Gibbs.RegretIdentity

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal Topology

lemma dw_boundedFeatures (d : ℕ) (hd : 4 ≤ d) :
    BoundedFeatures (dwExperiment d hd) := by
  intro x a
  by_cases ha : a = 0
  · simp [dwExperiment, dwFeature, ha]
  · simp [dwExperiment, dwFeature, ha]
    norm_num

lemma dw_linearRealizability (d : ℕ) (hd : 4 ≤ d) :
    LinearRealizability (dwExperiment d hd) (dwLaw d hd) := by
  constructor
  · intro x a
    rw [dw_linearReward]
    by_cases ha : a = 0 <;> simp [dwReward, ha] <;> norm_num [inv_le_one₀]
  · intro x a hcell
    have htuple : Measurable
        (fun z : BanditObservation (Fin d) (Fin 2) =>
          (z.context, z.action, z.reward)) := by
      change Measurable[MeasurableSpace.comap
        (fun z : BanditObservation (Fin d) (Fin 2) =>
          (z.context, z.action, z.reward)) inferInstance] _
      exact comap_measurable _
    let s : Set (BanditObservation (Fin d) (Fin 2)) :=
      {z | z.context = x ∧ z.action = a}
    have hs : MeasurableSet s := by
      dsimp [s]
      simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
        (Measurable.prodMk htuple.fst htuple.snd.fst)
          (MeasurableSet.singleton (x, a))
    have heq :
        (∫ z in s, z.reward ∂(dwLaw d hd).dataMeasure) =
          ∫ _z in s, dwReward a ∂(dwLaw d hd).dataMeasure := by
      apply integral_congr_ae
      apply (ae_restrict_iff' hs).2
      filter_upwards [dw_reward_eq_ae d hd] with z hz
      intro hzs
      rw [hz]
      exact congrArg dwReward hzs.2
    unfold rewardMean
    rw [show {z : BanditObservation (Fin d) (Fin 2) |
        z.context = x ∧ z.action = a} = s by rfl, heq,
      setIntegral_const, smul_eq_mul,
      show (dwLaw d hd).dataMeasure.real s = cellMass (dwLaw d hd) x a by rfl,
      dw_cellMass, dw_linearReward]
    field_simp

lemma dw_referenceLogging (d : ℕ) (hd : 4 ≤ d) :
    ReferenceLogging (dwExperiment d hd) (dwLaw d hd) := by
  intro x a
  rw [dw_cellMass, dw_contextMass]
  simp [dwExperiment]

lemma dw_gibbsNormalizer (d : ℕ) (hd : 4 ≤ d) (x : Fin d) :
    gibbsNormalizer (dwExperiment d hd) (dwLaw d hd) x = 6 := by
  unfold gibbsNormalizer
  rw [Fin.sum_univ_two]
  change (1 / 2 : ℝ) *
      Real.exp (dwEta * linearReward (dwLaw d hd) x 0) +
    (1 / 2 : ℝ) *
      Real.exp (dwEta * linearReward (dwLaw d hd) x 1) = 6
  rw [dw_linearReward, dw_linearReward]
  have hlog : Real.exp (Real.log 3) = 3 :=
    Real.exp_log (by norm_num)
  rw [show dwEta * dwReward 0 = 2 * Real.log 3 by
      simp [dwEta, dwReward]; ring,
    show dwEta * dwReward 1 = Real.log 3 by
      simp [dwEta, dwReward]; ring,
    show 2 * Real.log 3 = Real.log 3 + Real.log 3 by ring,
    Real.exp_add, hlog]
  norm_num

lemma dw_gibbsPolicy (d : ℕ) (hd : 4 ≤ d) (x : Fin d) (a : Fin 2) :
    gibbsPolicy (dwExperiment d hd) (dwLaw d hd) x a =
      if a = 0 then 3 / 4 else 1 / 4 := by
  rw [gibbsPolicy, dw_gibbsNormalizer]
  by_cases ha : a = 0
  · subst a
    change (1 / 2 : ℝ) *
        Real.exp (dwEta * linearReward (dwLaw d hd) x 0) / 6 = 3 / 4
    rw [dw_linearReward,
      show dwEta * dwReward 0 = Real.log 3 + Real.log 3 by
        simp [dwEta, dwReward]; ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  · have ha1 : a = 1 := by omega
    subst a
    change (1 / 2 : ℝ) *
        Real.exp (dwEta * linearReward (dwLaw d hd) x 1) / 6 = 1 / 4
    rw [dw_linearReward,
      show dwEta * dwReward 1 = Real.log 3 by
        simp [dwEta, dwReward]; ring,
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num

lemma dw_loggingCovariance (d : ℕ) (hd : 4 ≤ d) (i j : Fin d) :
    loggingCovariance (dwExperiment d hd) (dwLaw d hd) i j =
      if i = j then 5 / (8 * (d : ℝ)) else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [loggingCovariance]
    simp_rw [dw_contextMass]
    simp [dwExperiment, dwFeature, Fin.sum_univ_two]
    ring
  · simp only [loggingCovariance]
    simp_rw [dw_contextMass]
    simp [dwExperiment, dwFeature, Fin.sum_univ_two, hij, Ne.symm hij]

lemma dw_targetCovariance (d : ℕ) (hd : 4 ≤ d) (i j : Fin d) :
    targetCovariance (dwExperiment d hd) (dwLaw d hd) i j =
      if i = j then 13 / (16 * (d : ℝ)) else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [targetCovariance]
    simp_rw [dw_contextMass, dw_gibbsPolicy]
    simp [dwExperiment, dwFeature, Fin.sum_univ_two]
    ring
  · simp only [targetCovariance]
    simp_rw [dw_contextMass, dw_gibbsPolicy]
    simp [dwExperiment, dwFeature, Fin.sum_univ_two, hij, Ne.symm hij]

lemma dw_logging_posDef (d : ℕ) (hd : 4 ≤ d) :
    Matrix.PosDef (loggingCovariance (dwExperiment d hd) (dwLaw d hd)) := by
  rw [show loggingCovariance (dwExperiment d hd) (dwLaw d hd) =
      Matrix.diagonal (fun _ : Fin d => 5 / (8 * (d : ℝ))) by
    ext i j
    simp [dw_loggingCovariance, Matrix.diagonal_apply]]
  exact Matrix.PosDef.diagonal (fun _ => by positivity)

lemma dw_pointwiseCoverage (d : ℕ) (hd : 4 ≤ d) :
    pointwiseCoverage (dwExperiment d hd) (dwLaw d hd) = 3 / 2 := by
  let x0 : Fin d := ⟨0, by omega⟩
  let ratios : Set ℝ := {1 / 2, 3 / 2}
  have hset :
      {c : ℝ | ∃ x a, 0 < contextMass (dwLaw d hd) x ∧
          0 < (dwExperiment d hd).reference x a ∧
          c = gibbsPolicy (dwExperiment d hd) (dwLaw d hd) x a /
            (dwExperiment d hd).reference x a} = ratios := by
    ext c
    constructor
    · rintro ⟨x, a, hx, ha, rfl⟩
      by_cases hzero : a = 0
      · right
        rw [dw_gibbsPolicy]
        simp [dwExperiment, hzero]
        norm_num
      · left
        rw [dw_gibbsPolicy]
        simp [dwExperiment, hzero]
        norm_num
    · intro hc
      rcases hc with hc | hc
      · refine ⟨x0, 1, ?_, ?_, ?_⟩
        · rw [dw_contextMass]
          positivity
        · simp [dwExperiment]
        · rw [dw_gibbsPolicy]
          norm_num [dwExperiment]
          exact hc
      · refine ⟨x0, 0, ?_, ?_, ?_⟩
        · rw [dw_contextMass]
          positivity
        · simp [dwExperiment]
        · rw [dw_gibbsPolicy]
          norm_num [dwExperiment]
          simpa using hc
  unfold pointwiseCoverage
  rw [hset]
  simp [ratios]
  norm_num

lemma dw_loggingQuadratic (d : ℕ) (hd : 4 ≤ d) (v : Fin d → ℝ) :
    quadraticForm
        (loggingCovariance (dwExperiment d hd) (dwLaw d hd)) v =
      (5 / (8 * (d : ℝ))) * ∑ i, (v i) ^ 2 := by
  unfold quadraticForm
  simp_rw [dw_loggingCovariance]
  calc
    (∑ i, ∑ j, v i *
        (if i = j then 5 / (8 * (d : ℝ)) else 0) * v j) =
        ∑ i, v i * (5 / (8 * (d : ℝ))) * v i := by
          apply Finset.sum_congr rfl
          intro i _
          simp
    _ = (5 / (8 * (d : ℝ))) * ∑ i, (v i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma dw_targetQuadratic (d : ℕ) (hd : 4 ≤ d) (v : Fin d → ℝ) :
    quadraticForm
        (targetCovariance (dwExperiment d hd) (dwLaw d hd)) v =
      (13 / (16 * (d : ℝ))) * ∑ i, (v i) ^ 2 := by
  unfold quadraticForm
  simp_rw [dw_targetCovariance]
  calc
    (∑ i, ∑ j, v i *
        (if i = j then 13 / (16 * (d : ℝ)) else 0) * v j) =
        ∑ i, v i * (13 / (16 * (d : ℝ))) * v i := by
          apply Finset.sum_congr rfl
          intro i _
          simp
    _ = (13 / (16 * (d : ℝ))) * ∑ i, (v i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma dw_sum_sq_pos {d : ℕ} {v : Fin d → ℝ} (hv : v ≠ 0) :
    0 < ∑ i, (v i) ^ 2 := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos'
    (fun j _ => sq_nonneg (v j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

lemma dw_featureCoverage (d : ℕ) (hd : 4 ≤ d) :
    featureCoverage (dwExperiment d hd) (dwLaw d hd) = 13 / 10 := by
  let quotients : Set ℝ :=
    {q | ∃ v : Fin d → ℝ, v ≠ 0 ∧
      q = quadraticForm
          (targetCovariance (dwExperiment d hd) (dwLaw d hd)) v /
        quadraticForm
          (loggingCovariance (dwExperiment d hd) (dwLaw d hd)) v}
  have hquotients : quotients = {13 / 10} := by
    ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [dw_targetQuadratic, dw_loggingQuadratic]
      have hs : (∑ i, (v i) ^ 2) ≠ 0 := ne_of_gt (dw_sum_sq_pos hv)
      have hd0 : (d : ℝ) ≠ 0 := by positivity
      simp only [Set.mem_singleton_iff]
      field_simp
      ring
    · intro hq
      rw [Set.mem_singleton_iff] at hq
      subst q
      let i0 : Fin d := ⟨0, by omega⟩
      let v : Fin d → ℝ := fun i => if i = i0 then 1 else 0
      have hv : v ≠ 0 := by
        intro h
        have hi := congrFun h i0
        simp [v] at hi
      refine ⟨v, hv, ?_⟩
      rw [dw_targetQuadratic, dw_loggingQuadratic]
      have hs : ∑ i, (v i) ^ 2 = 1 := by simp [v]
      rw [hs]
      have hd0 : (d : ℝ) ≠ 0 := by positivity
      field_simp
      ring
  unfold featureCoverage maxGeneralizedEigenvalue
  change sSup quotients = 13 / 10
  rw [hquotients]
  simp

lemma dw_exactShell (d : ℕ) (hd : 4 ≤ d) :
    ExactShell (dwExperiment d hd) (dwLaw d hd)
      dwCoverageC dwCoverageD := by
  refine
    { finiteContexts := ⟨inferInstance⟩
      finiteActions := ⟨inferInstance⟩
      boundedFeatures := dw_boundedFeatures d hd
      linearRealizability := dw_linearRealizability d hd
      referenceLogging := dw_referenceLogging d hd
      nonsingularLoggingGeometry := dw_logging_posDef d hd
      pointwiseExactShell := ?_
      featureExactShell := ?_ }
  · constructor
    · norm_num [dwCoverageC]
    · simpa [dwCoverageC] using dw_pointwiseCoverage d hd
  · constructor
    · norm_num [dwCoverageD]
    · simpa [dwCoverageD] using dw_featureCoverage d hd

lemma dw_deterministicReward (d : ℕ) (hd : 4 ≤ d) :
    ∀ᵐ z ∂(dwLaw d hd).dataMeasure,
      z.reward = linearReward (dwLaw d hd) z.context z.action := by
  filter_upwards [dw_reward_eq_ae d hd] with z hz
  rw [hz, dw_linearReward]

end CausalSmith.Stat.ReverseKLTwoCoverage
