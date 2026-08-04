import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Gibbs.RegretIdentity

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

lemma policyKL_nonneg_of_isPolicy
    {𝒳 𝒜 : Type*} [Fintype 𝒜]
    (p q : Policy 𝒳 𝒜) (hp : IsPolicy p) (hq : IsPolicy q)
    (hsupp : PolicySupportedOn p q) (x : 𝒳) :
    0 ≤ policyKL p q x := by
  have hterm : ∀ a, p x a - q x a ≤
      if p x a = 0 then 0 else p x a * Real.log (p x a / q x a) := by
    intro a
    split_ifs with hpa
    · simp [hpa, hq.1 x a]
    · have hqa : q x a ≠ 0 := by
        intro hq0
        exact hpa (hsupp x a hq0)
      have hp_pos : 0 < p x a :=
        lt_of_le_of_ne (hp.1 x a) (Ne.symm hpa)
      have hq_pos : 0 < q x a :=
        lt_of_le_of_ne (hq.1 x a) (Ne.symm hqa)
      have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hp_pos hq_pos)
      have hmul := mul_le_mul_of_nonneg_left hlog hp_pos.le
      field_simp [hpa, hqa] at hmul
      exact hmul
  change 0 ≤ ∑ a, if p x a = 0 then 0
    else p x a * Real.log (p x a / q x a)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun a _ ↦ hterm a
  rw [Finset.sum_sub_distrib, hp.2 x, hq.2 x] at hsum
  norm_num at hsum
  exact hsum

lemma learnerPolicyOnSample_valid
    {d n : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜)
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hL : IsMeasurableLearner E L)
    (sample : LoggedSample n 𝒳 𝒜) :
    IsPolicy (learnerPolicyOnSample E L sample) ∧
      PolicySupportedOn (learnerPolicyOnSample E L sample) E.reference := by
  by_cases hs : BoundedLoggedSample sample
  · simpa [learnerPolicyOnSample, hs] using hL.2 sample hs
  · simp [learnerPolicyOnSample, hs, E.reference_isPolicy,
      PolicySupportedOn]

lemma measurableSet_boundedLoggedSample
    {n : ℕ} {𝒳 𝒜 : Type*}
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜] :
    MeasurableSet
      {sample : LoggedSample n 𝒳 𝒜 | BoundedLoggedSample sample} := by
  have hreward :
      Measurable (fun z : BanditObservation 𝒳 𝒜 => z.reward) := by
    change Measurable[MeasurableSpace.comap
      (fun z : BanditObservation 𝒳 𝒜 =>
        (z.context, z.action, z.reward)) inferInstance] _
    exact (comap_measurable _).snd.snd
  rw [show {sample : LoggedSample n 𝒳 𝒜 | BoundedLoggedSample sample} =
      ⋂ i : Fin n, {sample | (sample i).reward ∈ Set.Icc (0 : ℝ) 1} by
    ext sample
    simp [BoundedLoggedSample]]
  exact MeasurableSet.iInter fun i ↦
    (hreward.comp (measurable_pi_apply i)) measurableSet_Icc

lemma learnerRisk_nonneg
    {d n : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (C D : ℝ) (hP : ExactShell E P C D)
    (L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hL : IsMeasurableLearner E L) :
    0 ≤ learnerRisk E P n L := by
  apply integral_nonneg_of_ae
  filter_upwards with sample
  change 0 ≤ regularizedWelfare E P (gibbsPolicy E P) -
    regularizedWelfare E P (learnerPolicyOnSample E L sample)
  obtain ⟨hpol, hsupp⟩ := learnerPolicyOnSample_valid E L hL sample
  rw [gibbs_regret_identity E P C D hP
    (learnerPolicyOnSample E L sample) hpol
    (fun x a hp ↦ by
      by_contra href
      exact hp (hsupp x a href))]
  exact mul_nonneg (inv_nonneg.2 E.eta_pos.le)
    (Finset.sum_nonneg fun x _ ↦
      mul_nonneg ENNReal.toReal_nonneg
        (policyKL_nonneg_of_isPolicy
          (learnerPolicyOnSample E L sample) (gibbsPolicy E P)
          hpol (gibbsPolicy_isPolicy E P)
          (fun x a hq ↦ by
            apply hsupp x a
            by_contra href
            have hrefpos : 0 < E.reference x a :=
              lt_of_le_of_ne (E.reference_isPolicy.1 x a) (Ne.symm href)
            have hgpos : 0 < gibbsPolicy E P x a := by
              exact div_pos
                (mul_pos hrefpos (Real.exp_pos _))
                (gibbsNormalizer_pos E P x)
            linarith)
          x))

lemma common_gibbs_minimaxRisk_zero
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (C D : ℝ)
    (piDagger : Policy 𝒳 𝒜)
    (hpi : IsPolicy piDagger)
    (hsupp : PolicySupportedOn piDagger E.reference)
    (hmodel : (exactShellSet E C D).Nonempty)
    (hcommon : ∀ P ∈ exactShellSet E C D,
      gibbsPolicy E P = piDagger) :
    ∀ n, minimaxRisk E n (exactShellSet E C D) = 0 := by
  intro n
  classical
  let L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜) :=
    fun _ _ => piDagger
  have htotal (sample : LoggedSample n 𝒳 𝒜)
      (hs : BoundedLoggedSample sample) :
      learnerPolicyOnSample E L sample = piDagger := by
    funext x a
    simp [learnerPolicyOnSample, L, hs]
  have hL : IsMeasurableLearner E L := by
    constructor
    · intro x a
      rw [show (fun sample =>
          learnerPolicyOnSample E L sample x a) =
          fun sample => if BoundedLoggedSample sample
            then piDagger x a else E.reference x a by
        funext sample
        by_cases hs : BoundedLoggedSample sample <;>
          simp [learnerPolicyOnSample, L, hs]]
      exact Measurable.ite measurableSet_boundedLoggedSample
        measurable_const measurable_const
    · intro sample hs
      exact ⟨hpi, hsupp⟩
  have hrisk_zero :
      ∀ P ∈ exactShellSet E C D, learnerRisk E P n L = 0 := by
    intro P hP
    simp only [learnerRisk]
    calc
      (∫ sample,
          (regularizedWelfare E P (gibbsPolicy E P) -
            regularizedWelfare E P
              (learnerPolicyOnSample E L sample)) ∂productLaw E P n) =
          ∫ _sample, (0 : ℝ) ∂productLaw E P n := by
            apply integral_congr_ae
            filter_upwards [productLaw_bounded_sample E P n] with sample hs
            rw [htotal sample hs, hcommon P hP]
            ring
      _ = 0 := by simp
  apply le_antisymm
  · unfold minimaxRisk
    have hbdd : BddBelow
        {r : ℝ | ∃ L : Learner n (𝒳 := 𝒳) (𝒜 := 𝒜),
          IsMeasurableLearner E L ∧
          r = sSup {q : ℝ | ∃ P : BanditLaw E,
            P ∈ exactShellSet E C D ∧ q = learnerRisk E P n L}} := by
      refine ⟨0, ?_⟩
      rintro r ⟨L', hL', rfl⟩
      apply Real.sSup_nonneg
      rintro q ⟨P, hP, rfl⟩
      exact learnerRisk_nonneg E P C D hP L' hL'
    apply csInf_le hbdd
    refine ⟨L, hL, ?_⟩
    have hset :
        {q : ℝ | ∃ P : BanditLaw E,
          P ∈ exactShellSet E C D ∧ q = learnerRisk E P n L} = {0} := by
      ext q
      constructor
      · rintro ⟨P, hP, rfl⟩
        simp [hrisk_zero P hP]
      · intro hq
        have hq0 : q = 0 := by simpa using hq
        rcases hmodel with ⟨P, hP⟩
        exact ⟨P, hP, hq0.trans (hrisk_zero P hP).symm⟩
    rw [hset]
    simp
  · unfold minimaxRisk
    apply Real.sInf_nonneg
    rintro r ⟨L', hL', rfl⟩
    apply Real.sSup_nonneg
    rintro q ⟨P, hP, rfl⟩
    exact learnerRisk_nonneg E P C D hP L' hL'

lemma zero_minimax_sampleComplexityPositive_one
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (C D : ℝ)
    (hmodel : (exactShellSet E C D).Nonempty)
    (hzero : ∀ n, minimaxRisk E n (exactShellSet E C D) = 0)
    (eps : ℝ) (heps : 0 < eps) :
    sampleComplexityPositive E eps C D heps = 1 := by
  rw [sampleComplexityPositive, if_pos hmodel]
  apply le_antisymm
  · apply csInf_le
    · exact ⟨1, by
        rintro m ⟨n, hn, rfl, _⟩
        exact_mod_cast hn⟩
    · exact ⟨1, by omega, rfl, by rw [hzero 1]; exact heps.le⟩
  · apply le_csInf
    · exact ⟨(1 : WithTop ℕ),
        ⟨1, by omega, rfl, by rw [hzero 1]; exact heps.le⟩⟩
    · rintro m ⟨n, hn, rfl, _⟩
      exact_mod_cast hn
end

end CausalSmith.Stat.ReverseKLTwoCoverage

