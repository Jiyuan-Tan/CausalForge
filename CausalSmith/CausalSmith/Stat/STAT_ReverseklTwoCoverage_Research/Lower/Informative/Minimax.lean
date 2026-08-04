import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.RiskLower

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

lemma gibbsPolicy_uniform_lower
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (hlin : ∀ x a, linearReward P x a ∈ Set.Icc (0 : ℝ) 1)
    (x : 𝒳) (a : 𝒜) :
    E.reference x a / Real.exp E.eta ≤ gibbsPolicy E P x a := by
  have hZpos := gibbsNormalizer_pos E P x
  have hZle : gibbsNormalizer E P x ≤ Real.exp E.eta := by
    unfold gibbsNormalizer
    calc
      (∑ b, E.reference x b * Real.exp (E.eta * linearReward P x b)) ≤
          ∑ b, E.reference x b * Real.exp E.eta := by
        apply Finset.sum_le_sum
        intro b _
        apply mul_le_mul_of_nonneg_left
        · exact Real.exp_le_exp.mpr (by
            nlinarith [E.eta_pos, (hlin x b).2])
        · exact E.reference_isPolicy.1 x b
      _ = Real.exp E.eta := by
        rw [← Finset.sum_mul, E.reference_isPolicy.2 x, one_mul]
  have hnum :
      E.reference x a ≤
        E.reference x a * Real.exp (E.eta * linearReward P x a) := by
    have he : 1 ≤ Real.exp (E.eta * linearReward P x a) := by
      rw [show (1 : ℝ) = Real.exp 0 by simp]
      exact Real.exp_le_exp.mpr
        (mul_nonneg E.eta_pos.le (hlin x a).1)
    nlinarith [E.reference_isPolicy.1 x a]
  unfold gibbsPolicy
  apply (le_div_iff₀ hZpos).2
  have href := E.reference_isPolicy.1 x a
  have hexp := Real.exp_pos E.eta
  have hleft :
      E.reference x a / Real.exp E.eta * gibbsNormalizer E P x ≤
        E.reference x a := by
    calc
      E.reference x a / Real.exp E.eta * gibbsNormalizer E P x ≤
          E.reference x a / Real.exp E.eta * Real.exp E.eta :=
        mul_le_mul_of_nonneg_left hZle (div_nonneg href hexp.le)
      _ = E.reference x a := by field_simp [hexp.ne']
  exact hleft.trans hnum

lemma policyKL_uniform_upper
    {𝒳 𝒜 : Type*} [Fintype 𝒜]
    (p q ref : Policy 𝒳 𝒜)
    (hp : IsPolicy p) (hq : IsPolicy q) (href : IsPolicy ref)
    (hrefpos : ∀ x a, 0 < ref x a)
    (eta : ℝ) (heta : 0 < eta)
    (hqlower : ∀ x a, ref x a / Real.exp eta ≤ q x a)
    (x : 𝒳) :
    policyKL p q x ≤ ∑ a, Real.log (Real.exp eta / ref x a) := by
  unfold policyKL
  apply Finset.sum_le_sum
  intro a _
  by_cases hpa : p x a = 0
  · simp [hpa]
    have hratio : 1 ≤ Real.exp eta / ref x a := by
      apply (le_div_iff₀ (hrefpos x a)).2
      have href1 : ref x a ≤ 1 := le_trans
        (Finset.single_le_sum (fun b _ => href.1 x b) (Finset.mem_univ a))
        (le_of_eq (href.2 x))
      have he1 : 1 ≤ Real.exp eta := Real.one_le_exp heta.le
      nlinarith
    exact Real.log_nonneg hratio
  · rw [if_neg hpa]
    have hp0 : 0 < p x a :=
      lt_of_le_of_ne (hp.1 x a) (Ne.symm hpa)
    have hp1 : p x a ≤ 1 := le_trans
      (Finset.single_le_sum (fun b _ => hp.1 x b) (Finset.mem_univ a))
      (le_of_eq (hp.2 x))
    have hq0 : 0 < q x a := lt_of_lt_of_le
      (div_pos (hrefpos x a) (Real.exp_pos eta)) (hqlower x a)
    have hratio_pos : 0 < Real.exp eta / ref x a :=
      div_pos (Real.exp_pos eta) (hrefpos x a)
    have hratio_one : 1 ≤ Real.exp eta / ref x a := by
      apply (le_div_iff₀ (hrefpos x a)).2
      have href1 : ref x a ≤ 1 := le_trans
        (Finset.single_le_sum (fun b _ => href.1 x b) (Finset.mem_univ a))
        (le_of_eq (href.2 x))
      have he1 : 1 ≤ Real.exp eta := Real.one_le_exp heta.le
      nlinarith
    have hdiv :
        p x a / q x a ≤ Real.exp eta / ref x a := by
      apply (div_le_iff₀ hq0).2
      have hqbound : ref x a ≤ q x a * Real.exp eta :=
        (div_le_iff₀ (Real.exp_pos eta)).1 (hqlower x a)
      have hpref : p x a * ref x a ≤ ref x a := by
        nlinarith [hrefpos x a]
      rw [show Real.exp eta / ref x a * q x a =
          (Real.exp eta * q x a) / ref x a by ring]
      apply (le_div_iff₀ (hrefpos x a)).2
      nlinarith
    have hlog :
        Real.log (p x a / q x a) ≤
          Real.log (Real.exp eta / ref x a) :=
      Real.strictMonoOn_log.monotoneOn
        (div_pos hp0 hq0) hratio_pos hdiv
    have hM0 : 0 ≤ Real.log (Real.exp eta / ref x a) :=
      Real.log_nonneg hratio_one
    calc
      p x a * Real.log (p x a / q x a) ≤
          p x a * Real.log (Real.exp eta / ref x a) :=
        mul_le_mul_of_nonneg_left hlog (hp.1 x a)
      _ ≤ Real.log (Real.exp eta / ref x a) := by
        nlinarith

lemma informative_learnerRisk_uniform_upper
    {d n : ℕ} (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (P : BanditLaw
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp))
    (hP : ExactShell
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp) P C D)
    (L : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2))
    (hL : IsMeasurableLearner
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp) L) :
    learnerRisk
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp) P n L ≤
      eta⁻¹ * ∑ x : Fin (d + 1), ∑ a : Fin 2,
        Real.log (Real.exp eta /
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp).reference x a) := by
  let E := informativeExperiment d hd eta C D heta
    (lt_of_lt_of_le hD hDC) hCexp
  let M := eta⁻¹ * ∑ x : Fin (d + 1), ∑ a : Fin 2,
    Real.log (Real.exp eta / E.reference x a)
  have hpoint (sample : LoggedSample n (Fin (d + 1)) (Fin 2)) :
      regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P (learnerPolicyOnSample E L sample) ≤ M := by
    obtain ⟨hp, hsupp⟩ := learnerPolicyOnSample_valid E L hL sample
    rw [gibbs_regret_identity E P C D hP
      (learnerPolicyOnSample E L sample) hp
      (fun x a hp0 => by
        by_contra href
        exact hp0 (hsupp x a href))]
    have hkl (x) :
        policyKL (learnerPolicyOnSample E L sample) (gibbsPolicy E P) x ≤
          ∑ a, Real.log (Real.exp eta / E.reference x a) := by
      exact policyKL_uniform_upper
        (learnerPolicyOnSample E L sample) (gibbsPolicy E P) E.reference
        hp (gibbsPolicy_isPolicy E P) E.reference_isPolicy
        (informativeExperiment_reference_pos d hd eta C D heta hD hDC hCexp)
        eta heta
        (gibbsPolicy_uniform_lower E P hP.linearRealizability.1) x
    have hrho1 (x) : contextMass P x ≤ 1 := by
      have hsum := certificate_contextMass_sum_one E P
      have hrho0 : ∀ y, 0 ≤ contextMass P y :=
        fun _ => ENNReal.toReal_nonneg
      have hsingle : contextMass P x ≤ ∑ y, contextMass P y :=
        Finset.single_le_sum (fun y _ => hrho0 y) (Finset.mem_univ x)
      rwa [hsum] at hsingle
    have hMrow0 (x) : 0 ≤ ∑ a, Real.log (Real.exp eta / E.reference x a) := by
      apply Finset.sum_nonneg
      intro a _
      have href1 : E.reference x a ≤ 1 := le_trans
        (Finset.single_le_sum (fun b _ => E.reference_isPolicy.1 x b)
          (Finset.mem_univ a)) (le_of_eq (E.reference_isPolicy.2 x))
      apply Real.log_nonneg
      apply (le_div_iff₀
        (informativeExperiment_reference_pos d hd eta C D heta hD hDC
          hCexp x a)).2
      nlinarith [Real.one_le_exp heta.le]
    have hsum :
        ∑ x, contextMass P x *
            policyKL (learnerPolicyOnSample E L sample) (gibbsPolicy E P) x ≤
          ∑ x, ∑ a, Real.log (Real.exp eta / E.reference x a) := by
      apply Finset.sum_le_sum
      intro x _
      calc
        contextMass P x *
            policyKL (learnerPolicyOnSample E L sample) (gibbsPolicy E P) x ≤
          contextMass P x *
            (∑ a, Real.log (Real.exp eta / E.reference x a)) :=
          mul_le_mul_of_nonneg_left (hkl x) ENNReal.toReal_nonneg
        _ ≤ ∑ a, Real.log (Real.exp eta / E.reference x a) := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (hrho1 x) (hMrow0 x)
    exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr heta.le)
  have hnonneg :
      ∀ sample, 0 ≤ regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P (learnerPolicyOnSample E L sample) := by
    intro sample
    obtain ⟨hp, hsupp⟩ := learnerPolicyOnSample_valid E L hL sample
    rw [gibbs_regret_identity E P C D hP
      (learnerPolicyOnSample E L sample) hp
      (fun x a hp0 => by
        by_contra href
        exact hp0 (hsupp x a href))]
    exact mul_nonneg (inv_nonneg.mpr heta.le)
      (Finset.sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg
        (policyKL_nonneg_of_isPolicy _ _ hp (gibbsPolicy_isPolicy E P)
          (fun _ _ hzero => False.elim
            ((div_pos
              (mul_pos
                (informativeExperiment_reference_pos d hd eta C D heta hD
                  hDC hCexp _ _) (Real.exp_pos _))
              (gibbsNormalizer_pos E P _)).ne' hzero)) x))
  unfold learnerRisk
  letI : IsProbabilityMeasure (productLaw E P n) := by
    unfold productLaw
    letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
    infer_instance
  have hconst : Integrable (fun _ : LoggedSample n (Fin (d + 1)) (Fin 2) => M)
      (productLaw E P n) := integrable_const M
  have hi := integral_mono_of_nonneg
    (Filter.Eventually.of_forall hnonneg) hconst
    (Filter.Eventually.of_forall hpoint)
  rw [integral_const, probReal_univ, one_smul] at hi
  simpa [M] using hi

lemma informative_minimaxRisk_lower
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (hbudget :
      (n : ℝ) *
        (4 * gamma ^ 2 / informativeTotal d eta C D *
          (1 / informativeBeta eta D +
            1 / (1 - informativeBeta eta D))) ≤ 1) :
    eta⁻¹ * (1 / informativeTotal d eta C D) *
          ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
          ((d - 1 : ℕ) : ℝ) / 8 ≤
      minimaxRisk
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp)
        n
        (exactShellSet
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp) C D) := by
  classical
  let E := informativeExperiment d hd eta C D heta
    (lt_of_lt_of_le hD hDC) hCexp
  let L0 : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2) :=
    fun _ _ => E.reference
  have hL0 : IsMeasurableLearner E L0 := by
    constructor
    · intro x a
      rw [show (fun sample => learnerPolicyOnSample E L0 sample x a) =
          fun _sample => E.reference x a by
        funext sample
        by_cases hs : BoundedLoggedSample sample <;>
          simp [learnerPolicyOnSample, L0, hs]]
      exact measurable_const
    · intro sample hs
      exact ⟨E.reference_isPolicy, fun _ _ h => h⟩
  unfold minimaxRisk
  apply le_csInf
  · exact ⟨_, L0, hL0, rfl⟩
  · rintro r ⟨L, hL, rfl⟩
    obtain ⟨v, hv⟩ :=
      informative_exists_learnerRisk_lower hd eta C D gamma heta hD hDC
        hCexp hgamma0 hgamma hbudget L hL
    let P := informativeLaw d hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hgamma
    have hP : P ∈ exactShellSet E C D :=
      informativeLaw_exactShell d hd eta C D gamma heta hD hDC hCexp
        v hgamma0 hgamma
    have hbdd : BddAbove
        {q : ℝ | ∃ P' : BanditLaw E, P' ∈ exactShellSet E C D ∧
          q = learnerRisk E P' n L} := by
      refine ⟨eta⁻¹ * ∑ x : Fin (d + 1), ∑ a : Fin 2,
        Real.log (Real.exp eta / E.reference x a), ?_⟩
      rintro q ⟨P', hP', rfl⟩
      exact informative_learnerRisk_uniform_upper hd eta C D heta hD hDC
        hCexp P' hP' L hL
    exact hv.trans (le_csSup hbdd ⟨P, hP, rfl⟩)

end

end CausalSmith.Stat.ReverseKLTwoCoverage
