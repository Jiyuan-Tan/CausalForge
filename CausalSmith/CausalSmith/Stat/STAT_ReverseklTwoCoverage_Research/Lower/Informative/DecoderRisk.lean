import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.PolicyBridge
import Causalean.Stat.Minimax.Assouad

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def informativeMidpoint (eta D gamma : ℝ) : ℝ :=
  (informativeLogistic eta (informativeBeta eta D + gamma) +
    informativeLogistic eta (informativeBeta eta D - gamma)) / 2

noncomputable def informativeDecoder
    {d n : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (L : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2))
    (sample : LoggedSample n (Fin (d + 1)) (Fin 2))
    (j : Fin (d - 1)) : Bool :=
  decide (informativeMidpoint eta D gamma ≤
    learnerPolicyOnSample
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp) L sample
      (informativeCoordinate hd j).succ 1)

lemma informativeDecoder_measurable
    {d n : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (L : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2))
    (hL : IsMeasurableLearner
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp) L) :
    ∀ j b, MeasurableSet
      {sample | informativeDecoder hd eta C D gamma heta hD hDC hCexp
        L sample j = b} := by
  intro j b
  have hm : Measurable (fun sample =>
      learnerPolicyOnSample
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp) L sample
        (informativeCoordinate hd j).succ 1) :=
    hL.1 _ _
  cases b
  · have hset :
        {sample | informativeDecoder hd eta C D gamma heta hD hDC hCexp
            L sample j = false} =
          {sample | ¬ informativeMidpoint eta D gamma ≤
            learnerPolicyOnSample
              (informativeExperiment d hd eta C D heta
                (lt_of_lt_of_le hD hDC) hCexp) L sample
              (informativeCoordinate hd j).succ 1} := by
        ext sample
        simp [informativeDecoder]
    rw [hset]
    exact (measurableSet_Ici.preimage hm).compl
  · have hset :
        {sample | informativeDecoder hd eta C D gamma heta hD hDC hCexp
            L sample j = true} =
          {sample | informativeMidpoint eta D gamma ≤
            learnerPolicyOnSample
              (informativeExperiment d hd eta C D heta
                (lt_of_lt_of_le hD hDC) hCexp) L sample
              (informativeCoordinate hd j).succ 1} := by
        ext sample
        simp [informativeDecoder]
    rw [hset]
    exact measurableSet_Ici.preimage hm

lemma informativeDecoder_error_policyKL
    {d n : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (L : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2))
    (hL : IsMeasurableLearner
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp) L)
    (sample : LoggedSample n (Fin (d + 1)) (Fin 2))
    (j : Fin (d - 1))
    (herr : informativeDecoder hd eta C D gamma heta hD hDC hCexp
      L sample j ≠ v j) :
    (eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2 ≤
      policyKL
        (learnerPolicyOnSample
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp) L sample)
        (gibbsPolicy
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp)
          (informativeLaw d hd eta C D gamma heta hD hDC hCexp
            v hgamma0 hgamma))
        (informativeCoordinate hd j).succ := by
  let E := informativeExperiment d hd eta C D heta
    (lt_of_lt_of_le hD hDC) hCexp
  let P := informativeLaw d hd eta C D gamma heta hD hDC hCexp
    v hgamma0 hgamma
  let p := learnerPolicyOnSample E L sample
  let q := gibbsPolicy E P
  obtain ⟨hp, _⟩ := learnerPolicyOnSample_valid E L hL sample
  have hq := gibbsPolicy_isPolicy E P
  have hqpos : ∀ x a, 0 < q x a := by
    intro x a
    dsimp [q]
    exact div_pos
      (mul_pos
        (informativeExperiment_reference_pos d hd eta C D
          heta hD hDC hCexp x a)
        (Real.exp_pos _))
      (gibbsNormalizer_pos E P x)
  have hKL := policyKL_ge_half_sq_action p q hp hq hqpos
    (informativeCoordinate hd j).succ 1
  have hsep := informativeLogistic_gap heta hD
    (lt_of_le_of_lt hDC hCexp) hgamma0 hgamma
  have hsep2 :
      2 * (eta * gamma / (1 + Real.exp eta) ^ 2) ≤
        informativeLogistic eta (informativeBeta eta D + gamma) -
          informativeLogistic eta (informativeBeta eta D - gamma) := by
    convert hsep using 1 <;> ring
  have hqrow := informativeLaw_gibbs_plus d hd eta C D gamma
    heta hD hDC hCexp v hgamma0 hgamma j
  change (eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2 ≤
    policyKL p q (informativeCoordinate hd j).succ
  apply le_trans ?_ hKL
  rw [show q (informativeCoordinate hd j).succ 1 =
      informativeLogistic eta
        (informativeBeta eta D + gamma * informativeSign (v j)) by
    exact hqrow]
  have hk0 : 0 ≤ eta * gamma / (1 + Real.exp eta) ^ 2 := by positivity
  cases hv : v j
  · have hdecode :
        informativeMidpoint eta D gamma ≤
          p (informativeCoordinate hd j).succ 1 := by
      simpa [informativeDecoder, hv, E, p] using herr
    have hgap :
        eta * gamma / (1 + Real.exp eta) ^ 2 ≤
          p (informativeCoordinate hd j).succ 1 -
            informativeLogistic eta (informativeBeta eta D - gamma) := by
      unfold informativeMidpoint at hdecode
      nlinarith [hsep2]
    have hsquare :
        (eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2 ≤
        (p (informativeCoordinate hd j).succ 1 -
          informativeLogistic eta (informativeBeta eta D - gamma)) ^ 2 / 2
        := by
      nlinarith [sq_nonneg
        ((p (informativeCoordinate hd j).succ 1 -
          informativeLogistic eta (informativeBeta eta D - gamma)) -
            eta * gamma / (1 + Real.exp eta) ^ 2)]
    simpa [informativeSign] using hsquare
  · have hdecode :
        p (informativeCoordinate hd j).succ 1 <
          informativeMidpoint eta D gamma := by
      simpa [informativeDecoder, hv, E, p] using herr
    have hgap :
        eta * gamma / (1 + Real.exp eta) ^ 2 ≤
          informativeLogistic eta (informativeBeta eta D + gamma) -
            p (informativeCoordinate hd j).succ 1 := by
      unfold informativeMidpoint at hdecode
      nlinarith [hsep2]
    have hsquare :
        (eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2 ≤
        (p (informativeCoordinate hd j).succ 1 -
          informativeLogistic eta (informativeBeta eta D + gamma)) ^ 2 / 2
        := by
      nlinarith [sq_nonneg
        ((informativeLogistic eta (informativeBeta eta D + gamma) -
          p (informativeCoordinate hd j).succ 1) -
            eta * gamma / (1 + Real.exp eta) ^ 2)]
    simpa [informativeSign] using hsquare

def informativeContext {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (d - 1)) : Fin (d + 1) :=
  (informativeCoordinate hd j).succ

lemma informativeContext_injective {d : ℕ} (hd : 4 ≤ d) :
    Function.Injective (informativeContext hd) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simp [informativeContext, informativeCoordinate] at this
  omega

lemma informativeLaw_contextMass_context
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (j : Fin (d - 1)) :
    contextMass
        (informativeLaw d hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgamma)
        (informativeContext hd j) =
      1 / informativeTotal d eta C D := by
  rw [informativeLaw, ibBernoulliLaw_contextMass]
  simp [informativeContext, informativeRho]

lemma informative_pointwise_regret_ge_decode
    {d n : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (L : Learner n (𝒳 := Fin (d + 1)) (𝒜 := Fin 2))
    (hL : IsMeasurableLearner
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp) L)
    (sample : LoggedSample n (Fin (d + 1)) (Fin 2)) :
    eta⁻¹ * (1 / informativeTotal d eta C D) *
        ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
        (∑ j : Fin (d - 1),
          if informativeDecoder hd eta C D gamma heta hD hDC hCexp
              L sample j ≠ v j then (1 : ℝ) else 0) ≤
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
              (lt_of_lt_of_le hD hDC) hCexp) L sample) := by
  let E := informativeExperiment d hd eta C D heta
    (lt_of_lt_of_le hD hDC) hCexp
  let P := informativeLaw d hd eta C D gamma heta hD hDC hCexp
    v hgamma0 hgamma
  let p := learnerPolicyOnSample E L sample
  let q := gibbsPolicy E P
  obtain ⟨hp, hsupp⟩ := learnerPolicyOnSample_valid E L hL sample
  have hq := gibbsPolicy_isPolicy E P
  have hqpos : ∀ x a, 0 < q x a := by
    intro x a
    exact div_pos
      (mul_pos
        (informativeExperiment_reference_pos d hd eta C D
          heta hD hDC hCexp x a)
        (Real.exp_pos _))
      (gibbsNormalizer_pos E P x)
  have hkl0 : ∀ x, 0 ≤ policyKL p q x :=
    fun x => policyKL_nonneg_of_isPolicy p q hp hq
      (fun x a hzero => False.elim ((hqpos x a).ne' hzero)) x
  have hloss0 : ∀ x, 0 ≤ contextMass P x * policyKL p q x :=
    fun x => mul_nonneg ENNReal.toReal_nonneg (hkl0 x)
  have hinj : Set.InjOn (informativeContext hd)
      (Finset.univ : Finset (Fin (d - 1))) :=
    fun _ _ _ _ hij => informativeContext_injective hd hij
  have himage :
      (∑ j : Fin (d - 1),
          contextMass P (informativeContext hd j) *
            policyKL p q (informativeContext hd j)) ≤
        ∑ x, contextMass P x * policyKL p q x := by
    calc
      (∑ j : Fin (d - 1),
          contextMass P (informativeContext hd j) *
            policyKL p q (informativeContext hd j)) =
          ∑ x ∈ Finset.image (informativeContext hd)
              (Finset.univ : Finset (Fin (d - 1))),
            contextMass P x * policyKL p q x := by
              symm
              exact Finset.sum_image hinj
      _ ≤ ∑ x, contextMass P x * policyKL p q x :=
        Finset.sum_le_univ_sum_of_nonneg hloss0
  have hbits :
      (∑ j : Fin (d - 1),
          (1 / informativeTotal d eta C D) *
            ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
            (if informativeDecoder hd eta C D gamma heta hD hDC hCexp
                L sample j ≠ v j then (1 : ℝ) else 0)) ≤
        ∑ j : Fin (d - 1),
          contextMass P (informativeContext hd j) *
            policyKL p q (informativeContext hd j) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases herr : informativeDecoder hd eta C D gamma heta hD hDC hCexp
        L sample j ≠ v j
    · rw [if_pos herr]
      simp only [mul_one]
      rw [show contextMass P (informativeContext hd j) =
          1 / informativeTotal d eta C D by
        exact informativeLaw_contextMass_context hd eta C D gamma
          heta hD hDC hCexp v hgamma0 hgamma j]
      exact mul_le_mul_of_nonneg_left
        (informativeDecoder_error_policyKL hd eta C D gamma heta hD hDC
          hCexp v hgamma0 hgamma L hL sample j herr)
        (div_nonneg zero_le_one
          (informativeTotal_pos hd heta hD hDC hCexp).le)
    · rw [if_neg herr]
      simp
      exact hloss0 (informativeContext hd j)
  have hselected :
      (1 / informativeTotal d eta C D) *
          ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
          (∑ j : Fin (d - 1),
            if informativeDecoder hd eta C D gamma heta hD hDC hCexp
                L sample j ≠ v j then (1 : ℝ) else 0) ≤
        ∑ x, contextMass P x * policyKL p q x := by
    calc
      (1 / informativeTotal d eta C D) *
          ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
          (∑ j : Fin (d - 1),
            if informativeDecoder hd eta C D gamma heta hD hDC hCexp
                L sample j ≠ v j then (1 : ℝ) else 0) =
          ∑ j : Fin (d - 1),
            (1 / informativeTotal d eta C D) *
              ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
              (if informativeDecoder hd eta C D gamma heta hD hDC hCexp
                  L sample j ≠ v j then (1 : ℝ) else 0) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ j : Fin (d - 1),
          contextMass P (informativeContext hd j) *
            policyKL p q (informativeContext hd j) := hbits
      _ ≤ ∑ x, contextMass P x * policyKL p q x := himage
  rw [gibbs_regret_identity E P C D
    (informativeLaw_exactShell d hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hgamma)
    p hp
    (fun x a hp0 => by
      by_contra href
      exact hp0 (hsupp x a href))]
  change
    eta⁻¹ * (1 / informativeTotal d eta C D) *
        ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
        (∑ j : Fin (d - 1),
          if informativeDecoder hd eta C D gamma heta hD hDC hCexp
              L sample j ≠ v j then (1 : ℝ) else 0) ≤
      eta⁻¹ * ∑ x, contextMass P x * policyKL p q x
  calc
    eta⁻¹ * (1 / informativeTotal d eta C D) *
        ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
        (∑ j : Fin (d - 1),
          if informativeDecoder hd eta C D gamma heta hD hDC hCexp
              L sample j ≠ v j then (1 : ℝ) else 0) =
      eta⁻¹ * ((1 / informativeTotal d eta C D) *
        ((eta * gamma / (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
        (∑ j : Fin (d - 1),
          if informativeDecoder hd eta C D gamma heta hD hDC hCexp
              L sample j ≠ v j then (1 : ℝ) else 0)) := by ring
    _ ≤ eta⁻¹ * ∑ x, contextMass P x * policyKL p q x :=
      mul_le_mul_of_nonneg_left hselected (inv_nonneg.mpr heta.le)

end

end CausalSmith.Stat.ReverseKLTwoCoverage
