import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Assouad

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

noncomputable def hardGibbsLow (eta gamma : ℝ) : ℝ :=
  (1 / 4) * Real.exp (-2 * eta * gamma)

noncomputable def hardGibbsMidpoint (eta gamma : ℝ) : ℝ :=
  ((1 / 4) + hardGibbsLow eta gamma) / 2

noncomputable def hardDecoder
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (L : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3))
    (sample : LoggedSample n (Fin (hardContextCard d C D)) (Fin 3))
    (j : Fin (hardCoordinateCount d)) : Bool :=
  decide (hardGibbsMidpoint eta gamma ≤
    learnerPolicyOnSample
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      L sample (hardContext C D j) hardPlus)

lemma hardDecoder_measurable
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (L : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3))
    (hL : IsMeasurableLearner
      (hardExperiment d hd eta C D heta hD hDC hCexp) L) :
    ∀ j b, MeasurableSet
      {sample | hardDecoder hd eta C D gamma heta hD hDC hCexp
        L sample j = b} := by
  intro j b
  have hm : Measurable (fun sample =>
      learnerPolicyOnSample
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        L sample (hardContext C D j) hardPlus) :=
    hL.1 _ _
  cases b
  · have hset :
        {sample | hardDecoder hd eta C D gamma heta hD hDC hCexp
            L sample j = false} =
          {sample | ¬ hardGibbsMidpoint eta gamma ≤
            learnerPolicyOnSample
              (hardExperiment d hd eta C D heta hD hDC hCexp)
              L sample (hardContext C D j) hardPlus} := by
        ext sample
        simp [hardDecoder]
    rw [hset]
    exact (measurableSet_Ici.preimage hm).compl
  · have hset :
        {sample | hardDecoder hd eta C D gamma heta hD hDC hCexp
            L sample j = true} =
          {sample | hardGibbsMidpoint eta gamma ≤
            learnerPolicyOnSample
              (hardExperiment d hd eta C D heta hD hDC hCexp)
              L sample (hardContext C D j) hardPlus} := by
        ext sample
        simp [hardDecoder]
    rw [hset]
    exact measurableSet_Ici.preimage hm

lemma hard_low_ratio_eq
    {D eta gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma)) :
    Real.exp (eta * (hardBeta D eta gamma - gamma)) /
        (1 - 2 * hardP D +
          2 * hardP D * hardT D eta gamma * Real.cosh (eta * gamma)) =
      D * Real.exp (-2 * eta * gamma) := by
  let Z :=
    1 - 2 * hardP D +
      2 * hardP D * hardT D eta gamma * Real.cosh (eta * gamma)
  have hZ : 0 < Z := hard_hardNormalizer_pos heta hD hden
  have hhigh := hard_high_ratio_eq_D heta hD hden
  change Real.exp (eta * (hardBeta D eta gamma - gamma)) / Z =
    D * Real.exp (-2 * eta * gamma)
  change Real.exp (eta * (hardBeta D eta gamma + gamma)) / Z = D at hhigh
  calc
    Real.exp (eta * (hardBeta D eta gamma - gamma)) / Z =
        (Real.exp (eta * (hardBeta D eta gamma + gamma)) / Z) *
          Real.exp (-2 * eta * gamma) := by
      field_simp [hZ.ne']
      rw [← Real.exp_add]
      congr 2
      ring
    _ = D * Real.exp (-2 * eta * gamma) := by rw [hhigh]

lemma hardLaw_gibbs_plus
    {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (j : Fin (hardCoordinateCount d)) :
    gibbsPolicy
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardLaw hd eta C D gamma heta hD hDC hCexp v
        hgamma0 hgammaBeta hgammaOne)
      (hardContext C D j) hardPlus =
        if v j then (1 / 4 : ℝ) else hardGibbsLow eta gamma := by
  rw [gibbsPolicy_eq_candidate]
  change hardReferenceOnContext
        ((hardContextEquiv d C D).symm (hardContext C D j)) hardPlus *
      candidateWeight
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardTheta hd D eta gamma v)
        (hardContext C D j) hardPlus = _
  simp only [hardContext, Equiv.symm_apply_apply, hardReferenceOnContext,
    hardPlus]
  cases hv : v j
  · simp only [Bool.false_eq_true, if_false, if_true]
    change hardP D *
      candidateWeight
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardTheta hd D eta gamma v)
        (hardContextEquiv d C D (hardContextHard j)) hardPlus =
      hardGibbsLow eta gamma
    rw [candidateWeight,
      hard_hard_normalizer hd heta hD hDC hCexp hden v j]
    simp only [hardExperiment, Equiv.symm_apply_apply]
    rw [hard_score_on_context hd v]
    simp only [hardContextHard, hardPlus, hardMinus, hv,
      Bool.false_eq_true, if_false, if_true, mul_neg, mul_one]
    change hardP D *
      (Real.exp (eta * (hardBeta D eta gamma - gamma)) /
        (1 - 2 * hardP D +
          2 * hardP D * hardT D eta gamma *
            Real.cosh (eta * gamma))) = _
    rw [hard_low_ratio_eq heta hD hden]
    unfold hardGibbsLow hardP
    field_simp [ne_of_gt (lt_trans zero_lt_one hD)]
  · simp only [if_true]
    change hardP D *
      candidateWeight
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardTheta hd D eta gamma v)
        (hardContextEquiv d C D (hardContextHard j)) hardPlus = 1 / 4
    have hh := hard_hard_candidateWeight_high hd heta hD hDC hCexp
      hden v j
    simp [hv] at hh
    rw [hh]
    unfold hardP
    field_simp [ne_of_gt (lt_trans zero_lt_one hD)]

lemma hardGibbs_gap_pos {eta gamma : ℝ}
    (heta : 0 < eta) (hgamma : 0 < gamma) :
    hardGibbsLow eta gamma < 1 / 4 := by
  unfold hardGibbsLow
  have he : Real.exp (-2 * eta * gamma) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith [mul_pos heta hgamma])
  nlinarith [Real.exp_pos (-2 * eta * gamma)]

lemma hardExperiment_reference_pos
    {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    ∀ x a, 0 <
      (hardExperiment d hd eta C D heta hD hDC hCexp).reference x a := by
  intro x a
  change 0 < hardReferenceOnContext (eta := eta)
    ((hardContextEquiv d C D).symm x) a
  rcases (hardContextEquiv d C D).symm x with j | (hcal | (hanchor | hz))
  · have hp := hardP_pos hD
    have hp4 := hardP_lt_quarter hD
    fin_cases a <;>
      simp [hardReferenceOnContext, hardPlus, hardMinus, hardZero] <;>
      nlinarith
  · have hq0 := hardQ_pos heta hD hDC hCexp
    have hq1 := hardQ_lt_one heta hD hDC
    fin_cases a
    · simpa [hardReferenceOnContext, hardPlus] using hq0
    · simpa [hardReferenceOnContext, hardPlus] using
        div_pos (sub_pos.mpr hq1) (by norm_num : (0 : ℝ) < 2)
    · simpa [hardReferenceOnContext, hardPlus] using
        div_pos (sub_pos.mpr hq1) (by norm_num : (0 : ℝ) < 2)
  · norm_num [hardReferenceOnContext]
  · norm_num [hardReferenceOnContext]

lemma hardDecoder_error_policyKL
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma : 0 < gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (L : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3))
    (hL : IsMeasurableLearner
      (hardExperiment d hd eta C D heta hD hDC hCexp) L)
    (sample : LoggedSample n (Fin (hardContextCard d C D)) (Fin 3))
    (j : Fin (hardCoordinateCount d))
    (herr : hardDecoder hd eta C D gamma heta hD hDC hCexp
      L sample j ≠ v j) :
    (((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2 ≤
      policyKL
        (learnerPolicyOnSample
          (hardExperiment d hd eta C D heta hD hDC hCexp) L sample)
        (gibbsPolicy
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardLaw hd eta C D gamma heta hD hDC hCexp v
            hgamma.le hgammaBeta hgammaOne))
        (hardContext C D j) := by
  let E := hardExperiment d hd eta C D heta hD hDC hCexp
  let P := hardLaw hd eta C D gamma heta hD hDC hCexp v
    hgamma.le hgammaBeta hgammaOne
  let p := learnerPolicyOnSample E L sample
  let q := gibbsPolicy E P
  obtain ⟨hp, _⟩ := learnerPolicyOnSample_valid E L hL sample
  have hq := gibbsPolicy_isPolicy E P
  have hqpos : ∀ x a, 0 < q x a := by
    intro x a
    dsimp [q, E]
    exact div_pos
      (mul_pos
        (hardExperiment_reference_pos hd heta hD hDC hCexp x a)
        (Real.exp_pos _))
      (gibbsNormalizer_pos E P x)
  have hKL := policyKL_ge_half_sq_action p q hp hq hqpos
    (hardContext C D j) hardPlus
  have hqrow := hardLaw_gibbs_plus hd eta C D gamma heta hD hDC
    hCexp v hgamma.le hgammaBeta hgammaOne hden j
  have hgap := hardGibbs_gap_pos heta hgamma
  change (((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2 ≤
    policyKL p q (hardContext C D j)
  apply le_trans ?_ hKL
  rw [show q (hardContext C D j) hardPlus =
      if v j then (1 / 4 : ℝ) else hardGibbsLow eta gamma by
    exact hqrow]
  cases hv : v j
  · have hdecode :
        hardGibbsMidpoint eta gamma ≤ p (hardContext C D j) hardPlus := by
      simpa [hardDecoder, hv, E, p] using herr
    simp only [hv, Bool.false_eq_true, if_false]
    unfold hardGibbsMidpoint at hdecode
    have hdist :
        ((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2 ≤
          p (hardContext C D j) hardPlus - hardGibbsLow eta gamma := by
      linarith
    nlinarith [sq_nonneg
      ((p (hardContext C D j) hardPlus - hardGibbsLow eta gamma) -
        ((1 / 4 - hardGibbsLow eta gamma) / 2))]
  · have hdecode :
        p (hardContext C D j) hardPlus <
          hardGibbsMidpoint eta gamma := by
      simpa [hardDecoder, hv, E, p] using herr
    simp only [hv, if_true]
    unfold hardGibbsMidpoint at hdecode
    have hdist :
        ((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2 ≤
          1 / 4 - p (hardContext C D j) hardPlus := by
      linarith
    nlinarith [sq_nonneg
      ((1 / 4 - p (hardContext C D j) hardPlus) -
        ((1 / 4 - hardGibbsLow eta gamma) / 2))]

end

end CausalSmith.Stat.ReverseKLTwoCoverage
