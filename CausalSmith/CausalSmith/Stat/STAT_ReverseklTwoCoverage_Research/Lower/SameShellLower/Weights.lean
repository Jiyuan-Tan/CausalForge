import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Geometry

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

lemma hard_anchor_normalizer {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (x : Fin (if C > D then 1 else 0)) :
    candidateNormalizer
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardTheta hd D eta gamma v)
      (hardContextEquiv d C D
        (Sum.inr (Sum.inr (Sum.inl x)))) = Real.exp eta := by
  unfold candidateNormalizer
  simp only [hardExperiment, Equiv.symm_apply_apply, Fin.sum_univ_succ]
  rw [hard_score_on_context hd v, hard_score_on_context hd v,
    hard_score_on_context hd v]
  norm_num [hardReferenceOnContext]
  ring

lemma hard_residual_normalizer {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (x : Fin (if Even d then 1 else 0)) :
    candidateNormalizer
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardTheta hd D eta gamma v)
      (hardContextEquiv d C D
        (Sum.inr (Sum.inr (Sum.inr x)))) = 1 := by
  unfold candidateNormalizer
  simp only [hardExperiment, Equiv.symm_apply_apply, Fin.sum_univ_succ]
  rw [hard_score_on_context hd v, hard_score_on_context hd v,
    hard_score_on_context hd v]
  norm_num [hardReferenceOnContext]
  rfl

lemma hard_calibration_candidateWeight_plus {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool) :
    candidateWeight
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardTheta hd D eta gamma v)
      (hardContextEquiv d C D hardContextCalibration) hardPlus = C := by
  rw [candidateWeight, hard_calibration_normalizer hd heta hD hDC hCexp v]
  simp only [hardExperiment, Equiv.symm_apply_apply]
  rw [hard_score_on_context hd v]
  simp [hardContextCalibration, hardPlus]

lemma hard_constant_candidateWeight_anchor {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (x : Fin (if C > D then 1 else 0)) (a : Fin 3) :
    candidateWeight
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardTheta hd D eta gamma v)
      (hardContextEquiv d C D
        (Sum.inr (Sum.inr (Sum.inl x)))) a = 1 := by
  rw [candidateWeight, hard_anchor_normalizer hd heta hD hDC hCexp v x]
  simp only [hardExperiment, Equiv.symm_apply_apply]
  rw [hard_score_on_context hd v]
  simp

lemma hard_constant_candidateWeight_residual {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (x : Fin (if Even d then 1 else 0)) (a : Fin 3) :
    candidateWeight
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardTheta hd D eta gamma v)
      (hardContextEquiv d C D
        (Sum.inr (Sum.inr (Sum.inr x)))) a = 1 := by
  rw [candidateWeight, hard_residual_normalizer hd heta hD hDC hCexp v x]
  simp only [hardExperiment, Equiv.symm_apply_apply]
  rw [hard_score_on_context hd v]
  simp

lemma hard_hardNormalizer_pos {D eta gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma)) :
    0 < 1 - 2 * hardP D +
      2 * hardP D * hardT D eta gamma * Real.cosh (eta * gamma) := by
  have hbal := hardT_balance hden
  have hleft : 0 < hardT D eta gamma * Real.exp (eta * gamma) :=
    mul_pos (hardT_pos_of_admissible hD hden) (Real.exp_pos _)
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  nlinarith

lemma hard_high_ratio_eq_D {D eta gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma)) :
    Real.exp (eta * (hardBeta D eta gamma + gamma)) /
        (1 - 2 * hardP D +
          2 * hardP D * hardT D eta gamma * Real.cosh (eta * gamma)) = D := by
  have hZ := hard_hardNormalizer_pos heta hD hden
  rw [div_eq_iff hZ.ne']
  rw [mul_comm]
  rw [← hardT_balance hden]
  rw [show (hardBeta D eta gamma + gamma) * eta =
      eta * hardBeta D eta gamma + eta * gamma by ring,
    Real.exp_add, hard_exp_beta heta hD hden]

lemma hard_low_ratio_le_D {D eta gamma : ℝ}
    (hgamma : 0 ≤ gamma) (heta : 0 < eta) (hD : 1 < D)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma)) :
    Real.exp (eta * (hardBeta D eta gamma - gamma)) /
        (1 - 2 * hardP D +
          2 * hardP D * hardT D eta gamma * Real.cosh (eta * gamma)) ≤ D := by
  have hZ := hard_hardNormalizer_pos heta hD hden
  apply (div_le_iff₀ hZ).2
  rw [show eta * (hardBeta D eta gamma - gamma) =
      eta * hardBeta D eta gamma + -(eta * gamma) by ring,
    Real.exp_add, hard_exp_beta heta hD hden]
  simpa [mul_comm] using
    hardT_exp_neg_le_balance hgamma heta
      (hardT_pos_of_admissible hD hden).le hden

lemma hard_zero_ratio_le_D {D eta gamma : ℝ}
    (hgamma : 0 ≤ gamma) (heta : 0 < eta) (hD : 1 < D)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hgammaBeta : gamma ≤ hardBeta D eta gamma) :
    1 /
        (1 - 2 * hardP D +
          2 * hardP D * hardT D eta gamma * Real.cosh (eta * gamma)) ≤ D := by
  have hZ := hard_hardNormalizer_pos heta hD hden
  apply (div_le_iff₀ hZ).2
  have hlow :
      1 ≤ hardT D eta gamma * Real.exp (-(eta * gamma)) := by
    rw [← hard_exp_beta heta hD hden, ← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbalance :
      hardT D eta gamma * Real.exp (-(eta * gamma)) ≤
        D * (1 - 2 * hardP D +
          2 * hardP D * hardT D eta gamma * Real.cosh (eta * gamma)) := by
    simpa only [show -eta * gamma = -(eta * gamma) by ring] using
      hardT_exp_neg_le_balance hgamma heta
        (hardT_pos_of_admissible hD hden).le hden
  exact hlow.trans hbalance

lemma hard_hard_candidateWeight_le {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hgamma : 0 ≤ gamma)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    ∀ a,
      candidateWeight
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardTheta hd D eta gamma v)
        (hardContextEquiv d C D (hardContextHard j)) a ≤ D := by
  intro a
  rw [candidateWeight,
    hard_hard_normalizer hd heta hD hDC hCexp hden v j]
  simp only [hardExperiment, Equiv.symm_apply_apply]
  rw [hard_score_on_context hd v]
  cases hv : v j <;> fin_cases a
  · simpa [hardContextHard, hardPlus, hardMinus, hv] using
      hard_low_ratio_le_D hgamma heta hD hden
  · simpa [hardContextHard, hardPlus, hardMinus, hv] using
      hard_high_ratio_eq_D heta hD hden |>.le
  · simpa [hardContextHard, hardPlus, hardMinus, hv] using
      hard_zero_ratio_le_D hgamma heta hD hden hgammaBeta
  · simpa [hardContextHard, hardPlus, hardMinus, hv] using
      hard_high_ratio_eq_D heta hD hden |>.le
  · simpa [hardContextHard, hardPlus, hardMinus, hv] using
      hard_low_ratio_le_D hgamma heta hD hden
  · simpa [hardContextHard, hardPlus, hardMinus, hv] using
      hard_zero_ratio_le_D hgamma heta hD hden hgammaBeta

lemma hard_hard_candidateWeight_high {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    candidateWeight
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardTheta hd D eta gamma v)
        (hardContextEquiv d C D (hardContextHard j))
        (if v j then hardPlus else hardMinus) = D := by
  rw [candidateWeight,
    hard_hard_normalizer hd heta hD hDC hCexp hden v j]
  simp only [hardExperiment, Equiv.symm_apply_apply]
  rw [hard_score_on_context hd v]
  cases hv : v j <;>
    simpa [hardContextHard, hardPlus, hardMinus, hv] using
      hard_high_ratio_eq_D heta hD hden

lemma hard_certificate_bound {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hgamma : 0 ≤ gamma)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (v : Fin (hardCoordinateCount d) → Bool) :
    ∀ x a, 0 <
        (hardExperiment d hd eta C D heta hD hDC hCexp).reference x a →
      Real.exp
          ((hardExperiment d hd eta C D heta hD hDC hCexp).eta *
            ∑ i,
              (hardExperiment d hd eta C D heta hD hDC hCexp).feature
                x a i * hardTheta hd D eta gamma v i) ≤
        C * candidateNormalizer
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardTheta hd D eta gamma v) x := by
  intro x a _
  let y := (hardContextEquiv d C D).symm x
  change Real.exp (eta *
      ∑ i, hardFeatureOnContext hd y a i *
        hardTheta hd D eta gamma v i) ≤
    C * candidateNormalizer
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardTheta hd D eta gamma v) x
  have hx : x = hardContextEquiv d C D y := by
    exact (hardContextEquiv d C D).apply_symm_apply x |>.symm
  rw [hx]
  rcases y with j | (hcal | (hanchor | hz))
  · have hweight :=
      hard_hard_candidateWeight_le hd heta hD hDC hCexp hgamma hden
        hgammaBeta v j a
    have hnorm := hard_hardNormalizer_pos heta hD hden
    unfold candidateWeight at hweight
    rw [hard_hard_normalizer hd heta hD hDC hCexp hden v j] at hweight
    rw [hard_score_on_context hd v]
    rw [show candidateNormalizer
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardTheta hd D eta gamma v)
          (hardContextEquiv d C D (Sum.inl j)) =
        1 - 2 * hardP D +
          2 * hardP D * hardT D eta gamma *
            Real.cosh (eta * gamma) by
      simpa [hardContextHard] using
        hard_hard_normalizer hd heta hD hDC hCexp hden v j]
    have hnum :
        Real.exp
            (eta * (if a = hardPlus then
              hardBeta D eta gamma + gamma * (if v j then 1 else -1)
            else if a = hardMinus then
              hardBeta D eta gamma - gamma * (if v j then 1 else -1)
            else 0)) ≤
          D * (1 - 2 * hardP D +
            2 * hardP D * hardT D eta gamma *
              Real.cosh (eta * gamma)) := by
      have hweight' :
          Real.exp
              (eta * (if a = hardPlus then
                hardBeta D eta gamma + gamma * (if v j then 1 else -1)
              else if a = hardMinus then
                hardBeta D eta gamma - gamma * (if v j then 1 else -1)
              else 0)) /
              (1 - 2 * hardP D +
                2 * hardP D * hardT D eta gamma *
                  Real.cosh (eta * gamma)) ≤ D := by
        simpa [candidateWeight, hardContextHard, hardExperiment,
          hard_score_on_context] using hweight
      exact (div_le_iff₀ hnorm).1 hweight'
    exact hnum.trans
      (mul_le_mul_of_nonneg_right hDC hnorm.le)
  · have hcal0 : hcal = 0 := Subsingleton.elim _ _
    subst hcal
    rw [hard_score_on_context hd v]
    rw [show candidateNormalizer
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardTheta hd D eta gamma v)
          (hardContextEquiv d C D (Sum.inr (Sum.inl 0))) =
        Real.exp eta / C by
      simpa [hardContextCalibration] using
        hard_calibration_normalizer hd heta hD hDC hCexp v]
    have hC0 : 0 < C := lt_trans zero_lt_one (lt_of_lt_of_le hD hDC)
    have hcancel : C * (Real.exp eta / C) = Real.exp eta := by
      field_simp
    rw [hcancel]
    by_cases ha : a = hardPlus
    · simp [ha]
    · simp [ha]
      exact heta.le
  · rw [hard_score_on_context hd v,
      hard_anchor_normalizer hd heta hD hDC hCexp v hanchor]
    have hC1 : 1 ≤ C := (lt_of_lt_of_le hD hDC).le
    simp only [mul_one]
    exact le_mul_of_one_le_left (Real.exp_pos eta).le hC1
  · rw [hard_score_on_context hd v,
      hard_residual_normalizer hd heta hD hDC hCexp v hz]
    simpa using (lt_of_lt_of_le hD hDC).le

lemma hard_certificate_eq {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool) :
    Real.exp
        ((hardExperiment d hd eta C D heta hD hDC hCexp).eta *
          ∑ i,
            (hardExperiment d hd eta C D heta hD hDC hCexp).feature
              (hardContextEquiv d C D hardContextCalibration) hardPlus i *
              hardTheta hd D eta gamma v i) =
      C * candidateNormalizer
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardTheta hd D eta gamma v)
        (hardContextEquiv d C D hardContextCalibration) := by
  rw [hard_calibration_normalizer hd heta hD hDC hCexp v]
  simp only [hardExperiment, Equiv.symm_apply_apply]
  rw [hard_score_on_context hd v]
  simp [hardContextCalibration, hardPlus]
  field_simp [ne_of_gt (lt_trans zero_lt_one (lt_of_lt_of_le hD hDC))]

end

end CausalSmith.Stat.ReverseKLTwoCoverage
