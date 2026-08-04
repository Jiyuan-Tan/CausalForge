import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.ConstructionLaw

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

lemma hardT_pos_of_admissible {D eta gamma : ℝ}
    (hD : 1 < D)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma)) :
    0 < hardT D eta gamma := by
  have hp := hardP_lt_quarter hD
  unfold hardT
  apply div_pos
  · exact mul_pos (lt_trans zero_lt_one hD) (by nlinarith)
  · exact hden

lemma hard_exp_beta {D eta gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma)) :
    Real.exp (eta * hardBeta D eta gamma) = hardT D eta gamma := by
  have hT := hardT_pos_of_admissible hD hden
  unfold hardBeta
  rw [show eta * (eta⁻¹ * Real.log (hardT D eta gamma)) =
      Real.log (hardT D eta gamma) by field_simp]
  exact Real.exp_log hT

lemma hardT_balance {D eta gamma : ℝ}
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma)) :
    hardT D eta gamma * Real.exp (eta * gamma) =
      D * (1 - 2 * hardP D +
        2 * hardP D * hardT D eta gamma *
          Real.cosh (eta * gamma)) := by
  have hne : Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma) ≠ 0 := hden.ne'
  have hmul :
      hardT D eta gamma *
          (Real.exp (eta * gamma) -
            2 * hardP D * D * Real.cosh (eta * gamma)) =
        D * (1 - 2 * hardP D) := by
    rw [hardT]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_mul_cancel₀ (D * (1 - 2 * hardP D)) hne)
  calc
    hardT D eta gamma * Real.exp (eta * gamma) =
        hardT D eta gamma *
            (Real.exp (eta * gamma) -
              2 * hardP D * D * Real.cosh (eta * gamma)) +
          hardT D eta gamma *
            (2 * hardP D * D * Real.cosh (eta * gamma)) := by ring
    _ = D * (1 - 2 * hardP D) +
          hardT D eta gamma *
            (2 * hardP D * D * Real.cosh (eta * gamma)) := by rw [hmul]
    _ = D * (1 - 2 * hardP D +
        2 * hardP D * hardT D eta gamma *
          Real.cosh (eta * gamma)) := by ring

lemma hardT_exp_neg_le_balance {D eta gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (heta : 0 < eta)
    (hT : 0 ≤ hardT D eta gamma)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma)) :
    hardT D eta gamma * Real.exp (-eta * gamma) ≤
      D * (1 - 2 * hardP D +
        2 * hardP D * hardT D eta gamma *
          Real.cosh (eta * gamma)) := by
  rw [← hardT_balance hden]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith)) hT

lemma hard_calibration_normalizer {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool) :
    candidateNormalizer
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardTheta hd D eta gamma v)
      (hardContextEquiv d C D hardContextCalibration) =
        Real.exp eta / C := by
  unfold candidateNormalizer
  simp only [hardExperiment, Equiv.symm_apply_apply, Fin.sum_univ_succ]
  rw [hard_score_on_context hd v, hard_score_on_context hd v,
    hard_score_on_context hd v]
  norm_num [hardExperiment, hardContextCalibration, hardReferenceOnContext,
    hardPlus, hardMinus, hardZero]
  simpa [hardQ] using indexQ_normalizer heta
    (lt_trans zero_lt_one (lt_of_lt_of_le hD hDC))

lemma hard_hard_normalizer {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    candidateNormalizer
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardTheta hd D eta gamma v)
      (hardContextEquiv d C D (hardContextHard j)) =
        1 - 2 * hardP D +
          2 * hardP D * hardT D eta gamma *
            Real.cosh (eta * gamma) := by
  unfold candidateNormalizer
  simp only [hardExperiment, Equiv.symm_apply_apply, Fin.sum_univ_succ]
  rw [hard_score_on_context hd v, hard_score_on_context hd v,
    hard_score_on_context hd v]
  have hb := hard_exp_beta heta hD hden
  cases hv : v j
  · norm_num [Fin.sum_univ_succ, hardContextHard, hardReferenceOnContext,
      hardPlus, hardMinus, hardZero, hv]
    simp only [show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, if_false, Real.exp_zero, mul_one]
    rw [show eta * (hardBeta D eta gamma + -gamma) =
        eta * hardBeta D eta gamma + -(eta * gamma) by ring,
      show eta * (hardBeta D eta gamma + gamma) =
        eta * hardBeta D eta gamma + eta * gamma by ring,
      Real.exp_add, Real.exp_add, hb, Real.cosh_eq]
    ring
  · norm_num [Fin.sum_univ_succ, hardContextHard, hardReferenceOnContext,
      hardPlus, hardMinus, hardZero, hv]
    simp only [show (2 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 1 by decide, if_false, Real.exp_zero, mul_one]
    rw [show eta * (hardBeta D eta gamma + gamma) =
        eta * hardBeta D eta gamma + eta * gamma by ring,
      show eta * (hardBeta D eta gamma - gamma) =
        eta * hardBeta D eta gamma + -(eta * gamma) by ring,
      Real.exp_add, Real.exp_add, hb, Real.cosh_eq]
    ring

end

end CausalSmith.Stat.ReverseKLTwoCoverage
