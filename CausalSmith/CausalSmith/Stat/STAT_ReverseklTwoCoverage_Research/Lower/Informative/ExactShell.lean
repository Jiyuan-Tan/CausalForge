import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.ConstructionShell

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

lemma informativeAnchor_balance {eta C D : ℝ} (hD : 1 < D)
    (hDC : D ≤ C) :
    (if C = D then 0 else informativeAnchorRaw eta C D) +
        C * indexQ eta C =
      D * ((if C = D then 0 else informativeAnchorRaw eta C D) +
        indexQ eta C) := by
  by_cases h : C = D
  · subst C
    simp
  · simp only [h, if_false, informativeAnchorRaw]
    field_simp [ne_of_gt (sub_pos.mpr hD)]
    ring

lemma informativeLogCoeff_pos {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta) (i : Fin d) :
    0 < informativeLogCoeff (⟨0, by omega⟩ : Fin d) eta C D i := by
  have hT := informativeTotal_pos hd heta hD hDC hCexp
  unfold informativeLogCoeff
  by_cases hi : i = (⟨0, by omega⟩ : Fin d)
  · rw [if_pos hi]
    have hq : 0 < indexQ eta C :=
      indexQ_pos heta (lt_trans zero_lt_one (lt_of_lt_of_le hD hDC)) hCexp
    apply div_pos
    · split_ifs with h
      · simpa using hq
      · exact add_pos (informativeAnchorRaw_pos heta hD hDC hCexp) hq
    · exact hT
  · rw [if_neg hi]
    exact div_pos (by norm_num) hT

lemma informative_logging_posDef (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta) :
    Matrix.PosDef
      (∑ x : Fin (d + 1), informativeRho eta C D x •
        loggingBlock
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp) x) := by
  rw [informative_logging_sum_eq (d := d) hd eta C D heta hD hDC hCexp]
  exact Matrix.PosDef.diagonal
    (informativeLogCoeff_pos (d := d) hd heta hD hDC hCexp)

lemma informativeTargetCoeff_zero (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (v : Fin (d - 1) → Bool)
    (hD : 1 < D) (hDC : D ≤ C) :
    informativeTargetCoeff (by omega) (⟨0, by omega⟩ : Fin d)
        eta C D gamma v (⟨0, by omega⟩ : Fin d) =
      D * informativeLogCoeff (⟨0, by omega⟩ : Fin d)
        eta C D (⟨0, by omega⟩ : Fin d) := by
  simp [informativeTargetCoeff, informativeLogCoeff]
  rw [informativeAnchor_balance hD hDC]
  ring

lemma informativeTargetCoeff_le (d : ℕ) (hd : 4 ≤ d)
    {eta C D gamma : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (i : Fin d) :
    informativeTargetCoeff (by omega) (⟨0, by omega⟩ : Fin d)
        eta C D gamma v i ≤
      D * informativeLogCoeff (⟨0, by omega⟩ : Fin d) eta C D i := by
  by_cases hi : i = (⟨0, by omega⟩ : Fin d)
  · subst i
    rw [informativeTargetCoeff_zero d hd eta C D gamma v hD hDC]
  · have hT := informativeTotal_pos hd heta hD hDC hCexp
    have he := informative_info_exp_le_D hd v heta hD
      (lt_of_le_of_lt hDC hCexp) hgamma0 hgamma i hi
    have hexp := Real.exp_pos
      (eta * informativeTheta (by omega) eta D gamma v i)
    simp only [informativeTargetCoeff, informativeLogCoeff, if_neg hi]
    apply (div_le_iff₀ hT).2
    have hden : 0 < 1 + Real.exp
        (eta * informativeTheta (by omega) eta D gamma v i) := by positivity
    have hfrac :
        Real.exp (eta * informativeTheta (by omega) eta D gamma v i) /
            (1 + Real.exp
              (eta * informativeTheta (by omega) eta D gamma v i)) ≤ D / 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    field_simp [ne_of_gt hT]
    nlinarith

lemma informative_certificate_psd (d : ℕ) (hd : 4 ≤ d)
    {eta C D gamma : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    Matrix.PosSemidef
      (D • (∑ x : Fin (d + 1), informativeRho eta C D x •
        loggingBlock
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp) x) -
      ∑ x : Fin (d + 1), informativeRho eta C D x •
        targetBlock
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp)
          (informativeTheta (by omega) eta D gamma v) x) := by
  rw [informative_logging_sum_eq (d := d) hd eta C D heta hD hDC hCexp,
    informative_target_sum_eq (d := d) hd eta C D gamma heta hD hDC hCexp v]
  have heq :
      D • Matrix.diagonal
          (informativeLogCoeff (⟨0, by omega⟩ : Fin d) eta C D) -
        Matrix.diagonal
          (informativeTargetCoeff (by omega)
            (⟨0, by omega⟩ : Fin d) eta C D gamma v) =
      Matrix.diagonal (fun i =>
        D * informativeLogCoeff (⟨0, by omega⟩ : Fin d) eta C D i -
          informativeTargetCoeff (by omega)
            (⟨0, by omega⟩ : Fin d) eta C D gamma v i) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [heq]
  apply Matrix.PosSemidef.diagonal
  show (0 : Fin d → ℝ) ≤ fun i =>
    D * informativeLogCoeff (⟨0, by omega⟩ : Fin d) eta C D i -
      informativeTargetCoeff (by omega)
        (⟨0, by omega⟩ : Fin d) eta C D gamma v i
  intro i
  exact sub_nonneg.mpr
    (informativeTargetCoeff_le d hd heta hD hDC hCexp
      v hgamma0 hgamma i)

lemma informative_certificate_kernel (d : ℕ) (hd : 4 ≤ d)
    {eta C D gamma : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool) :
    (D • (∑ x : Fin (d + 1), informativeRho eta C D x •
        loggingBlock
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp) x) -
      ∑ x : Fin (d + 1), informativeRho eta C D x •
        targetBlock
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp)
          (informativeTheta (by omega) eta D gamma v) x).mulVec
        (indexBasis (⟨0, by omega⟩ : Fin d)) = 0 := by
  rw [informative_logging_sum_eq (d := d) hd eta C D heta hD hDC hCexp,
    informative_target_sum_eq (d := d) hd eta C D gamma heta hD hDC hCexp v]
  have heq :
      D • Matrix.diagonal
          (informativeLogCoeff (⟨0, by omega⟩ : Fin d) eta C D) -
        Matrix.diagonal
          (informativeTargetCoeff (by omega)
            (⟨0, by omega⟩ : Fin d) eta C D gamma v) =
      Matrix.diagonal (fun i =>
        D * informativeLogCoeff (⟨0, by omega⟩ : Fin d) eta C D i -
          informativeTargetCoeff (by omega)
            (⟨0, by omega⟩ : Fin d) eta C D gamma v i) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [heq]
  funext i
  by_cases hi : i = (⟨0, by omega⟩ : Fin d)
  · subst i
    have hc :
        D * informativeLogCoeff (⟨0, by omega⟩ : Fin d) eta C D
            (⟨0, by omega⟩ : Fin d) -
          informativeTargetCoeff (by omega)
            (⟨0, by omega⟩ : Fin d) eta C D gamma v
              (⟨0, by omega⟩ : Fin d) = 0 := by
      rw [informativeTargetCoeff_zero d hd eta C D gamma v hD hDC]
      ring
    rw [Matrix.mulVec_diagonal, hc]
    simp
  · have hb :
        indexBasis (⟨0, by omega⟩ : Fin d) i = 0 := by
      simp [indexBasis, hi]
    rw [Matrix.mulVec_diagonal, hb]
    simp

lemma informative_linear_bounds (d : ℕ) (hd : 4 ≤ d)
    {eta C D gamma : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    ∀ x a,
      (∑ i, (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).feature x a i *
        informativeTheta (by omega) eta D gamma v i) ∈ Set.Icc (0 : ℝ) 1 := by
  intro x a
  refine Fin.cases ?_ (fun j => ?_) x
  · rw [informative_score_anchor]
    split_ifs <;> norm_num
  · rw [informative_score_succ]
    split_ifs
    · exact informativeTheta_bounds hd v heta hD
        (lt_of_le_of_lt hDC hCexp) hgamma0 hgamma j
    · norm_num

theorem informative_exactShell (d : ℕ) (hd : 4 ≤ d)
    {eta C D gamma : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    ExactShell
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp)
      (ibBernoulliLaw
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp)
        (informativeRho eta C D)
        (informativeTheta (by omega) eta D gamma v)
        (fun x => (informativeRho_pos hd heta hD hDC hCexp x).le)
        (informativeRho_sum hd heta hD hDC hCexp)
        (informative_linear_bounds (d := d) hd heta hD hDC hCexp
          v hgamma0 hgamma))
      C D := by
  have ha0 : 0 <
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).reference
        (⟨0, by omega⟩ : Fin d).succ 1 := by
    change 0 < indexQ eta C
    exact indexQ_pos heta
      (lt_trans zero_lt_one (lt_of_lt_of_le hD hDC)) hCexp
  have hunorm :
      dotProduct (indexBasis (⟨0, by omega⟩ : Fin d))
        (indexBasis (⟨0, by omega⟩ : Fin d)) = 1 := by
    simpa [dotProduct, pow_two] using
      indexBasis_sum_sq (⟨0, by omega⟩ : Fin d)
  exact ibBernoulliLaw_exactShell_of_certificate
    (informativeExperiment d hd eta C D heta
      (lt_of_lt_of_le hD hDC) hCexp) C D
    (informativeTheta (by omega) eta D gamma v)
    (informativeRho eta C D)
    (⟨0, by omega⟩ : Fin d).succ 1
    (indexBasis (⟨0, by omega⟩ : Fin d))
    (informative_bounded d hd eta C D heta
      (lt_of_lt_of_le hD hDC) hCexp)
    ha0
    (informative_linear_bounds (d := d) hd heta hD hDC hCexp
      v hgamma0 hgamma)
    (informativeRho_pos hd heta hD hDC hCexp)
    (informativeRho_sum hd heta hD hDC hCexp)
    (informative_logging_posDef d hd eta C D heta hD hDC hCexp)
    (informative_certificate_bound (d := d) hd heta hD hDC hCexp
      v hgamma0 hgamma)
    (informative_certificate_attains (d := d) hd heta hD hDC hCexp v)
    (informative_certificate_psd (d := d) hd heta hD hDC hCexp
      v hgamma0 hgamma)
    (informative_certificate_kernel (d := d) hd heta hD hDC hCexp v)
    hunorm

end

end CausalSmith.Stat.ReverseKLTwoCoverage
