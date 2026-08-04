import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.ConstructionCore

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

def informativeBitIndex {d : ℕ} (hdpos : 0 < d)
    (i : Fin d) (hi : i ≠ ⟨0, hdpos⟩) : Fin (d - 1) :=
  ⟨i.val - 1, by omega⟩

def informativeSign (b : Bool) : ℝ := if b then 1 else -1

def informativeTheta {d : ℕ} (hdpos : 0 < d) (eta D gamma : ℝ)
    (v : Fin (d - 1) → Bool) (i : Fin d) : ℝ :=
  if hi : i = ⟨0, hdpos⟩ then 1
  else informativeBeta eta D +
    gamma * informativeSign (v (informativeBitIndex hdpos i hi))

lemma informativeSign_mem (b : Bool) :
    informativeSign b = 1 ∨ informativeSign b = -1 := by
  cases b <;> simp [informativeSign]

lemma informativeTheta_zero {d : ℕ} (hd : 4 ≤ d)
    (eta D gamma : ℝ) (v : Fin (d - 1) → Bool) :
    informativeTheta (by omega) eta D gamma v
      (⟨0, by omega⟩ : Fin d) = 1 := by
  simp [informativeTheta]

lemma informativeTheta_info_bounds {d : ℕ} (hd : 4 ≤ d)
    {eta D gamma : ℝ} (v : Fin (d - 1) → Bool)
    (heta : 0 < eta) (hD : 1 < D) (hDexp : D < Real.exp eta)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (i : Fin d) (hi : i ≠ (⟨0, by omega⟩ : Fin d)) :
    informativeTheta (by omega) eta D gamma v i ∈ Set.Icc (0 : ℝ) 1 := by
  have hb0 := informativeBeta_pos heta hD
  have hb1 := informativeBeta_lt_one heta hD hDexp
  have hgB : gamma ≤ informativeBeta eta D / 2 :=
    le_trans hgamma (min_le_left _ _)
  have hg1 : gamma ≤ (1 - informativeBeta eta D) / 2 :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  rw [informativeTheta, dif_neg hi]
  rcases informativeSign_mem
      (v (informativeBitIndex (by omega) i hi)) with hs | hs
  · rw [hs]
    constructor <;> nlinarith
  · rw [hs]
    constructor <;> nlinarith

lemma informativeTheta_bounds {d : ℕ} (hd : 4 ≤ d)
    {eta D gamma : ℝ} (v : Fin (d - 1) → Bool)
    (heta : 0 < eta) (hD : 1 < D) (hDexp : D < Real.exp eta)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (i : Fin d) :
    informativeTheta (by omega) eta D gamma v i ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hi : i = (⟨0, by omega⟩ : Fin d)
  · subst i
    rw [informativeTheta_zero hd]
    exact ⟨zero_le_one, le_rfl⟩
  · exact informativeTheta_info_bounds hd v heta hD hDexp hgamma0 hgamma i hi

lemma informative_bounded (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    BoundedFeatures
      (informativeExperiment d hd eta C D heta hC1 hCexp) := by
  intro x a
  refine Fin.cases ?_ (fun j => ?_) x
  · by_cases h : C = D
    · simp [informativeExperiment, informativeFeature, h]
    · simp [informativeExperiment, informativeFeature, h, indexBasis_sum_sq]
  · fin_cases a
    · simp [informativeExperiment, informativeFeature, diagonalIndexFeature]
    · simp [informativeExperiment, informativeFeature,
        diagonalIndexFeature, indexBasis_sum_sq]

lemma informative_score_anchor (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (v : Fin (d - 1) → Bool) (a : Fin 2) :
    ∑ i, (informativeExperiment d hd eta C D heta hC1 hCexp).feature
      0 a i * informativeTheta (by omega) eta D gamma v i =
        if C = D then 0 else 1 := by
  by_cases h : C = D
  · simp [informativeExperiment, informativeFeature, h]
  · simp only [informativeExperiment, informativeFeature, Fin.cases_zero, h, if_false]
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin d)]
    · simp [indexBasis, informativeTheta_zero hd]
    · intro i _ hi
      simp [indexBasis, hi]
    · simp

lemma informative_score_succ (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (v : Fin (d - 1) → Bool)
    (j : Fin d) (a : Fin 2) :
    ∑ i, (informativeExperiment d hd eta C D heta hC1 hCexp).feature
      j.succ a i * informativeTheta (by omega) eta D gamma v i =
        if a = 1 then informativeTheta (by omega) eta D gamma v j else 0 := by
  fin_cases a
  · simp [informativeExperiment, informativeFeature, diagonalIndexFeature]
  · simp [informativeExperiment, informativeFeature, diagonalIndexFeature,
      indexBasis]

lemma informative_info_exp_le_D {d : ℕ} (hd : 4 ≤ d)
    {eta D gamma : ℝ} (v : Fin (d - 1) → Bool)
    (heta : 0 < eta) (hD : 1 < D) (hDexp : D < Real.exp eta)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (j : Fin d) (hj : j ≠ (⟨0, by omega⟩ : Fin d)) :
    Real.exp (eta * informativeTheta (by omega) eta D gamma v j) ≤ D := by
  have hglog : gamma ≤
      (Real.log D - Real.log (informativeOdds D)) / (2 * eta) :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_right _ _))
  have hlogOD : Real.log (informativeOdds D) < Real.log D :=
    Real.strictMonoOn_log
      (lt_trans zero_lt_one (informativeOdds_gt_one hD))
      (lt_trans zero_lt_one hD) (informativeOdds_lt_D hD)
  have hbeta :
      eta * informativeBeta eta D = Real.log (informativeOdds D) := by
    unfold informativeBeta
    field_simp [ne_of_gt heta]
  have htheta :
      informativeTheta (by omega) eta D gamma v j ≤
        informativeBeta eta D + gamma := by
    rw [informativeTheta, dif_neg hj]
    rcases informativeSign_mem
      (v (informativeBitIndex (by omega) j hj)) with hs | hs
    · rw [hs]
      simpa using (le_refl (informativeBeta eta D + gamma))
    · rw [hs]
      nlinarith
  have harg :
      eta * informativeTheta (by omega) eta D gamma v j ≤ Real.log D := by
    have hhalf :
        eta * gamma ≤
          (Real.log D - Real.log (informativeOdds D)) / 2 := by
      have := mul_le_mul_of_nonneg_left hglog heta.le
      field_simp [ne_of_gt heta] at this
      linarith
    nlinarith
  calc
    Real.exp (eta * informativeTheta (by omega) eta D gamma v j)
        ≤ Real.exp (Real.log D) := Real.exp_le_exp.mpr harg
    _ = D := Real.exp_log (lt_trans zero_lt_one hD)

lemma informative_normalizer_anchor (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (v : Fin (d - 1) → Bool) :
    candidateNormalizer
      (informativeExperiment d hd eta C D heta hC1 hCexp)
      (informativeTheta (by omega) eta D gamma v) 0 =
        if C = D then 1 else Real.exp eta := by
  simp only [candidateNormalizer, Fin.sum_univ_two]
  rw [informative_score_anchor, informative_score_anchor]
  by_cases h : C = D
  · simp [h, informativeExperiment, informativeReference]
    norm_num
  · simp [h, informativeExperiment, informativeReference]
    ring

lemma informative_normalizer_calibration (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (v : Fin (d - 1) → Bool) :
    candidateNormalizer
      (informativeExperiment d hd eta C D heta hC1 hCexp)
      (informativeTheta (by omega) eta D gamma v)
      (⟨0, by omega⟩ : Fin d).succ = Real.exp eta / C := by
  simp only [candidateNormalizer, Fin.sum_univ_two]
  rw [informative_score_succ, informative_score_succ,
    informativeTheta_zero hd]
  norm_num [informativeExperiment, informativeReference,
    diagonalIndexReference]
  nlinarith [indexQ_normalizer (eta := eta) (K := C) heta
    (lt_trans zero_lt_one hC1)]

lemma informative_normalizer_info (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (v : Fin (d - 1) → Bool)
    (j : Fin d) (hj : j ≠ (⟨0, by omega⟩ : Fin d)) :
    candidateNormalizer
      (informativeExperiment d hd eta C D heta hC1 hCexp)
      (informativeTheta (by omega) eta D gamma v) j.succ =
        (1 + Real.exp
          (eta * informativeTheta (by omega) eta D gamma v j)) / 2 := by
  simp only [candidateNormalizer, Fin.sum_univ_two]
  rw [informative_score_succ, informative_score_succ]
  norm_num [informativeExperiment, informativeReference, hj]
  ring

lemma informative_certificate_bound (d : ℕ) (hd : 4 ≤ d)
    {eta C D gamma : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    ∀ x a, 0 < (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).reference x a →
      Real.exp ((informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp).eta *
        ∑ i, (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp).feature x a i *
          informativeTheta (by omega) eta D gamma v i) ≤
        C * candidateNormalizer
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp)
          (informativeTheta (by omega) eta D gamma v) x := by
  intro x a _
  refine Fin.cases ?_ (fun j => ?_) x
  · rw [informative_score_anchor, informative_normalizer_anchor]
    by_cases h : C = D
    · simp [h]
      linarith
    · simp [h]
      exact le_mul_of_one_le_left (Real.exp_pos eta).le (by linarith)
  · by_cases hj : j = (⟨0, by omega⟩ : Fin d)
    · subst j
      rw [informative_score_succ, informative_normalizer_calibration]
      fin_cases a
      · norm_num
        have he : 1 < Real.exp eta := (Real.one_lt_exp_iff).2 heta
        have hC0 : 0 < C := lt_trans zero_lt_one (lt_of_lt_of_le hD hDC)
        change 1 ≤ C * (Real.exp eta / C)
        calc
          1 ≤ Real.exp eta := he.le
          _ = C * (Real.exp eta / C) := by field_simp
      · norm_num
        rw [informativeTheta_zero hd]
        have heq : C * (Real.exp eta / C) = Real.exp eta := by
          field_simp [ne_of_gt (lt_trans zero_lt_one (lt_of_lt_of_le hD hDC))]
        simpa [informativeExperiment, heq]
    · rw [informative_score_succ,
        informative_normalizer_info (d := d) (hd := hd)
          (eta := eta) (C := C) (D := D) (gamma := gamma)
          (heta := heta) (hC1 := lt_of_lt_of_le hD hDC)
          (hCexp := hCexp) (v := v) (j := j) hj]
      have htbound := informative_info_exp_le_D hd v heta hD
        (lt_of_le_of_lt hDC hCexp) hgamma0 hgamma j hj
      have htheta := informativeTheta_info_bounds hd v heta hD
        (lt_of_le_of_lt hDC hCexp) hgamma0 hgamma j hj
      have ht1 : 1 ≤ Real.exp
          (eta * informativeTheta (by omega) eta D gamma v j) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonneg heta.le htheta.1)
      fin_cases a
      · norm_num
        have hnorm1 :
            1 ≤ (1 + Real.exp
              (eta * informativeTheta (by omega) eta D gamma v j)) / 2 := by
          linarith
        nlinarith
      · norm_num
        have htpos := Real.exp_pos
          (eta * informativeTheta (by omega) eta D gamma v j)
        have hratio :
            Real.exp (eta * informativeTheta (by omega) eta D gamma v j) ≤
              (1 + Real.exp
                (eta * informativeTheta (by omega) eta D gamma v j)) / 2 *
                D := by
          nlinarith
        rw [show (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp).eta = eta by rfl]
        calc
          Real.exp (eta * informativeTheta (by omega) eta D gamma v j) ≤
              (1 + Real.exp
                (eta * informativeTheta (by omega) eta D gamma v j)) / 2 *
                D := hratio
          _ ≤ (1 + Real.exp
                (eta * informativeTheta (by omega) eta D gamma v j)) / 2 *
                C := mul_le_mul_of_nonneg_left hDC (by positivity)
          _ = C * ((1 + Real.exp
                (eta * informativeTheta (by omega) eta D gamma v j)) / 2) := by
                ring

lemma informative_certificate_attains (d : ℕ) (hd : 4 ≤ d)
    {eta C D gamma : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool) :
    Real.exp ((informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).eta *
      ∑ i, (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).feature
          (⟨0, by omega⟩ : Fin d).succ 1 i *
        informativeTheta (by omega) eta D gamma v i) =
      C * candidateNormalizer
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp)
        (informativeTheta (by omega) eta D gamma v)
        (⟨0, by omega⟩ : Fin d).succ := by
  rw [informative_score_succ, informative_normalizer_calibration,
    informativeTheta_zero hd]
  norm_num
  change Real.exp eta = C * (Real.exp eta / C)
  field_simp [ne_of_gt (lt_trans zero_lt_one (lt_of_lt_of_le hD hDC))]

lemma informative_loggingBlock_anchor (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    loggingBlock (informativeExperiment d hd eta C D heta hC1 hCexp) 0 =
      if C = D then 0 else
        fun i j => indexBasis (⟨0, by omega⟩ : Fin d) i *
          indexBasis (⟨0, by omega⟩ : Fin d) j := by
  ext i j
  by_cases h : C = D
  · simp [loggingBlock, informativeExperiment, informativeFeature, h]
  · simp [loggingBlock, informativeExperiment, informativeFeature,
      informativeReference, h]

lemma informative_loggingBlock_succ (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (j : Fin d) :
    loggingBlock (informativeExperiment d hd eta C D heta hC1 hCexp) j.succ =
      (if j = (⟨0, by omega⟩ : Fin d) then indexQ eta C else 1 / 2) •
        (fun i k => indexBasis j i * indexBasis j k) := by
  ext i k
  simp [loggingBlock, informativeExperiment, informativeFeature,
    informativeReference, diagonalIndexReference, diagonalIndexFeature]

lemma informative_targetBlock_anchor (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (v : Fin (d - 1) → Bool) :
    targetBlock (informativeExperiment d hd eta C D heta hC1 hCexp)
      (informativeTheta (by omega) eta D gamma v) 0 =
        loggingBlock (informativeExperiment d hd eta C D heta hC1 hCexp) 0 := by
  ext i j
  simp only [targetBlock, Fin.sum_univ_two]
  rw [show candidateWeight
      (informativeExperiment d hd eta C D heta hC1 hCexp)
      (informativeTheta (by omega) eta D gamma v) 0 0 = 1 by
    rw [candidateWeight, informative_score_anchor,
      informative_normalizer_anchor]
    by_cases h : C = D <;> simp [h, informativeExperiment],
    show candidateWeight
      (informativeExperiment d hd eta C D heta hC1 hCexp)
      (informativeTheta (by omega) eta D gamma v) 0 1 = 1 by
    rw [candidateWeight, informative_score_anchor,
      informative_normalizer_anchor]
    by_cases h : C = D <;> simp [h, informativeExperiment],
    informative_loggingBlock_anchor]
  by_cases h : C = D
  · simp [h, informativeExperiment, informativeFeature]
  · simp [h, informativeExperiment, informativeFeature, informativeReference]
    ring

lemma informative_targetBlock_calibration (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (v : Fin (d - 1) → Bool) :
    targetBlock (informativeExperiment d hd eta C D heta hC1 hCexp)
      (informativeTheta (by omega) eta D gamma v)
      (⟨0, by omega⟩ : Fin d).succ =
        C • loggingBlock
          (informativeExperiment d hd eta C D heta hC1 hCexp)
          (⟨0, by omega⟩ : Fin d).succ := by
  ext i k
  simp only [targetBlock, Fin.sum_univ_two]
  rw [informative_loggingBlock_succ]
  simp only [if_pos, Matrix.smul_apply, smul_eq_mul]
  rw [show candidateWeight
      (informativeExperiment d hd eta C D heta hC1 hCexp)
      (informativeTheta (by omega) eta D gamma v)
      (⟨0, by omega⟩ : Fin d).succ 1 = C by
    rw [candidateWeight, informative_score_succ,
      informative_normalizer_calibration, informativeTheta_zero hd]
    norm_num [informativeExperiment]]
  simp [informativeExperiment, informativeReference, informativeFeature,
    diagonalIndexReference, diagonalIndexFeature]
  ring

lemma informative_targetBlock_info (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (v : Fin (d - 1) → Bool)
    (j : Fin d) (hj : j ≠ (⟨0, by omega⟩ : Fin d)) :
    targetBlock (informativeExperiment d hd eta C D heta hC1 hCexp)
      (informativeTheta (by omega) eta D gamma v) j.succ =
        (Real.exp (eta * informativeTheta (by omega) eta D gamma v j) /
          (1 + Real.exp
            (eta * informativeTheta (by omega) eta D gamma v j))) •
          (fun i k => indexBasis j i * indexBasis j k) := by
  ext i k
  simp only [targetBlock, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  rw [show candidateWeight
      (informativeExperiment d hd eta C D heta hC1 hCexp)
      (informativeTheta (by omega) eta D gamma v) j.succ 1 =
        2 * Real.exp
          (eta * informativeTheta (by omega) eta D gamma v j) /
            (1 + Real.exp
              (eta * informativeTheta (by omega) eta D gamma v j)) by
    rw [candidateWeight, informative_score_succ,
      informative_normalizer_info (d := d) (hd := hd)
        (eta := eta) (C := C) (D := D) (gamma := gamma)
        (heta := heta) (hC1 := hC1) (hCexp := hCexp)
        (v := v) (j := j) hj]
    norm_num [informativeExperiment]
    have hz : 1 + Real.exp
        (eta * informativeTheta (by omega) eta D gamma v j) ≠ 0 := by
      positivity
    field_simp [hz]
    <;> ring
    <;> try { exact Or.inl trivial }]
  have hz : 1 + Real.exp
      (eta * informativeTheta (by omega) eta D gamma v j) ≠ 0 := by
    positivity
  simp [informativeExperiment, informativeReference, informativeFeature,
    diagonalIndexFeature, hj]
  field_simp [hz]
  ring
  <;> try { exact Or.inl trivial }

def informativeLogCoeff {d : ℕ} (j0 : Fin d)
    (eta C D : ℝ) (i : Fin d) : ℝ :=
  if i = j0 then
    ((if C = D then 0 else informativeAnchorRaw eta C D) + indexQ eta C) /
      informativeTotal d eta C D
  else (1 / 2) / informativeTotal d eta C D

def informativeTargetCoeff {d : ℕ} (hdpos : 0 < d) (j0 : Fin d)
    (eta C D gamma : ℝ) (v : Fin (d - 1) → Bool) (i : Fin d) : ℝ :=
  if i = j0 then
    ((if C = D then 0 else informativeAnchorRaw eta C D) +
      C * indexQ eta C) / informativeTotal d eta C D
  else
    (Real.exp (eta * informativeTheta hdpos eta D gamma v i) /
      (1 + Real.exp (eta * informativeTheta hdpos eta D gamma v i))) /
        informativeTotal d eta C D

lemma informative_logging_sum_eq (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta) :
    (∑ x : Fin (d + 1), informativeRho eta C D x •
      loggingBlock
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp) x) =
      Matrix.diagonal
        (informativeLogCoeff (⟨0, by omega⟩ : Fin d) eta C D) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_succ, informative_loggingBlock_anchor]
  simp_rw [informative_loggingBlock_succ]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · subst i
      by_cases hCD : C = D <;>
        simp [informativeRho, informativeLogCoeff, Matrix.diagonal,
          indexBasis, hCD] <;> ring
    · by_cases hCD : C = D <;>
        simp [informativeRho, informativeLogCoeff, Matrix.diagonal,
          indexBasis, hi, Ne.symm hi, hCD] <;> ring
  · by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · by_cases hj : j = (⟨0, by omega⟩ : Fin d)
      · exact (hij (hi.trans hj.symm)).elim
      · by_cases hCD : C = D <;>
          simp [informativeRho, informativeLogCoeff, Matrix.diagonal,
            indexBasis, hi, hj, Ne.symm hj, hCD]
    · by_cases hCD : C = D <;>
        simp [informativeRho, informativeLogCoeff, Matrix.diagonal,
          indexBasis, hij, hi, hCD]

lemma informative_target_sum_eq (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool) :
    (∑ x : Fin (d + 1), informativeRho eta C D x •
      targetBlock
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp)
        (informativeTheta (by omega) eta D gamma v) x) =
      Matrix.diagonal
        (informativeTargetCoeff (by omega) (⟨0, by omega⟩ : Fin d)
          eta C D gamma v) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_succ, informative_targetBlock_anchor,
    informative_loggingBlock_anchor]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · subst i
      rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin d)]
      · rw [informative_targetBlock_calibration,
          informative_loggingBlock_succ]
        by_cases hCD : C = D <;>
          simp [informativeRho, informativeTargetCoeff, Matrix.diagonal,
            indexBasis, hCD] <;> ring
      · intro l _ hl
        rw [informative_targetBlock_info (d := d) (hd := hd)
          (eta := eta) (C := C) (D := D) (gamma := gamma)
          (heta := heta) (hC1 := lt_of_lt_of_le hD hDC)
          (hCexp := hCexp) (v := v) (j := l) hl]
        simp [indexBasis, hl, Ne.symm hl]
      · simp
    · rw [Finset.sum_eq_single i]
      · rw [informative_targetBlock_info (d := d) (hd := hd)
          (eta := eta) (C := C) (D := D) (gamma := gamma)
          (heta := heta) (hC1 := lt_of_lt_of_le hD hDC)
          (hCexp := hCexp) (v := v) (j := i) hi]
        by_cases hCD : C = D <;>
          simp [informativeRho, informativeTargetCoeff, Matrix.diagonal,
            indexBasis, hi, Ne.symm hi, hCD] <;> ring
      · intro l _ hli
        by_cases hl : l = (⟨0, by omega⟩ : Fin d)
        · subst l
          rw [informative_targetBlock_calibration,
            informative_loggingBlock_succ]
          simp [indexBasis, hi]
        · rw [informative_targetBlock_info (d := d) (hd := hd)
            (eta := eta) (C := C) (D := D) (gamma := gamma)
            (heta := heta) (hC1 := lt_of_lt_of_le hD hDC)
            (hCexp := hCexp) (v := v) (j := l) hl]
          simp [indexBasis, hli, Ne.symm hli]
      · simp
  · simp_rw [show ∀ l : Fin d,
        (targetBlock
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp)
          (informativeTheta (by omega) eta D gamma v) l.succ) i j = 0 by
      intro l
      by_cases hl : l = (⟨0, by omega⟩ : Fin d)
      · subst l
        rw [informative_targetBlock_calibration, informative_loggingBlock_succ]
        by_cases hi0 : i = (⟨0, by omega⟩ : Fin d) <;>
          by_cases hj0 : j = (⟨0, by omega⟩ : Fin d) <;>
          simp [indexBasis, hi0, hj0] at *
      · rw [informative_targetBlock_info (d := d) (hd := hd)
          (eta := eta) (C := C) (D := D) (gamma := gamma)
          (heta := heta) (hC1 := lt_of_lt_of_le hD hDC)
          (hCexp := hCexp) (v := v) (j := l) hl]
        by_cases hil : i = l <;> by_cases hjl : j = l <;>
          simp [indexBasis, hil, hjl] at *]
    by_cases hCD : C = D <;>
      by_cases hi0 : i = (⟨0, by omega⟩ : Fin d) <;>
      by_cases hj0 : j = (⟨0, by omega⟩ : Fin d) <;>
      simp [informativeRho, informativeTargetCoeff, Matrix.diagonal,
        indexBasis, hij, hCD, hi0, hj0] at * <;> aesop

end

end CausalSmith.Stat.ReverseKLTwoCoverage
