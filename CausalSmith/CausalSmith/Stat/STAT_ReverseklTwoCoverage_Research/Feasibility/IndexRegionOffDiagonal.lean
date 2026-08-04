import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegionConstruction

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

def offDiagonalFeature {d : ℕ} (j0 : Fin d)
    (x : Fin (d + 1)) (a : Fin 2)
    (i : Fin d) : ℝ :=
  Fin.cases (indexBasis j0 i)
    (fun j => diagonalIndexFeature j a i) x

def offDiagonalReference {d : ℕ} (j0 : Fin d) (eta C D : ℝ)
    (x : Fin (d + 1)) (a : Fin 2) : ℝ :=
  Fin.cases (1 / 2)
    (fun j => diagonalIndexReference eta (if j = j0 then C else D) j a) x

def offDiagonalExperiment (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    CommonExperiment d (Fin (d + 1)) (Fin 2) where
  feature := offDiagonalFeature ⟨0, by omega⟩
  reference := offDiagonalReference ⟨0, by omega⟩ eta C D
  eta := eta
  reference_isPolicy := by
    constructor
    · intro x a
      refine Fin.cases ?_ (fun j => ?_) x
      · norm_num [offDiagonalReference]
      · by_cases hj : j = (⟨0, by omega⟩ : Fin d)
        · subst j
          fin_cases a
          · simp [offDiagonalReference, diagonalIndexReference,
              indexQ_le_one heta (by linarith : 1 ≤ C)]
          · simp [offDiagonalReference, diagonalIndexReference,
              (indexQ_pos heta (by linarith : 0 < C) hCexp).le]
        · fin_cases a
          · simp [offDiagonalReference, diagonalIndexReference, hj,
              indexQ_le_one heta hD.le]
          · simp [offDiagonalReference, diagonalIndexReference, hj,
              (indexQ_pos heta (by linarith : 0 < D)
                (lt_trans hDC hCexp)).le]
    · intro x
      refine Fin.cases ?_ (fun j => ?_) x
      · norm_num [Fin.sum_univ_two, offDiagonalReference]
        rfl
      · simp [Fin.sum_univ_two, offDiagonalReference,
          diagonalIndexReference]
  eta_pos := heta
  dim_ge_four := hd

lemma offDiagonal_bounded (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    BoundedFeatures
      (offDiagonalExperiment d hd eta C D heta hD hDC hCexp) := by
  intro x a
  refine Fin.cases ?_ (fun j => ?_) x
  · simp [offDiagonalExperiment, offDiagonalFeature, indexBasis_sum_sq]
  · fin_cases a
    · simp [offDiagonalExperiment, offDiagonalFeature,
        diagonalIndexFeature]
    · simp [offDiagonalExperiment, offDiagonalFeature,
        diagonalIndexFeature, indexBasis_sum_sq]

lemma offDiagonal_score_zero (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta)
    (a : Fin 2) :
    ∑ i, (offDiagonalExperiment d hd eta C D heta hD hDC hCexp).feature
      0 a i * (1 : ℝ) = 1 := by
  simpa [offDiagonalExperiment, offDiagonalFeature] using
    indexBasis_dot_one (⟨0, by omega⟩ : Fin d)

lemma offDiagonal_score_succ (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta)
    (j : Fin d) (a : Fin 2) :
    ∑ i, (offDiagonalExperiment d hd eta C D heta hD hDC hCexp).feature
      j.succ a i * (1 : ℝ) = if a = 1 then 1 else 0 := by
  fin_cases a
  · simp [offDiagonalExperiment, offDiagonalFeature,
      diagonalIndexFeature]
  · simpa [offDiagonalExperiment, offDiagonalFeature,
      diagonalIndexFeature] using indexBasis_dot_one j

lemma offDiagonal_normalizer_zero (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    candidateNormalizer
      (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
      (fun _ => 1) 0 = Real.exp eta := by
  simp only [candidateNormalizer, Fin.sum_univ_two]
  rw [offDiagonal_score_zero, offDiagonal_score_zero]
  norm_num [offDiagonalExperiment, offDiagonalReference]
  ring

lemma offDiagonal_normalizer_succ (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta)
    (j : Fin d) :
    candidateNormalizer
      (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
      (fun _ => 1) j.succ =
        Real.exp eta / (if j = (⟨0, by omega⟩ : Fin d) then C else D) := by
  let K : ℝ := if j = (⟨0, by omega⟩ : Fin d) then C else D
  have hKpos : 0 < K := by
    simp only [K]
    split_ifs <;> linarith
  simp only [candidateNormalizer, Fin.sum_univ_two]
  rw [offDiagonal_score_succ, offDiagonal_score_succ]
  norm_num [offDiagonalExperiment, offDiagonalReference,
    diagonalIndexReference]
  nlinarith [indexQ_normalizer (eta := eta) (K := K) heta hKpos]

lemma offDiagonal_loggingBlock_zero (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    loggingBlock
      (offDiagonalExperiment d hd eta C D heta hD hDC hCexp) 0 =
        fun i j => indexBasis ⟨0, by omega⟩ i *
          indexBasis ⟨0, by omega⟩ j := by
  ext i j
  simp [loggingBlock, offDiagonalExperiment, offDiagonalReference,
    offDiagonalFeature]

lemma offDiagonal_loggingBlock_succ (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta)
    (j : Fin d) :
    loggingBlock
      (offDiagonalExperiment d hd eta C D heta hD hDC hCexp) j.succ =
        fun i k => indexQ eta
          (if j = (⟨0, by omega⟩ : Fin d) then C else D) *
          (indexBasis j i * indexBasis j k) := by
  ext i k
  simp [loggingBlock, offDiagonalExperiment, offDiagonalReference,
    offDiagonalFeature, diagonalIndexReference, diagonalIndexFeature]

lemma offDiagonal_targetBlock_zero (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    targetBlock
      (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
      (fun _ => 1) 0 =
        loggingBlock
          (offDiagonalExperiment d hd eta C D heta hD hDC hCexp) 0 := by
  ext i j
  simp only [targetBlock, Fin.sum_univ_two]
  rw [show candidateWeight
      (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
      (fun _ => 1) 0 0 = 1 by
    rw [candidateWeight, offDiagonal_score_zero,
      offDiagonal_normalizer_zero]
    simp [offDiagonalExperiment],
    show candidateWeight
      (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
      (fun _ => 1) 0 1 = 1 by
    rw [candidateWeight, offDiagonal_score_zero,
      offDiagonal_normalizer_zero]
    simp [offDiagonalExperiment],
    offDiagonal_loggingBlock_zero]
  simp [offDiagonalExperiment, offDiagonalReference, offDiagonalFeature]
  ring

lemma offDiagonal_targetBlock_succ (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta)
    (j : Fin d) :
    targetBlock
      (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
      (fun _ => 1) j.succ =
        (if j = (⟨0, by omega⟩ : Fin d) then C else D) •
          loggingBlock
            (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
            j.succ := by
  let K : ℝ := if j = (⟨0, by omega⟩ : Fin d) then C else D
  have hKpos : 0 < K := by
    simp only [K]
    split_ifs <;> linarith
  ext i k
  simp only [targetBlock, Fin.sum_univ_two]
  rw [offDiagonal_loggingBlock_succ]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [show candidateWeight
      (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
      (fun _ => 1) j.succ 1 = K by
    rw [candidateWeight, offDiagonal_score_succ,
      offDiagonal_normalizer_succ]
    simp [K, offDiagonalExperiment]]
  simp [offDiagonalExperiment, offDiagonalReference, offDiagonalFeature,
    diagonalIndexReference, diagonalIndexFeature, K]
  ring

def offDiagonalA (eta C D : ℝ) : ℝ :=
  indexQ eta C * (C - D) / (D - 1)

lemma offDiagonalA_pos {eta C D : ℝ} (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    0 < offDiagonalA eta C D := by
  exact div_pos
    (mul_pos (indexQ_pos heta (by linarith) hCexp) (sub_pos.2 hDC))
    (sub_pos.2 hD)

lemma offDiagonal_balance {eta C D : ℝ} (hD : 1 < D) :
    offDiagonalA eta C D * (D - 1) =
      indexQ eta C * (C - D) := by
  rw [offDiagonalA]
  field_simp [ne_of_gt (sub_pos.2 hD)]

def offDiagonalTotal (d : ℕ) (eta C D : ℝ) : ℝ :=
  d + offDiagonalA eta C D

def offDiagonalRho {d : ℕ} (eta C D : ℝ) (x : Fin (d + 1)) : ℝ :=
  Fin.cases (offDiagonalA eta C D) (fun _ => 1) x /
    offDiagonalTotal d eta C D

lemma offDiagonalTotal_pos {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ} (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    0 < offDiagonalTotal d eta C D := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  exact add_pos hdreal (offDiagonalA_pos heta hD hDC hCexp)

lemma offDiagonalRho_pos {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ} (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta)
    (x : Fin (d + 1)) :
    0 < offDiagonalRho eta C D x := by
  refine Fin.cases ?_ (fun j => ?_) x
  · exact div_pos (offDiagonalA_pos heta hD hDC hCexp)
      (offDiagonalTotal_pos hd heta hD hDC hCexp)
  · exact div_pos zero_lt_one
      (offDiagonalTotal_pos hd heta hD hDC hCexp)

lemma offDiagonalRho_sum {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ} (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    ∑ x : Fin (d + 1), offDiagonalRho eta C D x = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [offDiagonalRho, Fin.cases_zero, Fin.cases_succ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    one_div, div_eq_mul_inv]
  simp only [one_mul]
  rw [show offDiagonalA eta C D *
      (offDiagonalTotal d eta C D)⁻¹ +
      (d : ℝ) * (offDiagonalTotal d eta C D)⁻¹ =
      offDiagonalTotal d eta C D *
        (offDiagonalTotal d eta C D)⁻¹ by
    rw [offDiagonalTotal]
    ring]
  exact mul_inv_cancel₀
    (ne_of_gt (offDiagonalTotal_pos hd heta hD hDC hCexp))

def offDiagonalLogCoeff {d : ℕ} (j0 : Fin d)
    (eta C D : ℝ) (i : Fin d) : ℝ :=
  ((if i = j0 then offDiagonalA eta C D else 0) +
      indexQ eta (if i = j0 then C else D)) /
    offDiagonalTotal d eta C D

lemma offDiagonal_logging_sum_eq (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    (∑ x : (Finset.univ : Finset (Fin (d + 1))),
      offDiagonalRho eta C D x.1 •
        loggingBlock
          (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
          x.1) =
      Matrix.diagonal
        (offDiagonalLogCoeff (⟨0, by omega⟩ : Fin d) eta C D) := by
  simp only [Finset.univ_eq_attach, Finset.sum_attach_univ]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_succ, offDiagonal_loggingBlock_zero]
  simp_rw [offDiagonal_loggingBlock_succ]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · subst i
      simp [offDiagonalRho, offDiagonalLogCoeff, offDiagonalTotal,
        Matrix.diagonal, indexBasis]
      ring
    · simp [offDiagonalRho, offDiagonalLogCoeff, offDiagonalTotal,
        Matrix.diagonal, indexBasis, hi]
      ring
  · by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · by_cases hj : j = (⟨0, by omega⟩ : Fin d)
      · exact (hij (hi.trans hj.symm)).elim
      · have hj' : (⟨0, by omega⟩ : Fin d) ≠ j := Ne.symm hj
        simp [offDiagonalRho, offDiagonalLogCoeff, offDiagonalTotal,
          Matrix.diagonal, indexBasis, hi, hj, hj']
    · simp [offDiagonalRho, offDiagonalLogCoeff, offDiagonalTotal,
        Matrix.diagonal, indexBasis, hij, hi]

lemma offDiagonal_logging_posDef (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    Matrix.PosDef
      (∑ x : (Finset.univ : Finset (Fin (d + 1))),
        offDiagonalRho eta C D x.1 •
          loggingBlock
            (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
            x.1) := by
  rw [offDiagonal_logging_sum_eq]
  apply Matrix.PosDef.diagonal
  intro i
  have hqC : 0 < indexQ eta C :=
    indexQ_pos heta (by linarith) hCexp
  have hqD : 0 < indexQ eta D :=
    indexQ_pos heta (by linarith) (lt_trans hDC hCexp)
  have hT : 0 < offDiagonalTotal d eta C D :=
    offDiagonalTotal_pos hd heta hD hDC hCexp
  have hA : 0 < offDiagonalA eta C D :=
    offDiagonalA_pos heta hD hDC hCexp
  rw [offDiagonalLogCoeff]
  apply div_pos
  · by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · simp [hi, add_pos hA hqC]
    · simpa [hi] using hqD
  · exact hT

def offDiagonalTargetCoeff {d : ℕ} (j0 : Fin d)
    (eta C D : ℝ) (i : Fin d) : ℝ :=
  ((if i = j0 then offDiagonalA eta C D else 0) +
      (if i = j0 then C else D) *
        indexQ eta (if i = j0 then C else D)) /
    offDiagonalTotal d eta C D

lemma offDiagonal_target_sum_diagonal (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    (∑ x : (Finset.univ : Finset (Fin (d + 1))),
      offDiagonalRho eta C D x.1 •
        targetBlock
          (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
          (fun _ => 1) x.1) =
      Matrix.diagonal
        (offDiagonalTargetCoeff (⟨0, by omega⟩ : Fin d) eta C D) := by
  simp only [Finset.univ_eq_attach, Finset.sum_attach_univ]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_succ, offDiagonal_targetBlock_zero,
    offDiagonal_loggingBlock_zero]
  simp_rw [offDiagonal_targetBlock_succ, offDiagonal_loggingBlock_succ]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · subst i
      simp [offDiagonalRho, offDiagonalTargetCoeff, offDiagonalTotal,
        Matrix.diagonal, indexBasis, smul_eq_mul]
      ring
    · simp [offDiagonalRho, offDiagonalTargetCoeff, offDiagonalTotal,
        Matrix.diagonal, indexBasis, smul_eq_mul, hi]
      ring
  · by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · by_cases hj : j = (⟨0, by omega⟩ : Fin d)
      · exact (hij (hi.trans hj.symm)).elim
      · have hj' : (⟨0, by omega⟩ : Fin d) ≠ j := Ne.symm hj
        simp [offDiagonalRho, offDiagonalTargetCoeff, offDiagonalTotal,
          Matrix.diagonal, indexBasis, smul_eq_mul, hi, hj, hj']
    · simp [offDiagonalRho, offDiagonalTargetCoeff, offDiagonalTotal,
        Matrix.diagonal, indexBasis, smul_eq_mul, hij, hi]

lemma offDiagonal_target_sum_eq (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    (∑ x : (Finset.univ : Finset (Fin (d + 1))),
      offDiagonalRho eta C D x.1 •
        targetBlock
          (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
          (fun _ => 1) x.1) =
      D •
        (∑ x : (Finset.univ : Finset (Fin (d + 1))),
          offDiagonalRho eta C D x.1 •
            loggingBlock
              (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
              x.1) := by
  rw [offDiagonal_target_sum_diagonal, offDiagonal_logging_sum_eq]
  ext i j
  simp only [Matrix.diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · subst i
      simp [offDiagonalTargetCoeff, offDiagonalLogCoeff]
      field_simp [ne_of_gt
        (offDiagonalTotal_pos hd heta hD hDC hCexp)]
      nlinarith [offDiagonal_balance (eta := eta) (C := C) hD]
    · simp [offDiagonalTargetCoeff, offDiagonalLogCoeff, hi]
      ring
  · simp [hij]

lemma offDiagonal_feasible (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    FixedExperimentFeasibilitySystem
      (offDiagonalExperiment d hd eta C D heta hD hDC hCexp) C D := by
  let j0 : Fin d := ⟨0, by omega⟩
  refine ⟨Finset.univ, ⟨(0 : Fin (d + 1)), Finset.mem_univ _⟩,
    ⟨j0.succ, Finset.mem_univ _⟩, 1,
    (fun _ => 1), (fun x => offDiagonalRho eta C D x.1),
    indexBasis j0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 < indexQ eta C
    exact indexQ_pos heta (by linarith) hCexp
  · intro x a
    refine Fin.cases ?_ (fun j => ?_) x
    · rw [offDiagonal_score_zero]
      norm_num
    · rw [offDiagonal_score_succ]
      split_ifs <;> norm_num
  · intro x
    exact offDiagonalRho_pos hd heta hD hDC hCexp x
  · simpa only [Finset.univ_eq_attach, Finset.sum_attach_univ] using
      offDiagonalRho_sum hd heta hD hDC hCexp
  · exact offDiagonal_logging_posDef d hd eta C D heta hD hDC hCexp
  · intro x a ha
    refine Fin.cases ?_ (fun j => ?_) x.1
    · rw [offDiagonal_score_zero, offDiagonal_normalizer_zero]
      simp only [offDiagonalExperiment, mul_one]
      change Real.exp eta ≤ C * Real.exp eta
      nlinarith [Real.exp_pos eta]
    · rw [offDiagonal_score_succ, offDiagonal_normalizer_succ]
      let K : ℝ := if j = j0 then C else D
      have hKpos : 0 < K := by
        simp only [K, j0]
        split_ifs <;> linarith
      have hKle : K ≤ C := by
        simp only [K, j0]
        split_ifs <;> linarith
      fin_cases a
      · norm_num
        change 1 ≤ C * (Real.exp eta / K)
        have hCK : 1 ≤ C / K := (le_div_iff₀ hKpos).2 (by
          simpa only [one_mul] using hKle)
        have he : 1 < Real.exp eta := (Real.one_lt_exp_iff).2 heta
        calc
          1 ≤ C / K := hCK
          _ ≤ C / K * Real.exp eta :=
            le_mul_of_one_le_right (by positivity) he.le
          _ = C * (Real.exp eta / K) := by ring
      · norm_num
        change Real.exp eta ≤ C * (Real.exp eta / K)
        have hepos := Real.exp_pos eta
        calc
          Real.exp eta = K * (Real.exp eta / K) := by
            field_simp [ne_of_gt hKpos]
          _ ≤ C * (Real.exp eta / K) := by
            exact mul_le_mul_of_nonneg_right hKle
              (div_nonneg hepos.le hKpos.le)
  · rw [offDiagonal_score_succ, offDiagonal_normalizer_succ]
    simp [j0]
    change Real.exp eta = C * (Real.exp eta / C)
    field_simp [ne_of_gt (by linarith : 0 < C)]
  · rw [offDiagonal_target_sum_eq]
    simpa using (Matrix.PosSemidef.zero :
      Matrix.PosSemidef (0 : Matrix (Fin d) (Fin d) ℝ))
  · rw [offDiagonal_target_sum_eq]
    simp
  · exact indexBasis_sum_sq j0

theorem offDiagonal_exactShell (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    ∃ P : BanditLaw
        (offDiagonalExperiment d hd eta C D heta hD hDC hCexp),
      ExactShell
        (offDiagonalExperiment d hd eta C D heta hD hDC hCexp)
        P C D := by
  exact (fixed_experiment_shell_certificate
    (offDiagonalExperiment d hd eta C D heta hD hDC hCexp) C D).1.2
      ⟨offDiagonal_bounded d hd eta C D heta hD hDC hCexp,
        offDiagonal_feasible d hd eta C D heta hD hDC hCexp⟩

lemma offDiagonal_shared_feature (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    ∃ xC xA : Fin (d + 1), ∃ aC aA : Fin 2,
      xC ≠ xA ∧
      (∀ i, (offDiagonalExperiment d hd eta C D heta hD hDC hCexp).feature
        xC aC i =
        (offDiagonalExperiment d hd eta C D heta hD hDC hCexp).feature
          xA aA i) ∧
      ∃ i, (offDiagonalExperiment d hd eta C D heta hD hDC hCexp).feature
        xC aC i ≠ 0 := by
  let j0 : Fin d := ⟨0, by omega⟩
  refine ⟨j0.succ, 0, 1, 0, ?_, ?_, j0, ?_⟩
  · intro h
    have := congrArg Fin.val h
    simp [j0] at this
  · intro i
    simp [j0, offDiagonalExperiment, offDiagonalFeature,
      diagonalIndexFeature]
  · simp [offDiagonalExperiment, offDiagonalFeature, diagonalIndexFeature,
      indexBasis]

end

end CausalSmith.Stat.ReverseKLTwoCoverage
