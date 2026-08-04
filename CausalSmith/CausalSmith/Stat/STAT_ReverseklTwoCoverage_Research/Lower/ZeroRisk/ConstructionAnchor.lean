import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.ZeroRisk.ConstructionCore

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def zeroRiskAnchorFeature {d : ℕ} (j0 : Fin d)
    (x : Fin (d + 1)) (a : Fin 2) (i : Fin d) : ℝ :=
  Fin.cases (indexBasis j0 i) (fun j => zeroRiskCoreFeature j0 j a i) x

def zeroRiskAnchorReference {d : ℕ} (j0 : Fin d) (eta C : ℝ)
    (x : Fin (d + 1)) (a : Fin 2) : ℝ :=
  Fin.cases (1 / 2) (fun j => zeroRiskCoreReference j0 eta C j a) x

def zeroRiskAnchorExperiment (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    CommonExperiment d (Fin (d + 1)) (Fin 2) where
  feature := zeroRiskAnchorFeature ⟨0, by omega⟩
  reference := zeroRiskAnchorReference ⟨0, by omega⟩ eta C
  eta := eta
  reference_isPolicy := by
    constructor
    · intro x a
      refine Fin.cases ?_ (fun j => ?_) x
      · norm_num [zeroRiskAnchorReference]
      · exact (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp)
          |>.reference_isPolicy.1 j a
    · intro x
      refine Fin.cases ?_ (fun j => ?_) x
      · simp [Fin.sum_univ_two, zeroRiskAnchorReference]
      · exact (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp)
          |>.reference_isPolicy.2 j
  eta_pos := heta
  dim_ge_four := hd

lemma zeroRiskAnchor_bounded (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    BoundedFeatures
      (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp) := by
  intro x a
  refine Fin.cases ?_ (fun j => ?_) x
  · simp [zeroRiskAnchorExperiment, zeroRiskAnchorFeature,
      indexBasis_sum_sq]
  · simpa [zeroRiskAnchorExperiment, zeroRiskAnchorFeature] using
      zeroRiskCore_bounded d hd eta C heta hC1 hCexp j a

lemma zeroRiskAnchor_score_zero (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (a : Fin 2) :
    ∑ i, (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp).feature
      0 a i * (1 : ℝ) = 1 := by
  simpa [zeroRiskAnchorExperiment, zeroRiskAnchorFeature] using
    indexBasis_dot_one (⟨0, by omega⟩ : Fin d)

lemma zeroRiskAnchor_score_succ (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (j : Fin d) (a : Fin 2) :
    ∑ i, (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp).feature
      j.succ a i * (1 : ℝ) =
        if j = (⟨0, by omega⟩ : Fin d) then
          if a = 1 then 1 else 0
        else 1 := by
  simpa [zeroRiskAnchorExperiment, zeroRiskAnchorFeature] using
    zeroRiskCore_score d hd eta C heta hC1 hCexp j a

lemma zeroRiskAnchor_normalizer_zero (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    candidateNormalizer
      (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp)
      (fun _ => 1) 0 = Real.exp eta := by
  simp only [candidateNormalizer, Fin.sum_univ_two]
  rw [zeroRiskAnchor_score_zero, zeroRiskAnchor_score_zero]
  norm_num [zeroRiskAnchorExperiment, zeroRiskAnchorReference]
  ring

lemma zeroRiskAnchor_normalizer_succ (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (j : Fin d) :
    candidateNormalizer
      (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp)
      (fun _ => 1) j.succ =
        if j = (⟨0, by omega⟩ : Fin d) then Real.exp eta / C
        else Real.exp eta := by
  simpa [candidateNormalizer, zeroRiskAnchorExperiment,
    zeroRiskAnchorReference, zeroRiskAnchorFeature] using
    zeroRiskCore_normalizer d hd eta C heta hC1 hCexp j

lemma zeroRiskAnchor_loggingBlock_zero (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    loggingBlock
      (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp) 0 =
        fun i j => indexBasis ⟨0, by omega⟩ i *
          indexBasis ⟨0, by omega⟩ j := by
  ext i j
  simp [loggingBlock, zeroRiskAnchorExperiment, zeroRiskAnchorReference,
    zeroRiskAnchorFeature]

lemma zeroRiskAnchor_loggingBlock_succ (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (j : Fin d) :
    loggingBlock
      (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp) j.succ =
        fun i k =>
          (if j = (⟨0, by omega⟩ : Fin d) then indexQ eta C else 1) *
            (indexBasis j i * indexBasis j k) := by
  simpa [loggingBlock, zeroRiskAnchorExperiment, zeroRiskAnchorReference,
    zeroRiskAnchorFeature] using
    zeroRiskCore_loggingBlock d hd eta C heta hC1 hCexp j

lemma zeroRiskAnchor_targetBlock_zero (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    targetBlock
      (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp)
      (fun _ => 1) 0 =
        loggingBlock
          (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp) 0 := by
  ext i j
  simp only [targetBlock, Fin.sum_univ_two]
  rw [show candidateWeight
      (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp)
      (fun _ => 1) 0 0 = 1 by
    rw [candidateWeight, zeroRiskAnchor_score_zero,
      zeroRiskAnchor_normalizer_zero]
    simp [zeroRiskAnchorExperiment],
    show candidateWeight
      (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp)
      (fun _ => 1) 0 1 = 1 by
    rw [candidateWeight, zeroRiskAnchor_score_zero,
      zeroRiskAnchor_normalizer_zero]
    simp [zeroRiskAnchorExperiment],
    zeroRiskAnchor_loggingBlock_zero]
  simp [zeroRiskAnchorExperiment, zeroRiskAnchorReference,
    zeroRiskAnchorFeature]
  ring

lemma zeroRiskAnchor_targetBlock_succ (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (j : Fin d) :
    targetBlock
      (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp)
      (fun _ => 1) j.succ =
        (if j = (⟨0, by omega⟩ : Fin d) then C else 1) •
          loggingBlock
            (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp)
            j.succ := by
  simpa [targetBlock, loggingBlock, zeroRiskAnchorExperiment,
    zeroRiskAnchorReference, zeroRiskAnchorFeature] using
    zeroRiskCore_targetBlock d hd eta C heta hC1 hCexp j

def zeroRiskAnchorA (eta C D : ℝ) : ℝ :=
  indexQ eta C * (C - D) / (D - 1)

lemma zeroRiskAnchorA_pos {eta C D : ℝ} (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    0 < zeroRiskAnchorA eta C D := by
  exact div_pos
    (mul_pos (indexQ_pos heta (by linarith) hCexp) (sub_pos.2 hDC))
    (sub_pos.2 hD)

lemma zeroRiskAnchor_balance {eta C D : ℝ} (hD : 1 < D) :
    zeroRiskAnchorA eta C D * (D - 1) =
      indexQ eta C * (C - D) := by
  rw [zeroRiskAnchorA]
  field_simp [ne_of_gt (sub_pos.2 hD)]

def zeroRiskAnchorTotal (d : ℕ) (eta C D : ℝ) : ℝ :=
  d + zeroRiskAnchorA eta C D

def zeroRiskAnchorRho {d : ℕ} (eta C D : ℝ)
    (x : Fin (d + 1)) : ℝ :=
  Fin.cases (zeroRiskAnchorA eta C D) (fun _ => 1) x /
    zeroRiskAnchorTotal d eta C D

lemma zeroRiskAnchorTotal_pos {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ} (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    0 < zeroRiskAnchorTotal d eta C D := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  exact add_pos hdreal (zeroRiskAnchorA_pos heta hD hDC hCexp)

lemma zeroRiskAnchorRho_pos {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ} (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta)
    (x : Fin (d + 1)) :
    0 < zeroRiskAnchorRho eta C D x := by
  refine Fin.cases ?_ (fun j => ?_) x
  · exact div_pos (zeroRiskAnchorA_pos heta hD hDC hCexp)
      (zeroRiskAnchorTotal_pos hd heta hD hDC hCexp)
  · exact div_pos zero_lt_one
      (zeroRiskAnchorTotal_pos hd heta hD hDC hCexp)

lemma zeroRiskAnchorRho_sum {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ} (heta : 0 < eta)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    ∑ x : Fin (d + 1), zeroRiskAnchorRho eta C D x = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [zeroRiskAnchorRho, Fin.cases_zero, Fin.cases_succ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    one_div, div_eq_mul_inv, one_mul]
  rw [show zeroRiskAnchorA eta C D *
      (zeroRiskAnchorTotal d eta C D)⁻¹ +
      (d : ℝ) * (zeroRiskAnchorTotal d eta C D)⁻¹ =
      zeroRiskAnchorTotal d eta C D *
        (zeroRiskAnchorTotal d eta C D)⁻¹ by
    rw [zeroRiskAnchorTotal]
    ring]
  exact mul_inv_cancel₀
    (ne_of_gt (zeroRiskAnchorTotal_pos hd heta hD hDC hCexp))

def zeroRiskAnchorLogCoeff {d : ℕ} (j0 : Fin d)
    (eta C D : ℝ) (i : Fin d) : ℝ :=
  ((if i = j0 then zeroRiskAnchorA eta C D else 0) +
      (if i = j0 then indexQ eta C else 1)) /
    zeroRiskAnchorTotal d eta C D

def zeroRiskAnchorTargetCoeff {d : ℕ} (j0 : Fin d)
    (eta C D : ℝ) (i : Fin d) : ℝ :=
  ((if i = j0 then zeroRiskAnchorA eta C D else 0) +
      (if i = j0 then C * indexQ eta C else 1)) /
    zeroRiskAnchorTotal d eta C D

lemma zeroRiskAnchor_logging_sum_eq (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    (∑ x : (Finset.univ : Finset (Fin (d + 1))),
      zeroRiskAnchorRho eta C D x.1 •
        loggingBlock
          (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp) x.1) =
      Matrix.diagonal
        (zeroRiskAnchorLogCoeff
          (⟨0, by omega⟩ : Fin d) eta C D) := by
  simp only [Finset.univ_eq_attach, Finset.sum_attach_univ]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_succ, zeroRiskAnchor_loggingBlock_zero]
  simp_rw [zeroRiskAnchor_loggingBlock_succ]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · subst i
      simp [zeroRiskAnchorRho, zeroRiskAnchorLogCoeff,
        zeroRiskAnchorTotal, Matrix.diagonal, indexBasis]
      ring
    · simp [zeroRiskAnchorRho, zeroRiskAnchorLogCoeff,
        zeroRiskAnchorTotal, Matrix.diagonal, indexBasis, hi]
  · by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · by_cases hj : j = (⟨0, by omega⟩ : Fin d)
      · exact (hij (hi.trans hj.symm)).elim
      · have hj' : (⟨0, by omega⟩ : Fin d) ≠ j := Ne.symm hj
        simp [zeroRiskAnchorRho, zeroRiskAnchorLogCoeff,
          zeroRiskAnchorTotal, Matrix.diagonal, indexBasis,
          hi, hj, hj']
    · simp [zeroRiskAnchorRho, zeroRiskAnchorLogCoeff,
        zeroRiskAnchorTotal, Matrix.diagonal, indexBasis, hij, hi]

lemma zeroRiskAnchor_target_sum_eq (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    (∑ x : (Finset.univ : Finset (Fin (d + 1))),
      zeroRiskAnchorRho eta C D x.1 •
        targetBlock
          (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp)
          (fun _ => 1) x.1) =
      Matrix.diagonal
        (zeroRiskAnchorTargetCoeff
          (⟨0, by omega⟩ : Fin d) eta C D) := by
  simp only [Finset.univ_eq_attach, Finset.sum_attach_univ]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_succ, zeroRiskAnchor_targetBlock_zero,
    zeroRiskAnchor_loggingBlock_zero]
  simp_rw [zeroRiskAnchor_targetBlock_succ,
    zeroRiskAnchor_loggingBlock_succ]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · subst i
      simp [zeroRiskAnchorRho, zeroRiskAnchorTargetCoeff,
        zeroRiskAnchorTotal, Matrix.diagonal, indexBasis, smul_eq_mul]
      ring
    · simp [zeroRiskAnchorRho, zeroRiskAnchorTargetCoeff,
        zeroRiskAnchorTotal, Matrix.diagonal, indexBasis, smul_eq_mul, hi]
  · by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · by_cases hj : j = (⟨0, by omega⟩ : Fin d)
      · exact (hij (hi.trans hj.symm)).elim
      · have hj' : (⟨0, by omega⟩ : Fin d) ≠ j := Ne.symm hj
        simp [zeroRiskAnchorRho, zeroRiskAnchorTargetCoeff,
          zeroRiskAnchorTotal, Matrix.diagonal, indexBasis, smul_eq_mul,
          hi, hj, hj']
    · simp [zeroRiskAnchorRho, zeroRiskAnchorTargetCoeff,
        zeroRiskAnchorTotal, Matrix.diagonal, indexBasis, smul_eq_mul,
        hij, hi]

lemma zeroRiskAnchor_feasible (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    FixedExperimentFeasibilitySystem
      (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp) C D := by
  let j0 : Fin d := ⟨0, by omega⟩
  refine ⟨Finset.univ, ⟨(0 : Fin (d + 1)), Finset.mem_univ _⟩,
    ⟨j0.succ, Finset.mem_univ _⟩, 1, (fun _ => 1),
    (fun x => zeroRiskAnchorRho eta C D x.1), indexBasis j0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 < indexQ eta C
    exact indexQ_pos heta (by linarith) hCexp
  · intro x a
    refine Fin.cases ?_ (fun j => ?_) x
    · rw [zeroRiskAnchor_score_zero]
      norm_num
    · rw [zeroRiskAnchor_score_succ]
      split_ifs <;> norm_num
  · intro x
    exact zeroRiskAnchorRho_pos hd heta hD hDC hCexp x
  · simpa only [Finset.univ_eq_attach, Finset.sum_attach_univ] using
      zeroRiskAnchorRho_sum hd heta hD hDC hCexp
  · rw [zeroRiskAnchor_logging_sum_eq d hd eta C D heta hC1 hD hDC hCexp]
    apply Matrix.PosDef.diagonal
    intro i
    rw [zeroRiskAnchorLogCoeff]
    apply div_pos
    · by_cases hi : i = j0
      · subst i
        simp [j0]
        exact add_pos (zeroRiskAnchorA_pos heta hD hDC hCexp)
          (indexQ_pos heta (by linarith) hCexp)
      · have hi' : i ≠ (⟨0, by omega⟩ : Fin d) := by
          simpa [j0] using hi
        simpa [hi'] using (zero_lt_one : (0 : ℝ) < 1)
    · exact zeroRiskAnchorTotal_pos hd heta hD hDC hCexp
  · intro x a ha
    refine Fin.cases ?_ (fun j => ?_) x.1
    · rw [zeroRiskAnchor_score_zero, zeroRiskAnchor_normalizer_zero]
      simp only [zeroRiskAnchorExperiment, mul_one]
      nlinarith [Real.exp_pos eta]
    · rw [zeroRiskAnchor_score_succ, zeroRiskAnchor_normalizer_succ]
      by_cases hj : j = j0
      · fin_cases a
        · simp [hj, j0, zeroRiskAnchorExperiment]
          have hexp1 : 1 < Real.exp eta := (Real.one_lt_exp_iff).2 heta
          calc
            1 ≤ Real.exp eta := hexp1.le
            _ = C * (Real.exp eta / C) := by
              field_simp [ne_of_gt (by linarith : 0 < C)]
        · simp [hj, j0, zeroRiskAnchorExperiment]
          field_simp [ne_of_gt (by linarith : 0 < C)]
          norm_num
      · simp [hj, j0, zeroRiskAnchorExperiment]
        nlinarith [Real.exp_pos eta]
  · rw [zeroRiskAnchor_score_succ, zeroRiskAnchor_normalizer_succ]
    simp [j0, zeroRiskAnchorExperiment]
    field_simp [ne_of_gt (by linarith : 0 < C)]
  · rw [zeroRiskAnchor_logging_sum_eq d hd eta C D heta hC1 hD hDC hCexp,
      zeroRiskAnchor_target_sum_eq d hd eta C D heta hC1 hD hDC hCexp]
    rw [show
      D • Matrix.diagonal
          (zeroRiskAnchorLogCoeff j0 eta C D) -
        Matrix.diagonal
          (zeroRiskAnchorTargetCoeff j0 eta C D) =
        Matrix.diagonal (fun i =>
          D * zeroRiskAnchorLogCoeff j0 eta C D i -
            zeroRiskAnchorTargetCoeff j0 eta C D i) by
      ext i k
      by_cases hik : i = k <;>
        simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal,
          smul_eq_mul, hik]]
    apply Matrix.PosSemidef.diagonal
    intro i
    by_cases hi : i = j0
    · simp [zeroRiskAnchorLogCoeff, zeroRiskAnchorTargetCoeff, hi]
      have hT := zeroRiskAnchorTotal_pos hd heta hD hDC hCexp
      field_simp [ne_of_gt hT]
      nlinarith [zeroRiskAnchor_balance (eta := eta) (C := C) hD]
    · simp [zeroRiskAnchorLogCoeff, zeroRiskAnchorTargetCoeff, hi]
      have hT := zeroRiskAnchorTotal_pos hd heta hD hDC hCexp
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hD.le (inv_nonneg.2 hT.le)
  · rw [zeroRiskAnchor_logging_sum_eq d hd eta C D heta hC1 hD hDC hCexp,
      zeroRiskAnchor_target_sum_eq d hd eta C D heta hC1 hD hDC hCexp]
    rw [show
      D • Matrix.diagonal
          (zeroRiskAnchorLogCoeff j0 eta C D) -
        Matrix.diagonal
          (zeroRiskAnchorTargetCoeff j0 eta C D) =
        Matrix.diagonal (fun i =>
          D * zeroRiskAnchorLogCoeff j0 eta C D i -
            zeroRiskAnchorTargetCoeff j0 eta C D i) by
      ext i k
      by_cases hik : i = k <;>
        simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal,
          smul_eq_mul, hik]]
    funext i
    simp only [Matrix.mulVec, dotProduct, indexBasis]
    simp
    by_cases hi : i = j0
    · subst i
      simp [zeroRiskAnchorLogCoeff, zeroRiskAnchorTargetCoeff]
      have hT := zeroRiskAnchorTotal_pos hd heta hD hDC hCexp
      field_simp [ne_of_gt hT]
      nlinarith [zeroRiskAnchor_balance (eta := eta) (C := C) hD]
    · simp [Matrix.diagonal, hi]
  · exact indexBasis_sum_sq j0

theorem zeroRiskAnchor_exactShell (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hD : 1 < D) (hDC : D < C) (hCexp : C < Real.exp eta) :
    ∃ P : BanditLaw
        (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp),
      ExactShell
        (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp)
        P C D := by
  exact (fixed_experiment_shell_certificate
    (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp) C D).1.2
      ⟨zeroRiskAnchor_bounded d hd eta C heta hC1 hCexp,
        zeroRiskAnchor_feasible d hd eta C D heta hC1 hD hDC hCexp⟩
end

end CausalSmith.Stat.ReverseKLTwoCoverage

