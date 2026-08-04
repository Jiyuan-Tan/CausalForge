import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegionConstruction

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def zeroRiskCoreFeature {d : ℕ} (j0 : Fin d)
    (x : Fin d) (a : Fin 2) (i : Fin d) : ℝ :=
  if x = j0 then diagonalIndexFeature x a i else indexBasis x i

def zeroRiskCoreReference {d : ℕ} (j0 : Fin d) (eta C : ℝ)
    (x : Fin d) (a : Fin 2) : ℝ :=
  if x = j0 then diagonalIndexReference eta C x a else 1 / 2

def zeroRiskCoreExperiment (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    CommonExperiment d (Fin d) (Fin 2) where
  feature := zeroRiskCoreFeature ⟨0, by omega⟩
  reference := zeroRiskCoreReference ⟨0, by omega⟩ eta C
  eta := eta
  reference_isPolicy := by
    constructor
    · intro x a
      by_cases hx : x = (⟨0, by omega⟩ : Fin d)
      · subst x
        fin_cases a
        · simp [zeroRiskCoreReference, diagonalIndexReference,
            indexQ_le_one heta hC1.le]
        · simp [zeroRiskCoreReference, diagonalIndexReference,
            (indexQ_pos heta (by linarith : 0 < C) hCexp).le]
      · fin_cases a <;> norm_num [zeroRiskCoreReference, hx]
    · intro x
      by_cases hx : x = (⟨0, by omega⟩ : Fin d)
      · subst x
        simp [Fin.sum_univ_two, zeroRiskCoreReference,
          diagonalIndexReference]
      · simp [Fin.sum_univ_two, zeroRiskCoreReference, hx]
  eta_pos := heta
  dim_ge_four := hd

lemma zeroRiskCore_bounded (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    BoundedFeatures
      (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp) := by
  intro x a
  by_cases hx : x = (⟨0, by omega⟩ : Fin d)
  · subst x
    fin_cases a
    · simp [zeroRiskCoreExperiment, zeroRiskCoreFeature,
        diagonalIndexFeature]
    · simp [zeroRiskCoreExperiment, zeroRiskCoreFeature,
        diagonalIndexFeature, indexBasis_sum_sq]
  · simp [zeroRiskCoreExperiment, zeroRiskCoreFeature, hx,
      indexBasis_sum_sq]

lemma zeroRiskCore_score (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (x : Fin d) (a : Fin 2) :
    ∑ i, (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp).feature
      x a i * (1 : ℝ) =
        if x = (⟨0, by omega⟩ : Fin d) then
          if a = 1 then 1 else 0
        else 1 := by
  by_cases hx : x = (⟨0, by omega⟩ : Fin d)
  · subst x
    fin_cases a
    · simp [zeroRiskCoreExperiment, zeroRiskCoreFeature,
        diagonalIndexFeature]
    · simpa [zeroRiskCoreExperiment, zeroRiskCoreFeature,
        diagonalIndexFeature] using
        indexBasis_dot_one (⟨0, by omega⟩ : Fin d)
  · simpa [zeroRiskCoreExperiment, zeroRiskCoreFeature, hx] using
      indexBasis_dot_one x

lemma zeroRiskCore_normalizer (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (x : Fin d) :
    candidateNormalizer
      (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp)
      (fun _ => 1) x =
        if x = (⟨0, by omega⟩ : Fin d) then Real.exp eta / C
        else Real.exp eta := by
  by_cases hx : x = (⟨0, by omega⟩ : Fin d)
  · subst x
    simp only [candidateNormalizer, Fin.sum_univ_two]
    rw [zeroRiskCore_score, zeroRiskCore_score]
    norm_num [zeroRiskCoreExperiment, zeroRiskCoreReference,
      diagonalIndexReference]
    nlinarith [indexQ_normalizer (eta := eta) (K := C) heta
      (by linarith : 0 < C)]
  · simp only [candidateNormalizer, Fin.sum_univ_two]
    rw [zeroRiskCore_score, zeroRiskCore_score]
    norm_num [zeroRiskCoreExperiment, zeroRiskCoreReference, hx]
    ring

lemma zeroRiskCore_loggingBlock (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (x : Fin d) :
    loggingBlock
      (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp) x =
        fun i j =>
          (if x = (⟨0, by omega⟩ : Fin d) then indexQ eta C else 1) *
            (indexBasis x i * indexBasis x j) := by
  ext i j
  by_cases hx : x = (⟨0, by omega⟩ : Fin d)
  · subst x
    simp [loggingBlock, zeroRiskCoreExperiment, zeroRiskCoreReference,
      zeroRiskCoreFeature, diagonalIndexReference, diagonalIndexFeature]
  · simp [loggingBlock, zeroRiskCoreExperiment, zeroRiskCoreReference,
      zeroRiskCoreFeature, hx]

lemma zeroRiskCore_targetBlock (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (x : Fin d) :
    targetBlock
      (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp)
      (fun _ => 1) x =
        (if x = (⟨0, by omega⟩ : Fin d) then C else 1) •
          loggingBlock
            (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp) x := by
  ext i j
  by_cases hx : x = (⟨0, by omega⟩ : Fin d)
  · subst x
    simp only [targetBlock, Fin.sum_univ_two]
    rw [zeroRiskCore_loggingBlock]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [show candidateWeight
        (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp)
        (fun _ => 1) (⟨0, by omega⟩ : Fin d) 1 = C by
      rw [candidateWeight, zeroRiskCore_score, zeroRiskCore_normalizer]
      simp [zeroRiskCoreExperiment]]
    simp [zeroRiskCoreExperiment, zeroRiskCoreReference,
      zeroRiskCoreFeature, diagonalIndexReference, diagonalIndexFeature]
    ring
  · simp only [targetBlock, Fin.sum_univ_two]
    rw [zeroRiskCore_loggingBlock]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [show candidateWeight
        (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp)
        (fun _ => 1) x 0 = 1 by
      rw [candidateWeight, zeroRiskCore_score, zeroRiskCore_normalizer]
      simp [zeroRiskCoreExperiment, hx],
      show candidateWeight
        (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp)
        (fun _ => 1) x 1 = 1 by
      rw [candidateWeight, zeroRiskCore_score, zeroRiskCore_normalizer]
      simp [zeroRiskCoreExperiment, hx]]
    simp [zeroRiskCoreExperiment, zeroRiskCoreReference,
      zeroRiskCoreFeature, hx]
    ring

def zeroRiskCoreLogCoeff {d : ℕ} (j0 : Fin d)
    (eta C : ℝ) (i : Fin d) : ℝ :=
  (if i = j0 then indexQ eta C else 1) / d

def zeroRiskCoreTargetCoeff {d : ℕ} (j0 : Fin d)
    (eta C : ℝ) (i : Fin d) : ℝ :=
  (if i = j0 then C * indexQ eta C else 1) / d

lemma zeroRiskCore_logging_sum_eq (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    (∑ x : (Finset.univ : Finset (Fin d)), (1 / d : ℝ) •
      loggingBlock
        (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp) x.1) =
      Matrix.diagonal
        (zeroRiskCoreLogCoeff (⟨0, by omega⟩ : Fin d) eta C) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [zeroRiskCore_loggingBlock]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · simp [zeroRiskCoreLogCoeff, indexBasis, hi]
      ring
    · simp [zeroRiskCoreLogCoeff, indexBasis, hi]
  · simp [zeroRiskCoreLogCoeff, Matrix.diagonal, indexBasis, hij]

lemma zeroRiskCore_target_sum_eq (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    (∑ x : (Finset.univ : Finset (Fin d)), (1 / d : ℝ) •
      targetBlock
        (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp)
        (fun _ => 1) x.1) =
      Matrix.diagonal
        (zeroRiskCoreTargetCoeff (⟨0, by omega⟩ : Fin d) eta C) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [zeroRiskCore_targetBlock, zeroRiskCore_loggingBlock]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = (⟨0, by omega⟩ : Fin d)
    · simp [zeroRiskCoreTargetCoeff, indexBasis, hi]
      ring
    · simp [zeroRiskCoreTargetCoeff, indexBasis, hi]
  · simp [zeroRiskCoreTargetCoeff, Matrix.diagonal, indexBasis, hij]

lemma zeroRiskCore_feasible (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    FixedExperimentFeasibilitySystem
      (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp) C C := by
  let j0 : Fin d := ⟨0, by omega⟩
  refine ⟨Finset.univ, ⟨j0, Finset.mem_univ _⟩,
    ⟨j0, Finset.mem_univ _⟩, 1, (fun _ => 1),
    (fun _ => 1 / d), indexBasis j0, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · change 0 < indexQ eta C
    exact indexQ_pos heta (by linarith) hCexp
  · intro x a
    rw [zeroRiskCore_score]
    split_ifs <;> norm_num
  · intro x
    positivity
  · simp [Nat.cast_ne_zero.2 (by omega : d ≠ 0)]
  · rw [zeroRiskCore_logging_sum_eq]
    apply Matrix.PosDef.diagonal
    intro i
    rw [zeroRiskCoreLogCoeff]
    apply div_pos
    · split_ifs
      · exact indexQ_pos heta (by linarith) hCexp
      · positivity
    · positivity
  · intro x a ha
    rw [zeroRiskCore_score, zeroRiskCore_normalizer]
    by_cases hx : x.1 = j0
    · fin_cases a
      · simp [hx, j0, zeroRiskCoreExperiment]
        have hexp1 : 1 < Real.exp eta := (Real.one_lt_exp_iff).2 heta
        calc
          1 ≤ Real.exp eta := hexp1.le
          _ = C * (Real.exp eta / C) := by
            field_simp [ne_of_gt (by linarith : 0 < C)]
      · simp [hx, j0, zeroRiskCoreExperiment]
        field_simp [ne_of_gt (by linarith : 0 < C)]
        norm_num
    · simp [hx, j0, zeroRiskCoreExperiment]
      nlinarith [Real.exp_pos eta]
  · rw [zeroRiskCore_score, zeroRiskCore_normalizer]
    simp [j0, zeroRiskCoreExperiment]
    field_simp [ne_of_gt (by linarith : 0 < C)]
  · rw [zeroRiskCore_logging_sum_eq, zeroRiskCore_target_sum_eq]
    rw [show
      C • Matrix.diagonal
          (zeroRiskCoreLogCoeff (⟨0, by omega⟩ : Fin d) eta C) -
        Matrix.diagonal
          (zeroRiskCoreTargetCoeff (⟨0, by omega⟩ : Fin d) eta C) =
        Matrix.diagonal (fun i =>
          C * zeroRiskCoreLogCoeff (⟨0, by omega⟩ : Fin d) eta C i -
            zeroRiskCoreTargetCoeff
              (⟨0, by omega⟩ : Fin d) eta C i) by
      ext i k
      by_cases hik : i = k <;>
        simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal,
          smul_eq_mul, hik]]
    apply Matrix.PosSemidef.diagonal
    intro i
    by_cases hi : i = j0
    · simp [zeroRiskCoreLogCoeff, zeroRiskCoreTargetCoeff, hi, j0]
      have heq :
          C * indexQ eta C / (d : ℝ) =
            C * (indexQ eta C / (d : ℝ)) := by ring
      exact heq.le
    · simp [zeroRiskCoreLogCoeff, zeroRiskCoreTargetCoeff, hi, j0]
      have hdpos : (0 : ℝ) < d := by positivity
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hC1.le (inv_nonneg.2 hdpos.le)
  · rw [zeroRiskCore_logging_sum_eq, zeroRiskCore_target_sum_eq]
    rw [show
      C • Matrix.diagonal
          (zeroRiskCoreLogCoeff (⟨0, by omega⟩ : Fin d) eta C) -
        Matrix.diagonal
          (zeroRiskCoreTargetCoeff (⟨0, by omega⟩ : Fin d) eta C) =
        Matrix.diagonal (fun i =>
          C * zeroRiskCoreLogCoeff (⟨0, by omega⟩ : Fin d) eta C i -
            zeroRiskCoreTargetCoeff
              (⟨0, by omega⟩ : Fin d) eta C i) by
      ext i k
      by_cases hik : i = k <;>
        simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal,
          smul_eq_mul, hik]]
    funext i
    simp only [Matrix.mulVec, dotProduct, indexBasis]
    simp
    by_cases hi : i = j0
    · subst i
      simp [zeroRiskCoreLogCoeff, zeroRiskCoreTargetCoeff, j0]
      ring
    · simp [Matrix.diagonal, hi]
  · exact indexBasis_sum_sq j0

theorem zeroRiskCore_exactShell (d : ℕ) (hd : 4 ≤ d)
    (eta C : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    ∃ P : BanditLaw (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp),
      ExactShell (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp)
        P C C := by
  exact (fixed_experiment_shell_certificate
    (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp) C C).1.2
      ⟨zeroRiskCore_bounded d hd eta C heta hC1 hCexp,
        zeroRiskCore_feasible d hd eta C heta hC1 hCexp⟩

end

end CausalSmith.Stat.ReverseKLTwoCoverage

