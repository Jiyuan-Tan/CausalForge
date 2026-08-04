import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.Certificate

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

def indexQ (eta K : ℝ) : ℝ :=
  (Real.exp eta / K - 1) / (Real.exp eta - 1)

lemma indexQ_pos {eta K : ℝ} (heta : 0 < eta) (hK : 0 < K)
    (hKexp : K < Real.exp eta) :
    0 < indexQ eta K := by
  have hexp1 : 1 < Real.exp eta := (Real.one_lt_exp_iff).2 heta
  have hdiv : 1 < Real.exp eta / K := (lt_div_iff₀ hK).2 (by
    simpa only [one_mul] using hKexp)
  exact div_pos (sub_pos.2 hdiv) (sub_pos.2 hexp1)

lemma indexQ_le_one {eta K : ℝ} (heta : 0 < eta) (hK : 1 ≤ K) :
    indexQ eta K ≤ 1 := by
  have hexp1 : 1 < Real.exp eta := (Real.one_lt_exp_iff).2 heta
  rw [indexQ, div_le_one (sub_pos.2 hexp1)]
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hdiv : Real.exp eta / K ≤ Real.exp eta := by
    exact (div_le_iff₀ hKpos).2 (by nlinarith [Real.exp_pos eta])
  linarith

lemma indexQ_normalizer {eta K : ℝ} (heta : 0 < eta) (hK : 0 < K) :
    indexQ eta K * Real.exp eta + (1 - indexQ eta K) =
      Real.exp eta / K := by
  have hden : Real.exp eta - 1 ≠ 0 :=
    ne_of_gt (sub_pos.2 ((Real.one_lt_exp_iff).2 heta))
  rw [indexQ]
  field_simp
  ring

def indexBasis {d : ℕ} (j i : Fin d) : ℝ :=
  if i = j then 1 else 0

lemma indexBasis_sum_sq {d : ℕ} (j : Fin d) :
    ∑ i, (indexBasis j i) ^ 2 = 1 := by
  simp [indexBasis]

lemma indexBasis_dot_one {d : ℕ} (j : Fin d) :
    ∑ i, indexBasis j i * (1 : ℝ) = 1 := by
  simp [indexBasis]

def diagonalIndexFeature {d : ℕ} (x : Fin d) (a : Fin 2) (i : Fin d) : ℝ :=
  if a = 1 then indexBasis x i else 0

def diagonalIndexReference {d : ℕ} (eta K : ℝ)
    (_x : Fin d) (a : Fin 2) : ℝ :=
  if a = 1 then indexQ eta K else 1 - indexQ eta K

def diagonalIndexExperiment (d : ℕ) (hd : 4 ≤ d)
    (eta K : ℝ) (heta : 0 < eta) (hK : 1 ≤ K)
    (hKexp : K < Real.exp eta) :
    CommonExperiment d (Fin d) (Fin 2) where
  feature := diagonalIndexFeature
  reference := diagonalIndexReference eta K
  eta := eta
  reference_isPolicy := by
    constructor
    · intro x a
      fin_cases a
      · simp [diagonalIndexReference, indexQ_le_one heta hK]
      · simp [diagonalIndexReference,
          (indexQ_pos heta (by linarith) hKexp).le]
    · intro x
      simp [Fin.sum_univ_two, diagonalIndexReference]
  eta_pos := heta
  dim_ge_four := hd

lemma diagonalIndex_bounded (d : ℕ) (hd : 4 ≤ d)
    (eta K : ℝ) (heta : 0 < eta) (hK : 1 ≤ K)
    (hKexp : K < Real.exp eta) :
    BoundedFeatures (diagonalIndexExperiment d hd eta K heta hK hKexp) := by
  intro x a
  fin_cases a
  · simp [diagonalIndexExperiment, diagonalIndexFeature]
  · simp [diagonalIndexExperiment, diagonalIndexFeature,
      indexBasis_sum_sq]

lemma diagonalIndex_score (d : ℕ) (hd : 4 ≤ d)
    (eta K : ℝ) (heta : 0 < eta) (hK : 1 ≤ K)
    (hKexp : K < Real.exp eta)
    (x : Fin d) (a : Fin 2) :
    ∑ i, (diagonalIndexExperiment d hd eta K heta hK hKexp).feature x a i *
      (1 : ℝ) = if a = 1 then 1 else 0 := by
  fin_cases a
  · simp [diagonalIndexExperiment, diagonalIndexFeature]
  · simpa [diagonalIndexExperiment, diagonalIndexFeature] using
      indexBasis_dot_one x

lemma diagonalIndex_normalizer (d : ℕ) (hd : 4 ≤ d)
    (eta K : ℝ) (heta : 0 < eta) (hK : 1 ≤ K)
    (hKexp : K < Real.exp eta)
    (x : Fin d) :
    candidateNormalizer (diagonalIndexExperiment d hd eta K heta hK hKexp)
      (fun _ => 1) x = Real.exp eta / K := by
  simp only [candidateNormalizer, Fin.sum_univ_two]
  rw [diagonalIndex_score, diagonalIndex_score]
  norm_num [diagonalIndexExperiment, diagonalIndexReference]
  nlinarith [indexQ_normalizer (K := K) heta (by linarith)]

lemma diagonalIndex_loggingBlock (d : ℕ) (hd : 4 ≤ d)
    (eta K : ℝ) (heta : 0 < eta) (hK : 1 ≤ K)
    (hKexp : K < Real.exp eta)
    (x : Fin d) :
    loggingBlock (diagonalIndexExperiment d hd eta K heta hK hKexp) x =
      fun i j => indexQ eta K * (indexBasis x i * indexBasis x j) := by
  ext i j
  simp [loggingBlock, Fin.sum_univ_two, diagonalIndexExperiment,
    diagonalIndexReference, diagonalIndexFeature]

lemma diagonalIndex_targetBlock (d : ℕ) (hd : 4 ≤ d)
    (eta K : ℝ) (heta : 0 < eta) (hK : 1 ≤ K)
    (hKexp : K < Real.exp eta) (x : Fin d) :
    targetBlock (diagonalIndexExperiment d hd eta K heta hK hKexp)
        (fun _ => 1) x =
      K • loggingBlock (diagonalIndexExperiment d hd eta K heta hK hKexp) x := by
  ext i j
  simp only [targetBlock, Fin.sum_univ_two]
  rw [diagonalIndex_loggingBlock]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [show candidateWeight (diagonalIndexExperiment d hd eta K heta hK hKexp)
      (fun _ => 1) x 1 = K by
    rw [candidateWeight, diagonalIndex_score,
      diagonalIndex_normalizer]
    simp [diagonalIndexExperiment]]
  simp [diagonalIndexExperiment, diagonalIndexReference,
    diagonalIndexFeature]
  ring

def diagonalIndexRho {d : ℕ} (hdpos : 0 < d) (_x : Fin d) : ℝ :=
  1 / d

lemma diagonalIndexRho_pos {d : ℕ} (hdpos : 0 < d) (x : Fin d) :
    0 < diagonalIndexRho hdpos x := by
  simp [diagonalIndexRho, hdpos]

lemma diagonalIndexRho_sum {d : ℕ} (hdpos : 0 < d) :
    ∑ x : Fin d, diagonalIndexRho hdpos x = 1 := by
  simp [diagonalIndexRho, Nat.cast_ne_zero.2 (ne_of_gt hdpos)]

lemma diagonalIndex_logging_posDef (d : ℕ) (hd : 4 ≤ d)
    (eta K : ℝ) (heta : 0 < eta) (hK : 1 ≤ K)
    (hKexp : K < Real.exp eta) :
    Matrix.PosDef
      (∑ x : (Finset.univ : Finset (Fin d)),
        diagonalIndexRho (by omega : 0 < d) x.1 •
          loggingBlock
            (diagonalIndexExperiment d hd eta K heta hK hKexp) x.1) := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (sum_loggingBlock_isHermitian
      (diagonalIndexExperiment d hd eta K heta hK hKexp) Finset.univ
      (fun x => diagonalIndexRho (by omega : 0 < d) x.1))
  intro v hv
  rw [← quadraticForm_eq_dotProduct_mulVec]
  simp only [quadraticForm, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    diagonalIndex_loggingBlock, diagonalIndexRho]
  have hq : 0 < indexQ eta K :=
    indexQ_pos heta (by linarith) hKexp
  have hvpos : 0 < ∑ i, (v i) ^ 2 :=
    sum_sq_pos_of_ne_zero v hv
  simp_rw [indexBasis]
  simp
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hcoef : 0 < (d : ℝ)⁻¹ * indexQ eta K :=
    mul_pos (inv_pos.2 hdreal) hq
  have heq :
      (∑ x, v x * ((d : ℝ)⁻¹ * indexQ eta K) * v x) =
        ((d : ℝ)⁻¹ * indexQ eta K) * ∑ x, (v x) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  exact mul_pos hcoef hvpos

lemma diagonalIndex_feasible (d : ℕ) (hd : 4 ≤ d)
    (eta K : ℝ) (heta : 0 < eta) (hK : 1 ≤ K)
    (hKexp : K < Real.exp eta) :
    FixedExperimentFeasibilitySystem
      (diagonalIndexExperiment d hd eta K heta hK hKexp) K K := by
  refine ⟨Finset.univ, ⟨⟨0, by omega⟩, Finset.mem_univ _⟩,
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩, 1,
    (fun _ => 1), (fun _ => 1 / d), indexBasis ⟨0, by omega⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact indexQ_pos heta (by linarith) hKexp
  · intro x a
    rw [diagonalIndex_score]
    split_ifs <;> norm_num
  · intro x
    exact diagonalIndexRho_pos (by omega) x
  · simp [Nat.cast_ne_zero.2 (by omega : d ≠ 0)]
  · simpa [diagonalIndexRho] using
      diagonalIndex_logging_posDef d hd eta K heta hK hKexp
  · intro x a ha
    rw [diagonalIndex_score, diagonalIndex_normalizer]
    fin_cases a
    · norm_num
      have hexp1 : 1 < Real.exp eta := (Real.one_lt_exp_iff).2 heta
      have hKpos : 0 < K := by linarith
      calc
        1 ≤ Real.exp eta := hexp1.le
        _ = K * (Real.exp eta / K) := by
          field_simp [ne_of_gt hKpos]
    · norm_num
      change Real.exp eta ≤ K * (Real.exp eta / K)
      field_simp [ne_of_gt (by linarith : 0 < K)]
      norm_num
  · rw [diagonalIndex_score, diagonalIndex_normalizer]
    norm_num
    change Real.exp eta = K * (Real.exp eta / K)
    field_simp [ne_of_gt (by linarith : 0 < K)]
  · have hTG :
        (∑ x : (Finset.univ : Finset (Fin d)), (1 / d : ℝ) •
            targetBlock (diagonalIndexExperiment d hd eta K heta hK hKexp)
              (fun _ => 1) x.1) =
          K • (∑ x : (Finset.univ : Finset (Fin d)), (1 / d : ℝ) •
            loggingBlock
              (diagonalIndexExperiment d hd eta K heta hK hKexp) x.1) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [diagonalIndex_targetBlock d hd eta K heta hK hKexp]
      simp [smul_smul, mul_comm]
    rw [hTG]
    simpa using (Matrix.PosSemidef.zero :
      Matrix.PosSemidef (0 : Matrix (Fin d) (Fin d) ℝ))
  · have hTG :
        (∑ x : (Finset.univ : Finset (Fin d)), (1 / d : ℝ) •
            targetBlock (diagonalIndexExperiment d hd eta K heta hK hKexp)
              (fun _ => 1) x.1) =
          K • (∑ x : (Finset.univ : Finset (Fin d)), (1 / d : ℝ) •
            loggingBlock
              (diagonalIndexExperiment d hd eta K heta hK hKexp) x.1) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [diagonalIndex_targetBlock d hd eta K heta hK hKexp]
      simp [smul_smul, mul_comm]
    rw [hTG]
    simp
  · exact indexBasis_sum_sq ⟨0, by omega⟩

theorem diagonalIndex_exactShell (d : ℕ) (hd : 4 ≤ d)
    (eta K : ℝ) (heta : 0 < eta) (hK : 1 ≤ K)
    (hKexp : K < Real.exp eta) :
    ∃ P : BanditLaw (diagonalIndexExperiment d hd eta K heta hK hKexp),
      ExactShell (diagonalIndexExperiment d hd eta K heta hK hKexp) P K K := by
  exact (fixed_experiment_shell_certificate
    (diagonalIndexExperiment d hd eta K heta hK hKexp) K K).1.2
      ⟨diagonalIndex_bounded d hd eta K heta hK hKexp,
        diagonalIndex_feasible d hd eta K heta hK hKexp⟩

end

end CausalSmith.Stat.ReverseKLTwoCoverage
