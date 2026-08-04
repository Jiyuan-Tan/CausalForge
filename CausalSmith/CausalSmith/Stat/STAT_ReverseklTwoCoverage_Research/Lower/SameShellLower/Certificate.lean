import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Weights
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.FeasibilityRealization

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

lemma hard_plus_norm_sq {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) :
    ∑ i, ((hardBasisU hd j i + hardBasisW hd j i) / Real.sqrt 2) ^ 2 = 1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have horth := (hardBasis_coordinate_orthonormal hd).1 j
  have hu : ∑ i, (hardBasisU hd j i) ^ 2 = 1 := by
    simpa [dotProduct, pow_two] using horth.2.2.1
  have hw : ∑ i, (hardBasisW hd j i) ^ 2 = 1 := by
    simpa [dotProduct, pow_two] using horth.2.2.2.1
  have huw : ∑ i, hardBasisU hd j i * hardBasisW hd j i = 0 := by
    simpa [dotProduct] using horth.2.2.2.2
  rw [show (∑ i,
      ((hardBasisU hd j i + hardBasisW hd j i) / Real.sqrt 2) ^ 2) =
      ((∑ i, (hardBasisU hd j i) ^ 2) +
        2 * (∑ i, hardBasisU hd j i * hardBasisW hd j i) +
        ∑ i, (hardBasisW hd j i) ^ 2) / (Real.sqrt 2) ^ 2 by
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    congr 1
    simp_rw [add_sq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]]
  rw [hu, hw, huw, hs]
  norm_num

lemma hard_minus_norm_sq {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) :
    ∑ i, ((hardBasisU hd j i - hardBasisW hd j i) / Real.sqrt 2) ^ 2 = 1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have horth := (hardBasis_coordinate_orthonormal hd).1 j
  have hu : ∑ i, (hardBasisU hd j i) ^ 2 = 1 := by
    simpa [dotProduct, pow_two] using horth.2.2.1
  have hw : ∑ i, (hardBasisW hd j i) ^ 2 = 1 := by
    simpa [dotProduct, pow_two] using horth.2.2.2.1
  have huw : ∑ i, hardBasisU hd j i * hardBasisW hd j i = 0 := by
    simpa [dotProduct] using horth.2.2.2.2
  rw [show (∑ i,
      ((hardBasisU hd j i - hardBasisW hd j i) / Real.sqrt 2) ^ 2) =
      ((∑ i, (hardBasisU hd j i) ^ 2) -
        2 * (∑ i, hardBasisU hd j i * hardBasisW hd j i) +
        ∑ i, (hardBasisW hd j i) ^ 2) / (Real.sqrt 2) ^ 2 by
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    congr 1
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]]
  rw [hu, hw, huw, hs]
  norm_num

lemma hard_boundedFeatures {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    BoundedFeatures
      (hardExperiment d hd eta C D heta hD hDC hCexp) := by
  intro x a
  let y := (hardContextEquiv d C D).symm x
  change Real.sqrt
      (∑ i, (hardFeatureOnContext hd y a i) ^ 2) ≤ 1
  rcases y with j | (hcal | (hanchor | hz))
  · fin_cases a
    · simp [hardFeatureOnContext, hardPlus, hardMinus]
      rw [hard_plus_norm_sq hd j]
    · simp [hardFeatureOnContext, hardPlus, hardMinus]
      rw [hard_minus_norm_sq hd j]
    · simp [hardFeatureOnContext, hardPlus, hardMinus]
  · fin_cases a <;>
      simp [hardFeatureOnContext, hardPlus, hardMinus, hardZero,
        hardBasisE0, indexBasis]
  · simp [hardFeatureOnContext, hardBasisE0, indexBasis]
  · have heven : Even d := by
      by_contra hneven
      have hzlt := hz.isLt
      simp [hneven] at hzlt
    simp [hardFeatureOnContext, hardBasisZ, heven, indexBasis]

lemma hardBasis_projection_exists {d : ℕ} (hd : 4 ≤ d)
    (y : Fin d → ℝ) (hy : y ≠ 0) :
    dotProduct y (hardBasisE0 hd) ≠ 0 ∨
      (∃ j, dotProduct y (hardBasisU hd j) ≠ 0 ∨
        dotProduct y (hardBasisW hd j) ≠ 0) ∨
      (Even d ∧ dotProduct y (hardBasisZ hd) ≠ 0) := by
  by_contra h
  push_neg at h
  apply hy
  funext i
  rw [hardBasis_decomposition hd y i, h.1]
  simp only [zero_mul, zero_add]
  have hj : ∀ j,
      dotProduct y (hardBasisU hd j) = 0 ∧
        dotProduct y (hardBasisW hd j) = 0 := by
    intro j
    exact ⟨h.2.1 j |>.1, h.2.1 j |>.2⟩
  simp_rw [(hj _).1, (hj _).2, zero_mul, zero_add]
  by_cases heven : Even d
  · have hz : dotProduct y (hardBasisZ hd) = 0 := by
      by_contra hz
      exact hz (h.2.2 heven)
    simp [heven, hz]
  · simp [heven]

lemma hard_logging_posDef {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    Matrix.PosDef
      (∑ x,
        hardRho (d := d) (C := C) (D := D) (eta := eta) x •
          loggingBlock
            (hardExperiment d hd eta C D heta hD hDC hCexp) x) := by
  let E := hardExperiment d hd eta C D heta hD hDC hCexp
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [Finset.univ_eq_attach, Finset.sum_attach_univ] using
      sum_loggingBlock_isHermitian E (Finset.univ)
        (fun x : (Finset.univ : Finset (Fin (hardContextCard d C D))) =>
          hardRho (d := d) (C := C) (D := D) (eta := eta) x.1)
  · intro y hy
    rw [← quadraticForm_eq_dotProduct_mulVec,
      quadraticForm_sum_blocks]
    apply Finset.sum_pos'
    · intro x _
      apply mul_nonneg (hardRho_nonneg hd heta hD hDC hCexp x)
      rw [loggingBlock_quadratic]
      exact Finset.sum_nonneg (fun a _ =>
        mul_nonneg (E.reference_isPolicy.1 x a)
          (sq_nonneg _))
    · rcases hardBasis_projection_exists hd y hy with he0 | huwv | hz
      · refine ⟨hardContextEquiv d C D hardContextCalibration,
          Finset.mem_univ _, ?_⟩
        apply mul_pos (hardRho_pos hd heta hD hDC hCexp _)
        rw [hard_loggingBlock_quadratic_on_carrier hd heta hD hDC hCexp
          hardContextCalibration y]
        exact mul_pos (hardQ_pos heta hD hDC hCexp) (sq_pos_of_ne_zero he0)
      · rcases huwv with ⟨j, hu | hw⟩
        · refine ⟨hardContextEquiv d C D (hardContextHard j),
            Finset.mem_univ _, ?_⟩
          apply mul_pos (hardRho_pos hd heta hD hDC hCexp _)
          rw [hard_loggingBlock_quadratic_on_carrier hd heta hD hDC hCexp
            (hardContextHard j) y]
          exact mul_pos (hardP_pos hD)
            (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hu) (sq_nonneg _))
        · refine ⟨hardContextEquiv d C D (hardContextHard j),
            Finset.mem_univ _, ?_⟩
          apply mul_pos (hardRho_pos hd heta hD hDC hCexp _)
          rw [hard_loggingBlock_quadratic_on_carrier hd heta hD hDC hCexp
            (hardContextHard j) y]
          exact mul_pos (hardP_pos hD)
            (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hw))
      · rcases hz with ⟨heven, hz⟩
        let zindex : Fin (if Even d then 1 else 0) := ⟨0, by simp [heven]⟩
        refine ⟨hardContextEquiv d C D
            (Sum.inr (Sum.inr (Sum.inr zindex))),
          Finset.mem_univ _, ?_⟩
        apply mul_pos (hardRho_pos hd heta hD hDC hCexp _)
        rw [hard_loggingBlock_quadratic_on_carrier hd heta hD hDC hCexp
          (Sum.inr (Sum.inr (Sum.inr zindex))) y]
        exact sq_pos_of_ne_zero hz

lemma hard_targetBlock_quadratic_calibration {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool) (y : Fin d → ℝ) :
    quadraticForm
        (targetBlock
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardTheta hd D eta gamma v)
          (hardContextEquiv d C D hardContextCalibration)) y =
      C * hardQ C eta * dotProduct y (hardBasisE0 hd) ^ 2 := by
  rw [targetBlock_quadratic]
  simp only [Fin.sum_univ_succ]
  rw [show candidateWeight
        (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardTheta hd D eta gamma v)
        (hardContextEquiv d C D hardContextCalibration) (0 : Fin 3) = C by
    simpa [hardPlus] using
      hard_calibration_candidateWeight_plus hd heta hD hDC hCexp v]
  norm_num [hardExperiment, hardContextCalibration,
    hardFeatureOnContext, hardPlus, hardMinus, hardZero,
    hardReferenceOnContext]
  simp only [show (2 : Fin 3) ≠ 0 by decide, if_false]
  rw [show (∑ i, hardBasisE0 hd i * y i) =
      dotProduct y (hardBasisE0 hd) by
    rw [dotProduct_comm]
    rfl]
  ring

lemma hard_targetBlock_quadratic_anchor {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (x : Fin (if C > D then 1 else 0)) (y : Fin d → ℝ) :
    quadraticForm
        (targetBlock
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardTheta hd D eta gamma v)
          (hardContextEquiv d C D
            (Sum.inr (Sum.inr (Sum.inl x))))) y =
      dotProduct y (hardBasisE0 hd) ^ 2 := by
  rw [targetBlock_quadratic]
  simp_rw [hard_constant_candidateWeight_anchor hd heta hD hDC hCexp v x]
  norm_num [Fin.sum_univ_succ, hardExperiment, hardFeatureOnContext,
    hardReferenceOnContext]
  rw [show (∑ i, hardBasisE0 hd i * y i) =
      dotProduct y (hardBasisE0 hd) by
    rw [dotProduct_comm]
    rfl]
  ring

lemma hard_targetBlock_quadratic_residual {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (x : Fin (if Even d then 1 else 0)) (y : Fin d → ℝ) :
    quadraticForm
        (targetBlock
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardTheta hd D eta gamma v)
          (hardContextEquiv d C D
            (Sum.inr (Sum.inr (Sum.inr x))))) y =
      dotProduct y (hardBasisZ hd) ^ 2 := by
  rw [targetBlock_quadratic]
  simp_rw [hard_constant_candidateWeight_residual hd heta hD hDC hCexp v x]
  norm_num [Fin.sum_univ_succ, hardExperiment, hardFeatureOnContext,
    hardReferenceOnContext]
  rw [show (∑ i, hardBasisZ hd i * y i) =
      dotProduct y (hardBasisZ hd) by
    rw [dotProduct_comm]
    rfl]
  ring

lemma hard_targetBlock_le_hard_logging {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hgamma : 0 ≤ gamma)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) (y : Fin d → ℝ) :
    quadraticForm
        (targetBlock
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardTheta hd D eta gamma v)
          (hardContextEquiv d C D (hardContextHard j))) y ≤
      D * quadraticForm
        (loggingBlock
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardContextEquiv d C D (hardContextHard j))) y := by
  rw [targetBlock_quadratic, loggingBlock_quadratic, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hw := hard_hard_candidateWeight_le hd heta hD hDC hCexp hgamma
    hden hgammaBeta v j a
  have href :=
    (hardExperiment d hd eta C D heta hD hDC hCexp).reference_isPolicy.1
      (hardContextEquiv d C D (hardContextHard j)) a
  have hs := sq_nonneg
    (∑ i,
      (hardExperiment d hd eta C D heta hD hDC hCexp).feature
        (hardContextEquiv d C D (hardContextHard j)) a i * y i)
  calc
    ((hardExperiment d hd eta C D heta hD hDC hCexp).reference
          (hardContextEquiv d C D (hardContextHard j)) a *
        candidateWeight
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardTheta hd D eta gamma v)
          (hardContextEquiv d C D (hardContextHard j)) a) *
        (∑ i,
          (hardExperiment d hd eta C D heta hD hDC hCexp).feature
            (hardContextEquiv d C D (hardContextHard j)) a i * y i) ^ 2 ≤
      ((hardExperiment d hd eta C D heta hD hDC hCexp).reference
          (hardContextEquiv d C D (hardContextHard j)) a * D) *
        (∑ i,
          (hardExperiment d hd eta C D heta hD hDC hCexp).feature
            (hardContextEquiv d C D (hardContextHard j)) a i * y i) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw href) hs
    _ = D *
        ((hardExperiment d hd eta C D heta hD hDC hCexp).reference
          (hardContextEquiv d C D (hardContextHard j)) a *
        (∑ i,
          (hardExperiment d hd eta C D heta hD hDC hCexp).feature
            (hardContextEquiv d C D (hardContextHard j)) a i * y i) ^ 2) := by
      ring

lemma hard_targetBlock_quadratic_on_carrier {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (x : HardContextCarrier d C D) (y : Fin d → ℝ) :
    quadraticForm
        (targetBlock
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardTheta hd D eta gamma v)
          (hardContextEquiv d C D x)) y =
      match x with
      | Sum.inl j =>
          quadraticForm
            (targetBlock
              (hardExperiment d hd eta C D heta hD hDC hCexp)
              (hardTheta hd D eta gamma v)
              (hardContextEquiv d C D (hardContextHard j))) y
      | Sum.inr (Sum.inl _) =>
          C * hardQ C eta * dotProduct y (hardBasisE0 hd) ^ 2
      | Sum.inr (Sum.inr (Sum.inl _)) =>
          dotProduct y (hardBasisE0 hd) ^ 2
      | Sum.inr (Sum.inr (Sum.inr _)) =>
          dotProduct y (hardBasisZ hd) ^ 2 := by
  rcases x with j | (hcal | (hanchor | hz))
  · rfl
  · have hcal0 : hcal = 0 := Subsingleton.elim _ _
    subst hcal
    exact hard_targetBlock_quadratic_calibration hd heta hD hDC hCexp v y
  · exact hard_targetBlock_quadratic_anchor hd heta hD hDC hCexp v hanchor y
  · exact hard_targetBlock_quadratic_residual hd heta hD hDC hCexp v hz y

lemma hardRho_weighted_sum_carrier {d : ℕ} {eta C D : ℝ}
    (f : Fin (hardContextCard d C D) → ℝ) :
    (∑ x,
        hardRho (d := d) (C := C) (D := D) (eta := eta) x * f x) =
      ∑ y : HardContextCarrier d C D,
        (hardContextRawMass (eta := eta) y / hardTotal d C D eta) *
          f (hardContextEquiv d C D y) := by
  simpa [hardRho] using
    (Equiv.sum_comp (hardContextEquiv d C D).symm
      (fun y : HardContextCarrier d C D =>
        (hardContextRawMass (eta := eta) y / hardTotal d C D eta) *
          f (hardContextEquiv d C D y)))

lemma hard_carrier_gap_nonneg {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hgamma : 0 ≤ gamma)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (v : Fin (hardCoordinateCount d) → Bool) (y : Fin d → ℝ) :
    0 ≤ ∑ x : HardContextCarrier d C D,
      (hardContextRawMass (eta := eta) x / hardTotal d C D eta) *
        (D * quadraticForm
            (loggingBlock
              (hardExperiment d hd eta C D heta hD hDC hCexp)
              (hardContextEquiv d C D x)) y -
          quadraticForm
            (targetBlock
              (hardExperiment d hd eta C D heta hD hDC hCexp)
              (hardTheta hd D eta gamma v)
              (hardContextEquiv d C D x)) y) := by
  have hH := hardTotal_pos (d := d) heta hD hDC hCexp
  have hhard : 0 ≤ ∑ j : Fin (hardCoordinateCount d),
      (((hardCoordinateCount d : ℝ)⁻¹) / hardTotal d C D eta) *
        (D * (hardP D *
          (dotProduct y (hardBasisU hd j) ^ 2 +
            dotProduct y (hardBasisW hd j) ^ 2)) -
          quadraticForm
            (targetBlock
              (hardExperiment d hd eta C D heta hD hDC hCexp)
              (hardTheta hd D eta gamma v)
              (hardContextEquiv d C D (hardContextHard j))) y) := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg
    · exact div_nonneg (inv_nonneg.mpr (by positivity)) hH.le
    · apply sub_nonneg.mpr
      have hle :=
        hard_targetBlock_le_hard_logging hd heta hD hDC hCexp hgamma
          hden hgammaBeta v j y
      rw [hard_loggingBlock_quadratic_on_carrier hd heta hD hDC hCexp
        (hardContextHard j) y] at hle
      exact hle
  simp only [HardContextCarrier, Fintype.sum_sum_type]
  simp_rw [hard_loggingBlock_quadratic_on_carrier hd heta hD hDC hCexp]
  rw [Fin.sum_univ_one]
  rw [show quadraticForm
        (targetBlock
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardTheta hd D eta gamma v)
          (hardContextEquiv d C D (Sum.inr (Sum.inl 0)))) y =
      C * hardQ C eta * dotProduct y (hardBasisE0 hd) ^ 2 by
    simpa [hardContextCalibration] using
      hard_targetBlock_quadratic_calibration hd heta hD hDC hCexp v y]
  simp_rw [hard_targetBlock_quadratic_anchor hd heta hD hDC hCexp v,
    hard_targetBlock_quadratic_residual hd heta hD hDC hCexp v]
  simp only [hardContextRawMass]
  have hhard' : 0 ≤ ∑ j : Fin (hardCoordinateCount d),
      (((hardCoordinateCount d : ℝ)⁻¹) / hardTotal d C D eta) *
        (D * (hardP D *
          (dotProduct y (hardBasisU hd j) ^ 2 +
            dotProduct y (hardBasisW hd j) ^ 2)) -
          quadraticForm
            (targetBlock
              (hardExperiment d hd eta C D heta hD hDC hCexp)
              (hardTheta hd D eta gamma v)
              (hardContextEquiv d C D (Sum.inl j))) y) := by
    simpa [hardContextHard] using hhard
  by_cases hCD : C > D <;> by_cases heven : Even d
  · rw [sum_fin_ite_one hCD, sum_fin_ite_one heven]
    have hcancel :
        (hardTau C D eta / hardTotal d C D eta) *
              (D * (hardQ C eta * dotProduct y (hardBasisE0 hd) ^ 2) -
                C * hardQ C eta * dotProduct y (hardBasisE0 hd) ^ 2) +
            (hardTau C D eta * hardAnchorRaw C D eta /
                hardTotal d C D eta) *
              (D * dotProduct y (hardBasisE0 hd) ^ 2 -
                dotProduct y (hardBasisE0 hd) ^ 2) = 0 := by
      unfold hardAnchorRaw
      field_simp [hH.ne', ne_of_gt (sub_pos.mpr hD)]
      ring
    have hres : 0 ≤
        (1 / 4 / hardTotal d C D eta) *
          (D * dotProduct y (hardBasisZ hd) ^ 2 -
            dotProduct y (hardBasisZ hd) ^ 2) :=
      mul_nonneg (div_nonneg (by norm_num) hH.le)
        (by nlinarith [sq_nonneg (dotProduct y (hardBasisZ hd))])
    nlinarith
  · rw [sum_fin_ite_one hCD, sum_fin_ite_zero heven]
    have hcancel :
        (hardTau C D eta / hardTotal d C D eta) *
              (D * (hardQ C eta * dotProduct y (hardBasisE0 hd) ^ 2) -
                C * hardQ C eta * dotProduct y (hardBasisE0 hd) ^ 2) +
            (hardTau C D eta * hardAnchorRaw C D eta /
                hardTotal d C D eta) *
              (D * dotProduct y (hardBasisE0 hd) ^ 2 -
                dotProduct y (hardBasisE0 hd) ^ 2) = 0 := by
      unfold hardAnchorRaw
      field_simp [hH.ne', ne_of_gt (sub_pos.mpr hD)]
      ring
    nlinarith
  · have hCD_eq : C = D := le_antisymm (not_lt.mp hCD) hDC
    subst C
    rw [sum_fin_ite_zero (lt_irrefl D), sum_fin_ite_one heven]
    have hres : 0 ≤
        (1 / 4 / hardTotal d D D eta) *
          (D * dotProduct y (hardBasisZ hd) ^ 2 -
            dotProduct y (hardBasisZ hd) ^ 2) :=
      mul_nonneg (div_nonneg (by norm_num) hH.le)
        (by nlinarith [sq_nonneg (dotProduct y (hardBasisZ hd))])
    nlinarith
  · have hCD_eq : C = D := le_antisymm (not_lt.mp hCD) hDC
    subst C
    rw [sum_fin_ite_zero (lt_irrefl D), sum_fin_ite_zero heven]
    nlinarith

lemma hard_gap_posSemidef {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hgamma : 0 ≤ gamma)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (v : Fin (hardCoordinateCount d) → Bool) :
    Matrix.PosSemidef
      (D • (∑ x,
          hardRho (d := d) (C := C) (D := D) (eta := eta) x •
            loggingBlock
              (hardExperiment d hd eta C D heta hD hDC hCexp) x) -
        ∑ x,
          hardRho (d := d) (C := C) (D := D) (eta := eta) x •
            targetBlock
              (hardExperiment d hd eta C D heta hD hDC hCexp)
              (hardTheta hd D eta gamma v) x) := by
  let E := hardExperiment d hd eta C D heta hD hDC hCexp
  let theta := hardTheta hd D eta gamma v
  let rho : Fin (hardContextCard d C D) → ℝ :=
    hardRho (d := d) (C := C) (D := D) (eta := eta)
  have hBherm : (∑ x, rho x • loggingBlock E x).IsHermitian := by
    simpa only [Finset.univ_eq_attach, Finset.sum_attach_univ] using
      sum_loggingBlock_isHermitian E Finset.univ
        (fun x : (Finset.univ : Finset (Fin (hardContextCard d C D))) =>
          rho x.1)
  have hGherm : (∑ x, rho x • targetBlock E theta x).IsHermitian := by
    simpa only [Finset.univ_eq_attach, Finset.sum_attach_univ] using
      sum_targetBlock_isHermitian E Finset.univ
        (fun x : (Finset.univ : Finset (Fin (hardContextCard d C D))) =>
          rho x.1) theta
  have hDBherm : (D • (∑ x, rho x • loggingBlock E x)).IsHermitian := by
    ext i j
    have hsymm :
        (∑ x, rho x • loggingBlock E x) j i =
          (∑ x, rho x • loggingBlock E x) i j := by
      simpa using hBherm.apply i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, star_trivial,
      smul_eq_mul]
    rw [hsymm]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hDBherm.sub hGherm)
  intro y
  rw [← quadraticForm_eq_dotProduct_mulVec, quadraticForm_smul_sub,
    quadraticForm_sum_blocks, quadraticForm_sum_blocks]
  rw [show D * (∑ x, rho x *
        quadraticForm (loggingBlock E x) y) -
        ∑ x, rho x * quadraticForm (targetBlock E theta x) y =
      ∑ x, rho x *
        (D * quadraticForm (loggingBlock E x) y -
          quadraticForm (targetBlock E theta x) y) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [hardRho_weighted_sum_carrier]
  exact hard_carrier_gap_nonneg hd heta hD hDC hCexp hgamma hden
    hgammaBeta v y


end

end CausalSmith.Stat.ReverseKLTwoCoverage
