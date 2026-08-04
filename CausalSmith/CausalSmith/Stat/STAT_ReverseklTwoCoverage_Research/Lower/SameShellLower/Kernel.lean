import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Certificate

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators
open Matrix

noncomputable section
def hardHighVector {d : ℕ} (hd : 4 ≤ d)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) (i : Fin d) : ℝ :=
  if v j then
    (hardBasisU hd j i + hardBasisW hd j i) / Real.sqrt 2
  else
    (hardBasisU hd j i - hardBasisW hd j i) / Real.sqrt 2

lemma hardHighVector_norm {d : ℕ} (hd : 4 ≤ d)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    dotProduct (hardHighVector hd v j) (hardHighVector hd v j) = 1 := by
  cases hv : v j
  · simpa [dotProduct, pow_two, hardHighVector, hv] using
      hard_minus_norm_sq hd j
  · simpa [dotProduct, pow_two, hardHighVector, hv] using
      hard_plus_norm_sq hd j

lemma dot_pair_plus (u w y : Fin d → ℝ) :
    dotProduct (fun i => (u i + w i) / Real.sqrt 2) y =
      (dotProduct u y + dotProduct w y) / Real.sqrt 2 := by
  unfold dotProduct
  simp_rw [div_mul_eq_mul_div, add_mul]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

lemma dot_pair_minus (u w y : Fin d → ℝ) :
    dotProduct (fun i => (u i - w i) / Real.sqrt 2) y =
      (dotProduct u y - dotProduct w y) / Real.sqrt 2 := by
  unfold dotProduct
  simp_rw [div_mul_eq_mul_div, sub_mul]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

lemma hardHighVector_dot_u {d : ℕ} (hd : 4 ≤ d)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j l : Fin (hardCoordinateCount d)) :
    dotProduct (hardHighVector hd v j) (hardBasisU hd l) =
      if j = l then 1 / Real.sqrt 2 else 0 := by
  cases hv : v j
  · rw [show hardHighVector hd v j =
        fun i => (hardBasisU hd j i - hardBasisW hd j i) / Real.sqrt 2 by
      funext i
      simp [hardHighVector, hv],
      dot_pair_minus]
    by_cases hjl : j = l
    · subst l
      have horth := (hardBasis_coordinate_orthonormal hd).1 j
      rw [horth.2.2.1,
        show dotProduct (hardBasisW hd j) (hardBasisU hd j) = 0 by
          rw [dotProduct_comm]
          exact horth.2.2.2.2]
      simp
    · have hcross := (hardBasis_coordinate_orthonormal hd).2.1 j l hjl
      rw [hcross.1, hcross.2.2.1]
      simp [hjl]
  · rw [show hardHighVector hd v j =
        fun i => (hardBasisU hd j i + hardBasisW hd j i) / Real.sqrt 2 by
      funext i
      simp [hardHighVector, hv],
      dot_pair_plus]
    by_cases hjl : j = l
    · subst l
      have horth := (hardBasis_coordinate_orthonormal hd).1 j
      rw [horth.2.2.1,
        show dotProduct (hardBasisW hd j) (hardBasisU hd j) = 0 by
          rw [dotProduct_comm]
          exact horth.2.2.2.2]
      simp
    · have hcross := (hardBasis_coordinate_orthonormal hd).2.1 j l hjl
      rw [hcross.1, hcross.2.2.1]
      simp [hjl]

lemma hardHighVector_dot_w {d : ℕ} (hd : 4 ≤ d)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j l : Fin (hardCoordinateCount d)) :
    dotProduct (hardHighVector hd v j) (hardBasisW hd l) =
      if j = l then (if v j then 1 / Real.sqrt 2 else -1 / Real.sqrt 2)
      else 0 := by
  cases hv : v j
  · rw [show hardHighVector hd v j =
        fun i => (hardBasisU hd j i - hardBasisW hd j i) / Real.sqrt 2 by
      funext i
      simp [hardHighVector, hv],
      dot_pair_minus]
    by_cases hjl : j = l
    · subst l
      have horth := (hardBasis_coordinate_orthonormal hd).1 j
      rw [horth.2.2.2.2, horth.2.2.2.1]
      simp [hv]
    · have hcross := (hardBasis_coordinate_orthonormal hd).2.1 j l hjl
      rw [hcross.2.1, hcross.2.2.2]
      simp [hjl]
  · rw [show hardHighVector hd v j =
        fun i => (hardBasisU hd j i + hardBasisW hd j i) / Real.sqrt 2 by
      funext i
      simp [hardHighVector, hv],
      dot_pair_plus]
    by_cases hjl : j = l
    · subst l
      have horth := (hardBasis_coordinate_orthonormal hd).1 j
      rw [horth.2.2.2.2, horth.2.2.2.1]
      simp [hv]
    · have hcross := (hardBasis_coordinate_orthonormal hd).2.1 j l hjl
      rw [hcross.2.1, hcross.2.2.2]
      simp [hjl]

lemma hard_plus_projection_high {d : ℕ} (hd : 4 ≤ d)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j l : Fin (hardCoordinateCount d)) :
    ∑ i,
        ((hardBasisU hd l i + hardBasisW hd l i) / Real.sqrt 2) *
          hardHighVector hd v j i =
      if j = l ∧ v j then 1 else 0 := by
  rw [hard_plus_projection hd l (hardHighVector hd v j),
    hardHighVector_dot_u, hardHighVector_dot_w]
  by_cases hjl : j = l
  · subst l
    cases hv : v j
    · simp [hv]
      ring
    · simp [hv]
      have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
      field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
      try rw [hs]
      ring
  · simp [hjl]

lemma hard_minus_projection_high {d : ℕ} (hd : 4 ≤ d)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j l : Fin (hardCoordinateCount d)) :
    ∑ i,
        ((hardBasisU hd l i - hardBasisW hd l i) / Real.sqrt 2) *
          hardHighVector hd v j i =
      if j = l ∧ ¬ v j then 1 else 0 := by
  rw [hard_minus_projection hd l (hardHighVector hd v j),
    hardHighVector_dot_u, hardHighVector_dot_w]
  by_cases hjl : j = l
  · subst l
    cases hv : v j
    · simp [hv]
      have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
      field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
      try rw [hs]
      ring
    · simp [hv]
  · simp [hjl]

lemma hard_hard_gap_high_zero {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (v : Fin (hardCoordinateCount d) → Bool)
    (j l : Fin (hardCoordinateCount d)) :
    D * quadraticForm
          (loggingBlock
            (hardExperiment d hd eta C D heta hD hDC hCexp)
            (hardContextEquiv d C D (hardContextHard l)))
          (hardHighVector hd v j) -
        quadraticForm
          (targetBlock
            (hardExperiment d hd eta C D heta hD hDC hCexp)
            (hardTheta hd D eta gamma v)
            (hardContextEquiv d C D (hardContextHard l)))
          (hardHighVector hd v j) = 0 := by
  rw [hard_loggingBlock_quadratic_on_carrier hd heta hD hDC hCexp
      (hardContextHard l) (hardHighVector hd v j),
    targetBlock_quadratic]
  simp only [hardExperiment, Equiv.symm_apply_apply, hardContextHard]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  rw [show ∑ i,
        hardFeatureOnContext hd (Sum.inl l) (0 : Fin 3) i *
          hardHighVector hd v j i =
      if j = l ∧ v j then 1 else 0 by
    simpa [hardFeatureOnContext, hardPlus] using
      hard_plus_projection_high hd v j l,
    show ∑ i,
        hardFeatureOnContext hd (Sum.inl l) (Fin.succ 0 : Fin 3) i *
          hardHighVector hd v j i =
      if j = l ∧ ¬v j then 1 else 0 by
    simpa [hardFeatureOnContext, hardPlus, hardMinus] using
      hard_minus_projection_high hd v j l]
  have hzero :
      ∑ i, hardFeatureOnContext (C := C) (D := D) hd (Sum.inl l)
          ((Fin.succ 0).succ : Fin 3) i *
          hardHighVector hd v j i = 0 := by
    simp [hardFeatureOnContext, hardPlus, hardMinus]
  rw [hzero]
  norm_num
  rw [hardHighVector_dot_u hd v j l, hardHighVector_dot_w hd v j l]
  by_cases hjl : j = l
  · subst l
    cases hv : v j
    · have hhigh :=
      hard_hard_candidateWeight_high hd heta hD hDC hCexp hden v j
      simp [hardExperiment, hardContextHard, hv, hardReferenceOnContext,
        hardPlus, hardMinus] at hhigh ⊢
      rw [hhigh]
      have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
      field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
      try rw [hs]
      ring
    · have hhigh :=
      hard_hard_candidateWeight_high hd heta hD hDC hCexp hden v j
      simp [hardExperiment, hardContextHard, hv, hardReferenceOnContext,
        hardPlus, hardMinus] at hhigh ⊢
      rw [hhigh]
      have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
      field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
      try rw [hs]
      ring
  · simp [hjl]

lemma hardHighVector_dot_e0 {d : ℕ} (hd : 4 ≤ d)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    dotProduct (hardHighVector hd v j) (hardBasisE0 hd) = 0 := by
  have horth := (hardBasis_coordinate_orthonormal hd).1 j
  have hu : dotProduct (hardBasisU hd j) (hardBasisE0 hd) = 0 := by
    rw [dotProduct_comm]
    exact horth.1
  have hw : dotProduct (hardBasisW hd j) (hardBasisE0 hd) = 0 := by
    rw [dotProduct_comm]
    exact horth.2.1
  cases hv : v j
  · rw [show hardHighVector hd v j =
        fun i => (hardBasisU hd j i - hardBasisW hd j i) / Real.sqrt 2 by
      funext i
      simp [hardHighVector, hv],
      dot_pair_minus, hu, hw]
    ring
  · rw [show hardHighVector hd v j =
        fun i => (hardBasisU hd j i + hardBasisW hd j i) / Real.sqrt 2 by
      funext i
      simp [hardHighVector, hv],
      dot_pair_plus, hu, hw]
    ring

lemma hardHighVector_dot_z {d : ℕ} (hd : 4 ≤ d)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) (heven : Even d) :
    dotProduct (hardHighVector hd v j) (hardBasisZ hd) = 0 := by
  have horth := hardBasis_z_orthonormal_of_even hd heven
  cases hv : v j
  · rw [show hardHighVector hd v j =
        fun i => (hardBasisU hd j i - hardBasisW hd j i) / Real.sqrt 2 by
      funext i
      simp [hardHighVector, hv],
      dot_pair_minus, (horth.2.2 j).1, (horth.2.2 j).2]
    ring
  · rw [show hardHighVector hd v j =
        fun i => (hardBasisU hd j i + hardBasisW hd j i) / Real.sqrt 2 by
      funext i
      simp [hardHighVector, hv],
      dot_pair_plus, (horth.2.2 j).1, (horth.2.2 j).2]
    ring

lemma hard_carrier_gap_high_zero {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    (∑ x : HardContextCarrier d C D,
      (hardContextRawMass (eta := eta) x / hardTotal d C D eta) *
        (D * quadraticForm
            (loggingBlock
              (hardExperiment d hd eta C D heta hD hDC hCexp)
              (hardContextEquiv d C D x)) (hardHighVector hd v j) -
          quadraticForm
            (targetBlock
              (hardExperiment d hd eta C D heta hD hDC hCexp)
              (hardTheta hd D eta gamma v)
              (hardContextEquiv d C D x)) (hardHighVector hd v j))) = 0 := by
  simp only [HardContextCarrier, Fintype.sum_sum_type]
  have he0 := hardHighVector_dot_e0 hd v j
  have hhardzero (l : Fin (hardCoordinateCount d)) :
      D * quadraticForm
          (loggingBlock
            (hardExperiment d hd eta C D heta hD hDC hCexp)
            (hardContextEquiv d C D (Sum.inl l)))
          (hardHighVector hd v j) -
        quadraticForm
          (targetBlock
            (hardExperiment d hd eta C D heta hD hDC hCexp)
            (hardTheta hd D eta gamma v)
            (hardContextEquiv d C D (Sum.inl l)))
          (hardHighVector hd v j) = 0 := by
    simpa [hardContextHard] using
      hard_hard_gap_high_zero hd heta hD hDC hCexp hden v j l
  simp_rw [hhardzero]
  simp only [mul_zero, Finset.sum_const_zero, zero_add]
  rw [Fin.sum_univ_one]
  rw [show quadraticForm
        (loggingBlock
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardContextEquiv d C D (Sum.inr (Sum.inl 0))))
        (hardHighVector hd v j) = 0 by
      rw [hard_loggingBlock_quadratic_on_carrier hd heta hD hDC hCexp
        (Sum.inr (Sum.inl 0)) (hardHighVector hd v j), he0]
      ring,
    show quadraticForm
        (targetBlock
          (hardExperiment d hd eta C D heta hD hDC hCexp)
          (hardTheta hd D eta gamma v)
          (hardContextEquiv d C D (Sum.inr (Sum.inl 0))))
        (hardHighVector hd v j) = 0 by
      rw [show quadraticForm
          (targetBlock
            (hardExperiment d hd eta C D heta hD hDC hCexp)
            (hardTheta hd D eta gamma v)
            (hardContextEquiv d C D (Sum.inr (Sum.inl 0))))
          (hardHighVector hd v j) =
          C * hardQ C eta *
            dotProduct (hardHighVector hd v j) (hardBasisE0 hd) ^ 2 by
        simpa [hardContextCalibration] using
          hard_targetBlock_quadratic_calibration hd heta hD hDC hCexp v
            (hardHighVector hd v j),
        he0]
      ring]
  simp only [mul_zero, sub_self]
  by_cases hCD : C > D
  · simp_rw [hard_loggingBlock_quadratic_on_carrier hd heta hD hDC hCexp,
      hard_targetBlock_quadratic_anchor hd heta hD hDC hCexp v, he0]
    rw [sum_fin_ite_one hCD]
    simp
    by_cases heven : Even d
    · have hz := hardHighVector_dot_z hd v j heven
      rw [sum_fin_ite_one heven]
      rw [hard_targetBlock_quadratic_residual hd heta hD hDC hCexp v, hz]
      simp
    · rw [sum_fin_ite_zero heven]
  · rw [sum_fin_ite_zero hCD]
    simp
    by_cases heven : Even d
    · have hz := hardHighVector_dot_z hd v j heven
      rw [sum_fin_ite_one heven]
      rw [hard_loggingBlock_quadratic_on_carrier hd heta hD hDC hCexp,
        hard_targetBlock_quadratic_residual hd heta hD hDC hCexp v, hz]
      simp
    · rw [sum_fin_ite_zero heven]

lemma hard_global_gap_high_zero {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    quadraticForm
      (D • (∑ x,
          hardRho (d := d) (C := C) (D := D) (eta := eta) x •
            loggingBlock
              (hardExperiment d hd eta C D heta hD hDC hCexp) x) -
        ∑ x,
          hardRho (d := d) (C := C) (D := D) (eta := eta) x •
            targetBlock
              (hardExperiment d hd eta C D heta hD hDC hCexp)
              (hardTheta hd D eta gamma v) x)
      (hardHighVector hd v j) = 0 := by
  let E := hardExperiment d hd eta C D heta hD hDC hCexp
  let theta := hardTheta hd D eta gamma v
  let rho : Fin (hardContextCard d C D) → ℝ :=
    hardRho (d := d) (C := C) (D := D) (eta := eta)
  rw [quadraticForm_smul_sub, quadraticForm_sum_blocks,
    quadraticForm_sum_blocks]
  rw [show D * (∑ x, rho x *
        quadraticForm (loggingBlock E x) (hardHighVector hd v j)) -
        ∑ x, rho x *
          quadraticForm (targetBlock E theta x) (hardHighVector hd v j) =
      ∑ x, rho x *
        (D * quadraticForm (loggingBlock E x) (hardHighVector hd v j) -
          quadraticForm (targetBlock E theta x)
            (hardHighVector hd v j)) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  rw [hardRho_weighted_sum_carrier]
  exact hard_carrier_gap_high_zero hd heta hD hDC hCexp hden v j

private lemma posSemidef_mulVec_eq_zero_of_quadraticForm_eq_zero
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ)
    (hA : A.PosSemidef)
    (hzero : quadraticForm A y = 0) :
    A.mulVec y = 0 := by
  obtain ⟨B, rfl⟩ :=
    Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hA
  rw [quadraticForm_eq_dotProduct_mulVec] at hzero
  rw [← mulVec_mulVec] at hzero
  rw [dotProduct_mulVec] at hzero
  rw [vecMul_conjTranspose] at hzero
  simp only [star_trivial] at hzero
  have hBy : B *ᵥ y = 0 := dotProduct_self_eq_zero.mp hzero
  rw [← mulVec_mulVec, hBy, mulVec_zero]

lemma hard_gap_kernel {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hgamma : 0 ≤ gamma)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    (D • (∑ x,
        hardRho (d := d) (C := C) (D := D) (eta := eta) x •
          loggingBlock
            (hardExperiment d hd eta C D heta hD hDC hCexp) x) -
      ∑ x,
        hardRho (d := d) (C := C) (D := D) (eta := eta) x •
          targetBlock
            (hardExperiment d hd eta C D heta hD hDC hCexp)
            (hardTheta hd D eta gamma v) x).mulVec
      (hardHighVector hd v j) = 0 := by
  let A :=
    D • (∑ x,
        hardRho (d := d) (C := C) (D := D) (eta := eta) x •
          loggingBlock
            (hardExperiment d hd eta C D heta hD hDC hCexp) x) -
      ∑ x,
        hardRho (d := d) (C := C) (D := D) (eta := eta) x •
          targetBlock
            (hardExperiment d hd eta C D heta hD hDC hCexp)
            (hardTheta hd D eta gamma v) x
  have hA : Matrix.PosSemidef A :=
    hard_gap_posSemidef hd heta hD hDC hCexp hgamma hden hgammaBeta v
  have hzero : quadraticForm A (hardHighVector hd v j) = 0 :=
    hard_global_gap_high_zero hd heta hD hDC hCexp hden v j
  exact posSemidef_mulVec_eq_zero_of_quadraticForm_eq_zero
    A (hardHighVector hd v j) hA hzero

end

end CausalSmith.Stat.ReverseKLTwoCoverage
