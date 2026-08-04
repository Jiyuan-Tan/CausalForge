import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.ConstructionCore

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

lemma hardTheta_dot_e0 {d : ℕ} (hd : 4 ≤ d)
    (D eta gamma : ℝ) (v : Fin (hardCoordinateCount d) → Bool) :
    dotProduct (hardTheta hd D eta gamma v) (hardBasisE0 hd) = 1 := by
  rw [hardBasisE0, dot_indexBasis_right]
  simp [hardTheta, hardBasisEquiv]

lemma hardTheta_dot_u {d : ℕ} (hd : 4 ≤ d)
    (D eta gamma : ℝ) (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    dotProduct (hardTheta hd D eta gamma v) (hardBasisU hd j) =
      Real.sqrt 2 * hardBeta D eta gamma := by
  rw [hardBasisU, dot_indexBasis_right]
  simp [hardTheta]

lemma hardTheta_dot_w {d : ℕ} (hd : 4 ≤ d)
    (D eta gamma : ℝ) (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    dotProduct (hardTheta hd D eta gamma v) (hardBasisW hd j) =
      Real.sqrt 2 * gamma * (if v j then 1 else -1) := by
  rw [hardBasisW, dot_indexBasis_right]
  simp [hardTheta]

lemma hardTheta_dot_z_of_even {d : ℕ} (hd : 4 ≤ d)
    (D eta gamma : ℝ) (v : Fin (hardCoordinateCount d) → Bool)
    (heven : Even d) :
    dotProduct (hardTheta hd D eta gamma v) (hardBasisZ hd) = 0 := by
  rw [show hardBasisZ hd = indexBasis
      (hardBasisEquiv hd
        (Sum.inr (Sum.inr (Sum.inr ⟨0, by simp [heven]⟩)))) by
        simp [hardBasisZ, heven],
    dot_indexBasis_right]
  simp [hardTheta]

lemma hard_feature_plus_score {d : ℕ} (hd : 4 ≤ d)
    (D eta gamma : ℝ) (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    ∑ i, ((hardBasisU hd j i + hardBasisW hd j i) / Real.sqrt 2) *
        hardTheta hd D eta gamma v i =
      hardBeta D eta gamma + gamma * (if v j then 1 else -1) := by
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hu := hardTheta_dot_u hd D eta gamma v j
  have hw := hardTheta_dot_w hd D eta gamma v j
  rw [dotProduct_comm] at hu hw
  unfold dotProduct at hu hw
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, hu, hw]
  field_simp

lemma hard_feature_minus_score {d : ℕ} (hd : 4 ≤ d)
    (D eta gamma : ℝ) (v : Fin (hardCoordinateCount d) → Bool)
    (j : Fin (hardCoordinateCount d)) :
    ∑ i, ((hardBasisU hd j i - hardBasisW hd j i) / Real.sqrt 2) *
        hardTheta hd D eta gamma v i =
      hardBeta D eta gamma - gamma * (if v j then 1 else -1) := by
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hu := hardTheta_dot_u hd D eta gamma v j
  have hw := hardTheta_dot_w hd D eta gamma v j
  rw [dotProduct_comm] at hu hw
  unfold dotProduct at hu hw
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, hu, hw]
  field_simp

lemma hardContextRawMass_sum {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ} :
    (∑ x : HardContextCarrier d C D,
        hardContextRawMass (eta := eta) x) =
      hardTotal d C D eta := by
  simp only [HardContextCarrier, Fintype.sum_sum_type,
    hardContextRawMass]
  have hk : 0 < hardCoordinateCount d := hardCoordinateCount_pos hd
  have hhard :
      (∑ _j : Fin (hardCoordinateCount d),
          ((hardCoordinateCount d : ℝ)⁻¹)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)
  rw [hhard, Fin.sum_univ_one]
  by_cases hCD : C > D <;> by_cases heven : Even d
  · rw [sum_fin_ite_one hCD, sum_fin_ite_one heven]
    simp [hardTotal, hCD, heven]
    ring
  · rw [sum_fin_ite_one hCD, sum_fin_ite_zero heven]
    simp [hardTotal, hCD, heven]
    ring
  · rw [sum_fin_ite_zero hCD, sum_fin_ite_one heven]
    simp [hardTotal, hCD, heven]
    ring
  · rw [sum_fin_ite_zero hCD, sum_fin_ite_zero heven]
    simp [hardTotal, hCD, heven]

lemma hardRho_sum {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    ∑ x, hardRho (d := d) (C := C) (D := D) (eta := eta) x = 1 := by
  have hH : hardTotal d C D eta ≠ 0 :=
    (hardTotal_pos (d := d) heta hD hDC hCexp).ne'
  rw [show (∑ x, hardRho (d := d) (C := C) (D := D) (eta := eta) x) =
      ∑ y : HardContextCarrier d C D,
        hardContextRawMass (eta := eta) y / hardTotal d C D eta by
      simpa [hardRho] using
        (Equiv.sum_comp (hardContextEquiv d C D).symm
          (fun y : HardContextCarrier d C D =>
            hardContextRawMass (eta := eta) y /
              hardTotal d C D eta))]
  rw [← Finset.sum_div, hardContextRawMass_sum hd]
  exact div_self hH

lemma hardRho_nonneg {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    ∀ x, 0 ≤ hardRho (d := d) (C := C) (D := D) (eta := eta) x := by
  intro x
  have hH := (hardTotal_pos (d := d) heta hD hDC hCexp).le
  unfold hardRho
  apply div_nonneg ?_ hH
  let y := (hardContextEquiv d C D).symm x
  change 0 ≤ hardContextRawMass (eta := eta) y
  rcases y with j | (hcal | (hanchor | hz))
  · exact inv_nonneg.mpr (by positivity)
  · exact (hardTau_pos heta hD hDC hCexp).le
  · exact mul_nonneg (hardTau_pos heta hD hDC hCexp).le
      (hardAnchorRaw_nonneg heta hD hDC hCexp)
  · norm_num [hardContextRawMass]

lemma hardAnchorRaw_pos {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) (hCD : C > D) :
    0 < hardAnchorRaw C D eta := by
  unfold hardAnchorRaw
  exact div_pos
    (mul_pos (hardQ_pos heta hD hDC hCexp) (sub_pos.mpr hCD))
    (sub_pos.mpr hD)

lemma hardRho_pos {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    ∀ x, 0 < hardRho (d := d) (C := C) (D := D) (eta := eta) x := by
  intro x
  unfold hardRho
  apply div_pos ?_ (hardTotal_pos (d := d) heta hD hDC hCexp)
  let y := (hardContextEquiv d C D).symm x
  change 0 < hardContextRawMass (eta := eta) y
  rcases y with j | (hcal | (hanchor | hz))
  · exact inv_pos.mpr (Nat.cast_pos.mpr (hardCoordinateCount_pos hd))
  · exact hardTau_pos heta hD hDC hCexp
  · have hCD : C > D := by
      by_contra hn
      have hlt := hanchor.isLt
      simp [hn] at hlt
    exact mul_pos (hardTau_pos heta hD hDC hCexp)
      (hardAnchorRaw_pos heta hD hDC hCexp hCD)
  · norm_num [hardContextRawMass]

lemma hard_score_on_context {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (v : Fin (hardCoordinateCount d) → Bool)
    (y : HardContextCarrier d C D) (a : Fin 3) :
    ∑ i, hardFeatureOnContext hd y a i *
        hardTheta hd D eta gamma v i =
      match y with
      | Sum.inl j =>
          if a = hardPlus then
            hardBeta D eta gamma + gamma * (if v j then 1 else -1)
          else if a = hardMinus then
            hardBeta D eta gamma - gamma * (if v j then 1 else -1)
          else 0
      | Sum.inr (Sum.inl _) => if a = hardPlus then 1 else 0
      | Sum.inr (Sum.inr (Sum.inl _)) => 1
      | Sum.inr (Sum.inr (Sum.inr _)) => 0 := by
  rcases y with j | (hcal | (hanchor | hz))
  · by_cases hp : a = hardPlus
    · simp [hardFeatureOnContext, hp, hard_feature_plus_score]
    · by_cases hm : a = hardMinus
      · simp [hardFeatureOnContext, hm, hardPlus, hardMinus,
          hard_feature_minus_score]
      · simp [hardFeatureOnContext, hp, hm]
  · by_cases hp : a = hardPlus
    · simpa [hardFeatureOnContext, hp, dotProduct_comm] using
        hardTheta_dot_e0 hd D eta gamma v
    · simp [hardFeatureOnContext, hp]
  · simpa [hardFeatureOnContext, dotProduct_comm] using
      hardTheta_dot_e0 hd D eta gamma v
  · have heven : Even d := by
      by_contra hneven
      have hzlt := hz.isLt
      simp [hneven] at hzlt
    simpa [hardFeatureOnContext, dotProduct_comm] using
      hardTheta_dot_z_of_even hd D eta gamma v heven

lemma hard_linear_bounds {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma) :
    ∀ x a,
      (∑ i, hardFeatureOnContext hd
          ((hardContextEquiv d C D).symm x) a i *
        hardTheta hd D eta gamma v i) ∈ Set.Icc (0 : ℝ) 1 := by
  intro x a
  rw [hard_score_on_context hd v]
  let y := (hardContextEquiv d C D).symm x
  change (match y with
    | Sum.inl j =>
        if a = hardPlus then
          hardBeta D eta gamma + gamma * (if v j then 1 else -1)
        else if a = hardMinus then
          hardBeta D eta gamma - gamma * (if v j then 1 else -1)
        else 0
    | Sum.inr (Sum.inl _) => if a = hardPlus then 1 else 0
    | Sum.inr (Sum.inr (Sum.inl _)) => 1
    | Sum.inr (Sum.inr (Sum.inr _)) => 0) ∈ Set.Icc (0 : ℝ) 1
  rcases y with j | (hcal | (hanchor | hz))
  · by_cases hp : a = hardPlus
    · cases hv : v j <;> simp [hp, hv] <;> constructor <;> linarith
    · by_cases hm : a = hardMinus
      · cases hv : v j <;>
          simp [hm, hardPlus, hardMinus, hv] <;>
          constructor <;> linarith
      · simp [hp, hm]
  · by_cases hp : a = hardPlus <;> simp [hp]
  · simp
  · simp

end

end CausalSmith.Stat.ReverseKLTwoCoverage
