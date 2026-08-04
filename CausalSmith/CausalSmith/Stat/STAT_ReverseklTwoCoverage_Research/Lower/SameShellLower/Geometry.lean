import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.FamilyCore
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegionNecessityAlgebra

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

lemma hard_plus_projection {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) (y : Fin d → ℝ) :
    ∑ i, ((hardBasisU hd j i + hardBasisW hd j i) / Real.sqrt 2) * y i =
      (dotProduct y (hardBasisU hd j) +
        dotProduct y (hardBasisW hd j)) / Real.sqrt 2 := by
  have hu :
      (∑ i, hardBasisU hd j i * y i) =
        dotProduct y (hardBasisU hd j) := by
    rw [dotProduct_comm]
    rfl
  have hw :
      (∑ i, hardBasisW hd j i * y i) =
        dotProduct y (hardBasisW hd j) := by
    rw [dotProduct_comm]
    rfl
  simp_rw [div_mul_eq_mul_div, add_mul]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hu, hw]

lemma hard_minus_projection {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (hardCoordinateCount d)) (y : Fin d → ℝ) :
    ∑ i, ((hardBasisU hd j i - hardBasisW hd j i) / Real.sqrt 2) * y i =
      (dotProduct y (hardBasisU hd j) -
        dotProduct y (hardBasisW hd j)) / Real.sqrt 2 := by
  have hu :
      (∑ i, hardBasisU hd j i * y i) =
        dotProduct y (hardBasisU hd j) := by
    rw [dotProduct_comm]
    rfl
  have hw :
      (∑ i, hardBasisW hd j i * y i) =
        dotProduct y (hardBasisW hd j) := by
    rw [dotProduct_comm]
    rfl
  simp_rw [div_mul_eq_mul_div, sub_mul]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hu, hw]

lemma hard_loggingBlock_quadratic_on_carrier {d : ℕ} (hd : 4 ≤ d)
    {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (x : HardContextCarrier d C D) (y : Fin d → ℝ) :
    quadraticForm
      (loggingBlock (hardExperiment d hd eta C D heta hD hDC hCexp)
        (hardContextEquiv d C D x)) y =
      match x with
      | Sum.inl j =>
          hardP D *
            (dotProduct y (hardBasisU hd j) ^ 2 +
              dotProduct y (hardBasisW hd j) ^ 2)
      | Sum.inr (Sum.inl _) =>
          hardQ C eta * dotProduct y (hardBasisE0 hd) ^ 2
      | Sum.inr (Sum.inr (Sum.inl _)) =>
          dotProduct y (hardBasisE0 hd) ^ 2
      | Sum.inr (Sum.inr (Sum.inr _)) =>
          dotProduct y (hardBasisZ hd) ^ 2 := by
  rw [loggingBlock_quadratic]
  rcases x with j | (hcal | (hanchor | hz))
  · simp only [hardExperiment, Equiv.symm_apply_apply]
    norm_num [Fin.sum_univ_succ, hardReferenceOnContext,
      hardPlus, hardMinus, hardZero]
    have hp : ∑ i,
        hardFeatureOnContext (C := C) (D := D) hd
          (Sum.inl j) (0 : Fin 3) i * y i =
          (dotProduct y (hardBasisU hd j) +
            dotProduct y (hardBasisW hd j)) / Real.sqrt 2 := by
      simpa [hardPlus] using hard_plus_projection hd j y
    have hm : ∑ i,
        hardFeatureOnContext (C := C) (D := D) hd
          (Sum.inl j) (1 : Fin 3) i * y i =
          (dotProduct y (hardBasisU hd j) -
            dotProduct y (hardBasisW hd j)) / Real.sqrt 2 := by
      simpa [hardMinus] using hard_minus_projection hd j y
    rw [hp, hm]
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    simp [hardFeatureOnContext, hardPlus, hardMinus, h20, h21]
    have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
    field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
    rw [hs]
    ring
  · simp only [hardExperiment, Equiv.symm_apply_apply]
    norm_num [Fin.sum_univ_succ, hardFeatureOnContext,
      hardReferenceOnContext, hardPlus, hardMinus, hardZero]
    rw [show (∑ i, hardBasisE0 hd i * y i) =
        dotProduct y (hardBasisE0 hd) by
      rw [dotProduct_comm]
      rfl]
    exact Or.inl rfl
  · simp only [hardExperiment, Equiv.symm_apply_apply]
    norm_num [Fin.sum_univ_succ, hardFeatureOnContext,
      hardReferenceOnContext, hardPlus, hardMinus, hardZero]
    rw [show (∑ i, hardBasisE0 hd i * y i) =
        dotProduct y (hardBasisE0 hd) by
      rw [dotProduct_comm]
      rfl]
    ring
  · simp only [hardExperiment, Equiv.symm_apply_apply]
    norm_num [Fin.sum_univ_succ, hardFeatureOnContext,
      hardReferenceOnContext, hardPlus, hardMinus, hardZero]
    rw [show (∑ i, hardBasisZ hd i * y i) =
        dotProduct y (hardBasisZ hd) by
      rw [dotProduct_comm]
      rfl]
    ring

end

end CausalSmith.Stat.ReverseKLTwoCoverage
