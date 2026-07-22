import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Basic

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

-- @env: S2
variable (epsilon : ℝ)
  -- @realizes epsilon(two-category witness overlap constant)

-- @node: prop:two-category-confounding
/-- The explicit full-data witness is consistent, conditionally exchangeable and
overlapping, has ATE `1/2`, and naive observed contrast `epsilon`. -/
theorem two_category_confounding (epsilon : ℝ) (he0 : 0 < epsilon)
    (he1 : epsilon ≤ 1 / 2) :
    let Q := twoCategoryWitness epsilon he0.le (he1.trans (by norm_num))
    Consistency Q ∧
      ConditionalExchangeability Q ∧
      Overlap epsilon (observedMarginal Q) ∧
      ateFunctional (observedMarginal Q) = 1 / 2 ∧
      naiveContrast (observedMarginal Q) = epsilon := by
  classical
  let Q := twoCategoryWitness epsilon he0.le
    (he1.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  let P := observedMarginal Q
  change Consistency Q ∧ ConditionalExchangeability Q ∧ Overlap epsilon P ∧
    ateFunctional P = 1 / 2 ∧ naiveContrast P = epsilon
  have hOverlap : Overlap epsilon P := by
    simp [P, Q, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two,
      Overlap, observedMarginal, jointMass, cellMass, armMass, propensity,
      twoCategoryWitness, twoCategoryMass, PMF.ofFintype_apply, finTwoEquiv,
      he0.le,
      sub_nonneg.mpr (he1.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))]
    constructor
    · intro _
      have hden : (2 : ℝ)⁻¹ * epsilon + 2⁻¹ * (1 - epsilon) = 1 / 2 := by ring
      rw [hden]
      constructor <;> field_simp <;> nlinarith
    · intro _
      have hden : (2 : ℝ)⁻¹ * (1 - epsilon) + 2⁻¹ * epsilon = 1 / 2 := by ring
      rw [hden]
      constructor <;> field_simp <;> nlinarith
  have hATE : ateFunctional P = 1 / 2 := by
    rw [ateFunctional_eq_weighted_regression P hOverlap]
    simp [P, Q, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two,
      observedMarginal, jointMass, cellMass, armMass, outcomeMean,
      twoCategoryWitness, twoCategoryMass, PMF.ofFintype_apply, finTwoEquiv,
      he0.le,
      sub_nonneg.mpr (he1.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))]
    field_simp
    ring
  refine ⟨?_, ?_, hOverlap, hATE, ?_⟩
  · simp [Q, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two,
      Consistency, fullMass, twoCategoryWitness, twoCategoryMass,
      PMF.ofFintype_apply, finTwoEquiv, he0.le]
  · simp [Q, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two,
      ConditionalExchangeability, poAtom, fullMass, twoCategoryWitness,
      twoCategoryMass, PMF.ofFintype_apply, finTwoEquiv, he0.le]
    constructor
    · constructor <;> ring
    · constructor <;> ring
  · simp [P, Q, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two,
      naiveContrast, observedMarginal, jointMass, armMass, twoCategoryWitness,
      twoCategoryMass, PMF.ofFintype_apply, finTwoEquiv, he0.le,
      sub_nonneg.mpr (he1.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))]
    field_simp
    ring

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
