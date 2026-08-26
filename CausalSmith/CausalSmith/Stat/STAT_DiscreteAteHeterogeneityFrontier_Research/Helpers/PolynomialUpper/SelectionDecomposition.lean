/- Exact selected heavy/light error decomposition for the polynomial program. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.ClippingAssembly

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

/-! The pilot selector partitions the normalized pre-clipping error into a
heavy marked-ratio error and a light polynomial error.  Keeping this identity
separate lets the two fixed-set moment bounds be assembled independently. -/

-- @node: polynomialHeavySelectedError
/-- The normalized estimation error contributed by cells selected as heavy. -/
noncomputable def polynomialHeavySelectedError {n d : ℕ} (P : RealLaw d)
    (M : ℝ) (sample : Fin n → Obs d) : ℝ :=
  ∑ k : Fin d,
    if 256 * logEN n < pilotCount sample k then
      heavyEmpiricalTerm M sample k -
        P.cellMass k * cellEffect P k / M
    else 0

-- @node: polynomialLightSelectedError
/-- The normalized estimation error contributed by cells selected as light. -/
noncomputable def polynomialLightSelectedError {n d : ℕ} (P : RealLaw d)
    (M : ℝ) (sample : Fin n → Obs d) : ℝ :=
  let K := polynomialDegree n
  let B := 4096 * logEN n / (n - n / 2 : ℕ)
  ∑ k : Fin d,
    if 256 * logEN n < pilotCount sample k then 0
    else lightPolynomialTerm M B K sample k -
      P.cellMass k * cellEffect P k / M

-- @node: polynomialNormalizedSum_sub_target_eq_selectedErrors
/-- [The pre-clipping normalized error is exactly the sum of the selected heavy and selected light
  errors; no probability or moment assumption enters this partition identity](goal). -/
lemma polynomialNormalizedSum_sub_target_eq_selectedErrors {n d : ℕ}
    (P : RealLaw d) (M : ℝ) (sample : Fin n → Obs d) :
    polynomialNormalizedSum M sample - rawAteFormula P / M =
      polynomialHeavySelectedError P M sample +
        polynomialLightSelectedError P M sample := by
  unfold polynomialNormalizedSum polynomialHeavySelectedError
    polynomialLightSelectedError rawAteFormula
  rw [Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : 256 * logEN n < pilotCount sample k <;> simp [hk]

-- @node: polynomialNormalizedSum_error_sq_le_selectedErrors
/-- [The exact selector partition yields the standard two-term squared-error bound used to combine
  the heavy and light risk estimates](goal). -/
lemma polynomialNormalizedSum_error_sq_le_selectedErrors {n d : ℕ}
    (P : RealLaw d) (M : ℝ) (sample : Fin n → Obs d) :
    (polynomialNormalizedSum M sample - rawAteFormula P / M) ^ 2 ≤
      2 * polynomialHeavySelectedError P M sample ^ 2 +
        2 * polynomialLightSelectedError P M sample ^ 2 := by
  rw [polynomialNormalizedSum_sub_target_eq_selectedErrors]
  nlinarith [sq_nonneg
    (polynomialHeavySelectedError P M sample -
      polynomialLightSelectedError P M sample)]

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
