/- Bias interface for the heavy/light polynomial program. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Expectation

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory

-- @node: shiftedCoefficient_sum_eq_gPolynomial
/-- [The coefficients used by the real-outcome estimator are exactly the shifted-Chebyshev
  reciprocal polynomial from the binary construction](goal). -/
lemma shiftedCoefficient_sum_eq_gPolynomial (K : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range (K - 1), shiftedCoefficient K j * x ^ j =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.gPolynomial K x := by
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.gPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  rw [shiftedCoefficient_eq_gCoefficient]

-- @node: lightArmPolynomial_bias_le
/-- If [the polynomial or elbow parameter satisfies its stated bound](hyp:hK) and [the outcome
  bound is positive](hyp:hB) and [the overlap constant is positive](hyp:hepsilon) and [the
  probability lies in the stated range](hyp:hp) and [the scaled probability satisfies the budget
  bound](hyp:_hpB) and [the shifted probability satisfies the stated range](hyp:hsp) and [the
  shifted scaled probability satisfies the budget bound](hyp:hsB) and [the approximation argument
  lies in its stated range](hyp:hnu) and [the evaluation point lies in its stated range](hyp:hz),
  [on a genuinely light cell, the shifted-Chebyshev arm polynomial has the paper's deterministic
  `B /(2 ε K²)` bias bound](goal). -/
lemma lightArmPolynomial_bias_le {K : ℕ} (hK : 0 < K)
    {B epsilon p s nu z : ℝ} (hB : 0 < B) (hepsilon : 0 < epsilon)
    (hp : 0 ≤ p) (_hpB : p ≤ B) (hsp : epsilon * p ≤ s)
    (hsB : s ≤ B) (hnu : |nu| ≤ 1 / 2) (hz : z = s * nu) :
    |p * nu - p * z / B *
        (∑ j ∈ Finset.range (K - 1), shiftedCoefficient K j * (s / B) ^ j)|
      ≤ B / (2 * epsilon * (K : ℝ) ^ 2) := by
  have hs0 : 0 ≤ s := le_trans (mul_nonneg hepsilon.le hp) hsp
  have hx : s / B ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs0 hB.le, (div_le_one hB).2 hsB⟩
  have hcert :=
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.gPolynomial_certificate hK hx
  rw [shiftedCoefficient_sum_eq_gPolynomial, hz]
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hp_eps : p ≤ s / epsilon := by
    apply (le_div_iff₀ hepsilon).2
    simpa [mul_comm] using hsp
  have hfactor : p * |nu| ≤ B / (2 * epsilon) * (s / B) := by
    calc
      p * |nu| ≤ (s / epsilon) * (1 / 2) :=
        mul_le_mul hp_eps hnu (abs_nonneg nu) (div_nonneg hs0 hepsilon.le)
      _ = B / (2 * epsilon) * (s / B) := by field_simp [hB.ne']
  have hcoef0 : 0 ≤ B / (2 * epsilon) := by positivity
  have hE0 : 0 ≤ |1 - (s / B) *
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.gPolynomial K (s / B)| :=
    abs_nonneg _
  have hKsq : 0 < (K : ℝ) ^ 2 := sq_pos_of_pos hKreal
  have hcert' :
      (s / B) * |1 - (s / B) *
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.gPolynomial K (s / B)| ≤
        1 / (K : ℝ) ^ 2 := by
    change _ ≤ ((K : ℝ) ^ 2)⁻¹ at hcert
    rw [inv_eq_one_div] at hcert
    exact hcert
  have hid :
      p * nu - p * (s * nu) / B *
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.gPolynomial K (s / B) =
        p * nu * (1 - (s / B) *
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.gPolynomial K (s / B)) := by
    field_simp [hB.ne']
  rw [hid, abs_mul, abs_mul, abs_of_nonneg hp]
  calc
    p * |nu| *
          |1 - (s / B) *
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.gPolynomial K (s / B)|
        ≤ (B / (2 * epsilon) * (s / B)) *
            |1 - (s / B) *
              CausalSmith.Stat.DiscreteAteMinimaxLoggap.gPolynomial K (s / B)| :=
          mul_le_mul_of_nonneg_right hfactor hE0
    _ = B / (2 * epsilon) * ((s / B) *
            |1 - (s / B) *
              CausalSmith.Stat.DiscreteAteMinimaxLoggap.gPolynomial K (s / B)|) := by
          ring
    _ ≤ B / (2 * epsilon) * (1 / (K : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hcert' hcoef0
    _ = B / (2 * epsilon * (K : ℝ) ^ 2) := by field_simp [hKsq.ne']

-- @node: polynomialLightCellPopulationTerm
/-- Treated-minus-control population polynomial for one fixed light cell. -/
noncomputable def polynomialLightCellPopulationTerm {d : ℕ} (P : RealLaw d)
    (M B : ℝ) (K : ℕ) (k : Fin d) : ℝ :=
  let p := P.cellMass k
  let s (a : Bool) := p * (if a then P.propensity k else 1 - P.propensity k)
  let nu (a : Bool) := P.outcomeMean a k / M
  let arm (a : Bool) := p * (s a * nu a) / B *
    (∑ j ∈ Finset.range (K - 1),
      shiftedCoefficient K j * (s a / B) ^ j)
  arm true - arm false

-- @node: polynomialLightCellPopulationTerm_bias_le
/-- If [the polynomial or elbow parameter satisfies its stated bound](hyp:hK) and [the outcome
  bound is positive](hyp:hB) and [the cell is classified as light](hyp:hlight), [on a genuinely
  light supported cell, the signed population polynomial approximates its normalized cell
  contribution with bias at most `B /(ε K²)`](goal). -/
lemma polynomialLightCellPopulationTerm_bias_le {d K : ℕ}
    {epsilon M sigma B : ℝ} (P : ModelClass d epsilon M sigma)
    (k : Fin d) (hK : 0 < K) (hB : 0 < B)
    (hlight : P.law.cellMass k ≤ B) :
    |P.law.cellMass k * cellEffect P.law k / M -
        polynomialLightCellPopulationTerm P.law M B K k| ≤
      B / (epsilon * (K : ℝ) ^ 2) := by
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one P.M_ge_one
  by_cases hk : 0 < P.law.cellMass k
  · let p := P.law.cellMass k
    let q : Bool → ℝ := fun a =>
      if a then P.law.propensity k else 1 - P.law.propensity k
    let s : Bool → ℝ := fun a => p * q a
    let nu : Bool → ℝ := fun a => P.law.outcomeMean a k / M
    let arm : Bool → ℝ := fun a => p * (s a * nu a) / B *
      (∑ j ∈ Finset.range (K - 1),
        shiftedCoefficient K j * (s a / B) ^ j)
    have hp0 : 0 ≤ p := (P.law.cellMass_range k).1
    have hq_bounds (a : Bool) : q a ∈ Set.Icc (epsilon : ℝ) 1 := by
      have hov := P.overlap k hk
      rcases P.law.propensity_range k with ⟨hprop0, hprop1⟩
      cases a
      · simp only [q, Bool.false_eq_true, ↓reduceIte]
        constructor <;> linarith
      · simp only [q, ↓reduceIte]
        exact ⟨hov.1, hprop1⟩
    have hsB (a : Bool) : s a ≤ B := by
      calc
        s a = p * q a := rfl
        _ ≤ p * 1 := mul_le_mul_of_nonneg_left (hq_bounds a).2 hp0
        _ ≤ B := by simpa using hlight
    have hsp (a : Bool) : epsilon * p ≤ s a := by
      simpa [s, mul_comm] using
        mul_le_mul_of_nonneg_left (hq_bounds a).1 hp0
    have hnu (a : Bool) : |nu a| ≤ 1 / 2 := by
      dsimp [nu]
      rw [abs_div, abs_of_pos hM]
      apply (div_le_iff₀ hM).2
      simpa [div_eq_mul_inv, mul_comm] using P.mean_normalization a k hk
    have harm (a : Bool) :
        |p * nu a - arm a| ≤ B / (2 * epsilon * (K : ℝ) ^ 2) := by
      exact lightArmPolynomial_bias_le hK hB P.epsilon_pos hp0 hlight
        (hsp a) (hsB a) (hnu a) rfl
    have htarget :
        P.law.cellMass k * cellEffect P.law k / M =
          p * nu true - p * nu false := by
      dsimp [p, nu, cellEffect]
      field_simp [hM.ne']
    have hpoly : polynomialLightCellPopulationTerm P.law M B K k =
        arm true - arm false := by
      rfl
    rw [htarget, hpoly]
    have hrearrange :
        p * nu true - p * nu false - (arm true - arm false) =
          (p * nu true - arm true) - (p * nu false - arm false) := by ring
    rw [hrearrange]
    calc
      |(p * nu true - arm true) - (p * nu false - arm false)| ≤
          |p * nu true - arm true| + |p * nu false - arm false| :=
        abs_sub _ _
      _ ≤ B / (2 * epsilon * (K : ℝ) ^ 2) +
          B / (2 * epsilon * (K : ℝ) ^ 2) :=
        add_le_add (harm true) (harm false)
      _ = B / (epsilon * (K : ℝ) ^ 2) := by
        ring
  · have hp : P.law.cellMass k = 0 :=
      le_antisymm (not_lt.mp hk) (P.law.cellMass_range k).1
    have hright : 0 ≤ B / (epsilon * (K : ℝ) ^ 2) := by
      exact div_nonneg hB.le
        (mul_nonneg P.epsilon_pos.le (sq_nonneg (K : ℝ)))
    simpa [polynomialLightCellPopulationTerm, hp] using hright

-- @node: polynomialFixedLightPopulationBias
/-- Deterministic bias of the population polynomial over a fixed genuinely
light set. -/
noncomputable def polynomialFixedLightPopulationBias {d : ℕ} (P : RealLaw d)
    (M B : ℝ) (K : ℕ) (S : Finset (Fin d)) : ℝ :=
  ∑ k ∈ S, (P.cellMass k * cellEffect P k / M -
    polynomialLightCellPopulationTerm P M B K k)

-- @node: polynomialFixedLightPopulationBias_abs_le
/-- If [the polynomial or elbow parameter satisfies its stated bound](hyp:hK) and [the outcome
  bound is positive](hyp:hB) and [the cell is classified as light](hyp:hlight), [summing the
  cellwise Chebyshev approximation bound costs only the number of genuinely light cells](goal). -/
lemma polynomialFixedLightPopulationBias_abs_le {d K : ℕ}
    {epsilon M sigma B : ℝ} (P : ModelClass d epsilon M sigma)
    (S : Finset (Fin d)) (hK : 0 < K) (hB : 0 < B)
    (hlight : ∀ k ∈ S, P.law.cellMass k ≤ B) :
    |polynomialFixedLightPopulationBias P.law M B K S| ≤
      (S.card : ℝ) * (B / (epsilon * (K : ℝ) ^ 2)) := by
  unfold polynomialFixedLightPopulationBias
  calc
    |∑ k ∈ S, (P.law.cellMass k * cellEffect P.law k / M -
        polynomialLightCellPopulationTerm P.law M B K k)| ≤
        ∑ k ∈ S, |P.law.cellMass k * cellEffect P.law k / M -
          polynomialLightCellPopulationTerm P.law M B K k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ S, B / (epsilon * (K : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun k hk =>
        polynomialLightCellPopulationTerm_bias_le P k hK hB (hlight k hk)
    _ = (S.card : ℝ) * (B / (epsilon * (K : ℝ) ^ 2)) := by simp

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
