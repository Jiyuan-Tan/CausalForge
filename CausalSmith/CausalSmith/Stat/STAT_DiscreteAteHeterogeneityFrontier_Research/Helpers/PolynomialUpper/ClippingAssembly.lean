/- Scaling and clipping assembly for the polynomial upper bound. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Fallback

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory Set

-- @node: polynomialNormalizedSum
/-- The normalized heavy/light sum before the estimator's final clipping. -/
noncomputable def polynomialNormalizedSum {n d : ℕ} (M : ℝ)
    (sample : Fin n → Obs d) : ℝ :=
  let K := polynomialDegree n
  let B := 4096 * logEN n / (n - n / 2 : ℕ)
  ∑ k : Fin d,
    if 256 * logEN n < pilotCount sample k then
      heavyEmpiricalTerm M sample k
    else lightPolynomialTerm M B K sample k

/-- If [the indicated calibration branch applies](hyp:hbranch), [on the calibrated branch, the
  concrete estimator is exactly the outcome scale times the clipped normalized heavy/light
  sum](goal). -/
lemma polyEstimator_eq_scaled_clip_of_calibrated {n d N : ℕ} {M rho : ℝ}
    (hbranch : N ≤ n ∧ (d : ℝ) ≤ rho * n * logEN n) :
    rawPolyEstimator (n := n) (d := d) N rho M =
      fun sample => M * clip (-1) 1 (polynomialNormalizedSum M sample) := by
  funext sample
  simp [rawPolyEstimator, hbranch, polynomialNormalizedSum]

-- @node: modelClass_normalized_ate_mem_Icc
/-- [The model's ATE divided by its positive outcome scale lies in the clipping interval](goal). -/
lemma modelClass_normalized_ate_mem_Icc {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) :
    rawAteFormula P.law / M ∈ Icc (-1 : ℝ) 1 := by
  let Q : UnrestrictedClass d epsilon M :=
    { law := P.law
      epsilon_pos := P.epsilon_pos
      epsilon_lt_half := P.epsilon_lt_half
      M_ge_one := P.M_ge_one
      consistency := P.consistency
      exchangeability := P.exchangeability
      overlap := P.overlap
      mean_normalization := P.mean_normalization
      second_moment := P.second_moment }
  have hraw : |rawAteFormula P.law| ≤ M := scale_sanity.1 Q |>.2.1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one P.M_ge_one
  constructor
  · apply (le_div_iff₀ hM).2
    simpa using (neg_le_of_abs_le hraw)
  · rw [div_le_one hM]
    exact le_of_abs_le hraw

/-- If [the indicated calibration branch applies](hyp:hbranch) and [the specified random quantity
  is integrable](hyp:hright) and [the raw normalized-error bound holds](hyp:hraw), [a normalized
  pre-clipping mean-square bound transfers to the scaled, clipped estimator whenever the
  normalized target lies in `[-1,1]`](goal). -/
lemma mse_polyEstimator_le_of_normalized_error {n d N : ℕ}
    {epsilon M sigma rho R : ℝ} (P : ModelClass d epsilon M sigma)
    (hbranch : N ≤ n ∧ (d : ℝ) ≤ rho * n * logEN n)
    (hright : Integrable
      (fun sample : Fin n → Obs d =>
        M ^ 2 * (polynomialNormalizedSum M sample -
          rawAteFormula P.law / M) ^ 2)
      (productLaw n P.law))
    (hraw : (∫ sample : Fin n → Obs d,
        (polynomialNormalizedSum M sample - rawAteFormula P.law / M) ^ 2
          ∂productLaw n P.law) ≤ R) :
    mse P.law (rawPolyEstimator (n := n) (d := d) N rho M) ≤ M ^ 2 * R := by
  have hM : M ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one P.M_ge_one)
  have hpoint (sample : Fin n → Obs d) :
      (rawPolyEstimator N rho M sample - rawAteFormula P.law) ^ 2 ≤
        M ^ 2 * (polynomialNormalizedSum M sample -
          rawAteFormula P.law / M) ^ 2 := by
    rw [polyEstimator_eq_scaled_clip_of_calibrated hbranch]
    have hclip := clip_normalized_sq_error_le
      (polynomialNormalizedSum M sample) (rawAteFormula P.law / M)
      (modelClass_normalized_ate_mem_Icc P)
    have hid :
        (M * clip (-1) 1 (polynomialNormalizedSum M sample) -
            rawAteFormula P.law) ^ 2 =
          M ^ 2 * (clip (-1) 1 (polynomialNormalizedSum M sample) -
            rawAteFormula P.law / M) ^ 2 := by
      field_simp [hM]
    rw [hid]
    exact mul_le_mul_of_nonneg_left hclip (sq_nonneg M)
  have hleft : Integrable
      (fun sample : Fin n → Obs d =>
        (rawPolyEstimator N rho M sample - rawAteFormula P.law) ^ 2)
      (productLaw n P.law) := by
    have hadm := polyEstimator_admissible (n := n) (d := d) (N := N)
      (rho := rho) (le_trans zero_le_one P.M_ge_one)
    have htau : |rawAteFormula P.law| ≤ M := by
      let Q : UnrestrictedClass d epsilon M :=
        { law := P.law
          epsilon_pos := P.epsilon_pos
          epsilon_lt_half := P.epsilon_lt_half
          M_ge_one := P.M_ge_one
          consistency := P.consistency
          exchangeability := P.exchangeability
          overlap := P.overlap
          mean_normalization := P.mean_normalization
          second_moment := P.second_moment }
      exact scale_sanity.1 Q |>.2.1
    have hM0 : 0 ≤ M := le_trans zero_le_one P.M_ge_one
    apply Integrable.of_bound (C := (2 * M) ^ 2)
      ((hadm.1.sub measurable_const).pow_const 2).aestronglyMeasurable
    filter_upwards with sample
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hest : |rawPolyEstimator N rho M sample| ≤ M :=
      (abs_le).2 (hadm.2 sample)
    have habs : |rawPolyEstimator N rho M sample - rawAteFormula P.law| ≤ 2 * M :=
      (abs_sub _ _).trans (by linarith)
    exact (sq_le_sq).2 (by
      simpa [abs_mul, abs_of_nonneg hM0] using habs)
  unfold mse
  calc
    (∫ sample, (rawPolyEstimator N rho M sample - rawAteFormula P.law) ^ 2
        ∂productLaw n P.law) ≤
      ∫ sample, M ^ 2 * (polynomialNormalizedSum M sample -
          rawAteFormula P.law / M) ^ 2 ∂productLaw n P.law :=
        integral_mono hleft hright hpoint
    _ = M ^ 2 * (∫ sample,
        (polynomialNormalizedSum M sample - rawAteFormula P.law / M) ^ 2
          ∂productLaw n P.law) := by rw [integral_const_mul]
    _ ≤ M ^ 2 * R := mul_le_mul_of_nonneg_left hraw (sq_nonneg M)

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
