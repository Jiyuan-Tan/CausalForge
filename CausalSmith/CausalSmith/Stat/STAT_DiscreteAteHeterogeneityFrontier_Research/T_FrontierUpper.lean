/- Known-radius selector upper frontier. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.T_RobustUpperConstruction
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.CitedGates

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Filter Set

/-- Asymptotic comparison with the published collision remainder. -/
def PublishedCollisionComparison : Prop :=
  (∀ n d : ℕ, ∀ sigma : ℝ,
    0 < n → 0 < d → 0 ≤ sigma → sigma ≤ 2 →
    min 1 (min (polynomialComponent n d) (collisionComponent n d sigma)) ≤
      collisionComponent n d sigma) ∧
  ∀ dseq : ℕ → ℕ, ∀ sseq : ℕ → ℝ,
    (∀ n, 0 < n →
      0 < dseq n ∧ 0 ≤ sseq n ∧ sseq n ≤ 2) →
    Tendsto (fun n => polynomialComponent n (dseq n) /
      collisionComponent n (dseq n) (sseq n)) atTop (nhds 0) →
    Tendsto (fun n => (dseq n : ℝ) / ((n : ℝ) * logEN n)) atTop (nhds 0) →
    Tendsto (fun n =>
      min 1 (min (polynomialComponent n (dseq n))
        (collisionComponent n (dseq n) (sseq n))) /
          collisionComponent n (dseq n) (sseq n)) atTop (nhds 0)

/-- [The selector risk bound without the secondary published-comparison clause](goal). -/
lemma frontier_upper_bound_all_d :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon : ℝ, ∃ handle : PolynomialHandle,
      0 < C_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → ∀ hM : 1 ≤ M, 0 ≤ sigma → sigma ≤ 2 →
        let poly := polyEstimatorElement (n := n) (d := d) handle hM
        let collision := collisionEstimatorElement (n := n) (d := d) hM
        let selector := totalSelector hM sigma poly collision
        Measurable selector.1 ∧
        (∀ s : Fin n → Obs d, selector.1 s ∈ Icc (-M) M) ∧
        (∀ P : ModelClass d epsilon M sigma,
          mse P.law selector.1 ≤
            C_epsilon * M ^ 2 * frontierRate n d sigma) := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨C0, handle, hC0, hall⟩ :=
    robust_upper_construction_resolution_all_d
      epsilon hepsilon hepsilon_half
  let C := max 1 C0
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC0C : C0 ≤ C := le_max_right _ _
  refine ⟨C, handle, hC, ?_⟩
  intro n d M sigma hn hd hM hsigma hsigma_two
  obtain ⟨hpoly_meas, hpoly_mem, hcollision_meas, hcollision_mem, hrisk⟩ :=
    hall n d M sigma hn hd hM hsigma hsigma_two
  let poly := polyEstimatorElement (n := n) (d := d) handle hM
  let collision := collisionEstimatorElement (n := n) (d := d) hM
  let selector := totalSelector hM sigma poly collision
  have hpoly_nonneg : 0 ≤ polynomialComponent n d := by
    unfold polynomialComponent
    positivity
  have hcollision_nonneg : 0 ≤ collisionComponent n d sigma := by
    unfold collisionComponent
    positivity
  refine ⟨(totalSelector hM sigma poly collision).2.1,
    (totalSelector hM sigma poly collision).2.2, ?_⟩
  · intro P
    rcases hrisk P with ⟨hpoly_risk, hcollision_risk⟩
    change mse P.law (totalSelector hM sigma poly collision).1 ≤
      C * M ^ 2 * frontierRate n d sigma
    unfold totalSelector
    by_cases hcollision : collisionComponent n d sigma ≤
        min 1 (polynomialComponent n d)
    · rw [if_pos hcollision]
      dsimp only [collision]
      refine hcollision_risk.trans ?_
      have hmin : min 1
          (min (polynomialComponent n d) (collisionComponent n d sigma)) =
          collisionComponent n d sigma := by
        rw [min_eq_right (hcollision.trans (min_le_right _ _))]
        exact min_eq_right (hcollision.trans (min_le_left _ _))
      rw [frontierRate, hmin]
      unfold collisionComponent
      have hrate : 0 ≤ M ^ 2 *
          (1 / (n : ℝ) + (sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2)) := by
        positivity
      nlinarith [mul_le_mul_of_nonneg_right hC0C hrate]
    · rw [if_neg hcollision]
      unfold mse
      by_cases hpoly : polynomialComponent n d <
          min 1 (collisionComponent n d sigma)
      · simp only [hpoly]
        change mse P.law poly.1 ≤ C * M ^ 2 * frontierRate n d sigma
        dsimp only [poly]
        have hpoly_one : min 1 (polynomialComponent n d) =
            polynomialComponent n d :=
          min_eq_right (le_of_lt (hpoly.trans_le (min_le_left _ _)))
        rw [hpoly_one] at hpoly_risk
        refine hpoly_risk.trans ?_
        have hmin : min 1
            (min (polynomialComponent n d) (collisionComponent n d sigma)) =
            polynomialComponent n d := by
          rw [min_eq_left (le_of_lt (hpoly.trans_le (min_le_right _ _)))]
          exact min_eq_right (le_of_lt (hpoly.trans_le (min_le_left _ _)))
        rw [frontierRate, hmin]
        have hrate : 0 ≤ M ^ 2 *
            (1 / (n : ℝ) + polynomialComponent n d) := by
          positivity
        nlinarith [mul_le_mul_of_nonneg_right hC0C hrate]
      · simp only [hpoly]
        change mse P.law (fun _ : Fin n → Obs d => 0) ≤
          C * M ^ 2 * frontierRate n d sigma
        have hone_poly : 1 ≤ polynomialComponent n d := by
          by_contra hnot
          have hpoly_lt : polynomialComponent n d < 1 := lt_of_not_ge hnot
          have hpc_lt : polynomialComponent n d < collisionComponent n d sigma := by
            have := lt_of_not_ge hcollision
            rw [min_eq_right hpoly_lt.le] at this
            exact this
          have hmc_le : min 1 (collisionComponent n d sigma) ≤
              polynomialComponent n d := le_of_not_gt hpoly
          by_cases hc : collisionComponent n d sigma ≤ 1
          · rw [min_eq_right hc] at hmc_le
            linarith
          · rw [min_eq_left (le_of_not_ge hc)] at hmc_le
            linarith
        have hone_collision : 1 ≤ collisionComponent n d sigma := by
          have hmin_poly : min 1 (polynomialComponent n d) = 1 :=
            min_eq_left hone_poly
          simpa [hmin_poly] using lt_of_not_ge hcollision |>.le
        have hmin : min 1
            (min (polynomialComponent n d) (collisionComponent n d sigma)) = 1 := by
          exact min_eq_left (le_min hone_poly hone_collision)
        let U : UnrestrictedClass d epsilon M :=
          { law := P.law
            epsilon_pos := P.epsilon_pos
            epsilon_lt_half := P.epsilon_lt_half
            M_ge_one := P.M_ge_one
            consistency := P.consistency
            exchangeability := P.exchangeability
            overlap := P.overlap
            mean_normalization := P.mean_normalization
            second_moment := P.second_moment }
        have hate : |rawAteFormula P.law| ≤ M := by
          simpa [U] using
            (scale_sanity (d := d) (epsilon := epsilon) (M := M)).1 U |>.2.1
        have hmse : mse P.law (fun _ : Fin n → Obs d => 0) =
          rawAteFormula P.law ^ 2 := by
          unfold mse
          simp
        rw [hmse]
        unfold frontierRate
        rw [hmin]
        have hate_sq : rawAteFormula P.law ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs]
          exact (sq_le_sq₀ (abs_nonneg _)
            (le_trans zero_le_one hM)).2 hate
        have hfactor : M ^ 2 ≤ C * M ^ 2 * (1 / (n : ℝ) + 1) := by
          have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
          have hC_one : 1 ≤ C := le_max_left _ _
          have hM_sq : 0 ≤ M ^ 2 := sq_nonneg M
          have hone : 1 ≤ C * (1 / (n : ℝ) + 1) := by
            nlinarith [one_div_pos.mpr hn_real]
          nlinarith
        exact hate_sq.trans hfactor

-- @node: thm:frontier-upper-all-d
/-- [The total selector achieves the all-alphabet frontier rate](goal). -/
theorem frontier_upper_all_d :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon : ℝ, ∃ handle : PolynomialHandle,
      0 < C_epsilon ∧ -- @realizes C_{epsilon}(range [1,infinity) after enlargement)
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → ∀ hM : 1 ≤ M, 0 ≤ sigma → sigma ≤ 2 →
        let poly := polyEstimatorElement (n := n) (d := d) handle hM
        let collision := collisionEstimatorElement (n := n) (d := d) hM
        let selector := totalSelector hM sigma poly collision
        Measurable selector.1 ∧
        (∀ s : Fin n → Obs d, selector.1 s ∈ Icc (-M) M) ∧
        (∀ P : ModelClass d epsilon M sigma,
          mse P.law selector.1 ≤
            C_epsilon * M ^ 2 * frontierRate n d sigma) := by
  intro epsilon hepsilon hepsilon_half
  exact frontier_upper_bound_all_d epsilon hepsilon hepsilon_half

-- @node: thm:frontier-upper
/-- [Restricted-dimension selector upper bound](goal). -/
theorem frontier_upper :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon c_epsilon : ℝ, ∃ handle : PolynomialHandle,
      0 < C_epsilon ∧ 0 < c_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → ∀ hM : 1 ≤ M, 0 ≤ sigma → sigma ≤ 2 →
        (d : ℝ) ≤ c_epsilon * (n : ℝ) ^ 2 / logEN n →
        let poly := polyEstimatorElement (n := n) (d := d) handle hM
        let collision := collisionEstimatorElement (n := n) (d := d) hM
        let selector := totalSelector hM sigma poly collision
        Measurable selector.1 ∧
        (∀ s : Fin n → Obs d, selector.1 s ∈ Icc (-M) M) ∧
        (∀ P : ModelClass d epsilon M sigma,
          mse P.law selector.1 ≤
            C_epsilon * M ^ 2 * frontierRate n d sigma) := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨C_epsilon, handle, hC, hbound⟩ :=
    frontier_upper_all_d epsilon hepsilon hepsilon_half
  refine ⟨C_epsilon, 1, handle, hC, zero_lt_one, ?_⟩
  intro n d M sigma hn hd hM hsigma hsigma_two _
  exact hbound n d M sigma hn hd hM hsigma hsigma_two

-- @node: thm:published-binary-collision-comparison
/-- [The cited binary collision guarantee and the independent algebraic comparison to its
  remainder hold simultaneously](goal). -/
theorem published_binary_collision_comparison :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ZengBinaryCollisionUpper epsilon →
    ZengBinaryCollisionUpper epsilon ∧ PublishedCollisionComparison := by
  intro epsilon hepsilon hepsilon_half hcollision
  refine ⟨hcollision, ?_⟩
  refine ⟨?_, ?_⟩
  · intro n d sigma hn hd hsigma hsigma_two
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  · intro dseq sseq hdomain hpoly hdim
    refine squeeze_zero' ?_ ?_ hpoly
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hd : 0 < dseq n := (hdomain n hn).1
      have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
      have hd_real : 0 < (dseq n : ℝ) := by exact_mod_cast hd
      have hpoly_nonneg : 0 ≤ polynomialComponent n (dseq n) := by
        unfold polynomialComponent
        positivity
      have hcollision_nonneg :
          0 ≤ collisionComponent n (dseq n) (sseq n) := by
        unfold collisionComponent
        positivity
      have hnumerator_nonneg :
          0 ≤ min 1 (min (polynomialComponent n (dseq n))
            (collisionComponent n (dseq n) (sseq n))) := by
        positivity
      exact div_nonneg hnumerator_nonneg hcollision_nonneg
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hd : 0 < dseq n := (hdomain n hn).1
      have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
      have hd_real : 0 < (dseq n : ℝ) := by exact_mod_cast hd
      have hcollision_pos :
          0 < collisionComponent n (dseq n) (sseq n) := by
        unfold collisionComponent
        positivity
      apply div_le_div_of_nonneg_right _ hcollision_pos.le
      exact le_trans (min_le_right _ _) (min_le_left _ _)

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
