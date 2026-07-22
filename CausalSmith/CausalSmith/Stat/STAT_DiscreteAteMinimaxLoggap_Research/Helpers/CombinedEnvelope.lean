import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.T_SharpMinimaxFixedInterior

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory

/-- Deterministic choice between the hybrid and centered estimators. -/
noncomputable def selectedEstimator (C epsilon : ℝ) {n d : ℕ} :
    (Fin n → Obs d) → ℝ :=
  if C * minimaxRate n d ≤ 1 / (n : ℝ) + 4 * (1 / 2 - epsilon) ^ 2 then
    hybridEstimator
  else centeredEstimator

-- @node: lem:combined-upper-envelope
/-- The deterministic smaller-bound selector attains the combined envelope. -/
lemma combined_upper_envelope (epsilon C_epsilon rho_epsilon : ℝ)
    (N_epsilon : ℕ) (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hC : 0 < C_epsilon) (hrho : 0 < rho_epsilon)
    (hHybrid : ∀ n d : ℕ, 0 < n → N_epsilon ≤ n →
      (d : ℝ) ≤ rho_epsilon * n * Real.log n →
      worstCaseMSE n d epsilon hybridEstimator ≤
        C_epsilon * minimaxRate n d) :
    ∀ n d : ℕ, 0 < n → N_epsilon ≤ n →
      (d : ℝ) ≤ rho_epsilon * n * Real.log n →
      let K_epsilon := max C_epsilon 4
      minimaxRisk n d epsilon ≤
          worstCaseMSE n d epsilon (selectedEstimator C_epsilon epsilon) ∧
        worstCaseMSE n d epsilon (selectedEstimator C_epsilon epsilon) ≤
          K_epsilon *
            (1 / (n : ℝ) +
              min (d ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2))
                ((1 / 2 - epsilon) ^ 2)) := by
  intro n d hn hnN hd
  let a : ℝ := 1 / (n : ℝ)
  let u : ℝ := d ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)
  let v : ℝ := (1 / 2 - epsilon) ^ 2
  let K : ℝ := max C_epsilon 4
  have hcentered : worstCaseMSE n d epsilon centeredEstimator ≤ a + 4 * v := by
    unfold worstCaseMSE
    cases isEmpty_or_nonempty (ClassLaw n d epsilon) with
    | inl hempty =>
        letI := hempty
        simp
        positivity
    | inr hnonempty =>
        letI := hnonempty
        apply ciSup_le
        intro P
        simpa [a, v] using
          near_randomization_linear_upper P.1 (productLaw P.1 n) P.2 hn
  have hselected : worstCaseMSE n d epsilon
      (selectedEstimator C_epsilon epsilon) ≤ min (C_epsilon * (a + u)) (a + 4 * v) := by
    rw [selectedEstimator]
    split_ifs with hchoice
    · rw [min_eq_left]
      · simpa [a, u, minimaxRate] using hHybrid n d hn hnN hd
      · simpa [a, u, v, minimaxRate] using hchoice
    · rw [min_eq_right]
      · exact hcentered
      · exact le_of_not_ge hchoice
  have hminimax : minimaxRisk n d epsilon ≤
      worstCaseMSE n d epsilon (selectedEstimator C_epsilon epsilon) := by
    have hmeas : Measurable (@selectedEstimator C_epsilon epsilon n d) :=
      measurable_of_finite _
    have hb : BddBelow (Set.range (fun est :
        {f : (Fin n → Obs d) → ℝ // Measurable f} =>
          worstCaseMSE n d epsilon est.1)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨est, rfl⟩
      unfold worstCaseMSE
      cases isEmpty_or_nonempty (ClassLaw n d epsilon) with
      | inl hempty =>
          letI := hempty
          simp
      | inr hnonempty =>
          letI := hnonempty
          by_cases hbounded : BddAbove (Set.range (fun P : ClassLaw n d epsilon =>
              mse (productLaw P.1 n) est (ateFunctional P.1)))
          · have hmse : 0 ≤ mse
                (productLaw (Classical.arbitrary (ClassLaw n d epsilon)).1 n)
                est
                (ateFunctional (Classical.arbitrary (ClassLaw n d epsilon)).1) := by
              unfold mse
              exact integral_nonneg (fun x => sq_nonneg (est.1 x -
                ateFunctional (Classical.arbitrary (ClassLaw n d epsilon)).1))
            exact hmse.trans (le_ciSup hbounded (Classical.arbitrary _))
          · change 0 ≤ (⨆ P : ClassLaw n d epsilon,
                mse (productLaw P.1 n) est (ateFunctional P.1))
            rw [show (⨆ P : ClassLaw n d epsilon,
                mse (productLaw P.1 n) est (ateFunctional P.1)) = sSup ∅ from
                csSup_of_not_bddAbove hbounded]
            simp
    exact ciInf_le hb
      (⟨selectedEstimator C_epsilon epsilon, hmeas⟩ :
        {f : (Fin n → Obs d) → ℝ // Measurable f})
  refine ⟨hminimax, hselected.trans ?_⟩
  have hC_le_K : C_epsilon ≤ K := le_max_left _ _
  have h4_le_K : 4 ≤ K := le_max_right _ _
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hv : 0 ≤ v := sq_nonneg _
  have hfirst : C_epsilon * (a + u) ≤ K * (a + u) := by
    exact mul_le_mul_of_nonneg_right hC_le_K (add_nonneg ha hu)
  have hsecond : a + 4 * v ≤ K * (a + v) := by
    calc
      a + 4 * v ≤ K * a + K * v :=
        add_le_add (by nlinarith [h4_le_K])
          (mul_le_mul_of_nonneg_right h4_le_K hv)
      _ = K * (a + v) := by ring
  by_cases huv : u ≤ v
  · rw [min_eq_left huv]
    change min (C_epsilon * (a + u)) (a + 4 * v) ≤ K * (a + u)
    exact (min_le_left _ _).trans hfirst
  · rw [min_eq_right (le_of_not_ge huv)]
    change min (C_epsilon * (a + u)) (a + 4 * v) ≤ K * (a + v)
    exact (min_le_right _ _).trans hsecond

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
