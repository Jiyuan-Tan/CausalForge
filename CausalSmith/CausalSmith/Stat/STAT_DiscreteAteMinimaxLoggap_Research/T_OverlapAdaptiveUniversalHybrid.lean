import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.CombinedEnvelope
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HybridProgram

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory

/-!
Clause (v) is deliberately represented by this scope note rather than a Lean
proposition: every constant below is pointwise in a fixed `epsilon`.  Nothing in
this theorem asserts a matching lower envelope for triangular arrays
`epsilon = epsilon_n`.
-/

-- @node: overlap_adaptive_universal_hybrid_statistical
/-- The statistical clauses of the universal-hybrid theorem, assembled from
the fixed-interior upper bound, centered-estimator bound, endpoint bracket, and
deterministic selector. -/
lemma overlap_adaptive_universal_hybrid_statistical :
    (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
      ∃ C_epsilon rho_epsilon : ℝ, ∃ N_epsilon : ℕ,
        0 < C_epsilon ∧ 0 < rho_epsilon ∧
        ∀ n d : ℕ, 0 < n → 0 < d → N_epsilon ≤ n →
          (d : ℝ) ≤ rho_epsilon * n * Real.log n →
          worstCaseMSE n d epsilon hybridEstimator ≤
              C_epsilon * minimaxRate n d ∧
          minimaxRisk n d epsilon ≤
              worstCaseMSE n d epsilon
                (selectedEstimator C_epsilon epsilon) ∧
          worstCaseMSE n d epsilon
              (selectedEstimator C_epsilon epsilon) ≤
            max C_epsilon 4 *
              (1 / (n : ℝ) +
                min (d ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2))
                  ((1 / 2 - epsilon) ^ 2))) ∧
    (∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / 2 →
      ∀ n d : ℕ, 0 < n → 0 < d →
        worstCaseMSE n d epsilon centeredEstimator ≤
          1 / (n : ℝ) + 4 * (1 / 2 - epsilon) ^ 2) ∧
    (∀ n d : ℕ, 0 < n → 0 < d →
      1 / (100 * (n : ℝ)) ≤ minimaxRisk n d (1 / 2) ∧
        minimaxRisk n d (1 / 2) ≤ 1 / (n : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro epsilon he0 he1
    rcases hybrid_upper_fixed_interior epsilon he0 he1 with
      ⟨C, rho, N, hC, hrho, hupper⟩
    have hhybrid : ∀ n d : ℕ, 0 < n → N ≤ n →
        (d : ℝ) ≤ rho * n * Real.log n →
        worstCaseMSE n d epsilon hybridEstimator ≤ C * minimaxRate n d := by
      intro n d hn hnN hdim
      by_cases hd : 0 < d
      · let Q := canonicalClassLaw n d hd epsilon he0 he1
        exact (hupper n d Q.1 (productLaw Q.1 n) Q.2 hnN hdim).2
      · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
        subst d
        letI : IsEmpty (DiscreteLaw 0) := ⟨fun P => by
          have hmass := P.pmf.tsum_coe
          simpa using hmass⟩
        letI : IsEmpty (ClassLaw n 0 epsilon) :=
          ⟨fun Q => isEmptyElim Q.1⟩
        simpa [worstCaseMSE, minimaxRate] using
          mul_nonneg (le_of_lt hC) (inv_nonneg.mpr (Nat.cast_nonneg n))
    refine ⟨C, rho, N, hC, hrho, ?_⟩
    intro n d hn hd hnN hdim
    have hselector := combined_upper_envelope epsilon C rho N he0 he1 hC hrho
      hhybrid n d hn hnN hdim
    exact ⟨hhybrid n d hn hnN hdim, hselector.1, hselector.2⟩
  · intro epsilon he0 hehalf n d hn _hd
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
        simpa using near_randomization_linear_upper P.1 (productLaw P.1 n) P.2 hn
  · intro n d hn hd
    exact randomized_endpoint_minimax n d hn hd

-- @node: thm:overlap-adaptive-universal-hybrid
/-- Universal fixed-class calibration, the all-sample centered bound, the exact
randomization bracket, and the combined upper envelope.  Clause (i) includes a
finite real-arithmetic realization with the stated `O(d M^4)` operation bound;
the hybrid's type has no `epsilon` argument, realizing its no-selector claim. -/
theorem overlap_adaptive_universal_hybrid :
    HybridEstimatorComputable ∧
    (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
      ∃ C_epsilon rho_epsilon : ℝ, ∃ N_epsilon : ℕ,
        0 < C_epsilon ∧ 0 < rho_epsilon ∧
        ∀ n d : ℕ, 0 < n → 0 < d → N_epsilon ≤ n →
          (d : ℝ) ≤ rho_epsilon * n * Real.log n →
          worstCaseMSE n d epsilon hybridEstimator ≤
              C_epsilon * minimaxRate n d ∧
          minimaxRisk n d epsilon ≤
              worstCaseMSE n d epsilon
                (selectedEstimator C_epsilon epsilon) ∧
          worstCaseMSE n d epsilon
              (selectedEstimator C_epsilon epsilon) ≤
            max C_epsilon 4 *
              (1 / (n : ℝ) +
                min (d ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2))
                  ((1 / 2 - epsilon) ^ 2))) ∧
    (∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / 2 →
      ∀ n d : ℕ, 0 < n → 0 < d →
        worstCaseMSE n d epsilon centeredEstimator ≤
          1 / (n : ℝ) + 4 * (1 / 2 - epsilon) ^ 2) ∧
    (∀ n d : ℕ, 0 < n → 0 < d →
      1 / (100 * (n : ℝ)) ≤ minimaxRisk n d (1 / 2) ∧
        minimaxRisk n d (1 / 2) ≤ 1 / (n : ℝ)) := by
  refine ⟨?_, overlap_adaptive_universal_hybrid_statistical⟩
  exact hybridEstimatorComputable

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
