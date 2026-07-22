import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCell

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory

/-- The control-zero subclass `D₀`: overlap laws with `mu_0k=0` in every cell. -/
structure ControlZeroClass (n : ℕ) {d : ℕ} (epsilon : ℝ)
    (P : DiscreteLaw d) : Prop
    extends ExperimentClass n epsilon P (productLaw P n) where
  control_zero : ∀ k, outcomeMean P false k = 0

def ControlZeroLaw (n d : ℕ) (epsilon : ℝ) :=
  {P : DiscreteLaw d // ControlZeroClass n epsilon P}

/-- Treated-arm functional `psi₁(P)=sum_k p_k mu_1k`. -/
noncomputable def treatedFunctional {d : ℕ} (P : DiscreteLaw d) : ℝ :=
  ∑ k : Fin d, cellMass P k * outcomeMean P true k

noncomputable def oneArmWorstCaseMSE (n d : ℕ) (epsilon : ℝ)
    (est : (Fin n → Obs d) → ℝ) : ℝ :=
  ⨆ P : ControlZeroLaw n d epsilon,
    mse (productLaw P.1 n) est (treatedFunctional P.1)

noncomputable def oneArmMinimaxRisk (n d : ℕ) (epsilon : ℝ) : ℝ :=
  ⨅ est : {f : (Fin n → Obs d) → ℝ // Measurable f},
    oneArmWorstCaseMSE n d epsilon est.1

-- @node: mse_le_estimator_abs_sum_bound
/-- A uniform finite-alphabet bound used to justify the two class suprema. -/
lemma mse_le_estimator_abs_sum_bound {n d : ℕ} {epsilon : ℝ} (P : DiscreteLaw d)
    (hOverlap : Overlap epsilon P)
    (est : (Fin n → Obs d) → ℝ) :
    mse (productLaw P n) est (ateFunctional P) ≤
      ((∑ sample : Fin n → Obs d, |est sample|) + 1) ^ 2 := by
  have htau := ateFunctional_mem_interval P hOverlap
  have htau_abs : |ateFunctional P| ≤ 1 := (abs_le).2 htau
  have hest (sample : Fin n → Obs d) :
      |est sample| ≤ ∑ x : Fin n → Obs d, |est x| := by
    exact Finset.single_le_sum (fun i _ => abs_nonneg (est i)) (Finset.mem_univ sample)
  unfold mse
  calc
    ∫ x, (est x - ateFunctional P) ^ 2 ∂productLaw P n ≤
        ∫ _x, ((∑ sample : Fin n → Obs d, |est sample|) + 1) ^ 2
          ∂productLaw P n := by
      apply integral_mono_ae
      · exact MemLp.of_discrete.integrable_sq
      · exact integrable_const _
      · filter_upwards with x
        have habs : |est x - ateFunctional P| ≤
            (∑ sample : Fin n → Obs d, |est sample|) + 1 :=
          (abs_sub _ _).trans (add_le_add (hest x) htau_abs)
        have hB : 0 ≤ (∑ sample : Fin n → Obs d, |est sample|) + 1 := by
          positivity
        exact (sq_le_sq).2 (by simpa [abs_of_nonneg hB] using habs)
    _ = ((∑ sample : Fin n → Obs d, |est sample|) + 1) ^ 2 := by simp

-- @node: lem:zeng-one-arm-minimax-lower
/-- **Cited gate (Zeng, Balakrishnan, Han, Kennedy, 2026).**
Source handle `cite:zeng-balakrishnan-han-kennedy-2024`, arXiv:2405.00118v3,
Theorem 2 and Appendix C.5, with the fixed-sample transfer in Lemma 4 and
Appendix D.2.  This is the documented fixed-sample control-zero specialization:
the treated-arm minimax risk has the stated scale for every positive alphabet
size in the source range. -/
def ZengOneArmMinimaxLower (epsilon : ℝ) : Prop :=
  0 < epsilon ∧ epsilon < 1 / 2 →
    ∃ a_epsilon b_epsilon : ℝ, ∃ N_epsilon : ℕ,
      0 < a_epsilon ∧ 0 < b_epsilon ∧
      ∀ n d : ℕ, 0 < d → N_epsilon ≤ n →
        (d : ℝ) ≤ b_epsilon * n * Real.log n →
        a_epsilon * minimaxRate n d ≤ oneArmMinimaxRisk n d epsilon

/-- On the control-zero subclass the observed-data ATE is the treated functional. -/
lemma ateFunctional_eq_treated_on_controlZero {n d : ℕ} {epsilon : ℝ}
    (P : ControlZeroLaw n d epsilon) :
    ateFunctional P.1 = treatedFunctional P.1 := by
  rw [ateFunctional_eq_weighted_regression P.1 P.2.overlap]
  unfold treatedFunctional
  apply Finset.sum_congr rfl
  intro k _
  rw [P.2.control_zero k, sub_zero]

/-- Restricting the global ATE experiment to the control-zero subclass can only
decrease minimax risk.  The target identity is proved law-by-law before the
subclass supremum and common estimator infimum are compared. -/
-- @node: oneArmMinimaxRisk_le_minimaxRisk
lemma oneArmMinimaxRisk_le_minimaxRisk (n d : ℕ) (epsilon : ℝ) :
    oneArmMinimaxRisk n d epsilon ≤ minimaxRisk n d epsilon := by
  have htarget : ∀ P : ControlZeroLaw n d epsilon,
      ateFunctional P.1 = treatedFunctional P.1 :=
    ateFunctional_eq_treated_on_controlZero
  unfold oneArmMinimaxRisk minimaxRisk
  apply ciInf_mono
  · refine ⟨0, ?_⟩
    rintro _ ⟨est, rfl⟩
    unfold oneArmWorstCaseMSE
    cases isEmpty_or_nonempty (ControlZeroLaw n d epsilon) with
    | inl hempty =>
        letI := hempty
        simp
    | inr hnonempty =>
        letI := hnonempty
        change 0 ≤ ⨆ P : ControlZeroLaw n d epsilon,
          mse (productLaw P.1 n) est.1 (treatedFunctional P.1)
        let P : ControlZeroLaw n d epsilon := Classical.arbitrary _
        have hb : BddAbove (Set.range (fun R : ControlZeroLaw n d epsilon =>
            mse (productLaw R.1 n) est.1 (treatedFunctional R.1))) := by
          refine ⟨((∑ sample : Fin n → Obs d, |est.1 sample|) + 1) ^ 2, ?_⟩
          rintro _ ⟨R, rfl⟩
          change mse (productLaw R.1 n) est.1 (treatedFunctional R.1) ≤ _
          rw [← htarget R]
          exact mse_le_estimator_abs_sum_bound R.1 R.2.overlap est.1
        have hnonneg : 0 ≤ mse (productLaw P.1 n) est.1 (treatedFunctional P.1) := by
          unfold mse
          exact integral_nonneg
            (fun x => sq_nonneg (est.1 x - treatedFunctional P.1))
        exact hnonneg.trans (le_ciSup hb P)
  · intro est
    cases isEmpty_or_nonempty (ControlZeroLaw n d epsilon) with
    | inl hempty =>
        letI := hempty
        simp [oneArmWorstCaseMSE]
        unfold worstCaseMSE
        cases isEmpty_or_nonempty (ClassLaw n d epsilon) with
        | inl hclass_empty =>
            letI := hclass_empty
            simp
        | inr hclass_nonempty =>
            letI := hclass_nonempty
            change 0 ≤ ⨆ P : ClassLaw n d epsilon,
              mse (productLaw P.1 n) est.1 (ateFunctional P.1)
            let P : ClassLaw n d epsilon := Classical.arbitrary _
            have hb : BddAbove (Set.range (fun R : ClassLaw n d epsilon =>
                mse (productLaw R.1 n) est.1 (ateFunctional R.1))) := by
              refine ⟨((∑ sample : Fin n → Obs d, |est.1 sample|) + 1) ^ 2, ?_⟩
              rintro _ ⟨R, rfl⟩
              exact mse_le_estimator_abs_sum_bound R.1 R.2.overlap est.1
            have hnonneg : 0 ≤ mse (productLaw P.1 n) est.1 (ateFunctional P.1) := by
              unfold mse
              exact integral_nonneg
                (fun x => sq_nonneg (est.1 x - ateFunctional P.1))
            exact hnonneg.trans (le_ciSup hb P)
    | inr hnonempty =>
        letI := hnonempty
        unfold oneArmWorstCaseMSE worstCaseMSE
        apply ciSup_le
        intro P
        rw [← htarget P]
        let Q : ClassLaw n d epsilon := ⟨P.1, P.2.toExperimentClass⟩
        refine le_ciSup_of_le ?_ Q ?_
        · refine ⟨((∑ sample : Fin n → Obs d, |est.1 sample|) + 1) ^ 2, ?_⟩
          rintro _ ⟨R, rfl⟩
          exact mse_le_estimator_abs_sum_bound R.1 R.2.overlap est.1
        · exact le_rfl

-- @node: lem:ate-lower-bound-transfer
/-- Transfers the cited control-zero one-arm converse to the unrestricted ATE
minimax problem by restriction of the law class. -/
lemma ate_lower_bound_transfer {epsilon : ℝ}
    (hZeng : ZengOneArmMinimaxLower epsilon) (he0 : 0 < epsilon)
    (he1 : epsilon < 1 / 2) :
    ∃ a_epsilon b_epsilon : ℝ, ∃ N_epsilon : ℕ,
      0 < a_epsilon ∧ 0 < b_epsilon ∧
      ∀ n d : ℕ, 0 < d → N_epsilon ≤ n →
        (d : ℝ) ≤ b_epsilon * n * Real.log n →
        a_epsilon * minimaxRate n d ≤ minimaxRisk n d epsilon := by
  rcases hZeng ⟨he0, he1⟩ with
    ⟨a_epsilon, b_epsilon, N_epsilon, ha, hb, hLower⟩
  refine ⟨a_epsilon, b_epsilon, N_epsilon, ha, hb, ?_⟩
  intro n d hd_pos hn hd_range
  exact (hLower n d hd_pos hn hd_range).trans
    (oneArmMinimaxRisk_le_minimaxRisk n d epsilon)

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
