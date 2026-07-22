import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HeavyCell
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LowerBound
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Endpoint

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory Filter
open scoped Topology

-- @node: clamp_sq_error_le
/-- Establishes the stated upper bound for clamp sq error le. -/
lemma clamp_sq_error_le (x t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (max (-1) (min 1 x) - t) ^ 2 ≤ (x - t) ^ 2 := by
  rcases ht with ⟨htl, htu⟩
  by_cases hxlow : x ≤ -1
  · rw [min_eq_right (hxlow.trans (by norm_num : (-1 : ℝ) ≤ 1)),
      max_eq_left hxlow]
    nlinarith [sq_nonneg (x - t)]
  · have hxlow' : -1 ≤ x := le_of_not_ge hxlow
    rw [max_eq_right (le_min (by norm_num) hxlow')]
    by_cases hxhigh : x ≤ 1
    · rw [min_eq_right hxhigh]
    · rw [min_eq_left (le_of_not_ge hxhigh)]
      nlinarith [sq_nonneg (x - t)]

-- @node: targetHeavy_add_targetLight
/-- Establishes the stated property of target Heavy add target Light in the discrete average-treatment-effect construction. -/
lemma targetHeavy_add_targetLight {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) :
    targetHeavy P sample + targetLight P sample = ateFunctional P := by
  rw [targetHeavy, targetLight, ateFunctional]
  rw [← Finset.sum_union]
  · congr 1
    rw [lightCells_eq_compl]
    exact Finset.union_compl _
  · rw [Finset.disjoint_left]
    intro k hkH hkL
    rw [lightCells_eq_compl] at hkL
    exact (Finset.mem_compl.mp hkL) hkH

-- @node: hybrid_mse_le_component_errors
/-- Establishes the stated upper bound for hybrid mse le component errors. -/
lemma hybrid_mse_le_component_errors {n d : ℕ} {epsilon : ℝ} (P : DiscreteLaw d)
    (mu_n : Measure (Fin n → Obs d)) (hclass : ExperimentClass n epsilon P mu_n) :
    mse mu_n hybridEstimator (ateFunctional P) ≤
      2 * componentErrorMSE mu_n heavyContribution (targetHeavy P) +
        2 * componentErrorMSE mu_n lightContribution (targetLight P) := by
  have hpoint : ∀ sample : Fin n → Obs d,
      (hybridEstimator sample - ateFunctional P) ^ 2 ≤
        2 * (heavyContribution sample - targetHeavy P sample) ^ 2 +
        2 * (lightContribution sample - targetLight P sample) ^ 2 := by
    intro sample
    calc
      (hybridEstimator sample - ateFunctional P) ^ 2 ≤
          (heavyContribution sample + lightContribution sample -
            ateFunctional P) ^ 2 := by
        exact clamp_sq_error_le _ _ (ateFunctional_mem_interval P hclass.overlap)
      _ = ((heavyContribution sample - targetHeavy P sample) +
            (lightContribution sample - targetLight P sample)) ^ 2 := by
        have ht := targetHeavy_add_targetLight P sample
        rw [← ht]
        ring
      _ ≤ 2 * (heavyContribution sample - targetHeavy P sample) ^ 2 +
            2 * (lightContribution sample - targetLight P sample) ^ 2 := by
        nlinarith [sq_nonneg ((heavyContribution sample - targetHeavy P sample) -
          (lightContribution sample - targetLight P sample))]
  rw [hclass.product_law]
  unfold mse componentErrorMSE
  calc
    ∫ sample, (hybridEstimator sample - ateFunctional P) ^ 2 ∂productLaw P n ≤
        ∫ sample, (2 * (heavyContribution sample - targetHeavy P sample) ^ 2 +
          2 * (lightContribution sample - targetLight P sample) ^ 2) ∂productLaw P n :=
      integral_mono_ae Integrable.of_finite Integrable.of_finite
        (Filter.Eventually.of_forall hpoint)
    _ = 2 * ∫ sample, (heavyContribution sample - targetHeavy P sample) ^ 2 ∂productLaw P n +
          2 * ∫ sample, (lightContribution sample - targetLight P sample) ^ 2 ∂productLaw P n := by
      rw [integral_add Integrable.of_finite Integrable.of_finite,
        integral_const_mul, integral_const_mul]

-- @node: canonicalClassLaw
/-- Defines canonical Class Law, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def canonicalClassLaw (n d : ℕ) (hd : 0 < d) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) : ClassLaw n d epsilon := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let hv := Causalean.Estimation.MinimaxATE.Parametric.validDGP_null
    (C := Fin d) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let P := endpointParametricLaw hv
  refine ⟨P, ⟨he0, le_of_lt he1, rfl, ?_⟩⟩
  have hhalf := endpointParametricLaw_overlap (d := d) hv
  intro k hk
  rcases hhalf k hk with ⟨hl, hu⟩
  constructor <;> linarith

/-- Certified upper half, separated from the cited lower gate for downstream use. -/
-- @node: hybrid_upper_fixed_interior
lemma hybrid_upper_fixed_interior (epsilon : ℝ) (he0 : 0 < epsilon)
    (he1 : epsilon < 1 / 2) :
    ∃ C_epsilon rho_epsilon : ℝ, ∃ N_epsilon : ℕ,
      0 < C_epsilon ∧ 0 < rho_epsilon ∧
      ∀ (n d : ℕ) (P : DiscreteLaw d)
        (mu_n : Measure (Fin n → Obs d)),
        ExperimentClass n epsilon P mu_n →
        N_epsilon ≤ n →
        (d : ℝ) ≤ rho_epsilon * n * Real.log n →
        minimaxRisk n d epsilon ≤ worstCaseMSE n d epsilon hybridEstimator ∧
        worstCaseMSE n d epsilon hybridEstimator ≤
          C_epsilon * minimaxRate n d := by
  rcases light_cell_polynomial epsilon he0 (le_of_lt he1) with ⟨_, hlightRate⟩
  rcases hlightRate with ⟨CL, ⟨cL, ⟨hCL, ⟨hcL, hlight⟩⟩⟩⟩
  rcases universal_heavy_cell_rate epsilon he0 he1 with
    ⟨CH, cH, NH, hCH, hcH, hheavy⟩
  refine ⟨2 * (CL + CH), min cL cH, NH, by positivity, lt_min hcL hcH, ?_⟩
  intro n d P mu_n hclass hn hd
  have hdL : (d : ℝ) ≤ cL * n * Real.log n :=
    hd.trans (by gcongr; exact min_le_left _ _)
  have hdH : (d : ℝ) ≤ cH * n * Real.log n :=
    hd.trans (by gcongr; exact min_le_right _ _)
  have hL := hlight n d P mu_n hclass hdL
  have hH := hheavy n d P mu_n hn hdH hclass
  have hrate : 0 ≤ minimaxRate n d := by
    unfold minimaxRate
    positivity
  have hLaw : mse mu_n hybridEstimator (ateFunctional P) ≤
      (2 * (CL + CH)) * minimaxRate n d := by
    calc
      _ ≤ 2 * componentErrorMSE mu_n heavyContribution (targetHeavy P) +
          2 * componentErrorMSE mu_n lightContribution (targetLight P) :=
        hybrid_mse_le_component_errors P mu_n hclass
      _ ≤ 2 * (CH * minimaxRate n d) + 2 * (CL * minimaxRate n d) := by
        gcongr
      _ = (2 * (CL + CH)) * minimaxRate n d := by ring
  constructor
  · have hmeas : Measurable (@hybridEstimator n d) := measurable_of_finite _
    have hb : BddBelow (Set.range (fun est :
        {f : (Fin n → Obs d) → ℝ // Measurable f} =>
          worstCaseMSE n d epsilon est.1)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨est, rfl⟩
      unfold worstCaseMSE
      let Q : ClassLaw n d epsilon := ⟨P,
        ⟨hclass.epsilon_pos, hclass.epsilon_le_half, rfl, hclass.overlap⟩⟩
      letI : Nonempty (ClassLaw n d epsilon) := ⟨Q⟩
      exact (integral_nonneg (fun x => sq_nonneg (est.1 x - ateFunctional Q.1))).trans
        (le_ciSup (show BddAbove (Set.range (fun R : ClassLaw n d epsilon =>
          mse (productLaw R.1 n) est.1 (ateFunctional R.1))) from by
            refine ⟨((∑ sample : Fin n → Obs d, |est.1 sample|) + 1) ^ 2, ?_⟩
            rintro _ ⟨R, rfl⟩
            exact mse_le_estimator_abs_sum_bound R.1 R.2.overlap est.1) Q)
    exact ciInf_le hb ⟨hybridEstimator, hmeas⟩
  · unfold worstCaseMSE
    let Q0 : ClassLaw n d epsilon := ⟨P,
      ⟨hclass.epsilon_pos, hclass.epsilon_le_half, rfl, hclass.overlap⟩⟩
    letI : Nonempty (ClassLaw n d epsilon) := ⟨Q0⟩
    apply ciSup_le
    intro Q
    have hLQ := hlight n d Q.1 (productLaw Q.1 n) Q.2 hdL
    have hHQ := hheavy n d Q.1 (productLaw Q.1 n) hn hdH Q.2
    calc
      mse (productLaw Q.1 n) hybridEstimator (ateFunctional Q.1) ≤
          2 * componentErrorMSE (productLaw Q.1 n) heavyContribution (targetHeavy Q.1) +
            2 * componentErrorMSE (productLaw Q.1 n) lightContribution (targetLight Q.1) :=
        hybrid_mse_le_component_errors Q.1 (productLaw Q.1 n) Q.2
      _ ≤ 2 * (CH * minimaxRate n d) + 2 * (CL * minimaxRate n d) := by gcongr
      _ = (2 * (CL + CH)) * minimaxRate n d := by ring

-- @node: thm:sharp-minimax-fixed-interior
/-- Matched fixed-interior minimax rate.  The lower half is explicitly
conditional on the cited `ZengOneArmMinimaxLower` interface. -/
theorem sharp_minimax_fixed_interior (epsilon : ℝ)
    (hZeng : ZengOneArmMinimaxLower epsilon) (he0 : 0 < epsilon)
    (he1 : epsilon < 1 / 2) :
    ∃ a_epsilon rho_epsilon C_epsilon : ℝ, ∃ N_epsilon : ℕ,
      0 < a_epsilon ∧ 0 < rho_epsilon ∧ 0 < C_epsilon ∧
      (∀ (n d : ℕ) (P : DiscreteLaw d)
        (mu_n : Measure (Fin n → Obs d)),
        ExperimentClass n epsilon P mu_n →
        0 < d →
        N_epsilon ≤ n →
        (d : ℝ) ≤ rho_epsilon * n * Real.log n →
        a_epsilon * minimaxRate n d ≤ minimaxRisk n d epsilon ∧
        minimaxRisk n d epsilon ≤ worstCaseMSE n d epsilon hybridEstimator ∧
        worstCaseMSE n d epsilon hybridEstimator ≤
          C_epsilon * minimaxRate n d) ∧
      (∀ K : ℝ, 0 < K → ∃ C_K : ℝ, 0 < C_K ∧
        ∀ (n d : ℕ) (P : DiscreteLaw d)
          (mu_n : Measure (Fin n → Obs d)),
          ExperimentClass n epsilon P mu_n →
          0 < d →
          N_epsilon ≤ n →
          (d : ℝ) ≤ K * Real.sqrt n * Real.log n →
          (d : ℝ) ≤ rho_epsilon * n * Real.log n →
          a_epsilon / n ≤ minimaxRisk n d epsilon ∧
          minimaxRisk n d epsilon ≤ C_K / n) ∧
      (∀ ns ds : ℕ → ℕ,
        Tendsto ns atTop atTop →
        (∀ᶠ j in atTop, 0 < ds j) →
        (∀ᶠ j in atTop,
          (ds j : ℝ) ≤ rho_epsilon * ns j * Real.log (ns j)) →
        (Tendsto (fun j => minimaxRisk (ns j) (ds j) epsilon) atTop (nhds 0) ↔
          Tendsto (fun j => (ds j : ℝ) / (ns j * Real.log (ns j)))
            atTop (nhds 0))) := by
  rcases hybrid_upper_fixed_interior epsilon he0 he1 with
    ⟨CU, rhoU, NU, hCU, hrhoU, hupper⟩
  rcases ate_lower_bound_transfer hZeng he0 he1 with
    ⟨a, rhoL, NL, ha, hrhoL, hlower⟩
  let rho := min rhoU rhoL
  let N := max NU NL
  refine ⟨a, rho, CU, N, ha, lt_min hrhoU hrhoL, hCU, ?_, ?_, ?_⟩
  · intro n d P mu_n hclass hd hn hdRange
    have hnU : NU ≤ n := (le_max_left _ _).trans hn
    have hnL : NL ≤ n := (le_max_right _ _).trans hn
    have hdU : (d : ℝ) ≤ rhoU * n * Real.log n :=
      hdRange.trans (by dsimp [rho]; gcongr; exact min_le_left _ _)
    have hdL : (d : ℝ) ≤ rhoL * n * Real.log n :=
      hdRange.trans (by dsimp [rho]; gcongr; exact min_le_right _ _)
    rcases hupper n d P mu_n hclass hnU hdU with ⟨hmin, hU⟩
    exact ⟨hlower n d hd hnL hdL, hmin, hU⟩
  · intro K hK
    refine ⟨CU * (1 + K ^ 2), by positivity, ?_⟩
    intro n d P mu_n hclass hd hn hdK hdRange
    have hnpos : 0 < n := by
      by_contra hn0
      have hnz : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      norm_num at hdK
      omega
    have hlog : 0 < Real.log (n : ℝ) := by
      have hdcast : 0 < (d : ℝ) := by exact_mod_cast hd
      have hfactor : 0 ≤ K * Real.sqrt (n : ℝ) := by positivity
      by_contra hnot
      have hnonpos : Real.log (n : ℝ) ≤ 0 := le_of_not_gt hnot
      have : K * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hfactor hnonpos
      linarith
    have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hdcast : 0 ≤ (d : ℝ) := by positivity
    have hright : 0 ≤ K * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by positivity
    have hsq : (d : ℝ) ^ 2 ≤ K ^ 2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
      have := (sq_le_sq₀ hdcast hright).2 hdK
      rw [mul_pow, mul_pow, Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)] at this
      nlinarith
    have hratio : d ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2) ≤ K ^ 2 / n := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      apply (div_le_div_iff₀
        (mul_pos (sq_pos_of_pos hnR) (sq_pos_of_pos hlog)) hnR).2
      nlinarith [hsq]
    have hnU : NU ≤ n := (le_max_left _ _).trans hn
    have hdU : (d : ℝ) ≤ rhoU * n * Real.log n :=
      hdRange.trans (by dsimp [rho]; gcongr; exact min_le_left _ _)
    rcases hupper n d P mu_n hclass hnU hdU with ⟨hmin, hU⟩
    constructor
    · calc
        a / n ≤ a * minimaxRate n d := by
          unfold minimaxRate
          have : 0 ≤ d ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2) := by positivity
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right this) (le_of_lt ha)
        _ ≤ minimaxRisk n d epsilon := by
          have hnL : NL ≤ n := (le_max_right _ _).trans hn
          have hdL : (d : ℝ) ≤ rhoL * n * Real.log n :=
            hdRange.trans (by dsimp [rho]; gcongr; exact min_le_right _ _)
          exact hlower n d hd hnL hdL
    · calc
        minimaxRisk n d epsilon ≤ CU * minimaxRate n d := hmin.trans hU
        _ ≤ (CU * (1 + K ^ 2)) / n := by
          unfold minimaxRate
          have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
          calc
            CU * (1 / (n : ℝ) + d ^ 2 / ((n : ℝ) ^ 2 * Real.log n ^ 2)) ≤
                CU * (1 / (n : ℝ) + K ^ 2 / n) := by gcongr
            _ = (CU * (1 + K ^ 2)) / n := by ring
  · intro ns ds hns hdsPos hdsRange
    let q : ℕ → ℝ := fun j => (ds j : ℝ) / (ns j * Real.log (ns j))
    have hnsCast : Tendsto (fun j => (ns j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hns
    have hinv : Tendsto (fun j => 1 / (ns j : ℝ)) atTop (nhds 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero.comp hnsCast
    have hq_nonneg : ∀ᶠ j in atTop, 0 ≤ q j := by
      filter_upwards [hns (eventually_ge_atTop 2)] with j hj
      dsimp [q]
      positivity
    have hrate_eq : ∀ᶠ j in atTop,
        minimaxRate (ns j) (ds j) = 1 / (ns j : ℝ) + (q j) ^ 2 := by
      filter_upwards with j
      dsimp [q, minimaxRate]
      ring
    have hbounds : ∀ᶠ j in atTop,
        a * minimaxRate (ns j) (ds j) ≤ minimaxRisk (ns j) (ds j) epsilon ∧
        minimaxRisk (ns j) (ds j) epsilon ≤ CU * minimaxRate (ns j) (ds j) := by
      filter_upwards [hdsPos, hdsRange, hns (eventually_ge_atTop N)] with j hdj hrange hn
      let Pj := canonicalClassLaw (ns j) (ds j) hdj epsilon he0 he1
      have hmain := hupper (ns j) (ds j) Pj.1 (productLaw Pj.1 (ns j)) Pj.2
        ((le_max_left _ _).trans hn)
        (hrange.trans (by dsimp [rho]; gcongr; exact min_le_left _ _))
      exact ⟨hlower (ns j) (ds j) hdj ((le_max_right _ _).trans hn)
        (hrange.trans (by dsimp [rho]; gcongr; exact min_le_right _ _)), hmain.1.trans hmain.2⟩
    constructor
    · intro hrisk
      have hrate : Tendsto (fun j => minimaxRate (ns j) (ds j)) atTop (nhds 0) := by
        apply squeeze_zero'
        · filter_upwards with j
          unfold minimaxRate
          positivity
        · filter_upwards [hbounds] with j hj
          calc
            minimaxRate (ns j) (ds j) = a⁻¹ * (a * minimaxRate (ns j) (ds j)) := by
              field_simp
            _ ≤ a⁻¹ * minimaxRisk (ns j) (ds j) epsilon :=
              mul_le_mul_of_nonneg_left hj.1 (inv_nonneg.mpr (le_of_lt ha))
        · simpa using (tendsto_const_nhds.mul hrisk :
            Tendsto (fun j => a⁻¹ * minimaxRisk (ns j) (ds j) epsilon)
              atTop (nhds (a⁻¹ * 0)))
      have hq_sq : Tendsto (fun j => (q j) ^ 2) atTop (nhds 0) := by
        apply squeeze_zero'
        · exact Filter.Eventually.of_forall (fun j => sq_nonneg (q j))
        · filter_upwards [hrate_eq] with j hj
          change q j ^ 2 ≤ minimaxRate (ns j) (ds j)
          rw [hj]
          exact le_add_of_nonneg_left (by positivity)
        · exact hrate
      have hsqrt := (Real.continuous_sqrt.continuousAt.tendsto.comp hq_sq)
      have hsqrt' : Tendsto (fun j => Real.sqrt ((q j) ^ 2)) atTop (nhds 0) := by
        simpa [Function.comp_def] using hsqrt
      apply hsqrt'.congr'
      filter_upwards [hq_nonneg] with j hj
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hj]
    · intro hq
      have hrate : Tendsto (fun j => minimaxRate (ns j) (ds j)) atTop (nhds 0) := by
        have hadd := hinv.add (hq.pow 2)
        norm_num at hadd
        have hsum : Tendsto (fun j => 1 / (ns j : ℝ) + q j ^ 2) atTop (nhds 0) := by
          simpa [q, one_div] using hadd
        exact hsum.congr' (Filter.EventuallyEq.symm hrate_eq)
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall (fun j => (minimaxRisk_mem_unitInterval _ _ _).1)
      · filter_upwards [hbounds] with j hj
        exact hj.2
      · simpa using (tendsto_const_nhds.mul hrate :
          Tendsto (fun j => CU * minimaxRate (ns j) (ds j)) atTop (nhds (CU * 0)))

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
