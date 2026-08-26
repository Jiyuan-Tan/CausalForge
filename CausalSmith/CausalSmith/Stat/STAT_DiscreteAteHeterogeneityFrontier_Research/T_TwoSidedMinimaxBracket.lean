/- Headline two-sided minimax brackets. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.T_FrontierUpper
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.T_RadiusChannelConverse

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory Set

-- @node: thm:two-sided-minimax-bracket-all-d
/-- [All-alphabet two-sided minimax bracket on one and the same real-outcome model class. The two
  benchmarks are not asserted to be uniformly equivalent for every shrinking interior
  radius](goal). -/
theorem two_sided_minimax_bracket_all_d :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ c_epsilon : ℝ, -- @realizes c_{\epsilon}(carrier Real)
    ∃ C_epsilon : ℝ, -- @realizes C_{\epsilon}(carrier Real)
      0 < c_epsilon ∧ c_epsilon ≤ 1 ∧ -- @realizes c_{\epsilon}(range (0,1])
      1 ≤ C_epsilon ∧ -- @realizes C_{\epsilon}(range [1,infinity))
      c_epsilon ≤ C_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        c_epsilon * M ^ 2 * converseRate n d sigma ≤
          minimaxRisk n d epsilon M sigma ∧
        minimaxRisk n d epsilon M sigma ≤
          C_epsilon * M ^ 2 * frontierRate n d sigma := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨C0, handle, hC0, hupper⟩ :=
    frontier_upper_bound_all_d epsilon hepsilon hepsilon_half
  obtain ⟨c, bRad, hc, hc_one, hbRad, hlower⟩ :=
    radius_channel_converse_all_d
      epsilon hepsilon hepsilon_half
  refine ⟨c, max 1 C0, hc, hc_one, le_max_left _ _,
    hc_one.trans (le_max_left _ _), ?_⟩
  intro n d M sigma hn hd hM hsigma hsigma_two
  obtain ⟨hrisk, hradial⟩ :=
    hlower n d M sigma hn hd hM hsigma hsigma_two
  rcases hradial with
    ⟨cap, source, pad, embedding, coupling, hchannelData,
      _htargetSeparation, _hriskTransfer⟩
  rcases hchannelData with
    ⟨_hcap, _hinjective,
      hsourceHard, _hmass, _hzero, _hcoupling, _hchannel,
      hmembership, _hradius, _hprocessing⟩
  rcases hsourceHard with ⟨cHard, hcHard, hHard⟩
  obtain ⟨Psrc, hPsrc, _hPsrcRisk⟩ :=
    hHard ⟨fun _ => 0, measurable_const⟩
  obtain ⟨Q, _hQ⟩ := hmembership Psrc hPsrc
  letI : Nonempty (ModelClass d epsilon M sigma) := ⟨Q⟩
  let poly := polyEstimatorElement (n := n) (d := d) handle hM
  let collision := collisionEstimatorElement (n := n) (d := d) hM
  let selector := totalSelector hM sigma poly collision
  obtain ⟨hselector_meas, hselector_mem, hselector_risk⟩ :=
    hupper n d M sigma hn hd hM hsigma hsigma_two
  have hworst_nonneg (est : Estimator n d M) :
      0 ≤ worstCaseMSE n d epsilon M sigma est.1 := by
    unfold worstCaseMSE
    cases isEmpty_or_nonempty (ModelClass d epsilon M sigma) with
    | inl hempty =>
        letI := hempty
        simp
    | inr hnonempty =>
        letI := hnonempty
        by_cases hbounded : BddAbove (Set.range (fun P : ModelClass d epsilon M sigma =>
            mse P.law est.1))
        · have hmse : 0 ≤ mse
              (Classical.arbitrary (ModelClass d epsilon M sigma)).law est.1 := by
            unfold mse
            exact integral_nonneg (fun x => sq_nonneg (est.1 x -
              rawAteFormula (Classical.arbitrary
                (ModelClass d epsilon M sigma)).law))
          exact hmse.trans (le_ciSup hbounded (Classical.arbitrary _))
        · change 0 ≤ (⨆ P : ModelClass d epsilon M sigma, mse P.law est.1)
          rw [show (⨆ P : ModelClass d epsilon M sigma, mse P.law est.1) = sSup ∅ from
            csSup_of_not_bddAbove hbounded]
          simp
  have hb : BddBelow (Set.range (fun est : Estimator n d M =>
      worstCaseMSE n d epsilon M sigma est.1)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨est, rfl⟩
    exact hworst_nonneg est
  have hminimax_selector :
      minimaxRisk n d epsilon M sigma ≤
        worstCaseMSE n d epsilon M sigma selector.1 := by
    unfold minimaxRisk
    exact ciInf_le hb selector
  have hworst_selector :
      worstCaseMSE n d epsilon M sigma selector.1 ≤
        C0 * M ^ 2 * frontierRate n d sigma := by
    unfold worstCaseMSE
    apply ciSup_le
    intro P
    exact hselector_risk P
  refine ⟨hrisk, hminimax_selector.trans (hworst_selector.trans ?_)⟩
  have hrate : 0 ≤ M ^ 2 * frontierRate n d sigma := by
    exact mul_nonneg (sq_nonneg M) (le_of_lt (frontierRate_pos hn))
  calc
    C0 * M ^ 2 * frontierRate n d sigma =
        C0 * (M ^ 2 * frontierRate n d sigma) := by ring
    _ ≤ max 1 C0 * (M ^ 2 * frontierRate n d sigma) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 C0) hrate
    _ = max 1 C0 * M ^ 2 * frontierRate n d sigma := by ring

-- @node: thm:two-sided-minimax-bracket
/-- [Restricted-range form of the headline minimax bracket](goal). -/
theorem two_sided_minimax_bracket :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ c_epsilon : ℝ, -- @realizes c_{\epsilon}(existential range (0,1])
    ∃ C_epsilon : ℝ, -- @realizes C_{\epsilon}(existential range [1,infinity))
      0 < c_epsilon ∧ c_epsilon ≤ 1 ∧
      1 ≤ C_epsilon ∧ c_epsilon ≤ C_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        (d : ℝ) ≤ c_epsilon * (n : ℝ) ^ 2 / logEN n →
        c_epsilon * M ^ 2 *
            (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2 +
              sigma ^ 2 * min 1 (polynomialComponent n d)) ≤
          minimaxRisk n d epsilon M sigma ∧
        minimaxRisk n d epsilon M sigma ≤
          C_epsilon * M ^ 2 * frontierRate n d sigma := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨c_epsilon, C_epsilon, hc, hc_one, hC, hcC, hall⟩ :=
    two_sided_minimax_bracket_all_d epsilon hepsilon hepsilon_half
  refine ⟨c_epsilon, C_epsilon, hc, hc_one, hC, hcC, ?_⟩
  intro n d M sigma hn hd hM hsigma hsigma_two hd_range
  obtain ⟨hlower, hupper⟩ := hall n d M sigma hn hd hM hsigma hsigma_two
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn_one : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hlog : 1 ≤ logEN n := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hn_real), Real.log_exp]
    exact le_add_of_nonneg_right (Real.log_nonneg hn_one)
  have hnumerator :
      c_epsilon * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hcap : (d : ℝ) ≤ (n : ℝ) ^ 2 := calc
    (d : ℝ) ≤ c_epsilon * (n : ℝ) ^ 2 / logEN n := hd_range
    _ ≤ c_epsilon * (n : ℝ) ^ 2 :=
      div_le_self (mul_nonneg (le_of_lt hc) (sq_nonneg (n : ℝ))) hlog
    _ ≤ (n : ℝ) ^ 2 := hnumerator
  have hratio : (d : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hn_real)]
    exact hcap
  refine ⟨?_, hupper⟩
  simpa [converseRate, min_eq_right hratio] using hlower

private abbrev BinLaw := CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw

-- @node: prop:zeng-class-inclusion-and-lower-transfer
/-- [The canonical affine embedding realizes the binary subclasses, with strict image inclusion
  and the lower- and upper-bound transfers assembled here](goal). -/
theorem zeng_class_inclusion_and_lower_transfer :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ c_exact c_radius b_radius C_upper : ℝ, ∃ handle : PolynomialHandle,
      0 < c_exact ∧ 0 < c_radius ∧ 0 < b_radius ∧
      0 < C_upper ∧
    ∀ d : ℕ, ∀ M : ℝ, 0 < d → 1 ≤ M → -- @realizes M(range [1,infinity))
      ∃ Phi : BinLaw d → RealLaw d,
        (∀ P, AffineBinaryEmbedding M P (Phi P)) ∧
        (∀ P, CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P →
          ∃ Q : UnrestrictedClass d epsilon M, Q.law = Phi P) ∧
        (∀ P, BinaryExactHomogeneous epsilon P →
          ∃ Q : ModelClass d epsilon M 0, Q.law = Phi P) ∧
        (∀ sigma : ℝ, 0 ≤ sigma → sigma ≤ 2 →
          ∃ Q : ModelClass d epsilon M sigma, ∀ P, Phi P ≠ Q.law) ∧
        ∀ n : ℕ, ∀ sigma : ℝ,
          0 < n → 0 ≤ sigma → sigma ≤ 2 →
          ((d : ℝ) ≤ c_exact * (n : ℝ) ^ 2 →
            (∀ est : Estimator n d M,
              ∃ P : BinaryExactLaw n d epsilon,
                c_exact * M ^ 2 *
                    (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) ≤
                  mse (Phi P.1) est.1) ∧
            c_exact * M ^ 2 *
                  (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) ≤
                minimaxRisk n d epsilon M sigma) ∧
          ((c_radius * M ^ 2 * sigma ^ 2 *
                min 1 (polynomialComponent n d) ≤
              minimaxRisk n d epsilon M sigma) ∧
            RadialTargetRiskTransferCertificate n d epsilon M sigma
              c_radius b_radius) ∧
          Measurable
            (polyEstimator handle (n := n) (d := d) M) ∧
          (∀ s : Fin n → Obs d,
            polyEstimator handle (n := n) (d := d) M s ∈ Icc (-M) M) ∧
          (∀ Q : ModelClass d epsilon M sigma,
            mse Q.law
                (polyEstimator handle (n := n) (d := d) M) ≤
              C_upper * M ^ 2 *
                (1 / (n : ℝ) + min 1 (polynomialComponent n d))) := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨cExact, hcExact, hExact⟩ :=
    scaled_binary_exact_lower_transfer_all_d epsilon hepsilon hepsilon_half
  obtain ⟨cRadius, bRad, hcRadius, _hcRadiusOne, hbRad, hRadius⟩ :=
    radius_channel_converse_all_d epsilon hepsilon hepsilon_half
  obtain ⟨CUpper, handle, hCUpper, _hcomplexity, hUpper⟩ :=
    continuous_ratio_polynomial_upper_all_d epsilon hepsilon hepsilon_half
  let uExact : ℝ := min (1 / 2) (8 * (1 / 2 - epsilon) ^ 2)
  have huExact : 0 < uExact := by dsimp [uExact]; positivity
  let cWitness : ℝ := min (1 / 100) (uExact ^ 2 / 64) / 4
  have hcWitness : 0 < cWitness := by dsimp [cWitness]; positivity
  let cOut := min cExact (min cWitness 1)
  have hcOut : 0 < cOut := lt_min hcExact (lt_min hcWitness zero_lt_one)
  have hcOutExact : cOut ≤ cExact := min_le_left _ _
  have hcOutWitness : cOut ≤ cWitness :=
    (min_le_right cExact (min cWitness 1)).trans (min_le_left _ _)
  have hcOutOne : cOut ≤ 1 :=
    (min_le_right cExact (min cWitness 1)).trans (min_le_right _ _)
  refine ⟨cOut, cRadius, bRad, CUpper, handle,
    hcOut, hcRadius, hbRad, hCUpper, ?_⟩
  intro d M hd hM
  let k : Fin d := ⟨0, hd⟩
  refine ⟨affineBinaryRealLaw M, affineBinaryRealLaw_embedding M, ?_, ?_, ?_, ?_⟩
  · intro P hP
    exact ⟨affineBinaryRealLaw_unrestricted P hepsilon hepsilon_half hM hP, rfl⟩
  · intro P hP
    exact ⟨affineBinaryRealLaw_model_zero P hepsilon hepsilon_half hM hP, rfl⟩
  · intro sigma hsigma hsigma_two
    let Q := testModelClass k epsilon M sigma 0 hepsilon hepsilon_half hM
      hsigma hsigma_two (by rw [abs_zero]; positivity)
    refine ⟨Q, ?_⟩
    intro P
    exact affineBinaryRealLaw_ne_testModelLaw k hepsilon hepsilon_half hM
      hsigma hsigma_two P
  · intro n sigma hn hsigma hsigma_two
    have hexact := hExact n d M sigma hn hd hM hsigma hsigma_two
    obtain ⟨hradius, hradialTransfer⟩ :=
      hRadius n d M sigma hn hd hM hsigma hsigma_two
    obtain ⟨hmeas, hmem, hrisk⟩ :=
      hUpper n d M sigma hn hd hM hsigma hsigma_two
    refine ⟨?_, ⟨?_, hradialTransfer⟩, hmeas, hmem, hrisk⟩
    · intro hdRange
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hdOne : (d : ℝ) ≤ (n : ℝ) ^ 2 := calc
        (d : ℝ) ≤ cOut * (n : ℝ) ^ 2 := hdRange
        _ ≤ 1 * (n : ℝ) ^ 2 := by gcongr
        _ = (n : ℝ) ^ 2 := one_mul _
      have hratio : (d : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (sq_pos_of_pos hnR)]
        exact hdOne
      have hrate : 0 ≤ 1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2 := by
        positivity
      constructor
      · intro est
        have hparam := binaryExactMinimaxRisk_parametric_lower
          hn hd hepsilon hepsilon_half
        have hcollision := binaryExactMinimaxRisk_collision_lower
          hn hd hepsilon hepsilon_half hdOne
        have hbasePos : 0 < min (1 / 100 : ℝ) (uExact ^ 2 / 64) :=
          lt_min (by norm_num) (by positivity)
        have hparam' : min (1 / 100 : ℝ) (uExact ^ 2 / 64) *
              (1 / (n : ℝ)) ≤ binaryExactMinimaxRisk n d epsilon := by
          calc
            _ ≤ (1 / 100 : ℝ) * (1 / (n : ℝ)) :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
            _ = 1 / (100 * (n : ℝ)) := by ring
            _ ≤ binaryExactMinimaxRisk n d epsilon := hparam
        have hcollision' : min (1 / 100 : ℝ) (uExact ^ 2 / 64) *
              ((d : ℝ) / (n : ℝ) ^ 2) ≤
            binaryExactMinimaxRisk n d epsilon := by
          calc
            _ ≤ (uExact ^ 2 / 64) * ((d : ℝ) / (n : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
            _ ≤ binaryExactMinimaxRisk n d epsilon := by
              simpa [uExact] using hcollision
        have hriskPos : 0 < binaryExactMinimaxRisk n d epsilon :=
          lt_of_lt_of_le (by positivity) hparam
        have hsourceLt : cOut *
              (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) <
            binaryExactMinimaxRisk n d epsilon := by
          have hout : cOut ≤
              min (1 / 100 : ℝ) (uExact ^ 2 / 64) / 4 := by
            simpa [cWitness] using hcOutWitness
          have hx : 0 ≤ 1 / (n : ℝ) := by positivity
          have hy : 0 ≤ (d : ℝ) / (n : ℝ) ^ 2 := by positivity
          have hsum := add_le_add hparam' hcollision'
          nlinarith [mul_le_mul_of_nonneg_right hout (add_nonneg hx hy)]
        have hhard := binaryExactMinimaxRisk_hard_family_of_lt
          hn hd hepsilon hepsilon_half hsourceLt
        have hMne : M ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hM)
        have htransport :=
          Causalean.Stat.forall_estimator_exists_sqRisk_ge_of_deterministic_affine_transport_pi
            (Iota := BinaryExactLaw n d epsilon) (n := n)
            (P := fun P => CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P.1)
            (Q := fun P => (affineBinaryRealLaw M P.1).observedLaw)
            (theta := fun P =>
              CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1)
            (phi := affineObserved M) (a := M) (b := 0)
            (L := cOut *
              (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2))
            hMne (measurable_affineObserved M)
            (fun P => (affineBinaryRealLaw_embedding M P.1).1)
            (by
              intro sourceEst hsourceEst
              obtain ⟨P, hP⟩ := hhard sourceEst hsourceEst
              exact ⟨P, by
                simpa [Causalean.Stat.sqRisk,
                  CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse,
                  CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw] using hP⟩)
            est.1 est.2.1
        obtain ⟨P, hP⟩ := htransport
        refine ⟨P, ?_⟩
        have htau : rawAteFormula (affineBinaryRealLaw M P.1) =
            M * CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1 :=
          rawAteFormula_eq_mul_binaryAte_of_embedding
            (affineBinaryRealLaw_embedding M P.1) P.2.1
        rw [← htau] at hP
        simp only [Causalean.Stat.sqRisk, mse, productLaw] at hP ⊢
        rw [show cOut * M ^ 2 *
            (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) =
          M ^ 2 * (cOut *
            (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2)) by ring]
        simpa only [add_zero] using hP
      · calc
          cOut * M ^ 2 * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) ≤
              cExact * M ^ 2 * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) := by
            gcongr
          _ ≤ minimaxRisk n d epsilon M sigma := by
            simpa [min_eq_right hratio] using hexact
    · unfold converseRate at hradius
      have hpoly : 0 ≤ polynomialComponent n d := by
        unfold polynomialComponent
        positivity
      have hbase : 0 ≤ 1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) := by
        positivity
      have hradterm : 0 ≤ sigma ^ 2 * min 1 (polynomialComponent n d) :=
        mul_nonneg (sq_nonneg _) (le_min zero_le_one hpoly)
      have hcoeff : 0 ≤ cRadius * M ^ 2 :=
        mul_nonneg (le_of_lt hcRadius) (sq_nonneg M)
      calc
        cRadius * M ^ 2 * sigma ^ 2 * min 1 (polynomialComponent n d) =
            (cRadius * M ^ 2) *
              (sigma ^ 2 * min 1 (polynomialComponent n d)) := by ring
        _ ≤ cRadius * M ^ 2 *
            (1 / (n : ℝ) + min 1 ((d : ℝ) / (n : ℝ) ^ 2) +
              sigma ^ 2 * min 1 (polynomialComponent n d)) := by
          apply mul_le_mul_of_nonneg_left _ hcoeff
          linarith
        _ ≤ minimaxRisk n d epsilon M sigma := hradius

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
