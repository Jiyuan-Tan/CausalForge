import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCellRate
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HybridProgram

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory
open scoped BigOperators

/-- Defines target Light, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def targetLight {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) : ℝ :=
  ∑ k ∈ lightCells sample, cellPhi (cellVector P k)

/-- Defines component Error MSE, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def componentErrorMSE {n d : ℕ}
    (mu_n : Measure (Fin n → Obs d))
    (component target : (Fin n → Obs d) → ℝ) : ℝ :=
  ∫ sample, (component sample - target sample) ^ 2 ∂mu_n

/-- Defines minimax Rate, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def minimaxRate (n d : ℕ) : ℝ :=
  1 / (n : ℝ) + d ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)

-- @node: lightCells_eq_pilotHeavyAt_compl_of_cutoff_le
/-- Establishes the stated equality relating light Cells eq pilot Heavy At compl of cutoff le. -/
lemma lightCells_eq_pilotHeavyAt_compl_of_cutoff_le {n d : ℕ}
    (sample : Fin n → Obs d) (hcut : calibrationCutoff ≤ n) :
    lightCells sample = (pilotHeavyAt sample 256)ᶜ := by
  classical
  rw [lightCells_eq_compl, heavyCells_eq_filter_of_cutoff_le sample hcut]
  congr 1
  ext k
  simp only [pilotHeavyAt, Finset.mem_filter, Finset.mem_univ, true_and,
    lambda0]
  exact (Int.floor_lt).symm

-- @node: selected_light_mass_le_bandwidth_quarter
/-- Establishes the stated upper bound for selected light mass le bandwidth quarter. -/
lemma selected_light_mass_le_bandwidth_quarter {n d : ℕ}
    (P : DiscreteLaw d) (sample : Fin n → Obs d)
    (hcut : calibrationCutoff ≤ n) (hgood : sample ∉ pilotBadEvent P 256)
    (k : Fin d) (hk : k ∈ lightCells sample) :
    cellMass P k ≤ bandwidth n / 4 := by
  classical
  have hbase : cutoffProperty calibrationCutoff := by
    rw [calibrationCutoff]
    exact Nat.find_spec cutoffProperty_eventually
  have hprops := hbase n hcut
  rcases hprops with ⟨hscale, hdegreeSize, _hshift⟩
  have hdeg2 : 2 ≤ polynomialDegree n := by simp [polynomialDegree]
  have hm1large : 16 ≤ splitSize n 1 := by nlinarith
  have hn2 : 2 ≤ n := by
    rw [splitSize_one_eq] at hm1large
    omega
  have hm0pos : 0 < splitSize n 0 := by
    rw [splitSize_zero_eq]
    omega
  have hm1pos : 0 < splitSize n 1 := lt_of_lt_of_le (by norm_num) hm1large
  have hmratio : splitSize n 1 ≤ 2 * splitSize n 0 := by
    rw [splitSize_zero_eq, splitSize_one_eq]
    omega
  have hscale0 : 0 ≤ logScale n := by
    have ha0 : 0 < alpha0 := by
      unfold alpha0 dA
      have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
      have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
      positivity
    nlinarith
  have hknot : k ∉ pilotHeavyAt sample 256 := by
    rw [lightCells_eq_pilotHeavyAt_compl_of_cutoff_le sample hcut] at hk
    simpa using hk
  have hsand :
      (∀ l ∈ pilotHeavyAt sample 256,
          256 * logScale n / (2 * splitSize n 0) ≤ cellMass P l) ∧
      (∀ l ∉ pilotHeavyAt sample 256,
          cellMass P l ≤ 2 * 256 * logScale n / splitSize n 0) := by
    simpa only [pilotBadEvent, Set.mem_setOf_eq, not_or, not_not] using hgood
  have hkbound := hsand.2 k hknot
  rw [bandwidth]
  have hmratioR : (splitSize n 1 : ℝ) ≤ 2 * splitSize n 0 := by
    exact_mod_cast hmratio
  have hm0R : 0 < (splitSize n 0 : ℝ) := by exact_mod_cast hm0pos
  have hm1R : 0 < (splitSize n 1 : ℝ) := by exact_mod_cast hm1pos
  calc
    cellMass P k ≤ 2 * 256 * logScale n / splitSize n 0 := hkbound
    _ ≤ (b0 : ℝ) * logScale n / splitSize n 1 / 4 := by
      rw [div_div, div_le_div_iff₀ hm0R (by positivity :
        0 < (splitSize n 1 : ℝ) * 4)]
      norm_num [b0]
      nlinarith

-- @node: selected_light_approximation_bias
/-- Establishes the stated upper bound for selected light approximation bias. -/
lemma selected_light_approximation_bias {n d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P)
    (sample : Fin n → Obs d) (hcut : calibrationCutoff ≤ n)
    (hgood : sample ∉ pilotBadEvent P 256) (he0 : 0 < epsilon) :
    |Finset.sum (lightCells sample) (fun k : Fin d =>
        (cellApproxPolynomial (polynomialDegree n) (bandwidth n)).eval
            (cellVector P k) - cellPhi (cellVector P k))| ≤
      d * (2 * bandwidth n / (epsilon * polynomialDegree n ^ 2)) := by
  classical
  have hM : 0 < polynomialDegree n := by simp [polynomialDegree]
  have hB (k : Fin d) (hk : k ∈ lightCells sample) :
      vectorMass (cellVector P k) ≤ bandwidth n := by
    rw [vectorMass_cellVector]
    exact (selected_light_mass_le_bandwidth_quarter P sample hcut hgood k hk).trans
      (by
        have hbase : cutoffProperty calibrationCutoff := by
          rw [calibrationCutoff]
          exact Nat.find_spec cutoffProperty_eventually
        have hs := (hbase n hcut).1
        have ha0 : 0 < alpha0 := by
          unfold alpha0 dA
          have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
          have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
          positivity
        have hL : 0 < logScale n := by nlinarith
        have hm1 : 0 < splitSize n 1 := by
          have hd : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1 := (hbase n hcut).2.1
          nlinarith
        have hB0 : 0 ≤ bandwidth n := by
          rw [bandwidth]
          positivity
        linarith)
  calc
    |Finset.sum (lightCells sample) (fun k : Fin d =>
        (cellApproxPolynomial (polynomialDegree n) (bandwidth n)).eval
            (cellVector P k) - cellPhi (cellVector P k))| ≤
        ∑ k ∈ lightCells sample,
          |(cellApproxPolynomial (polynomialDegree n) (bandwidth n)).eval
              (cellVector P k) - cellPhi (cellVector P k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ lightCells sample,
        (2 * bandwidth n / (epsilon * polynomialDegree n ^ 2)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact cellApproxPolynomial_error hM he0
        (cellVector_mem_overlapCone P hOverlap k) (hB k hk)
    _ ≤ d * (2 * bandwidth n / (epsilon * polynomialDegree n ^ 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (lightCells sample).card ≤ d := by
        calc
          (lightCells sample).card ≤ (Finset.univ : Finset (Fin d)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = d := Fintype.card_fin d
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (div_nonneg (by
          have hbase : cutoffProperty calibrationCutoff := by
            rw [calibrationCutoff]
            exact Nat.find_spec cutoffProperty_eventually
          have hs := (hbase n hcut).1
          have ha0 : 0 < alpha0 := by
            unfold alpha0 dA
            have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
            have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
            positivity
          have hm1 : 0 < splitSize n 1 := by
            have hd := (hbase n hcut).2.1
            nlinarith
          have hL : 0 < logScale n := by nlinarith
          rw [bandwidth]
          positivity) (by positivity))

-- @node: integrable_factorialPolynomialContribution_trunc
/-- Shows that integrable factorial Polynomial Contribution trunc is integrable under the stated sampling distribution. -/
lemma integrable_factorialPolynomialContribution_trunc {n d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) :
    Integrable (fun ω : ℕ → Obs d =>
      factorialPolynomialContribution (fun i : Fin n => ω i) k)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  let arm (a : Fin 2) := fun ω : ℕ → Obs d =>
    ∑ j ∈ Finset.range (polynomialDegree n - 1),
      ∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
        ((bandwidth n)⁻¹ * gCoefficient (polynomialDegree n) j *
          (bandwidth n)⁻¹ ^ j * (Nat.choose j t : ℝ)) *
          factorialMonomial (fun i : Fin n => ω i) k
            (factorialExpansionIndex a ay j t)
  have harm (a : Fin 2) : Integrable (arm a)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    apply integrable_finset_sum
    intro j _hj
    apply integrable_finset_sum
    intro t _ht
    apply integrable_finset_sum
    intro ay _hay
    exact Integrable.const_mul
      (integrable_factorialMonomial_trunc P k
        (factorialExpansionIndex a ay j t)) _
  simpa only [factorialPolynomialContribution, arm] using (harm 1).sub (harm 0)

-- @node: integral_factorialPolynomialContribution_trunc
/-- Evaluates or bounds the stated integral involving integral factorial Polynomial Contribution trunc. -/
lemma integral_factorialPolynomialContribution_trunc {n d : ℕ}
    (P : DiscreteLaw d) (k : Fin d)
    (hcut : calibrationCutoff ≤ n) :
    ∫ ω : ℕ → Obs d,
        factorialPolynomialContribution (fun i : Fin n => ω i) k
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) =
      (cellApproxPolynomial (polynomialDegree n) (bandwidth n)).eval
        (cellVector P k) := by
  classical
  have hbase : cutoffProperty calibrationCutoff := by
    rw [calibrationCutoff]
    exact Nat.find_spec cutoffProperty_eventually
  have hprops := hbase n hcut
  rcases hprops with ⟨_hdegreeLower, hdegreeSize, _hshift⟩
  let coeff (j t : ℕ) : ℝ :=
    (bandwidth n)⁻¹ * gCoefficient (polynomialDegree n) j *
      (bandwidth n)⁻¹ ^ j * (Nat.choose j t : ℝ)
  let arm (a : Fin 2) := fun ω : ℕ → Obs d =>
    ∑ j ∈ Finset.range (polynomialDegree n - 1),
      ∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
        coeff j t * factorialMonomial (fun i : Fin n => ω i) k
          (factorialExpansionIndex a ay j t)
  let meanArm (a : Fin 2) :=
    ∑ j ∈ Finset.range (polynomialDegree n - 1),
      ∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
        coeff j t * (factorialExpansionIndex a ay j t).prod
          (fun ay' e => (cellVector P k ay') ^ e)
  have hMle : polynomialDegree n ≤ splitSize n 1 := by
    have hMpos : 0 < polynomialDegree n := by simp [polynomialDegree]
    nlinarith [sq_nonneg (polynomialDegree n : ℝ)]
  have hdeg (a : Fin 2) (j t : ℕ) (ay : Cell)
      (hj : j ∈ Finset.range (polynomialDegree n - 1))
      (ht : t ∈ Finset.range (j + 1)) :
      multiDegree (factorialExpansionIndex a ay j t) ≤ splitSize n 1 := by
    have htj : t ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
    rw [multiDegree_factorialExpansionIndex a ay j t htj]
    have hjM : j + 2 ≤ polynomialDegree n := by
      have := Finset.mem_range.mp hj
      omega
    exact hjM.trans hMle
  have hterm (a : Fin 2) (j t : ℕ) (ay : Cell) : Integrable
      (fun ω : ℕ → Obs d => coeff j t *
        factorialMonomial (fun i : Fin n => ω i) k
          (factorialExpansionIndex a ay j t))
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) :=
    Integrable.const_mul
      (integrable_factorialMonomial_trunc P k
        (factorialExpansionIndex a ay j t)) _
  have htSum (a : Fin 2) (j t : ℕ) : Integrable
      (fun ω : ℕ → Obs d => ∑ ay : Cell, coeff j t *
        factorialMonomial (fun i : Fin n => ω i) k
          (factorialExpansionIndex a ay j t))
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    exact integrable_finset_sum _ fun ay _ => hterm a j t ay
  have hjSum (a : Fin 2) (j : ℕ) : Integrable
      (fun ω : ℕ → Obs d => ∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
        coeff j t * factorialMonomial (fun i : Fin n => ω i) k
          (factorialExpansionIndex a ay j t))
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    exact integrable_finset_sum _ fun t _ => htSum a j t
  have harm (a : Fin 2) : Integrable (arm a)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    exact integrable_finset_sum _ fun j _ => hjSum a j
  have hmean (a : Fin 2) :
      ∫ ω : ℕ → Obs d, arm a ω
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) = meanArm a := by
    unfold arm meanArm
    rw [integral_finset_sum _ (fun j _ => hjSum a j)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finset_sum _ (fun t _ => htSum a j t)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [integral_finset_sum _ (fun ay _ => hterm a j t ay)]
    apply Finset.sum_congr rfl
    intro ay _hay
    rw [integral_const_mul, integral_factorialMonomial_trunc P k _
      (hdeg a j t ay hj ht)]
  change ∫ ω : ℕ → Obs d, arm 1 ω - arm 0 ω
      ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) = _
  rw [integral_sub (harm 1) (harm 0), hmean 1, hmean 0]
  have hcollapse (a : Fin 2) (j : ℕ) :
      ∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
          coeff j t * (factorialExpansionIndex a ay j t).prod
            (fun ay' e => (cellVector P k ay') ^ e) =
        ((bandwidth n)⁻¹ * gCoefficient (polynomialDegree n) j *
          (bandwidth n)⁻¹ ^ j) *
          ((∑ ay : Cell, cellVector P k ay) * cellVector P k (a, 1) *
            (cellVector P k (a, 0) + cellVector P k (a, 1)) ^ j) := by
    rw [show (∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
        coeff j t * (factorialExpansionIndex a ay j t).prod
          (fun ay' e => (cellVector P k ay') ^ e)) =
        ((bandwidth n)⁻¹ * gCoefficient (polynomialDegree n) j *
          (bandwidth n)⁻¹ ^ j) *
          (∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
            (Nat.choose j t : ℝ) *
              (factorialExpansionIndex a ay j t).prod
                (fun ay' e => (cellVector P k ay') ^ e)) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ay _hay
      simp only [coeff]
      ring]
    rw [factorialExpansionIndex_binomial_sum]
  unfold meanArm
  simp_rw [hcollapse]
  have houter (a : Fin 2) :
      ∑ j ∈ Finset.range (polynomialDegree n - 1),
          ((bandwidth n)⁻¹ * gCoefficient (polynomialDegree n) j *
            (bandwidth n)⁻¹ ^ j) *
            ((∑ ay : Cell, cellVector P k ay) * cellVector P k (a, 1) *
              (cellVector P k (a, 0) + cellVector P k (a, 1)) ^ j) =
        (bandwidth n)⁻¹ * (∑ ay : Cell, cellVector P k ay) *
          cellVector P k (a, 1) *
          (∑ j ∈ Finset.range (polynomialDegree n - 1),
            gCoefficient (polynomialDegree n) j *
              ((bandwidth n)⁻¹ *
                (cellVector P k (a, 0) + cellVector P k (a, 1))) ^ j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [mul_pow]
    ring
  rw [houter 1, houter 0]
  have hmass : (MvPolynomial.eval (cellVector P k)) mvMass =
      ∑ ay : Cell, cellVector P k ay := by
    simp [mvMass, mvArmMass, Fintype.sum_prod_type, Fin.sum_univ_two]
  have harmEval (a : Fin 2) :
      (MvPolynomial.eval (cellVector P k)) (mvArmMass a) =
        cellVector P k (a, 0) + cellVector P k (a, 1) := by
    simp [mvArmMass]
  simp only [cellApproxPolynomial, MvPolynomial.eval_sub,
    MvPolynomial.eval_mul, map_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_X, map_pow]
  rw [hmass, harmEval 1, harmEval 0]

/-- Establishes the stated equality relating sparse Polynomial Mean eq cell Approx. -/
lemma sparsePolynomialMean_eq_cellApprox {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (hcut : calibrationCutoff ≤ n) :
    sparsePolynomialMean P k (polynomialDegree n) (bandwidth n) =
      (cellApproxPolynomial (polynomialDegree n) (bandwidth n)).eval
        (cellVector P k) := by
  classical
  have hbase : cutoffProperty calibrationCutoff := by
    rw [calibrationCutoff]
    exact Nat.find_spec cutoffProperty_eventually
  have hsize := (hbase n hcut).2.1
  have hMle : polynomialDegree n ≤ splitSize n 1 := by
    have hM1 : 1 ≤ polynomialDegree n := by simp [polynomialDegree]
    nlinarith [Nat.mul_self_le_mul_self hM1]
  rw [← integral_factorialPolynomialContribution_eq_sparsePolynomialMean P k hMle,
    integral_factorialPolynomialContribution_trunc P k hcut]

/-- Defines selected Genuine Light Bias, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def selectedGenuineLightBias {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) : ℝ :=
  ∑ k ∈ genuineLightSet (n := n) P, lightIndicator sample k *
    (sparsePolynomialMean P k (polynomialDegree n) (bandwidth n) -
      cellPhi (cellVector P k))

/-- Establishes the stated upper bound for selected Genuine Light Bias abs. -/
lemma selectedGenuineLightBias_abs {n d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P)
    (he0 : 0 < epsilon) (hcut : calibrationCutoff ≤ n)
    (sample : Fin n → Obs d) :
    |selectedGenuineLightBias P sample| ≤
      d * (2 * bandwidth n / (epsilon * polynomialDegree n ^ 2)) := by
  classical
  have hM : 0 < polynomialDegree n := by simp [polynomialDegree]
  have hB0 : 0 ≤ bandwidth n := by
    rw [bandwidth]
    have hp := (Nat.find_spec cutoffProperty_eventually) n
    have hL : 0 < logScale n := by
      have ha0 : 0 < alpha0 := by
        unfold alpha0 dA
        have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
        have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
        positivity
      have hs := (show cutoffProperty calibrationCutoff by
        rw [calibrationCutoff]; exact Nat.find_spec cutoffProperty_eventually) n hcut
      nlinarith [hs.1]
    positivity
  unfold selectedGenuineLightBias
  calc
    |∑ k ∈ genuineLightSet (n := n) P, lightIndicator sample k *
        (sparsePolynomialMean P k (polynomialDegree n) (bandwidth n) -
          cellPhi (cellVector P k))| ≤
      ∑ k ∈ genuineLightSet (n := n) P,
        |lightIndicator sample k *
          (sparsePolynomialMean P k (polynomialDegree n) (bandwidth n) -
            cellPhi (cellVector P k))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ genuineLightSet (n := n) P,
        (2 * bandwidth n / (epsilon * polynomialDegree n ^ 2)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      have hI : |lightIndicator sample k| ≤ 1 := by
        rw [abs_of_nonneg (lightIndicator_nonneg _ _)]
        exact lightIndicator_le_one _ _
      have hkB : vectorMass (cellVector P k) ≤ bandwidth n := by
        rw [vectorMass_cellVector]
        have : cellMass P k ≤ bandwidth n / 4 := by
          simpa [genuineLightSet] using hk
        linarith
      have happ := cellApproxPolynomial_error hM he0
        (cellVector_mem_overlapCone P hOverlap k) hkB
      rw [sparsePolynomialMean_eq_cellApprox P k hcut]
      calc
        |lightIndicator sample k| *
            |(cellApproxPolynomial (polynomialDegree n) (bandwidth n)).eval
                (cellVector P k) - cellPhi (cellVector P k)| ≤
          1 * (2 * bandwidth n / (epsilon * polynomialDegree n ^ 2)) := by
            gcongr
        _ = _ := one_mul _
    _ ≤ d * (2 * bandwidth n / (epsilon * polynomialDegree n ^ 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : ((genuineLightSet (n := n) P).card : ℝ) ≤ d := by
        exact_mod_cast (calc
          (genuineLightSet (n := n) P).card ≤ (Finset.univ : Finset (Fin d)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = d := Fintype.card_fin d)
      exact mul_le_mul_of_nonneg_right hc (div_nonneg (mul_nonneg (by norm_num) hB0)
        (mul_nonneg he0.le (sq_nonneg _)))

/-- Establishes the stated property of polynomial Degree lower half in the discrete average-treatment-effect construction. -/
lemma polynomialDegree_lower_half {n : ℕ}
    (hscale : 2 ≤ alpha0 * logScale n) :
    alpha0 * logScale n / 2 ≤ (polynomialDegree n : ℝ) := by
  classical
  have hfloor2 : (2 : ℤ) ≤ ⌊alpha0 * logScale n⌋ := by
    rw [Int.le_floor]
    exact_mod_cast hscale
  have hmax : polynomialDegree n = Int.toNat ⌊alpha0 * logScale n⌋ := by
    rw [polynomialDegree, max_eq_right]
    exact Int.toNat_le_toNat hfloor2
  rw [hmax]
  have hfloor0 : 0 ≤ ⌊alpha0 * logScale n⌋ := le_trans (by norm_num) hfloor2
  rw [show ((Int.toNat ⌊alpha0 * logScale n⌋ : ℕ) : ℝ) =
      ((⌊alpha0 * logScale n⌋ : ℤ) : ℝ) by
    exact_mod_cast Int.toNat_of_nonneg hfloor0]
  have hf := Int.sub_one_lt_floor (alpha0 * logScale n)
  exact le_of_lt (by nlinarith)

/-- The selected genuine-light approximation bias has the squared minimax
normalization. -/
lemma selectedGenuineLightBias_sq_rate {n d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P)
    (he0 : 0 < epsilon) (hcut : calibrationCutoff ≤ n)
    (sample : Fin n → Obs d) :
    selectedGenuineLightBias P sample ^ 2 ≤
      (65536 / (epsilon * alpha0 ^ 2)) ^ 2 * lightAsymptoticRate n d := by
  classical
  let L := logScale n
  let ell := Real.log (n : ℝ)
  let M := polynomialDegree n
  let B := bandwidth n
  rcases large_calibration_bounds hcut (cutoff_logScale_ge_240 hcut) with
    ⟨hell, hellL, _hLell, _hm, _hnm, _hM, hB, _hgrowth⟩
  have hbase : cutoffProperty calibrationCutoff := by
    rw [calibrationCutoff]
    exact Nat.find_spec cutoffProperty_eventually
  have hscale := (hbase n hcut).1
  have ha0 : 0 < alpha0 := by
    unfold alpha0 dA
    have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
    have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hn : 0 < (n : ℝ) := by
    have hnNat : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      norm_num at hell
    exact_mod_cast hnNat
  have hLpos : 0 < L := lt_of_lt_of_le (by simpa only [ell] using hell)
    (by simpa only [L, ell] using hellL)
  have hMlower : alpha0 * L / 2 ≤ (M : ℝ) := by
    simpa only [L, M] using polynomialDegree_lower_half hscale
  have hMpos : 0 < (M : ℝ) := lt_of_lt_of_le
    (div_pos (mul_pos ha0 hLpos) (by norm_num)) hMlower
  have hden : 0 < epsilon * (M : ℝ) ^ 2 := mul_pos he0 (sq_pos_of_pos hMpos)
  have hsmallDen : 0 < epsilon * (alpha0 * L / 2) ^ 2 := by positivity
  have hdenLe : epsilon * (alpha0 * L / 2) ^ 2 ≤ epsilon * (M : ℝ) ^ 2 := by
    gcongr
  have hnum : 2 * B ≤ 16384 * L / (n : ℝ) := by
    calc
      2 * B ≤ 2 * (8192 * L / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = 16384 * L / (n : ℝ) := by ring
  have hnum0 : 0 ≤ 16384 * L / (n : ℝ) := by positivity
  have hratio : 2 * B / (epsilon * (M : ℝ) ^ 2) ≤
      65536 / (epsilon * alpha0 ^ 2 * (n : ℝ) * L) := by
    calc
      2 * B / (epsilon * (M : ℝ) ^ 2) ≤
          (16384 * L / (n : ℝ)) / (epsilon * (M : ℝ) ^ 2) := by
        exact div_le_div_of_nonneg_right hnum hden.le
      _ ≤ (16384 * L / (n : ℝ)) /
          (epsilon * (alpha0 * L / 2) ^ 2) := by
        exact div_le_div_of_nonneg_left hnum0 hsmallDen hdenLe
      _ = 65536 / (epsilon * alpha0 ^ 2 * (n : ℝ) * L) := by
        field_simp
        ring
  have hratioEll : 2 * B / (epsilon * (M : ℝ) ^ 2) ≤
      65536 / (epsilon * alpha0 ^ 2 * (n : ℝ) * ell) := by
    refine hratio.trans ?_
    apply div_le_div_of_nonneg_left (by norm_num)
    · positivity
    · gcongr
  have habs := selectedGenuineLightBias_abs P hOverlap he0 hcut sample
  have hcoef0 : 0 ≤ 65536 / (epsilon * alpha0 ^ 2 * (n : ℝ) * ell) := by positivity
  have habs' : |selectedGenuineLightBias P sample| ≤
      (d : ℝ) * (65536 / (epsilon * alpha0 ^ 2 * (n : ℝ) * ell)) := by
    exact habs.trans (mul_le_mul_of_nonneg_left hratioEll (Nat.cast_nonneg d))
  have hsq := pow_le_pow_left₀ (abs_nonneg _) habs' 2
  rw [sq_abs] at hsq
  calc
    selectedGenuineLightBias P sample ^ 2 ≤
        ((d : ℝ) * (65536 /
          (epsilon * alpha0 ^ 2 * (n : ℝ) * ell))) ^ 2 := hsq
    _ = (65536 / (epsilon * alpha0 ^ 2)) ^ 2 *
        ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * ell ^ 2)) := by
      field_simp
    _ ≤ (65536 / (epsilon * alpha0 ^ 2)) ^ 2 *
        lightAsymptoticRate n d := by
      gcongr
      unfold lightAsymptoticRate
      exact le_add_of_nonneg_left (by positivity)

/-- Establishes the stated property of light error decompose in the discrete average-treatment-effect construction. -/
lemma light_error_decompose {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) :
    lightContribution sample - targetLight P sample =
      selectedFixedLightCentered P sample (genuineLightSet (n := n) P) +
        selectedGenuineLightBias P sample + selectedFalseLightError P sample := by
  classical
  let e := fun k : Fin d =>
    factorialPolynomialContribution sample k - cellPhi (cellVector P k)
  have hselected :
      ∑ k ∈ lightCells sample, e k = ∑ k : Fin d, lightIndicator sample k * e k := by
    rw [show (∑ k ∈ lightCells sample, e k) =
        Finset.sum (Finset.univ.filter fun k : Fin d => k ∈ lightCells sample) e by
      congr 1
      ext k
      simp]
    simp [lightIndicator]
  have hpartition :
      (∑ k : Fin d, lightIndicator sample k * e k) =
        (∑ k ∈ genuineLightSet (n := n) P, lightIndicator sample k * e k) +
          ∑ k ∈ falseLightSet (n := n) P, lightIndicator sample k * e k := by
    rw [genuineLightSet, falseLightSet]
    simpa only [Finset.sum_filter, not_le] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin d)))
        (p := fun k => cellMass P k ≤ bandwidth n / 4)
        (f := fun k => lightIndicator sample k * e k)).symm
  calc
    lightContribution sample - targetLight P sample =
        ∑ k ∈ lightCells sample, e k := by
      unfold lightContribution targetLight
      rw [← Finset.sum_sub_distrib]
    _ = ∑ k : Fin d, lightIndicator sample k * e k := hselected
    _ = (∑ k ∈ genuineLightSet (n := n) P, lightIndicator sample k * e k) +
          ∑ k ∈ falseLightSet (n := n) P, lightIndicator sample k * e k := hpartition
    _ = selectedFixedLightCentered P sample (genuineLightSet (n := n) P) +
        selectedGenuineLightBias P sample + selectedFalseLightError P sample := by
      unfold selectedFixedLightCentered selectedGenuineLightBias selectedFalseLightError
      rw [← Finset.sum_add_distrib]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro k hk
        dsimp only [e]
        ring
      · rfl

-- @node: lem:light-cell-polynomial
/-- The factorial-polynomial light branch attains the fixed-interior minimax rate.
The constants are chosen before the law and are allowed to depend only on the
fixed overlap constant. -/
lemma light_cell_polynomial (epsilon : ℝ) (he0 : 0 < epsilon)
    (he1 : epsilon ≤ 1 / 2) :
    HybridEstimatorComputable ∧
      ∃ C_epsilon c_epsilon : ℝ,
        0 < C_epsilon ∧ 0 < c_epsilon ∧
        ∀ (n d : ℕ) (P : DiscreteLaw d)
          (mu_n : Measure (Fin n → Obs d)),
          ExperimentClass n epsilon P mu_n →
          (d : ℝ) ≤ c_epsilon * n * Real.log n →
          componentErrorMSE mu_n lightContribution (targetLight P) ≤
            C_epsilon * minimaxRate n d := by
  classical
  refine ⟨hybridEstimatorComputable, ?_⟩
  let Kc := 4 * (Real.exp 1 + 1) * 8192 ^ 2 + 16 * 8192 ^ 2
  let Kb := (65536 / (epsilon * alpha0 ^ 2)) ^ 2
  let Kf := 8 * (Real.exp 1 + 1) * 8192 ^ 2
  let C := 3 * (Kc + Kb + Kf)
  have hC : 0 < C := by
    dsimp only [C, Kc, Kb, Kf]
    have ha0 : 0 < alpha0 := by
      unfold alpha0 dA
      have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
      have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
      positivity
    positivity
  refine ⟨C, 1, hC, by norm_num, ?_⟩
  intro n d P mu_n hclass _hd
  rw [hclass.product_law]
  by_cases hcut : calibrationCutoff ≤ n
  · let X := fun sample : Fin n → Obs d =>
      selectedFixedLightCentered P sample (genuineLightSet (n := n) P)
    let Y := fun sample : Fin n → Obs d => selectedGenuineLightBias P sample
    let Z := fun sample : Fin n → Obs d => selectedFalseLightError P sample
    let R := lightAsymptoticRate n d
    have hLlarge := cutoff_logScale_ge_240 hcut
    have hX : (∫ sample, X sample ^ 2 ∂productLaw P n) ≤ Kc * R := by
      calc
        (∫ sample, X sample ^ 2 ∂productLaw P n) =
            ∫ ω : ℕ → Obs d, X (fun i : Fin n => ω i) ^ 2
              ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) :=
          light_integral_productLaw_eq_infinite P (fun sample => X sample ^ 2)
        _ ≤ Kc * R := by
          simpa only [X, Kc, R] using
            selectedGenuineLightCentered_rate P hcut hLlarge
    have hZ : (∫ sample, Z sample ^ 2 ∂productLaw P n) ≤ Kf * R := by
      calc
        (∫ sample, Z sample ^ 2 ∂productLaw P n) =
            ∫ ω : ℕ → Obs d, Z (fun i : Fin n => ω i) ^ 2
              ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) :=
          light_integral_productLaw_eq_infinite P (fun sample => Z sample ^ 2)
        _ ≤ Kf * R := by
          simpa only [Z, Kf, R] using
            selectedFalseLightError_rate P hclass.overlap hcut hLlarge
    have hYpoint (sample : Fin n → Obs d) : Y sample ^ 2 ≤ Kb * R := by
      simpa only [Y, Kb, R] using
        selectedGenuineLightBias_sq_rate P hclass.overlap he0 hcut sample
    have hY : (∫ sample, Y sample ^ 2 ∂productLaw P n) ≤ Kb * R := by
      calc
        (∫ sample, Y sample ^ 2 ∂productLaw P n) ≤
            ∫ _sample, Kb * R ∂productLaw P n := by
          apply integral_mono Integrable.of_finite (integrable_const _)
          exact hYpoint
        _ = Kb * R := by simp
    have hpoint (sample : Fin n → Obs d) :
        (X sample + Y sample + Z sample) ^ 2 ≤
          3 * (X sample ^ 2 + Y sample ^ 2 + Z sample ^ 2) := by
      nlinarith [sq_nonneg (X sample - Y sample),
        sq_nonneg (X sample - Z sample), sq_nonneg (Y sample - Z sample)]
    unfold componentErrorMSE
    rw [show (fun sample : Fin n → Obs d =>
        (lightContribution sample - targetLight P sample) ^ 2) =
        (fun sample => (X sample + Y sample + Z sample) ^ 2) by
      funext sample
      rw [light_error_decompose P sample]
      ]
    calc
      (∫ sample, (X sample + Y sample + Z sample) ^ 2 ∂productLaw P n) ≤
          ∫ sample, 3 * (X sample ^ 2 + Y sample ^ 2 + Z sample ^ 2)
            ∂productLaw P n := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        exact hpoint
      _ = 3 * ((∫ sample, X sample ^ 2 ∂productLaw P n) +
          (∫ sample, Y sample ^ 2 ∂productLaw P n) +
            ∫ sample, Z sample ^ 2 ∂productLaw P n) := by
        rw [integral_const_mul,
          integral_add Integrable.of_finite Integrable.of_finite,
          integral_add Integrable.of_finite Integrable.of_finite]
      _ ≤ 3 * (Kc * R + Kb * R + Kf * R) := by
        gcongr
      _ = C * R := by dsimp only [C]; ring
      _ = C * minimaxRate n d := by
        unfold R lightAsymptoticRate minimaxRate
        rfl
  · have hlt : n < calibrationCutoff := Nat.lt_of_not_ge hcut
    have hrate : 0 ≤ minimaxRate n d := by
      unfold minimaxRate
      positivity
    simpa [componentErrorMSE, lightContribution, targetLight,
      lightCells_eq_empty_of_lt_cutoff _ hlt] using mul_nonneg hC.le hrate

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
