import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCellRateDeterministic

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The balanced split, duplicated here to keep the light-cell assembly below
the final `LightCell` module in the import graph. -/
noncomputable def lightBalancedSplit {d : ℕ} (P : DiscreteLaw d) :
    Causalean.Stat.OneShotSplit
      (Causalean.Stat.iidSample_infinitePi (obsLaw P)) where
  n₁ n := n / 2
  bound n := Nat.div_le_self n 2
  grow := Nat.tendsto_div_const_atTop (by norm_num)
  cogrow := by
    show Filter.Tendsto (fun n : ℕ => n - n / 2) Filter.atTop Filter.atTop
    apply Filter.tendsto_atTop_mono
      (f := fun n : ℕ => n / 2) (g := fun n => n - n / 2)
    · intro n
      omega
    · exact Nat.tendsto_div_const_atTop (by norm_num)

def rebuildPilotSample {n d : ℕ} (P : DiscreteLaw d) (base : Obs d)
    (x : (lightBalancedSplit P).foldA n → Obs d) : Fin n → Obs d :=
  fun i => if h : i.1 < n / 2 then
    x ⟨i.1, by simpa [Causalean.Stat.OneShotSplit.foldA, lightBalancedSplit] using h⟩
  else base

/-- Defines rebuild Estimation Sample, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def rebuildEstimationSample {n d : ℕ} (P : DiscreteLaw d) (base : Obs d)
    (x : (lightBalancedSplit P).foldB n → Obs d) : Fin n → Obs d :=
  fun i => if h : n / 2 ≤ i.1 then
    x ⟨i.1, by
      simp only [Causalean.Stat.OneShotSplit.foldB, lightBalancedSplit,
        Finset.mem_filter, Finset.mem_range]
      exact ⟨i.2, h⟩⟩
  else base

/-- Establishes the stated property of split Category Count rebuild Pilot in the discrete average-treatment-effect construction. -/
lemma splitCategoryCount_rebuildPilot {n d : ℕ} (P : DiscreteLaw d)
    (base : Obs d) (ω : ℕ → Obs d) (k : Fin d) :
    splitCategoryCount (rebuildPilotSample P base
      (fun i : (lightBalancedSplit P).foldA n => ω i)) 0 k =
      splitCategoryCount (fun i : Fin n => ω i) 0 k := by
  classical
  unfold splitCategoryCount
  congr 1
  ext i
  simp only [Finset.mem_filter]
  by_cases hi : i.1 < n / 2
  · simp [splitIndices, rebuildPilotSample, hi]
  · simp [splitIndices, rebuildPilotSample, hi]

/-- Establishes the stated property of light Cells rebuild Pilot in the discrete average-treatment-effect construction. -/
lemma lightCells_rebuildPilot {n d : ℕ} (P : DiscreteLaw d)
    (base : Obs d) (ω : ℕ → Obs d) :
    lightCells (rebuildPilotSample P base
      (fun i : (lightBalancedSplit P).foldA n => ω i)) =
      lightCells (fun i : Fin n => ω i) := by
  classical
  by_cases hn : n < calibrationCutoff
  · simp [lightCells, hn]
  · ext k
    simp only [lightCells, heavyCells, hn, if_false, Finset.mem_compl,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [splitCategoryCount_rebuildPilot P base ω k]

/-- Establishes the stated property of split Cell Count rebuild Estimation in the discrete average-treatment-effect construction. -/
lemma splitCellCount_rebuildEstimation {n d : ℕ} (P : DiscreteLaw d)
    (base : Obs d) (ω : ℕ → Obs d) (k : Fin d) (a y : Fin 2) :
    splitCellCount (rebuildEstimationSample P base
      (fun i : (lightBalancedSplit P).foldB n => ω i)) 1 k a y =
      splitCellCount (fun i : Fin n => ω i) 1 k a y := by
  classical
  unfold splitCellCount
  congr 1
  ext i
  simp only [Finset.mem_filter]
  by_cases hi : n / 2 ≤ i.1
  · simp [splitIndices, rebuildEstimationSample, hi]
  · have hnot : ¬n / 2 ≤ i.1 := hi
    simp [splitIndices, rebuildEstimationSample, hi, hnot]

/-- Establishes the stated property of factorial Monomial rebuild Estimation in the discrete average-treatment-effect construction. -/
lemma factorialMonomial_rebuildEstimation {n d : ℕ} (P : DiscreteLaw d)
    (base : Obs d) (ω : ℕ → Obs d) (k : Fin d) (r : MultiIndex) :
    factorialMonomial (rebuildEstimationSample P base
      (fun i : (lightBalancedSplit P).foldB n => ω i)) k r =
      factorialMonomial (fun i : Fin n => ω i) k r := by
  unfold factorialMonomial
  apply congrArg (fun x : ℝ => x /
    (fallingFactorial (splitSize n 1) (multiDegree r) : ℝ))
  apply Finset.prod_congr rfl
  intro ay _hay
  rw [splitCellCount_rebuildEstimation P base ω]

/-- Establishes the stated property of factorial Polynomial Contribution rebuild Estimation in the discrete average-treatment-effect construction. -/
lemma factorialPolynomialContribution_rebuildEstimation {n d : ℕ}
    (P : DiscreteLaw d) (base : Obs d) (ω : ℕ → Obs d) (k : Fin d) :
    factorialPolynomialContribution (rebuildEstimationSample P base
      (fun i : (lightBalancedSplit P).foldB n => ω i)) k =
      factorialPolynomialContribution (fun i : Fin n => ω i) k := by
  unfold factorialPolynomialContribution
  simp_rw [factorialMonomial_rebuildEstimation P base ω]

/-- Defines light Indicator, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def lightIndicator {n d : ℕ} (sample : Fin n → Obs d)
    (k : Fin d) : ℝ := if k ∈ lightCells sample then 1 else 0

/-- Establishes the stated property of light Indicator rebuild Pilot in the discrete average-treatment-effect construction. -/
lemma lightIndicator_rebuildPilot {n d : ℕ} (P : DiscreteLaw d)
    (base : Obs d) (ω : ℕ → Obs d) (k : Fin d) :
    lightIndicator (rebuildPilotSample P base
      (fun i : (lightBalancedSplit P).foldA n => ω i)) k =
      lightIndicator (fun i : Fin n => ω i) k := by
  unfold lightIndicator
  rw [lightCells_rebuildPilot P base ω]

/-- Exact pilot/estimation factorization for two selected centered cell
errors.  This is the formal conditioning step behind equation (25). -/
lemma lightIndicator_centered_pair_factorization {n d : ℕ}
    (P : DiscreteLaw d) (k l : Fin d) :
    ∫ ω : ℕ → Obs d,
        (lightIndicator (fun i : Fin n => ω i) k *
          lightIndicator (fun i : Fin n => ω i) l) *
        ((factorialPolynomialContribution (fun i : Fin n => ω i) k -
            sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)) *
          (factorialPolynomialContribution (fun i : Fin n => ω i) l -
            sparsePolynomialMean P l (polynomialDegree n) (bandwidth n)))
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) =
      (∫ ω : ℕ → Obs d,
          lightIndicator (fun i : Fin n => ω i) k *
            lightIndicator (fun i : Fin n => ω i) l
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) *
        ∫ ω : ℕ → Obs d,
          (factorialPolynomialContribution (fun i : Fin n => ω i) k -
            sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)) *
          (factorialPolynomialContribution (fun i : Fin n => ω i) l -
            sparsePolynomialMean P l (polynomialDegree n) (bandwidth n))
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  let base : Obs d := (k, false, false)
  let pilot := fun x : (lightBalancedSplit P).foldA n → Obs d =>
    lightIndicator (rebuildPilotSample P base x) k *
      lightIndicator (rebuildPilotSample P base x) l
  let estimate := fun x : (lightBalancedSplit P).foldB n → Obs d =>
    (factorialPolynomialContribution (rebuildEstimationSample P base x) k -
      sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)) *
    (factorialPolynomialContribution (rebuildEstimationSample P base x) l -
      sparsePolynomialMean P l (polynomialDegree n) (bandwidth n))
  have h := oneShot_integral_mul_factorization (lightBalancedSplit P) n
    pilot estimate (measurable_of_finite _) (measurable_of_finite _)
  have hp (ω : ℕ → Obs d) :
      pilot (fun i : (lightBalancedSplit P).foldA n => ω i) =
        lightIndicator (fun i : Fin n => ω i) k *
          lightIndicator (fun i : Fin n => ω i) l := by
    dsimp only [pilot]
    rw [lightIndicator_rebuildPilot P base ω k,
      lightIndicator_rebuildPilot P base ω l]
  have he (ω : ℕ → Obs d) :
      estimate (fun i : (lightBalancedSplit P).foldB n => ω i) =
        (factorialPolynomialContribution (fun i : Fin n => ω i) k -
          sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)) *
        (factorialPolynomialContribution (fun i : Fin n => ω i) l -
          sparsePolynomialMean P l (polynomialDegree n) (bandwidth n)) := by
    dsimp only [estimate]
    rw [factorialPolynomialContribution_rebuildEstimation P base ω k,
      factorialPolynomialContribution_rebuildEstimation P base ω l]
  dsimp only [Causalean.Stat.iidSample_infinitePi] at h
  calc
    _ = ∫ ω, (pilot (fun i => ω i)) * estimate (fun i => ω i)
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [hp, he]
    _ = _ := h
    _ = _ := by
      congr 1
      · apply integral_congr_ae
        filter_upwards with ω
        exact hp ω
      · apply integral_congr_ae
        filter_upwards with ω
        exact he ω

/-- Shows that light Indicator nonneg is nonnegative. -/
lemma lightIndicator_nonneg {n d : ℕ} (sample : Fin n → Obs d) (k : Fin d) :
    0 ≤ lightIndicator sample k := by
  unfold lightIndicator
  split_ifs <;> norm_num

/-- Establishes the stated upper bound for light Indicator le one. -/
lemma lightIndicator_le_one {n d : ℕ} (sample : Fin n → Obs d) (k : Fin d) :
    lightIndicator sample k ≤ 1 := by
  unfold lightIndicator
  split_ifs <;> norm_num

/-- Evaluates or bounds the stated integral involving integral light Indicator pair mem Icc. -/
lemma integral_lightIndicator_pair_mem_Icc {n d : ℕ} (P : DiscreteLaw d)
    (k l : Fin d) :
    (∫ ω : ℕ → Obs d,
      lightIndicator (fun i : Fin n => ω i) k *
        lightIndicator (fun i : Fin n => ω i) l
      ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards with ω
    exact mul_nonneg (lightIndicator_nonneg _ _) (lightIndicator_nonneg _ _)
  · have hmono :
        (∫ ω : ℕ → Obs d,
          lightIndicator (fun i : Fin n => ω i) k *
            lightIndicator (fun i : Fin n => ω i) l
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ≤
          ∫ _ω : ℕ → Obs d, (1 : ℝ)
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
      have htrunc : Measurable (fun ω : ℕ → Obs d =>
          fun i : Fin n => ω i) := by fun_prop
      have hmeas : AEStronglyMeasurable (fun ω : ℕ → Obs d =>
          lightIndicator (fun i : Fin n => ω i) k *
            lightIndicator (fun i : Fin n => ω i) l)
          (Measure.infinitePi (fun _ : ℕ => obsLaw P)) :=
        ((measurable_of_finite (fun sample : Fin n → Obs d =>
          lightIndicator sample k * lightIndicator sample l)).comp
          htrunc).aestronglyMeasurable
      apply integral_mono (Integrable.of_bound hmeas 1
          (Filter.Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg]
            · exact mul_le_one₀ (lightIndicator_le_one _ _)
                (lightIndicator_nonneg _ _) (lightIndicator_le_one _ _)
            · exact mul_nonneg (lightIndicator_nonneg _ _) (lightIndicator_nonneg _ _)))
        (integrable_const (1 : ℝ))
      intro ω
      exact mul_le_one₀ (lightIndicator_le_one _ _)
        (lightIndicator_nonneg _ _) (lightIndicator_le_one _ _)
    simpa using hmono

/-- Shows that integrable centered Polynomial pair is integrable under the stated sampling distribution. -/
lemma integrable_centeredPolynomial_pair {n d : ℕ} (P : DiscreteLaw d)
    (k l : Fin d) :
    Integrable (fun ω : ℕ → Obs d =>
      (factorialPolynomialContribution (fun i : Fin n => ω i) k -
        sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)) *
      (factorialPolynomialContribution (fun i : Fin n => ω i) l -
        sparsePolynomialMean P l (polynomialDegree n) (bandwidth n)))
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  let mk := sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)
  let ml := sparsePolynomialMean P l (polynomialDegree n) (bandwidth n)
  have hi : Integrable (fun ω : ℕ → Obs d =>
      ((factorialPolynomialContribution (fun i : Fin n => ω i) k *
          factorialPolynomialContribution (fun i : Fin n => ω i) l -
        ml * factorialPolynomialContribution (fun i : Fin n => ω i) k) -
        mk * factorialPolynomialContribution (fun i : Fin n => ω i) l) +
        mk * ml) (Measure.infinitePi (fun _ : ℕ => obsLaw P)) :=
    (((integrable_factorialPolynomial_cross_mul (n := n) P k l).sub
      ((integrable_factorialPolynomialContribution_trunc_rate P k).const_mul ml)).sub
      ((integrable_factorialPolynomialContribution_trunc_rate P l).const_mul mk)).add
      (integrable_const (mk * ml))
  convert hi using 1
  funext ω
  dsimp only [mk, ml]
  ring

/-- Shows that integrable selected centered Polynomial pair is integrable under the stated sampling distribution. -/
lemma integrable_selected_centeredPolynomial_pair {n d : ℕ}
    (P : DiscreteLaw d) (k l : Fin d) :
    Integrable (fun ω : ℕ → Obs d =>
      (lightIndicator (fun i : Fin n => ω i) k *
        lightIndicator (fun i : Fin n => ω i) l) *
      ((factorialPolynomialContribution (fun i : Fin n => ω i) k -
          sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)) *
        (factorialPolynomialContribution (fun i : Fin n => ω i) l -
          sparsePolynomialMean P l (polynomialDegree n) (bandwidth n))))
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  have htrunc : Measurable (fun ω : ℕ → Obs d =>
      fun i : Fin n => ω i) := by fun_prop
  apply (integrable_centeredPolynomial_pair P k l).bdd_mul
    (((measurable_of_finite (fun sample : Fin n → Obs d =>
      lightIndicator sample k * lightIndicator sample l)).comp htrunc).aestronglyMeasurable)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact mul_le_one₀ (lightIndicator_le_one _ _)
      (lightIndicator_nonneg _ _) (lightIndicator_le_one _ _)
  · exact mul_nonneg (lightIndicator_nonneg _ _) (lightIndicator_nonneg _ _)

/-- Defines selected Fixed Light Centered, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def selectedFixedLightCentered {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) (S : Finset (Fin d)) : ℝ :=
  ∑ k ∈ S, lightIndicator sample k *
    (factorialPolynomialContribution sample k -
      sparsePolynomialMean P k (polynomialDegree n) (bandwidth n))

/- Random pilot selection costs nothing in the deterministic light-set bound:
the indicator pair factors from the estimation-fold covariance and lies in
`[0,1]`. -/
set_option maxHeartbeats 800000 in
/-- Establishes the stated upper bound for selected Fixed Light Centered second moment le. -/
lemma selectedFixedLightCentered_second_moment_le {n d : ℕ}
    (P : DiscreteLaw d) (S : Finset (Fin d))
    (hn : 0 < splitSize n 1) (hM : 0 < polynomialDegree n)
    (hB : 0 < bandwidth n)
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1)
    (hlight : ∀ k ∈ S,
      cellMass P k + 4 * (polynomialDegree n : ℝ) / splitSize n 1 ≤
        bandwidth n) :
    ∫ ω : ℕ → Obs d,
        selectedFixedLightCentered P (fun i : Fin n => ω i) S ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      (S.card : ℝ) * (8 * (Real.exp 1 + 1)) *
          (bandwidth n * 6 ^ polynomialDegree n) ^ 2 +
        (S.card : ℝ) ^ 2 *
          (8 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1) *
          (bandwidth n * 6 ^ polynomialDegree n) ^ 2 := by
  classical
  let E := fun k : Fin d => fun ω : ℕ → Obs d =>
    factorialPolynomialContribution (fun i : Fin n => ω i) k -
      sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)
  let I := fun k : Fin d => fun ω : ℕ → Obs d =>
    lightIndicator (fun i : Fin n => ω i) k
  let D := 8 * (Real.exp 1 + 1) *
    (bandwidth n * 6 ^ polynomialDegree n) ^ 2
  let Q := 8 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1 *
    (bandwidth n * 6 ^ polynomialDegree n) ^ 2
  have hmass (k : Fin d) (hk : k ∈ S) : cellMass P k ≤ bandwidth n :=
    (le_add_of_nonneg_right (by positivity :
      0 ≤ 4 * (polynomialDegree n : ℝ) / splitSize n 1)).trans (hlight k hk)
  have hest (k : Fin d) (hk : k ∈ S) (l : Fin d) (hl : l ∈ S) :
      ∫ ω : ℕ → Obs d, E k ω * E l ω
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
        (if k = l then D else 0) + Q := by
    by_cases hkl : k = l
    · subst l
      rw [if_pos rfl]
      have hd := integral_factorialPolynomial_centered_sq_le
        P k hn hM hB hsize (hlight k hk) (hmass k hk)
      have hd' : (∫ ω, E k ω * E k ω
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ≤ D := by
        simpa only [E, D, pow_two] using hd
      refine hd'.trans (le_add_of_nonneg_right ?_)
      dsimp only [Q]
      positivity
    · rw [if_neg hkl, zero_add]
      simpa only [E, Q] using
        integral_factorialPolynomial_centered_cross_le P k l hkl hM hB hsize
          (hmass k hk) (hmass l hl)
  have hpair (k : Fin d) (hk : k ∈ S) (l : Fin d) (hl : l ∈ S) :
      ∫ ω : ℕ → Obs d, (I k ω * I l ω) * (E k ω * E l ω)
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
        (if k = l then D else 0) + Q := by
    dsimp only [I, E]
    rw [lightIndicator_centered_pair_factorization P k l]
    let p := ∫ ω : ℕ → Obs d, I k ω * I l ω
      ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))
    let x := ∫ ω : ℕ → Obs d, E k ω * E l ω
      ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))
    let U := (if k = l then D else 0) + Q
    have hp := integral_lightIndicator_pair_mem_Icc (n := n) P k l
    have hx : x ≤ U := hest k hk l hl
    have hU : 0 ≤ U := by
      dsimp only [U, D, Q]
      split_ifs <;> positivity
    change p * x ≤ U
    by_cases hx0 : 0 ≤ x
    · calc
        p * x ≤ 1 * x := mul_le_mul_of_nonneg_right hp.2 hx0
        _ ≤ U := by simpa using hx
    · have hxneg : x ≤ 0 := le_of_not_ge hx0
      exact (mul_nonpos_of_nonneg_of_nonpos hp.1 hxneg).trans hU
  change (∫ ω : ℕ → Obs d, (∑ k ∈ S, I k ω * E k ω) ^ 2
    ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ≤ _
  rw [show (fun ω : ℕ → Obs d => (∑ k ∈ S, I k ω * E k ω) ^ 2) =
      (fun ω => ∑ k ∈ S, ∑ l ∈ S, (I k ω * I l ω) * (E k ω * E l ω)) by
    funext ω
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring]
  rw [integral_finset_sum S (fun k _ =>
    integrable_finset_sum S (fun l _ =>
      integrable_selected_centeredPolynomial_pair P k l))]
  simp_rw [integral_finset_sum S (fun l _ =>
    integrable_selected_centeredPolynomial_pair P _ l)]
  refine (Finset.sum_le_sum fun k hk =>
    Finset.sum_le_sum fun l hl => hpair k hk l hl).trans ?_
  have hsum : Finset.sum S (fun k =>
      Finset.sum S (fun l => (if k = l then D else 0) + Q)) =
      (S.card : ℝ) * D + (S.card : ℝ) ^ 2 * Q := by
    simp [Finset.sum_add_distrib, pow_two]
    ring
  rw [hsum]
  dsimp only [D, Q]
  ring_nf
  exact le_refl _

/-- Coefficient growth away from the genuinely-light cone.  This is the
quantitative content of equations (21)--(22), before inserting the pilot-tail
exponent. -/
lemma sparseArmEnvelope_le_growth {M : ℕ} (hM : 2 ≤ M) {B w : ℝ}
    (hB : 0 < B) (hw : 1 ≤ w) (v : Cell → ℝ)
    (hv : ∀ ay, 0 ≤ v ay) (hR : (∑ ay : Cell, v ay) ≤ B * w)
    (a : Fin 2) :
    sparseArmEnvelope M B v a ≤ B * 6 ^ M * w ^ M := by
  rw [sparseArmEnvelope_eq hB v hv a]
  let R := ∑ ay : Cell, v ay
  let A := v (a, 0) + v (a, 1)
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun ay _ => hv ay
  have hA0 : 0 ≤ A := add_nonneg (hv _) (hv _)
  have hAR : A ≤ R := by
    rcases a with ⟨a, ha⟩
    interval_cases a <;>
      simp [A, R, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
      linarith [hv (0, 0), hv (0, 1), hv (1, 0), hv (1, 1)]
  have hvaR : v (a, 1) ≤ R :=
    (le_add_of_nonneg_left (hv (a, 0))).trans hAR
  have hBw0 : 0 ≤ B * w := mul_nonneg hB.le (le_trans (by norm_num) hw)
  have hz0 : 0 ≤ A / B := div_nonneg hA0 hB.le
  have hzw : A / B ≤ w := by
    apply (div_le_iff₀ hB).2
    simpa [mul_comm] using hAR.trans hR
  have hpow : (A / B) ^ (M - 2) ≤ w ^ (M - 2) :=
    pow_le_pow_left₀ hz0 hzw _
  have hg : gpos M (A / B) ≤ 6 ^ M * w ^ (M - 2) := by
    refine (gpos_bound (by omega) hz0).trans ?_
    have hmax : max 1 ((A / B) ^ (M - 2)) ≤ w ^ (M - 2) := by
      apply max_le
      · exact one_le_pow₀ hw
      · exact hpow
    exact mul_le_mul_of_nonneg_left hmax (by positivity)
  have hbinv : 0 ≤ B⁻¹ := (inv_pos.mpr hB).le
  have hgp0 := gpos_nonneg M hz0
  have hvaBw : v (a, 1) ≤ B * w := hvaR.trans hR
  calc
    B⁻¹ * R * v (a, 1) * gpos M (A / B) ≤
        B⁻¹ * (B * w) * (B * w) * (6 ^ M * w ^ (M - 2)) := by
      exact mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hR hbinv) hvaBw
          (hv _) (mul_nonneg hbinv hBw0)) hg
        hgp0 (mul_nonneg (mul_nonneg hbinv hBw0) hBw0)
    _ = B * 6 ^ M * w ^ M := by
      calc
        B⁻¹ * (B * w) * (B * w) * (6 ^ M * w ^ (M - 2)) =
            B * 6 ^ M * (w ^ 2 * w ^ (M - 2)) := by
          field_simp [hB.ne']
        _ = B * 6 ^ M * w ^ M := by
          rw [← pow_add]
          congr 3
          omega

/-- Establishes the stated property of sparse Arm Envelope cell growth in the discrete average-treatment-effect construction. -/
lemma sparseArmEnvelope_cell_growth {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Fin 2) (hM : 2 ≤ polynomialDegree n)
    (hB : 0 < bandwidth n) (hn : 0 < splitSize n 1)
    (hshift : 4 * polynomialDegree n / (splitSize n 1 : ℝ) ≤
      3 * bandwidth n / 4) :
    sparseArmEnvelope (polynomialDegree n) (bandwidth n)
        (shiftedCellVector P k (polynomialDegree n) (splitSize n 1)) a ≤
      bandwidth n * 6 ^ polynomialDegree n *
        (1 + cellMass P k / bandwidth n) ^ polynomialDegree n := by
  let w := 1 + cellMass P k / bandwidth n
  have hw : 1 ≤ w := by
    dsimp only [w]
    exact le_add_of_nonneg_right
      (div_nonneg (cellMass_mem_unitInterval P k).1 hB.le)
  apply sparseArmEnvelope_le_growth hM hB hw _
    (shiftedCellVector_nonneg P k (polynomialDegree n) (splitSize n 1))
  rw [shiftedCellVector_sum]
  change cellMass P k + 4 * (polynomialDegree n : ℝ) / splitSize n 1 ≤
    bandwidth n * w
  have hs : 4 * (polynomialDegree n : ℝ) / splitSize n 1 ≤ bandwidth n :=
    hshift.trans (by linarith [hB])
  dsimp only [w]
  rw [mul_add, mul_one, mul_div_cancel₀ _ hB.ne']
  linarith

/-- Evaluates or bounds the stated integral involving integral factorial Polynomial sq growth. -/
lemma integral_factorialPolynomial_sq_growth {n d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) (hn : 0 < splitSize n 1)
    (hM : 2 ≤ polynomialDegree n) (hB : 0 < bandwidth n)
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1)
    (hshift : 4 * polynomialDegree n / (splitSize n 1 : ℝ) ≤
      3 * bandwidth n / 4) :
    ∫ ω : ℕ → Obs d,
        factorialPolynomialContribution (fun i : Fin n => ω i) k ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      4 * Real.exp 1 *
        (bandwidth n * 6 ^ polynomialDegree n *
          (1 + cellMass P k / bandwidth n) ^ polynomialDegree n) ^ 2 := by
  let R := bandwidth n * 6 ^ polynomialDegree n *
    (1 + cellMass P k / bandwidth n) ^ polynomialDegree n
  have henv (a : Fin 2) :
      sparseArmEnvelope (polynomialDegree n) (bandwidth n)
          (shiftedCellVector P k (polynomialDegree n) (splitSize n 1)) a ≤ R :=
    sparseArmEnvelope_cell_growth P k a hM hB hn hshift
  let X := fun ω : ℕ → Obs d =>
    sparseArmContribution (fun i : Fin n => ω i) k 1
  let Y := fun ω : ℕ → Obs d =>
    sparseArmContribution (fun i : Fin n => ω i) k 0
  have hpoint (ω : ℕ → Obs d) :
      factorialPolynomialContribution (fun i : Fin n => ω i) k ^ 2 ≤
        2 * X ω ^ 2 + 2 * Y ω ^ 2 := by
    rw [factorialPolynomialContribution_eq_sparseArms]
    dsimp only [X, Y]
    nlinarith [sq_nonneg
      (sparseArmContribution (fun i : Fin n => ω i) k 1 +
       sparseArmContribution (fun i : Fin n => ω i) k 0)]
  have hmono :
      ∫ ω : ℕ → Obs d,
          factorialPolynomialContribution (fun i : Fin n => ω i) k ^ 2
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
        ∫ ω : ℕ → Obs d, (2 * X ω ^ 2 + 2 * Y ω ^ 2)
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    apply integral_mono (integrable_factorialPolynomialContribution_sq P k)
    · exact ((integrable_sparseArm_sq P k 1).const_mul 2).add
        ((integrable_sparseArm_sq P k 0).const_mul 2)
    · exact hpoint
  refine hmono.trans ?_
  rw [integral_add, integral_const_mul, integral_const_mul]
  · have h1 := integral_sparseArm_sq_le P k 1 hn hsize
      |>.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (sparseArmEnvelope_nonneg _
          (shiftedCellVector_nonneg P k _ _) 1) (henv 1) 2)
        (Real.exp_pos 1).le)
    have h0 := integral_sparseArm_sq_le P k 0 hn hsize
      |>.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (sparseArmEnvelope_nonneg _
          (shiftedCellVector_nonneg P k _ _) 0) (henv 0) 2)
        (Real.exp_pos 1).le)
    change 2 * (∫ ω, X ω ^ 2 ∂_) + 2 * (∫ ω, Y ω ^ 2 ∂_) ≤ _
    nlinarith
  · exact (integrable_sparseArm_sq P k 1).const_mul 2
  · exact (integrable_sparseArm_sq P k 0).const_mul 2

/-- Evaluates or bounds the stated integral involving light integral product Law eq infinite. -/
lemma light_integral_productLaw_eq_infinite {n d : ℕ} (P : DiscreteLaw d)
    (f : (Fin n → Obs d) → ℝ) :
    ∫ sample, f sample ∂productLaw P n =
      ∫ ω : ℕ → Obs d, f (fun i : Fin n => ω i)
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  let trunc : (ℕ → Obs d) → (Fin n → Obs d) := fun ω i => ω i
  have htrunc : Measurable trunc := by fun_prop
  rw [productLaw, ← finProductLaw_eq_map (obsLaw P) n,
    integral_map htrunc.aemeasurable (measurable_of_finite f).aestronglyMeasurable]

/-- Evaluates or bounds the stated integral involving integral light Indicator eq probability. -/
lemma integral_lightIndicator_eq_probability {n d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) :
    ∫ ω : ℕ → Obs d, lightIndicator (fun i : Fin n => ω i) k
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) =
      (productLaw P n).real {sample | k ∈ lightCells sample} := by
  calc
    (∫ ω : ℕ → Obs d, lightIndicator (fun i : Fin n => ω i) k
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) =
      ∫ sample, lightIndicator sample k ∂productLaw P n :=
        (light_integral_productLaw_eq_infinite (n := n) P
          (fun sample : Fin n → Obs d => lightIndicator sample k)).symm
    _ = _ := by
      have hpred : Measurable (fun sample : Fin n → Obs d =>
          k ∈ lightCells sample) := measurable_of_finite _
      have hE : MeasurableSet {sample : Fin n → Obs d |
          k ∈ lightCells sample} := by
        exact (Set.toFinite _).measurableSet
      rw [show (fun sample : Fin n → Obs d => lightIndicator sample k) =
          Set.indicator {sample | k ∈ lightCells sample} (fun _ => (1 : ℝ)) by
        funext sample
        simp [lightIndicator, Set.indicator]]
      rw [integral_indicator hE]
      simp [Measure.real]

/-- Equation (20) for the actual calibrated light indicator. -/
lemma falseLight_selection_probability {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (hcut : calibrationCutoff ≤ n)
    (hfalse : bandwidth n / 4 < cellMass P k) :
    (productLaw P n).real {sample | k ∈ lightCells sample} ≤
      Real.exp (-((n / 2 : ℕ) * cellMass P k) / 8) := by
  classical
  have hbase : cutoffProperty calibrationCutoff := by
    rw [calibrationCutoff]
    exact Nat.find_spec cutoffProperty_eventually
  have hp := hbase n hcut
  have hLpos : 0 < logScale n := by
    have ha0 : 0 < alpha0 := by
      unfold alpha0 dA
      have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
      have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
      positivity
    nlinarith [hp.1]
  have hm0 : 0 < splitSize n 0 := by
    have hM2 : 2 ≤ polynomialDegree n := by simp [polynomialDegree]
    have hm1sq := hp.2.1
    have hM4 : 4 ≤ polynomialDegree n ^ 2 := by
      simpa [pow_two] using Nat.mul_self_le_mul_self hM2
    have h16 : 16 ≤ splitSize n 1 := by nlinarith
    have hm1le : splitSize n 1 ≤ n := by rw [splitSize_one_eq]; omega
    have hn16 : 16 ≤ n := h16.trans hm1le
    rw [splitSize_zero_eq]
    omega
  have hmratio : splitSize n 1 ≤ 2 * splitSize n 0 := by
    have hM2 : 2 ≤ polynomialDegree n := by simp [polynomialDegree]
    have hM4 : 4 ≤ polynomialDegree n ^ 2 := by
      simpa [pow_two] using Nat.mul_self_le_mul_self hM2
    have h16 : 16 ≤ splitSize n 1 := by nlinarith [hp.2.1]
    have hm1le : splitSize n 1 ≤ n := by rw [splitSize_one_eq]; omega
    have hn16 : 16 ≤ n := h16.trans hm1le
    rw [splitSize_zero_eq, splitSize_one_eq]
    omega
  have hmean :
      2 * (256 * logScale n) < (n / 2 : ℕ) * cellMass P k := by
    rw [← splitSize_zero_eq]
    rw [bandwidth] at hfalse
    have hm0R : 0 < (splitSize n 0 : ℝ) := by exact_mod_cast hm0
    have hM2 : 2 ≤ polynomialDegree n := by simp [polynomialDegree]
    have hM4 : 4 ≤ polynomialDegree n ^ 2 := by
      simpa [pow_two] using Nat.mul_self_le_mul_self hM2
    have hm1nat : 0 < splitSize n 1 := by nlinarith [hp.2.1]
    have hm1R : 0 < (splitSize n 1 : ℝ) := by exact_mod_cast hm1nat
    have hmratioR : (splitSize n 1 : ℝ) ≤ 2 * splitSize n 0 := by
      exact_mod_cast hmratio
    norm_num [b0] at hfalse
    have hf : 1024 * logScale n / (splitSize n 1 : ℝ) < cellMass P k := by
      convert hfalse using 1 <;> ring
    have hmul := (div_lt_iff₀ hm1R).mp hf
    nlinarith
  have htail := pilotCategory_lower_tail P k hmean
  refine (measureReal_mono ?_).trans htail
  intro sample hs
  have hnlt : ¬n < calibrationCutoff := by omega
  have hnotHeavy : k ∉ heavyCells sample := by
    simpa [lightCells, hnlt] using hs
  rw [heavyCells, if_neg hnlt] at hnotHeavy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnotHeavy
  change (splitCategoryCount sample 0 k : ℝ) ≤ 256 * logScale n
  simpa [lambda0] using hnotHeavy

/-- The positive polynomial growth is dominated by the calibrated pilot-tail
exponent.  The deliberately coarse constant `49` leaves ample slack. -/
lemma falseLight_tail_times_growth {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (hcut : calibrationCutoff ≤ n)
    (hfalse : bandwidth n / 4 < cellMass P k) :
    Real.exp (-((n / 2 : ℕ) * cellMass P k) / 8) *
        (6 ^ polynomialDegree n *
          (1 + cellMass P k / bandwidth n) ^ polynomialDegree n) ^ 2 ≤
      Real.exp (-49 * logScale n) := by
  classical
  have hbase : cutoffProperty calibrationCutoff := by
    rw [calibrationCutoff]
    exact Nat.find_spec cutoffProperty_eventually
  rcases hbase n hcut with ⟨hscale, hsize, hshift⟩
  have ha0 : 0 < alpha0 := by
    unfold alpha0 dA
    have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
    have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have ha1 : alpha0 ≤ 1 := by simp [alpha0]
  have hL : 0 < logScale n := by nlinarith
  have hM2 : 2 ≤ polynomialDegree n := by simp [polynomialDegree]
  have hm1 : 0 < splitSize n 1 := by nlinarith
  have hm0 : 0 < splitSize n 0 := by
    have hM4 : 4 ≤ polynomialDegree n ^ 2 := by
      simpa [pow_two] using Nat.mul_self_le_mul_self hM2
    have h16 : 16 ≤ splitSize n 1 := by nlinarith
    have hm1le : splitSize n 1 ≤ n := by rw [splitSize_one_eq]; omega
    have hn16 : 16 ≤ n := h16.trans hm1le
    rw [splitSize_zero_eq]
    omega
  have hmratio : splitSize n 1 ≤ 2 * splitSize n 0 := by
    have hM4 : 4 ≤ polynomialDegree n ^ 2 := by
      simpa [pow_two] using Nat.mul_self_le_mul_self hM2
    have h16 : 16 ≤ splitSize n 1 := by nlinarith
    have hm1le : splitSize n 1 ≤ n := by rw [splitSize_one_eq]; omega
    have hn16 : 16 ≤ n := h16.trans hm1le
    rw [splitSize_zero_eq, splitSize_one_eq]
    omega
  have hB : 0 < bandwidth n := by
    rw [bandwidth]
    exact div_pos (mul_pos (by norm_num [b0]) hL) (by exact_mod_cast hm1)
  let M := polynomialDegree n
  let B := bandwidth n
  let p := cellMass P k
  let z := p / B
  let w := 1 + z
  have hz : 1 / 4 < z := by
    dsimp only [z, p, B]
    apply (lt_div_iff₀ hB).2
    nlinarith [hfalse]
  have hz0 : 0 < z := (by linarith : 0 < z)
  have hw : 0 < w := by dsimp only [w]; linarith
  have hx : 0 < 6 * w := mul_pos (by norm_num) hw
  have hwz : w ≤ 5 * z := by dsimp only [w]; linarith
  have hxz : 6 * w ≤ 30 * z := by nlinarith
  have hMle : (M : ℝ) ≤ logScale n := by
    have hfloor2 : (2 : ℤ) ≤ ⌊alpha0 * logScale n⌋ := by
      rw [Int.le_floor]
      exact_mod_cast hscale
    have hmax : M = Int.toNat ⌊alpha0 * logScale n⌋ := by
      dsimp only [M]
      rw [polynomialDegree, max_eq_right]
      exact Int.toNat_le_toNat hfloor2
    rw [hmax]
    have hfloor0 : 0 ≤ ⌊alpha0 * logScale n⌋ := le_trans (by norm_num) hfloor2
    rw [show ((Int.toNat ⌊alpha0 * logScale n⌋ : ℕ) : ℝ) =
        ((⌊alpha0 * logScale n⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg hfloor0]
    exact (Int.floor_le _).trans
      (mul_le_of_le_one_left hL.le ha1)
  have hlog : Real.log (6 * w) ≤ 30 * z :=
    (Real.log_le_sub_one_of_pos hx).trans (by linarith)
  have hgrowthExp :
      2 * (M : ℝ) * Real.log (6 * w) ≤ 60 * logScale n * z := by
    have hlog0 : 0 ≤ Real.log (6 * w) :=
      Real.log_nonneg (by nlinarith [hz] : 1 ≤ 6 * w)
    nlinarith
  have htailExp :
      256 * logScale n * z ≤ (splitSize n 0 : ℝ) * p / 8 := by
    have hm0R : 0 < (splitSize n 0 : ℝ) := by exact_mod_cast hm0
    have hm1R : 0 < (splitSize n 1 : ℝ) := by exact_mod_cast hm1
    have hmratioR : (splitSize n 1 : ℝ) ≤ 2 * splitSize n 0 := by
      exact_mod_cast hmratio
    have hpz : p = B * z := by
      dsimp only [z]
      rw [mul_div_cancel₀ p hB.ne']
    rw [hpz]
    dsimp only [B]
    rw [bandwidth]
    norm_num [b0]
    field_simp
    nlinarith
  have hexp :
      -((splitSize n 0 : ℝ) * p) / 8 +
          2 * (M : ℝ) * Real.log (6 * w) ≤
        -49 * logScale n := by
    have hzquarter : 1 / 4 ≤ z := hz.le
    nlinarith
  have hpow :
      (6 ^ M * w ^ M) ^ 2 =
        Real.exp (2 * (M : ℝ) * Real.log (6 * w)) := by
    have hnat : (6 * w) ^ M =
        Real.exp ((M : ℝ) * Real.log (6 * w)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hx]
      congr 1
      ring
    rw [← mul_pow, hnat, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hfinal : Real.exp (-((splitSize n 0 : ℝ) * p) / 8) *
      (6 ^ M * w ^ M) ^ 2 ≤ Real.exp (-49 * logScale n) := by
    rw [hpow, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp
  simpa only [M, p, z, w, splitSize_zero_eq] using hfinal

/-- Establishes the stated property of light Indicator target pair factorization in the discrete average-treatment-effect construction. -/
lemma lightIndicator_target_pair_factorization {n d : ℕ}
    (P : DiscreteLaw d) (k l : Fin d) (tk tl : ℝ) :
    ∫ ω : ℕ → Obs d,
        (lightIndicator (fun i : Fin n => ω i) k *
          lightIndicator (fun i : Fin n => ω i) l) *
        ((factorialPolynomialContribution (fun i : Fin n => ω i) k - tk) *
          (factorialPolynomialContribution (fun i : Fin n => ω i) l - tl))
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) =
      (∫ ω : ℕ → Obs d,
          lightIndicator (fun i : Fin n => ω i) k *
            lightIndicator (fun i : Fin n => ω i) l
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) *
        ∫ ω : ℕ → Obs d,
          (factorialPolynomialContribution (fun i : Fin n => ω i) k - tk) *
            (factorialPolynomialContribution (fun i : Fin n => ω i) l - tl)
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  let base : Obs d := (k, false, false)
  let pilot := fun x : (lightBalancedSplit P).foldA n → Obs d =>
    lightIndicator (rebuildPilotSample P base x) k *
      lightIndicator (rebuildPilotSample P base x) l
  let estimate := fun x : (lightBalancedSplit P).foldB n → Obs d =>
    (factorialPolynomialContribution (rebuildEstimationSample P base x) k - tk) *
      (factorialPolynomialContribution (rebuildEstimationSample P base x) l - tl)
  have h := oneShot_integral_mul_factorization (lightBalancedSplit P) n
    pilot estimate (measurable_of_finite _) (measurable_of_finite _)
  have hp (ω : ℕ → Obs d) :
      pilot (fun i : (lightBalancedSplit P).foldA n => ω i) =
        lightIndicator (fun i : Fin n => ω i) k *
          lightIndicator (fun i : Fin n => ω i) l := by
    dsimp only [pilot]
    rw [lightIndicator_rebuildPilot P base ω k,
      lightIndicator_rebuildPilot P base ω l]
  have he (ω : ℕ → Obs d) :
      estimate (fun i : (lightBalancedSplit P).foldB n => ω i) =
        (factorialPolynomialContribution (fun i : Fin n => ω i) k - tk) *
          (factorialPolynomialContribution (fun i : Fin n => ω i) l - tl) := by
    dsimp only [estimate]
    rw [factorialPolynomialContribution_rebuildEstimation P base ω k,
      factorialPolynomialContribution_rebuildEstimation P base ω l]
  dsimp only [Causalean.Stat.iidSample_infinitePi] at h
  calc
    _ = ∫ ω, (pilot (fun i => ω i)) * estimate (fun i => ω i)
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [hp, he]
    _ = _ := h
    _ = _ := by
      congr 1
      · apply integral_congr_ae
        filter_upwards with ω
        exact hp ω
      · apply integral_congr_ae
        filter_upwards with ω
        exact he ω

/-- Evaluates or bounds the stated integral involving integral factorial Polynomial target sq growth. -/
lemma integral_factorialPolynomial_target_sq_growth {n d : ℕ}
    {epsilon : ℝ} (P : DiscreteLaw d) (hOverlap : Overlap epsilon P)
    (k : Fin d) (hn : 0 < splitSize n 1) (hM : 2 ≤ polynomialDegree n)
    (hB : 0 < bandwidth n)
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1)
    (hshift : 4 * polynomialDegree n / (splitSize n 1 : ℝ) ≤
      3 * bandwidth n / 4) :
    ∫ ω : ℕ → Obs d,
        (factorialPolynomialContribution (fun i : Fin n => ω i) k -
          cellPhi (cellVector P k)) ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      8 * (Real.exp 1 + 1) * bandwidth n ^ 2 *
        (6 ^ polynomialDegree n *
          (1 + cellMass P k / bandwidth n) ^ polynomialDegree n) ^ 2 := by
  let X := fun ω : ℕ → Obs d =>
    factorialPolynomialContribution (fun i : Fin n => ω i) k
  let t := cellPhi (cellVector P k)
  let G := 6 ^ polynomialDegree n *
    (1 + cellMass P k / bandwidth n) ^ polynomialDegree n
  have hz0 : 0 ≤ cellMass P k / bandwidth n :=
    div_nonneg (cellMass_mem_unitInterval P k).1 hB.le
  have hw0 : 0 ≤ 1 + cellMass P k / bandwidth n := by linarith
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact mul_nonneg (pow_nonneg (by norm_num) _ ) (pow_nonneg hw0 _)
  have hzone : cellMass P k / bandwidth n ≤ G := by
    have hw : 1 ≤ 1 + cellMass P k / bandwidth n := by linarith
    have hM1 : 1 ≤ polynomialDegree n := by omega
    calc
      cellMass P k / bandwidth n ≤ 1 + cellMass P k / bandwidth n := by linarith
      _ ≤ (1 + cellMass P k / bandwidth n) ^ polynomialDegree n := by
        simpa using pow_le_pow_right₀ hw hM1
      _ ≤ G := by
        dsimp only [G]
        have h6 : (1 : ℝ) ≤ 6 ^ polynomialDegree n := one_le_pow₀ (by norm_num)
        nlinarith [pow_nonneg (by linarith : 0 ≤ 1 + cellMass P k / bandwidth n)
          (polynomialDegree n)]
  have ht : |t| ≤ bandwidth n * G := by
    refine (abs_cellPhi_cellVector_le_mass P hOverlap k).trans ?_
    have hp : cellMass P k = bandwidth n *
        (cellMass P k / bandwidth n) := by field_simp [hB.ne']
    rw [hp]
    exact mul_le_mul_of_nonneg_left hzone hB.le
  have ht2 : t ^ 2 ≤ (bandwidth n * G) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  have hpoint (ω : ℕ → Obs d) :
      (X ω - t) ^ 2 ≤ 2 * X ω ^ 2 + 2 * t ^ 2 := by
    nlinarith [sq_nonneg (X ω + t)]
  have hmono : (∫ ω, (X ω - t) ^ 2
      ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ≤
      ∫ ω, (2 * X ω ^ 2 + 2 * t ^ 2)
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    apply integral_mono
    · have hi : Integrable (fun ω : ℕ → Obs d =>
          factorialPolynomialContribution (fun i : Fin n => ω i) k ^ 2 -
            ((2 * t) * factorialPolynomialContribution (fun i : Fin n => ω i) k -
              t ^ 2)) (Measure.infinitePi (fun _ : ℕ => obsLaw P)) :=
        (integrable_factorialPolynomialContribution_sq (n := n) P k).sub
        (((integrable_factorialPolynomialContribution_trunc_rate P k).const_mul
          (2 * t)).sub (integrable_const (t ^ 2)))
      convert hi using 1
      funext ω
      dsimp only [X]
      ring
    · exact ((integrable_factorialPolynomialContribution_sq P k).const_mul 2).add
        (integrable_const (2 * t ^ 2))
    · exact hpoint
  refine hmono.trans ?_
  rw [integral_add, integral_const_mul, integral_const]
  simp only [measureReal_univ_eq_one, one_smul]
  · have hX := integral_factorialPolynomial_sq_growth P k hn hM hB hsize hshift
    change 2 * (∫ ω, X ω ^ 2 ∂_) + 2 * t ^ 2 ≤ _
    nlinarith [Real.exp_pos 1, sq_nonneg (bandwidth n * G)]
  · exact (integrable_factorialPolynomialContribution_sq P k).const_mul 2
  · exact integrable_const _

/-- Equations (20)--(24) combined for one falsely selected light cell. -/
lemma falseLight_selected_error_sq {n d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P) (k : Fin d)
    (hcut : calibrationCutoff ≤ n)
    (hfalse : bandwidth n / 4 < cellMass P k) :
    ∫ ω : ℕ → Obs d,
        lightIndicator (fun i : Fin n => ω i) k *
          (factorialPolynomialContribution (fun i : Fin n => ω i) k -
            cellPhi (cellVector P k)) ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      8 * (Real.exp 1 + 1) * bandwidth n ^ 2 *
        Real.exp (-49 * logScale n) := by
  classical
  have hbase : cutoffProperty calibrationCutoff := by
    rw [calibrationCutoff]
    exact Nat.find_spec cutoffProperty_eventually
  rcases hbase n hcut with ⟨_hscale, hsize, hshift⟩
  have hM : 2 ≤ polynomialDegree n := by simp [polynomialDegree]
  have hM4 : 4 ≤ polynomialDegree n ^ 2 := by
    simpa [pow_two] using Nat.mul_self_le_mul_self hM
  have hn : 0 < splitSize n 1 := by nlinarith
  have hL : 0 < logScale n := by
    have ha0 : 0 < alpha0 := by
      unfold alpha0 dA
      have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
      have hlog : 0 < Real.log (27 / 4 : ℝ) := Real.log_pos (by norm_num)
      positivity
    nlinarith
  have hB : 0 < bandwidth n := by
    rw [bandwidth]
    exact div_pos (mul_pos (by norm_num [b0]) hL) (by exact_mod_cast hn)
  rw [show (fun ω : ℕ → Obs d =>
      lightIndicator (fun i : Fin n => ω i) k *
        (factorialPolynomialContribution (fun i : Fin n => ω i) k -
          cellPhi (cellVector P k)) ^ 2) =
      (fun ω => (lightIndicator (fun i : Fin n => ω i) k *
        lightIndicator (fun i : Fin n => ω i) k) *
        ((factorialPolynomialContribution (fun i : Fin n => ω i) k -
          cellPhi (cellVector P k)) *
        (factorialPolynomialContribution (fun i : Fin n => ω i) k -
          cellPhi (cellVector P k)))) by
    funext ω
    unfold lightIndicator
    split_ifs <;> ring,
    lightIndicator_target_pair_factorization P k k
      (cellPhi (cellVector P k)) (cellPhi (cellVector P k))]
  have hp : (∫ ω : ℕ → Obs d,
      lightIndicator (fun i : Fin n => ω i) k *
        lightIndicator (fun i : Fin n => ω i) k
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ≤
      Real.exp (-((n / 2 : ℕ) * cellMass P k) / 8) := by
    rw [show (fun ω : ℕ → Obs d =>
      lightIndicator (fun i : Fin n => ω i) k *
        lightIndicator (fun i : Fin n => ω i) k) =
      (fun ω => lightIndicator (fun i : Fin n => ω i) k) by
      funext ω
      unfold lightIndicator
      split_ifs <;> norm_num,
      integral_lightIndicator_eq_probability]
    exact falseLight_selection_probability P k hcut hfalse
  have he := integral_factorialPolynomial_target_sq_growth
    P hOverlap k hn hM hB hsize hshift
  have he' : (∫ ω : ℕ → Obs d,
      (factorialPolynomialContribution (fun i : Fin n => ω i) k -
        cellPhi (cellVector P k)) *
      (factorialPolynomialContribution (fun i : Fin n => ω i) k -
        cellPhi (cellVector P k))
      ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ≤
      8 * (Real.exp 1 + 1) * bandwidth n ^ 2 *
        (6 ^ polynomialDegree n *
          (1 + cellMass P k / bandwidth n) ^ polynomialDegree n) ^ 2 := by
    simpa only [pow_two] using he
  have hp0 := (integral_lightIndicator_pair_mem_Icc (n := n) P k k).1
  have he0 : 0 ≤ ∫ ω : ℕ → Obs d,
      (factorialPolynomialContribution (fun i : Fin n => ω i) k -
        cellPhi (cellVector P k)) *
      (factorialPolynomialContribution (fun i : Fin n => ω i) k -
        cellPhi (cellVector P k))
      ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    apply integral_nonneg_of_ae
    filter_upwards with ω
    exact mul_self_nonneg _
  calc
    (∫ ω : ℕ → Obs d,
        lightIndicator (fun i : Fin n => ω i) k *
          lightIndicator (fun i : Fin n => ω i) k
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) *
      (∫ ω : ℕ → Obs d,
        (factorialPolynomialContribution (fun i : Fin n => ω i) k -
          cellPhi (cellVector P k)) *
        (factorialPolynomialContribution (fun i : Fin n => ω i) k -
          cellPhi (cellVector P k))
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ≤
      Real.exp (-((n / 2 : ℕ) * cellMass P k) / 8) *
        (8 * (Real.exp 1 + 1) * bandwidth n ^ 2 *
          (6 ^ polynomialDegree n *
            (1 + cellMass P k / bandwidth n) ^ polynomialDegree n) ^ 2) := by
      exact mul_le_mul hp he' he0 (Real.exp_pos _).le
    _ ≤ 8 * (Real.exp 1 + 1) * bandwidth n ^ 2 *
        Real.exp (-49 * logScale n) := by
      have hg := falseLight_tail_times_growth P k hcut hfalse
      have hc : 0 ≤ 8 * (Real.exp 1 + 1) * bandwidth n ^ 2 := by positivity
      nlinarith

/-- Defines false Light Set, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def falseLightSet {n d : ℕ} (P : DiscreteLaw d) :
    Finset (Fin d) :=
  Finset.univ.filter fun k => bandwidth n / 4 < cellMass P k

/-- Defines selected False Light Error, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def selectedFalseLightError {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) : ℝ :=
  ∑ k ∈ falseLightSet (n := n) P, lightIndicator sample k *
    (factorialPolynomialContribution sample k - cellPhi (cellVector P k))

/-- Shows that integrable selected target pair is integrable under the stated sampling distribution. -/
lemma integrable_selected_target_pair {n d : ℕ} (P : DiscreteLaw d)
    (k l : Fin d) (tk tl : ℝ) :
    Integrable (fun ω : ℕ → Obs d =>
      (lightIndicator (fun i : Fin n => ω i) k *
        lightIndicator (fun i : Fin n => ω i) l) *
      ((factorialPolynomialContribution (fun i : Fin n => ω i) k - tk) *
        (factorialPolynomialContribution (fun i : Fin n => ω i) l - tl)))
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  have hest : Integrable (fun ω : ℕ → Obs d =>
      (factorialPolynomialContribution (fun i : Fin n => ω i) k - tk) *
        (factorialPolynomialContribution (fun i : Fin n => ω i) l - tl))
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    have hi : Integrable (fun ω : ℕ → Obs d =>
        ((factorialPolynomialContribution (fun i : Fin n => ω i) k *
            factorialPolynomialContribution (fun i : Fin n => ω i) l -
          tl * factorialPolynomialContribution (fun i : Fin n => ω i) k) -
          tk * factorialPolynomialContribution (fun i : Fin n => ω i) l) +
          tk * tl) (Measure.infinitePi (fun _ : ℕ => obsLaw P)) :=
      (((integrable_factorialPolynomial_cross_mul (n := n) P k l).sub
        ((integrable_factorialPolynomialContribution_trunc_rate P k).const_mul tl)).sub
        ((integrable_factorialPolynomialContribution_trunc_rate P l).const_mul tk)).add
        (integrable_const (tk * tl))
    convert hi using 1
    funext ω
    ring
  have htrunc : Measurable (fun ω : ℕ → Obs d =>
      fun i : Fin n => ω i) := by fun_prop
  apply hest.bdd_mul (((measurable_of_finite (fun sample : Fin n → Obs d =>
    lightIndicator sample k * lightIndicator sample l)).comp htrunc).aestronglyMeasurable)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact mul_le_one₀ (lightIndicator_le_one _ _)
      (lightIndicator_nonneg _ _) (lightIndicator_le_one _ _)
  · exact mul_nonneg (lightIndicator_nonneg _ _) (lightIndicator_nonneg _ _)

/-- Summed false-light remainder from equations (23)--(24). -/
lemma selectedFalseLightError_second_moment_le {n d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P)
    (hcut : calibrationCutoff ≤ n) :
    ∫ ω : ℕ → Obs d,
        selectedFalseLightError P (fun i : Fin n => ω i) ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      (d : ℝ) ^ 2 * (8 * (Real.exp 1 + 1) * bandwidth n ^ 2 *
        Real.exp (-49 * logScale n)) := by
  classical
  let F := falseLightSet (n := n) P
  let e := fun k : Fin d => fun ω : ℕ → Obs d =>
    lightIndicator (fun i : Fin n => ω i) k *
      (factorialPolynomialContribution (fun i : Fin n => ω i) k -
        cellPhi (cellVector P k))
  let R := 8 * (Real.exp 1 + 1) * bandwidth n ^ 2 *
    Real.exp (-49 * logScale n)
  have hcard : (F.card : ℝ) ≤ d := by
    exact_mod_cast (calc
      F.card ≤ (Finset.univ : Finset (Fin d)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = d := Fintype.card_fin d)
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hpoint (ω : ℕ → Obs d) :
      (∑ k ∈ F, e k ω) ^ 2 ≤ (F.card : ℝ) * ∑ k ∈ F, (e k ω) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := F) (f := fun k => e k ω))
  have hepair (k l : Fin d) : Integrable (fun ω => e k ω * e l ω)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    convert integrable_selected_target_pair P k l
      (cellPhi (cellVector P k)) (cellPhi (cellVector P l)) using 1
    funext ω
    dsimp only [e]
    ring
  have hesq (k : Fin d) : Integrable (fun ω => (e k ω) ^ 2)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    convert hepair k k using 1
    funext ω
    rw [pow_two]
  have hmono :
      (∫ ω, (∑ k ∈ F, e k ω) ^ 2
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ≤
        ∫ ω, (F.card : ℝ) * ∑ k ∈ F, (e k ω) ^ 2
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    apply integral_mono
    · have hs := integrable_finset_sum F fun k _ =>
          integrable_finset_sum F fun l _ => hepair k l
      convert hs using 1
      funext ω
      rw [pow_two, Finset.sum_mul_sum]
    · have hs : Integrable (fun ω => ∑ k ∈ F, (e k ω) ^ 2)
          (Measure.infinitePi (fun _ : ℕ => obsLaw P)) :=
        integrable_finset_sum F fun k _ => hesq k
      exact hs.const_mul _
    · exact hpoint
  change (∫ ω, (∑ k ∈ F, e k ω) ^ 2
    ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ≤ _
  refine hmono.trans ?_
  rw [integral_const_mul,
    integral_finset_sum F (fun k _ => hesq k)]
  have hterm (k : Fin d) (hk : k ∈ F) :
      ∫ ω : ℕ → Obs d, e k ω ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤ R := by
    have hkfalse : bandwidth n / 4 < cellMass P k := by
      simpa [F, falseLightSet] using hk
    have h := falseLight_selected_error_sq P hOverlap k hcut hkfalse
    calc
      (∫ ω : ℕ → Obs d, e k ω ^ 2
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) =
          ∫ ω : ℕ → Obs d,
            lightIndicator (fun i : Fin n => ω i) k *
              (factorialPolynomialContribution (fun i : Fin n => ω i) k -
                cellPhi (cellVector P k)) ^ 2
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
        apply integral_congr_ae
        filter_upwards with ω
        dsimp only [e]
        unfold lightIndicator
        split_ifs <;> ring
      _ ≤ R := by simpa only [R] using h
  calc
    (F.card : ℝ) * ∑ k ∈ F, (∫ ω, e k ω ^ 2 ∂_) ≤
        (F.card : ℝ) * ∑ _k ∈ F, R := by
      gcongr with k hk
      exact hterm k hk
    _ = (F.card : ℝ) ^ 2 * R := by
      simp [pow_two]
      ring
    _ ≤ (d : ℝ) ^ 2 * R := by
      gcongr

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
