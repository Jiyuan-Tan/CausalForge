import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Estimator
import Causalean.Stat.Minimax.MinimaxRisk
import Causalean.Stat.Minimax.Pinsker
import Causalean.Stat.Minimax.TotalVariation
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Parametric
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LowerBound
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Complex.ExponentialBounds

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory

/-- The bounded one-observation score averaged by `centeredEstimator`. -/
-- @node: centeredUnitScore
noncomputable def centeredUnitScore {d : ℕ} (z : Obs d) : ℝ :=
  2 * (if z.2.1 then 1 else -1) * ((if z.2.2 then 1 else 0) - 1 / 2)

-- @node: centeredUnitScore_sq
lemma centeredUnitScore_sq {d : ℕ} (z : Obs d) : centeredUnitScore z ^ 2 = 1 := by
  rcases z with ⟨k, a, y⟩
  cases a <;> cases y <;> norm_num [centeredUnitScore]
  all_goals exact Or.inl rfl

-- @node: centeredEstimator_eq_scoreMean
lemma centeredEstimator_eq_scoreMean {n d : ℕ} (sample : Fin n → Obs d) :
    centeredEstimator sample = (n : ℝ)⁻¹ * ∑ i : Fin n, centeredUnitScore (sample i) := by
  rfl

-- @node: centeredUnitScore_mean
/-- Establishes the stated property of centered Unit Score mean in the discrete average-treatment-effect construction. -/
lemma centeredUnitScore_mean {d : ℕ} (P : DiscreteLaw d) :
    ∫ z, centeredUnitScore z ∂obsLaw P =
      ∑ k : Fin d,
        (jointMass P k true true - jointMass P k true false +
          jointMass P k false false - jointMass P k false true) := by
  classical
  rw [show obsLaw P = P.pmf.toMeasure by rfl, PMF.integral_eq_sum]
  simp [Fintype.sum_prod_type, centeredUnitScore, jointMass]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Exact conditional-bias identity on a positive-mass category. -/
-- @node: centeredScore_category_identity
lemma centeredScore_category_identity {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P) (hepsilon : 0 < epsilon)
    (k : Fin d) (hk : 0 < cellMass P k) :
    jointMass P k true true - jointMass P k true false +
          jointMass P k false false - jointMass P k false true =
      cellMass P k * (outcomeMean P true k - outcomeMean P false k) +
        2 * (propensity P k - 1 / 2) * cellMass P k *
          (outcomeMean P true k + outcomeMean P false k - 1) := by
  have hpi := hOverlap k hk
  have hmass_ne : cellMass P k ≠ 0 := ne_of_gt hk
  have harm_one : armMass P k true = propensity P k * cellMass P k := by
    rw [propensity]
    field_simp
  have hmass : cellMass P k = armMass P k false + armMass P k true := by
    simp [cellMass, armMass]
    ring
  have hprop_pos : 0 < propensity P k := lt_of_lt_of_le hepsilon hpi.1
  have hprop_lt : propensity P k < 1 := by linarith
  have harm_one_pos : 0 < armMass P k true := by rw [harm_one]; exact mul_pos hprop_pos hk
  have harm_zero : armMass P k false = (1 - propensity P k) * cellMass P k := by
    rw [harm_one] at hmass
    linarith
  have harm_zero_pos : 0 < armMass P k false := by
    rw [harm_zero]
    exact mul_pos (sub_pos.mpr hprop_lt) hk
  have hy_one :
      jointMass P k true true = outcomeMean P true k * armMass P k true := by
    rw [outcomeMean]
    field_simp
  have hy_zero :
      jointMass P k false true = outcomeMean P false k * armMass P k false := by
    rw [outcomeMean]
    field_simp
  have harm_one_sum : armMass P k true =
      jointMass P k true false + jointMass P k true true := by
    simp [armMass]
    ring
  have harm_zero_sum : armMass P k false =
      jointMass P k false false + jointMass P k false true := by
    simp [armMass]
    ring
  rw [harm_one] at harm_one_sum hy_one
  rw [harm_zero] at harm_zero_sum hy_zero
  nlinarith

-- @node: jointMass_eq_zero_of_cellMass_eq_zero
/-- Establishes the stated equality relating joint Mass eq zero of cell Mass eq zero. -/
lemma jointMass_eq_zero_of_cellMass_eq_zero {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (hk : cellMass P k = 0) (a y : Bool) : jointMass P k a y = 0 := by
  have h00 := (jointMass_mem_unitInterval P k false false).1
  have h01 := (jointMass_mem_unitInterval P k false true).1
  have h10 := (jointMass_mem_unitInterval P k true false).1
  have h11 := (jointMass_mem_unitInterval P k true true).1
  simp [cellMass] at hk
  cases a <;> cases y <;> nlinarith

-- @node: cellMass_sum
/-- Establishes the stated summation identity or bound for cell Mass sum. -/
lemma cellMass_sum {d : ℕ} (P : DiscreteLaw d) : ∑ k : Fin d, cellMass P k = 1 := by
  classical
  have htotal : ∑ z : Obs d, (P.pmf z).toReal = 1 := by
    simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm
  calc
    ∑ k : Fin d, cellMass P k = ∑ z : Obs d, (P.pmf z).toReal := by
      simp [cellMass, jointMass, Fintype.sum_prod_type]
    _ = 1 := htotal

-- @node: centeredUnitScore_bias_identity
/-- Establishes the stated property of centered Unit Score bias identity in the discrete average-treatment-effect construction. -/
lemma centeredUnitScore_bias_identity {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P) (hepsilon : 0 < epsilon) :
    (∫ z, centeredUnitScore z ∂obsLaw P) - ateFunctional P =
      ∑ k : Fin d, 2 * (propensity P k - 1 / 2) * cellMass P k *
        (outcomeMean P true k + outcomeMean P false k - 1) := by
  rw [centeredUnitScore_mean P, ateFunctional_eq_weighted_regression P hOverlap,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hpk : 0 < cellMass P k
  · rw [centeredScore_category_identity P hOverlap hepsilon k hpk]
    ring
  · have hpk0 : cellMass P k = 0 := by
      have := (cellMass_mem_unitInterval P k).1
      linarith
    have h00 := jointMass_eq_zero_of_cellMass_eq_zero P k hpk0 false false
    have h01 := jointMass_eq_zero_of_cellMass_eq_zero P k hpk0 false true
    have h10 := jointMass_eq_zero_of_cellMass_eq_zero P k hpk0 true false
    have h11 := jointMass_eq_zero_of_cellMass_eq_zero P k hpk0 true true
    simp [hpk0, h00, h01, h10, h11]

-- @node: centeredUnitScore_bias_bound
/-- Establishes the stated upper bound for centered Unit Score bias bound. -/
lemma centeredUnitScore_bias_bound {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P)
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon ≤ 1 / 2) :
    |(∫ z, centeredUnitScore z ∂obsLaw P) - ateFunctional P| ≤
      2 * (1 / 2 - epsilon) := by
  rw [centeredUnitScore_bias_identity P hOverlap hepsilon]
  calc
    |∑ k : Fin d, 2 * (propensity P k - 1 / 2) * cellMass P k *
        (outcomeMean P true k + outcomeMean P false k - 1)| ≤
        ∑ k : Fin d, |2 * (propensity P k - 1 / 2) * cellMass P k *
          (outcomeMean P true k + outcomeMean P false k - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin d, 2 * (1 / 2 - epsilon) * cellMass P k := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hpk : 0 < cellMass P k
      · have hpi := hOverlap k hpk
        have hpabs : |propensity P k - 1 / 2| ≤ 1 / 2 - epsilon := by
          rw [abs_le]
          constructor <;> linarith
        have hm1 := outcomeMean_mem_unitInterval P true k
        have hm0 := outcomeMean_mem_unitInterval P false k
        rcases hm1 with ⟨hm1lo, hm1hi⟩
        rcases hm0 with ⟨hm0lo, hm0hi⟩
        have hmabs : |outcomeMean P true k + outcomeMean P false k - 1| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (le_of_lt hpk)]
        calc
          2 * |propensity P k - 1 / 2| * cellMass P k *
              |outcomeMean P true k + outcomeMean P false k - 1| ≤
              2 * (1 / 2 - epsilon) * cellMass P k *
                |outcomeMean P true k + outcomeMean P false k - 1| := by
            gcongr
          _ ≤ 2 * (1 / 2 - epsilon) * cellMass P k * 1 := by
            apply mul_le_mul_of_nonneg_left hmabs
            exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hepsilon_half))
              (le_of_lt hpk)
          _ = 2 * (1 / 2 - epsilon) * cellMass P k := by ring
      · have hpk0 : cellMass P k = 0 := by
          have := (cellMass_mem_unitInterval P k).1
          linarith
        simp [hpk0]
    _ = 2 * (1 / 2 - epsilon) := by
      rw [← Finset.mul_sum, cellMass_sum P]
      ring

-- @node: centeredEstimator_mean
/-- Establishes the stated property of centered Estimator mean in the discrete average-treatment-effect construction. -/
lemma centeredEstimator_mean {n d : ℕ} (P : DiscreteLaw d) (hn : 0 < n) :
    ∫ sample, centeredEstimator sample ∂productLaw P n =
      ∫ z, centeredUnitScore z ∂obsLaw P := by
  rw [show productLaw P n = Measure.pi (fun _ : Fin n => obsLaw P) by rfl]
  simp_rw [centeredEstimator_eq_scoreMean]
  rw [integral_const_mul, integral_finset_sum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin n => obsLaw P)
        (Measurable.aestronglyMeasurable (measurable_of_finite _))]
    simp [Finset.sum_const, hn.ne']
  · intro i hi
    exact MemLp.of_discrete.integrable one_le_two

-- @node: centeredUnitScore_variance_le_one
/-- Establishes the stated upper bound for centered Unit Score variance le one. -/
lemma centeredUnitScore_variance_le_one {d : ℕ} (P : DiscreteLaw d) :
    variance (fun z => centeredUnitScore z) (obsLaw P) ≤ 1 := by
  rw [variance_eq_sub (MemLp.of_discrete : MemLp centeredUnitScore 2 (obsLaw P))]
  have hsquare : ∫ z, ((fun z => centeredUnitScore z) ^ 2) z ∂obsLaw P = 1 := by
    change ∫ z, centeredUnitScore z ^ 2 ∂obsLaw P = 1
    simp_rw [centeredUnitScore_sq]
    simp
  rw [hsquare]
  nlinarith [sq_nonneg (∫ z, centeredUnitScore z ∂obsLaw P)]

-- @node: centeredEstimator_variance_le
/-- Establishes the stated upper bound for centered Estimator variance le. -/
lemma centeredEstimator_variance_le {n d : ℕ} (P : DiscreteLaw d) (hn : 0 < n) :
    variance (fun sample => centeredEstimator sample) (productLaw P n) ≤ 1 / (n : ℝ) := by
  rw [show productLaw P n = Measure.pi (fun _ : Fin n => obsLaw P) by rfl]
  simp_rw [centeredEstimator_eq_scoreMean]
  rw [variance_const_mul]
  have hvarsum :
      variance (fun sample : Fin n → Obs d => ∑ i, centeredUnitScore (sample i))
          (Measure.pi (fun _ : Fin n => obsLaw P)) =
        ∑ _i : Fin n, variance (fun z => centeredUnitScore z) (obsLaw P) := by
    calc
      _ = variance (∑ i : Fin n, fun sample => centeredUnitScore (sample i))
          (Measure.pi (fun _ : Fin n => obsLaw P)) := by
            congr 2
            funext sample
            simp
      _ = _ := variance_sum_pi (ι := Fin n) (Ω := fun _ => Obs d)
        (μ := fun _ => obsLaw P) (fun _ =>
          (MemLp.of_discrete : MemLp centeredUnitScore 2 (obsLaw P)))
  rw [hvarsum]
  have hsum : (∑ _i : Fin n, variance (fun z => centeredUnitScore z) (obsLaw P)) ≤
      (n : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun _ _ =>
        centeredUnitScore_variance_le_one P)
      _ = n := by simp
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (n : ℝ)⁻¹ ^ 2 *
        (∑ _i : Fin n, variance (fun z => centeredUnitScore z) (obsLaw P)) ≤
        (n : ℝ)⁻¹ ^ 2 * n := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = 1 / (n : ℝ) := by field_simp

-- @node: mse_eq_variance_add_sq_bias
/-- Establishes the stated equality relating mse eq variance add sq bias. -/
lemma mse_eq_variance_add_sq_bias {n d : ℕ}
    (mu : Measure (Fin n → Obs d)) [IsProbabilityMeasure mu]
    (est : (Fin n → Obs d) → ℝ) (target : ℝ) :
    mse mu est target = variance est mu + ((∫ x, est x ∂mu) - target) ^ 2 := by
  have hest : MemLp est 2 mu := MemLp.of_discrete
  unfold mse
  have hsq : Integrable (fun x => est x ^ 2) mu := hest.integrable_sq
  have hint : Integrable est mu := hest.integrable one_le_two
  have hlinear : Integrable (fun x => 2 * target * est x) mu := hint.const_mul _
  have hpow : (∫ x, (est ^ 2) x ∂mu) = ∫ x, est x ^ 2 ∂mu := by rfl
  rw [variance_eq_sub hest]
  calc
    ∫ x, (est x - target) ^ 2 ∂mu =
        ∫ x, (est x ^ 2 - 2 * target * est x) + target ^ 2 ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = (∫ x, est x ^ 2 - 2 * target * est x ∂mu) +
        (∫ _x, target ^ 2 ∂mu) :=
      integral_add (hsq.sub hlinear) (integrable_const _)
    _ = (∫ x, est x ^ 2 ∂mu) - (∫ x, 2 * target * est x ∂mu) + target ^ 2 := by
      rw [integral_sub hsq hlinear, integral_const, probReal_univ, one_smul]
    _ = (∫ x, est x ^ 2 ∂mu) - 2 * target * (∫ x, est x ∂mu) + target ^ 2 := by
      rw [integral_const_mul]
    _ = (∫ x, (est ^ 2) x ∂mu) - (∫ x, est x ∂mu) ^ 2 +
        ((∫ x, est x ∂mu) - target) ^ 2 := by
      rw [hpow]
      ring

-- @node: lem:near-randomization-linear-upper
/-- All-`n,d` MSE bound for the centered estimator. -/
lemma near_randomization_linear_upper {n d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (mu_n : Measure (Fin n → Obs d))
    (hClass : ExperimentClass n epsilon P mu_n) (hn : 0 < n) :
    mse mu_n centeredEstimator (ateFunctional P) ≤
      1 / (n : ℝ) + 4 * (1 / 2 - epsilon) ^ 2 := by
  rw [hClass.product_law]
  rw [mse_eq_variance_add_sq_bias]
  have hb := centeredUnitScore_bias_bound P hClass.overlap
    hClass.epsilon_pos hClass.epsilon_le_half
  rw [← centeredEstimator_mean P hn] at hb
  have hbnonneg : 0 ≤ 2 * (1 / 2 - epsilon) := by linarith [hClass.epsilon_le_half]
  have hb' :
      ((∫ sample, centeredEstimator sample ∂productLaw P n) - ateFunctional P) ^ 2 ≤
        (2 * (1 / 2 - epsilon)) ^ 2 := by
    rw [abs_le] at hb
    nlinarith [sq_nonneg
      ((2 * (1 / 2 - epsilon)) -
        ((∫ sample, centeredEstimator sample ∂productLaw P n) - ateFunctional P)),
      sq_nonneg
      ((2 * (1 / 2 - epsilon)) +
        ((∫ sample, centeredEstimator sample ∂productLaw P n) - ateFunctional P))]
  calc
    variance (fun sample => centeredEstimator sample) (productLaw P n) +
        ((∫ sample, centeredEstimator sample ∂productLaw P n) - ateFunctional P) ^ 2 ≤
      1 / (n : ℝ) + (2 * (1 / 2 - epsilon)) ^ 2 :=
        add_le_add (centeredEstimator_variance_le P hn) hb'
    _ = 1 / (n : ℝ) + 4 * (1 / 2 - epsilon) ^ 2 := by ring

-- @node: endpointParametricLaw
/-- Defines endpoint Parametric Law, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def endpointParametricLaw {d : ℕ} [Nonempty (Fin d)]
    {m g : ℝ} (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) m)
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g)) : DiscreteLaw d :=
  ⟨Causalean.Estimation.MinimaxATE.obsPMF hv⟩

-- @node: endpointParametricPertLaw
/-- Defines endpoint Parametric Pert Law, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def endpointParametricPertLaw {d : ℕ} [Nonempty (Fin d)]
    {m g delta : ℝ} (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) m)
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta)) : DiscreteLaw d :=
  ⟨Causalean.Estimation.MinimaxATE.obsPMF hv⟩

-- @node: endpointParametricLaw_jointMass
/-- Establishes the stated property of endpoint Parametric Law joint Mass in the discrete average-treatment-effect construction. -/
lemma endpointParametricLaw_jointMass {d : ℕ} [Nonempty (Fin d)]
    {m g : ℝ} (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) m)
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g))
    (k : Fin d) (a y : Bool) :
    jointMass (endpointParametricLaw hv) k a y =
      Causalean.Estimation.MinimaxATE.obsReal
        (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) m)
        (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g) (k, a, y) := by
  simp [jointMass, endpointParametricLaw,
    Causalean.Estimation.MinimaxATE.obsPMF,
    ENNReal.toReal_ofReal
      (Causalean.Estimation.MinimaxATE.obsReal_nonneg hv (k, a, y))]

-- @node: endpointParametricPertLaw_jointMass
/-- Establishes the stated property of endpoint Parametric Pert Law joint Mass in the discrete average-treatment-effect construction. -/
lemma endpointParametricPertLaw_jointMass {d : ℕ} [Nonempty (Fin d)]
    {m g delta : ℝ} (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) m)
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta))
    (k : Fin d) (a y : Bool) :
    jointMass (endpointParametricPertLaw hv) k a y =
      Causalean.Estimation.MinimaxATE.obsReal
        (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) m)
        (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta) (k, a, y) := by
  simp [jointMass, endpointParametricPertLaw,
    Causalean.Estimation.MinimaxATE.obsPMF,
    ENNReal.toReal_ofReal
      (Causalean.Estimation.MinimaxATE.obsReal_nonneg hv (k, a, y))]

-- @node: endpointParametricLaw_overlap
/-- Establishes the stated property of endpoint Parametric Law overlap in the discrete average-treatment-effect construction. -/
lemma endpointParametricLaw_overlap {d : ℕ} [Nonempty (Fin d)]
    {g : ℝ} (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g)) :
    Overlap (1 / 2) (endpointParametricLaw (d := d) hv) := by
  intro k hk
  have hcard : (Fintype.card (Fin d) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdcast : (d : ℝ) ≠ 0 := by simpa using hcard
  have hmass : cellMass (endpointParametricLaw hv) k =
      (Fintype.card (Fin d) : ℝ)⁻¹ := by
    simp [cellMass, endpointParametricLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gNull]
    ring
  have harm : armMass (endpointParametricLaw hv) k true =
      (1 / 2) * (Fintype.card (Fin d) : ℝ)⁻¹ := by
    simp [armMass, endpointParametricLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gNull]
    ring
  rw [propensity, hmass, harm]
  field_simp
  norm_num

-- @node: endpointParametricPertLaw_overlap
/-- Establishes the stated property of endpoint Parametric Pert Law overlap in the discrete average-treatment-effect construction. -/
lemma endpointParametricPertLaw_overlap {d : ℕ} [Nonempty (Fin d)]
    {g delta : ℝ} (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta)) :
    Overlap (1 / 2) (endpointParametricPertLaw (d := d) hv) := by
  intro k hk
  have hcard : (Fintype.card (Fin d) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hmass : cellMass (endpointParametricPertLaw hv) k =
      (Fintype.card (Fin d) : ℝ)⁻¹ := by
    simp [cellMass, endpointParametricPertLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gPert]
    ring
  have harm : armMass (endpointParametricPertLaw hv) k true =
      (1 / 2) * (Fintype.card (Fin d) : ℝ)⁻¹ := by
    simp [armMass, endpointParametricPertLaw_jointMass,
      Causalean.Estimation.MinimaxATE.obsReal,
      Causalean.Estimation.MinimaxATE.Parametric.mC,
      Causalean.Estimation.MinimaxATE.Parametric.gPert]
    ring
  rw [propensity, hmass, harm]
  field_simp
  norm_num

-- @node: endpointParametricLaw_ate
/-- Establishes the stated property of endpoint Parametric Law ate in the discrete average-treatment-effect construction. -/
lemma endpointParametricLaw_ate {d : ℕ} [Nonempty (Fin d)]
    {g : ℝ} (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin d) g g)) :
    ateFunctional (endpointParametricLaw (d := d) hv) = 0 := by
  rw [ateFunctional_eq_weighted_regression _ (endpointParametricLaw_overlap hv)]
  apply Finset.sum_eq_zero
  intro k hk
  have hcard : (Fintype.card (Fin d) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdcast : (d : ℝ) ≠ 0 := by simpa using hcard
  have hmean (a : Bool) : outcomeMean (endpointParametricLaw hv) a k = g := by
    cases a <;>
      simp [outcomeMean, armMass, endpointParametricLaw_jointMass,
        Causalean.Estimation.MinimaxATE.obsReal,
        Causalean.Estimation.MinimaxATE.Parametric.mC,
        Causalean.Estimation.MinimaxATE.Parametric.gNull] <;>
      field_simp [hcard, hdcast] <;> ring
  rw [hmean true, hmean false, sub_self, mul_zero]

-- @node: endpointParametricPertLaw_ate
/-- Establishes the stated property of endpoint Parametric Pert Law ate in the discrete average-treatment-effect construction. -/
lemma endpointParametricPertLaw_ate {d : ℕ} [Nonempty (Fin d)]
    {g delta : ℝ} (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin d) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin d) g g delta)) :
    ateFunctional (endpointParametricPertLaw (d := d) hv) = delta := by
  rw [ateFunctional_eq_weighted_regression _ (endpointParametricPertLaw_overlap hv)]
  have hcard : (Fintype.card (Fin d) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdcast : (d : ℝ) ≠ 0 := by simpa using hcard
  have hmean (a : Bool) (k : Fin d) :
      outcomeMean (endpointParametricPertLaw hv) a k = if a then g + delta else g := by
    cases a <;>
      simp [outcomeMean, armMass, endpointParametricPertLaw_jointMass,
        Causalean.Estimation.MinimaxATE.obsReal,
        Causalean.Estimation.MinimaxATE.Parametric.mC,
        Causalean.Estimation.MinimaxATE.Parametric.gPert] <;>
      field_simp [hcard, hdcast] <;> ring
  simp_rw [hmean true, hmean false]
  have hsum := cellMass_sum (endpointParametricPertLaw (d := d) hv)
  calc
    ∑ x, cellMass (endpointParametricPertLaw hv) x *
        ((if true then g + delta else g) - if false then g + delta else g) =
        ∑ x, cellMass (endpointParametricPertLaw hv) x * delta := by
          apply Finset.sum_congr rfl
          intro k hk
          simp
    _ = (∑ x, cellMass (endpointParametricPertLaw hv) x) * delta :=
      by rw [Finset.sum_mul]
    _ = delta := by rw [hsum]; ring

-- @node: lem:one-category-bernoulli-lower
/-- Explicit one-category Bernoulli two-point lower bound at randomization. -/
lemma one_category_bernoulli_lower (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    -- @realizes d(positive alphabet size for the one-category witness)
    1 / (100 * (n : ℝ)) ≤ minimaxRisk n d (1 / 2) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let delta : ℝ := (2 / 5) / Real.sqrt n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hdelta0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hdeltasq : delta ^ 2 = 4 / (25 * (n : ℝ)) := by
    dsimp [delta]
    rw [div_pow, Real.sq_sqrt (le_of_lt hnR)]
    ring
  let hv0 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_null
    (C := Fin d) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdeltaU : (1 / 2 : ℝ) + delta ≤ 1 := by
    have hsqrt_one : 1 ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    have hdelta : delta ≤ 2 / 5 := by
      dsimp [delta]
      exact div_le_self (by norm_num) hsqrt_one
    linarith
  let hv1 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_pert
    (C := Fin d) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (δ := delta) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hdelta0 hdeltaU
  let P0 : DiscreteLaw d := endpointParametricLaw hv0
  let P1 : DiscreteLaw d := endpointParametricPertLaw hv1
  have hclass0 : ExperimentClass n (1 / 2) P0 (productLaw P0 n) := by
    refine ⟨by norm_num, by norm_num, rfl, ?_⟩
    exact endpointParametricLaw_overlap hv0
  have hclass1 : ExperimentClass n (1 / 2) P1 (productLaw P1 n) := by
    refine ⟨by norm_num, by norm_num, rfl, ?_⟩
    exact endpointParametricPertLaw_overlap hv1
  have htau0 : ateFunctional P0 = 0 := endpointParametricLaw_ate hv0
  have htau1 : ateFunctional P1 = delta := endpointParametricPertLaw_ate hv1
  have hreg : (n : ℝ) *
      ((1 / 2 : ℝ) * delta ^ 2 / ((1 / 2 : ℝ) * (1 - 1 / 2))) ≤ Real.log 2 := by
    rw [hdeltasq]
    have hlog : (8 / 25 : ℝ) ≤ Real.log 2 :=
      le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
    convert hlog using 1 <;> field_simp <;> ring
  have htv : Causalean.Stat.tvDist (productLaw P0 n) (productLaw P1 n) ≤ 1 / 2 := by
    simpa [P0, P1, endpointParametricLaw, endpointParametricPertLaw,
      productLaw, obsLaw, Causalean.Estimation.MinimaxATE.productLaw,
      Causalean.Estimation.MinimaxATE.obsLaw] using
      (Causalean.Estimation.MinimaxATE.Parametric.tvDist_productLaw_le_half
        hv0 hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hreg)
  unfold minimaxRisk
  let est0 : {f : (Fin n → Obs d) → ℝ // Measurable f} :=
    ⟨fun _ => 0, measurable_const⟩
  letI : Nonempty {f : (Fin n → Obs d) → ℝ // Measurable f} := ⟨est0⟩
  apply le_ciInf
  intro est
  have hprob := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := productLaw P0 n) (P₁ := productLaw P1 n) est.2
    (θ₀ := ateFunctional P0) (θ₁ := ateFunctional P1)
    (s := delta / 2) (c := (1 / 2 : ℝ))
    (by rw [htau0, htau1, zero_sub, abs_neg, abs_of_nonneg hdelta0]; linarith) htv
  have hmse0 : (delta / 2) ^ 2 *
      (productLaw P0 n).real {x | delta / 2 ≤ |est.1 x - ateFunctional P0|} ≤
      mse (productLaw P0 n) est.1 (ateFunctional P0) := by
    unfold mse
    have hset : {x | delta / 2 ≤ |est.1 x - ateFunctional P0|} =
        {x | (delta / 2) ^ 2 ≤ (est.1 x - ateFunctional P0) ^ 2} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;>
        nlinarith [hdelta0, abs_nonneg (est.1 x - ateFunctional P0),
          sq_abs (est.1 x - ateFunctional P0)]
    rw [hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (μ := productLaw P0 n)
      (Filter.Eventually.of_forall fun x => sq_nonneg (est.1 x - ateFunctional P0))
      MemLp.of_discrete.integrable_sq ((delta / 2) ^ 2)
  have hmse1 : (delta / 2) ^ 2 *
      (productLaw P1 n).real {x | delta / 2 ≤ |est.1 x - ateFunctional P1|} ≤
      mse (productLaw P1 n) est.1 (ateFunctional P1) := by
    unfold mse
    have hset : {x | delta / 2 ≤ |est.1 x - ateFunctional P1|} =
        {x | (delta / 2) ^ 2 ≤ (est.1 x - ateFunctional P1) ^ 2} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;>
        nlinarith [hdelta0, abs_nonneg (est.1 x - ateFunctional P1),
          sq_abs (est.1 x - ateFunctional P1)]
    rw [hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (μ := productLaw P1 n)
      (Filter.Eventually.of_forall fun x => sq_nonneg (est.1 x - ateFunctional P1))
      MemLp.of_discrete.integrable_sq ((delta / 2) ^ 2)
  have htwo : delta ^ 2 / 16 ≤ max
      (mse (productLaw P0 n) est.1 (ateFunctional P0))
      (mse (productLaw P1 n) est.1 (ateFunctional P1)) := by
    have hscale : 0 ≤ (delta / 2) ^ 2 := sq_nonneg _
    have hp := mul_le_mul_of_nonneg_left hprob hscale
    norm_num at hp
    rw [mul_max_of_nonneg _ _ hscale] at hp
    calc
      delta ^ 2 / 16 = (delta / 2) ^ 2 * (1 / 4) := by ring
      _ ≤ max
          ((delta / 2) ^ 2 *
            (productLaw P0 n).real {x | delta / 2 ≤ |est.1 x - ateFunctional P0|})
          ((delta / 2) ^ 2 *
            (productLaw P1 n).real {x | delta / 2 ≤ |est.1 x - ateFunctional P1|}) := hp
      _ ≤ _ := max_le_max hmse0 hmse1
  have hb : BddAbove (Set.range (fun P : ClassLaw n d (1 / 2) =>
      mse (productLaw P.1 n) est.1 (ateFunctional P.1))) := by
    refine ⟨((∑ sample : Fin n → Obs d, |est.1 sample|) + 1) ^ 2, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact mse_le_estimator_abs_sum_bound P.1 P.2.overlap est.1
  have hmax_le : max
      (mse (productLaw P0 n) est.1 (ateFunctional P0))
      (mse (productLaw P1 n) est.1 (ateFunctional P1)) ≤
      worstCaseMSE n d (1 / 2) est.1 := by
    apply max_le
    · exact le_ciSup hb (⟨P0, hclass0⟩ : ClassLaw n d (1 / 2))
    · exact le_ciSup hb (⟨P1, hclass1⟩ : ClassLaw n d (1 / 2))
  rw [hdeltasq] at htwo
  exact (by convert htwo.trans hmax_le using 1 <;> field_simp <;> ring)

-- @node: lem:randomized-endpoint-minimax
/-- At exact randomization the minimax risk is parametric uniformly in `d`. -/
lemma randomized_endpoint_minimax (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    -- @realizes d(positive alphabet size inherited by the endpoint bracket)
    1 / (100 * (n : ℝ)) ≤ minimaxRisk n d (1 / 2) ∧
      minimaxRisk n d (1 / 2) ≤ 1 / (n : ℝ) := by
  constructor
  · exact one_category_bernoulli_lower n d hn hd
  · have hmeas : Measurable (@centeredEstimator n d) := measurable_of_finite _
    have hb : BddBelow (Set.range (fun est :
        {f : (Fin n → Obs d) → ℝ // Measurable f} =>
          worstCaseMSE n d (1 / 2) est.1)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨est, rfl⟩
      unfold worstCaseMSE
      cases isEmpty_or_nonempty (ClassLaw n d (1 / 2)) with
      | inl hempty =>
          letI := hempty
          simp
      | inr hnonempty =>
          letI := hnonempty
          by_cases hbounded : BddAbove (Set.range (fun P : ClassLaw n d (1 / 2) =>
              mse (productLaw P.1 n) est.1 (ateFunctional P.1)))
          · have hmse : 0 ≤ mse
                (productLaw (Classical.arbitrary (ClassLaw n d (1 / 2))).1 n)
                est.1
                (ateFunctional (Classical.arbitrary (ClassLaw n d (1 / 2))).1) := by
              unfold mse
              exact integral_nonneg (fun x => sq_nonneg (est.1 x -
                ateFunctional (Classical.arbitrary (ClassLaw n d (1 / 2))).1))
            exact hmse.trans (le_ciSup hbounded (Classical.arbitrary _))
          · change 0 ≤ (⨆ P : ClassLaw n d (1 / 2),
                mse (productLaw P.1 n) est.1 (ateFunctional P.1))
            rw [show (⨆ P : ClassLaw n d (1 / 2),
                mse (productLaw P.1 n) est.1 (ateFunctional P.1)) = sSup ∅ from
                csSup_of_not_bddAbove hbounded]
            simp
    calc
      minimaxRisk n d (1 / 2) ≤
          worstCaseMSE n d (1 / 2) centeredEstimator :=
        ciInf_le hb
          (⟨centeredEstimator, hmeas⟩ :
            {f : (Fin n → Obs d) → ℝ // Measurable f})
      _ ≤ 1 / (n : ℝ) := by
        unfold worstCaseMSE
        cases isEmpty_or_nonempty (ClassLaw n d (1 / 2)) with
        | inl hempty =>
            letI := hempty
            simp
        | inr hnonempty =>
            letI := hnonempty
            apply ciSup_le
            intro P
            simpa using near_randomization_linear_upper P.1 (productLaw P.1 n) P.2 hn

end CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- The endpoint law is unchanged when the category space, nuisance parameters, and valid
data-generating-process witness are replaced by equal values. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw.congr_simp

/-- The perturbed endpoint law is unchanged when the category space, parameters, perturbation,
and valid data-generating-process witness are replaced by equal values. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw.congr_simp

/-- The observational probability mass function is unchanged when the underlying model and its
valid data-generating-process witness are replaced by equal values. -/
add_decl_doc Causalean.Estimation.MinimaxATE.obsPMF.congr_simp
