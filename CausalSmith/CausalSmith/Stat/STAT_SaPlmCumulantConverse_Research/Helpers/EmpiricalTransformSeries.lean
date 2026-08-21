import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.EmpiricalTransform
import Causalean.Stat.Orthogonality.ConditionalOp

/-!
# Factorial-series assembly for empirical transforms

This module converts real exponential-envelope bounds into uniform disk L²
bounds for centered empirical analytic transforms and proves the exact
coefficient-series identity used to connect those bounds to the paper's
empirical transforms.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.SaPlmCumulantConverse

/-- Take a [nonempty block of sample indices](hyp:hI), a [measurable
weight](hyp:hW) and a [measurable exponent variable](hyp:hV), and fix a [disk of
positive radius](hyp:hR). If the [envelope given by the absolute weight times the
exponential of twice the radius times the absolute exponent variable has second
moment no larger than the square of a](hyp:henv) [nonnegative
constant](hyp:hC), then, for the power series whose `k`-th coefficient is the
block average of the centered factorial statistic — weight times exponent
variable to the power `k` over `k` factorial, minus its population mean — the
[expected squared supremum of that series over the disk is at most four times the
squared constant divided by the block size](goal).

The block average is over an independent sample of size `n` drawn from the same
law, so the bound is the usual one-over-block-size variance gain applied
uniformly on the disk. -/
theorem centered_factorial_empirical_disk_l2
    {X : Type*} [MeasurableSpace X] {P : Measure X} [IsProbabilityMeasure P]
    {n : ℕ} (I : Finset (Fin n)) (hI : I.Nonempty)
    (W V : X → ℝ) (hW : Measurable W) (hV : Measurable V)
    (R : ℝ) (hR : 0 < R) (C : ℝ) (hC : 0 ≤ C)
    (henv : ∫⁻ o, ENNReal.ofReal
        ((|W o| * Real.exp (2 * R * |V o|)) ^ 2) ∂P ≤ ENNReal.ofReal (C ^ 2)) :
    let c : (Fin n → X) → ℕ → ℝ := fun data k ↦
      (I.card : ℝ)⁻¹ * ∑ i ∈ I,
        (W (data i) * V (data i) ^ k / k.factorial -
          ∫ o, W o * V o ^ k / k.factorial ∂P)
    ∫⁻ data, ENNReal.ofReal
        ((diskSupNorm (fun data z ↦ ∑' k, (c data k : ℂ) * z ^ k) R data) ^ 2)
        ∂Measure.pi (fun _ : Fin n ↦ P) ≤
      ENNReal.ofReal ((2 * C / Real.sqrt I.card) ^ 2) := by
  dsimp only
  let f : ℕ → X → ℝ := fun k o ↦ W o * V o ^ k / k.factorial
  let c : (Fin n → X) → ℕ → ℝ := fun data k ↦
    (I.card : ℝ)⁻¹ * ∑ i ∈ I, (f k (data i) - ∫ o, f k o ∂P)
  have hf (k : ℕ) : MemLp (f k) 2 P ∧
      eLpNorm (f k) 2 P ≤ ENNReal.ofReal (C / (2 * R) ^ k) := by
    simpa [f] using factorial_coefficient_memLp_two P W V hW hV R hR C hC henv k
  have hcmeas (k : ℕ) : Measurable (c · k) := by
    dsimp [c]
    fun_prop
  have hcl2 (k : ℕ) : MemLp (c · k) 2 (Measure.pi (fun _ : Fin n ↦ P)) ∧
      eLpNorm (c · k) 2 (Measure.pi (fun _ : Fin n ↦ P)) ≤
        ENNReal.ofReal ((C / (2 * R) ^ k) / Real.sqrt I.card) := by
    have hs := pi_finset_centered_average_sq_lintegral_le I hI (hf k).1
      (div_nonneg hC (pow_nonneg (mul_nonneg (by norm_num) hR.le) _)) (hf k).2
    have heq : (I.card : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((C / (2 * R) ^ k) ^ 2) =
        ENNReal.ofReal (((C / (2 * R) ^ k) / Real.sqrt I.card) ^ 2) := by
      have haux (B : ℝ) :
          (I.card : ℝ≥0∞)⁻¹ * ENNReal.ofReal (B ^ 2) =
            ENNReal.ofReal ((B / Real.sqrt I.card) ^ 2) := by
        have hmR : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
        rw [div_pow, Real.sq_sqrt hmR.le]
        rw [ENNReal.ofReal_div_of_pos hmR]
        simp only [ENNReal.ofReal_natCast]
        ac_rfl
      exact haux _
    apply memLp_two_and_eLpNorm_le_of_sq_lintegral_le _ (hcmeas k)
      (div_nonneg (div_nonneg hC (pow_nonneg (mul_nonneg (by norm_num) hR.le) _))
        (Real.sqrt_nonneg _))
    exact hs.trans_eq heq
  have hcsum : ∀ data, Summable (fun k ↦ |c data k| * R ^ k) := by
    intro data
    have hpoint (x : X) : Summable (fun k ↦ |f k x| * R ^ k) := by
      refine ((Real.summable_pow_div_factorial (|V x| * R)).mul_left |W x|).congr
        (fun k ↦ ?_)
      symm
      simp only [f, abs_div, abs_mul, abs_pow, Nat.cast_nonneg, abs_of_nonneg,
        mul_pow]
      ring
    have hfinite : Summable (fun k ↦ ∑ i ∈ I, |f k (data i)| * R ^ k) := by
      classical
      have haux : ∀ s : Finset (Fin n),
          Summable (fun k ↦ ∑ i ∈ s, |f k (data i)| * R ^ k) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            simp_rw [Finset.sum_insert hi]
            exact (hpoint (data i)).add ih
      exact haux I
    have hmean_bound (k : ℕ) : |∫ o, f k o ∂P| ≤ C / (2 * R) ^ k := by
      have hle := Causalean.Stat.abs_integral_le_eLpNorm_two (hf k).1
      exact hle.trans ((ENNReal.toReal_mono ENNReal.ofReal_ne_top (hf k).2).trans_eq
        (ENNReal.toReal_ofReal
          (div_nonneg hC (pow_nonneg (mul_nonneg (by norm_num) hR.le) _))))
    have hmean : Summable (fun k ↦ |∫ o, f k o ∂P| * R ^ k) := by
      apply Summable.of_nonneg_of_le
        (fun k ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hR.le _))
        (fun k ↦ mul_le_mul_of_nonneg_right (hmean_bound k) (pow_nonneg hR.le _))
      refine ((summable_geometric_of_norm_lt_one
        (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left C).congr (fun k ↦ ?_)
      symm
      have hR0 : R ≠ 0 := hR.ne'
      field_simp
      have ht : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by
        rw [one_div, inv_pow, inv_mul_cancel₀]
        positivity
      calc
        C * R ^ k = C * R ^ k * 1 := by ring
        _ = C * R ^ k * ((1 / 2 : ℝ) ^ k * 2 ^ k) := by rw [ht]
        _ = _ := by ring
    apply Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hR.le _)) (fun k ↦ ?_)
      ((hfinite.mul_left (I.card : ℝ)⁻¹).add hmean)
    have hcardR : (I.card : ℝ) ≠ 0 := by exact_mod_cast hI.card_pos.ne'
    have hinv : 0 ≤ (I.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    dsimp [c]
    calc
      |(I.card : ℝ)⁻¹ * ∑ i ∈ I, (f k (data i) - ∫ o, f k o ∂P)| * R ^ k =
          (I.card : ℝ)⁻¹ * |∑ i ∈ I, (f k (data i) - ∫ o, f k o ∂P)| *
            R ^ k := by rw [abs_mul, abs_of_nonneg hinv]
      _ ≤ (I.card : ℝ)⁻¹ *
          (∑ i ∈ I, |f k (data i) - ∫ o, f k o ∂P|) * R ^ k := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ (I.card : ℝ)⁻¹ *
          (∑ i ∈ I, (|f k (data i)| + |∫ o, f k o ∂P|)) * R ^ k := by
        gcongr with i hi
        exact abs_sub _ _
      _ = (I.card : ℝ)⁻¹ * (∑ i ∈ I, |f k (data i)| * R ^ k) +
          |∫ o, f k o ∂P| * R ^ k := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        field_simp
        rw [add_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hbsum : Summable (fun k ↦
      ((C / (2 * R) ^ k) / Real.sqrt I.card) * R ^ k) := by
    refine ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left
      (C / Real.sqrt I.card)).congr (fun k ↦ ?_)
    symm
    have hR0 : R ≠ 0 := hR.ne'
    field_simp
    have ht : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by
      rw [one_div, inv_pow, inv_mul_cancel₀]
      positivity
    calc
      C * R ^ k = C * R ^ k * 1 := by ring
      _ = C * R ^ k * ((1 / 2 : ℝ) ^ k * 2 ^ k) := by rw [ht]
      _ = _ := by ring
  have hmain := centered_real_series_diskSupNorm_sq_lintegral_le
    (Measure.pi (fun _ : Fin n ↦ P)) c R hR.le hcmeas hcsum
    (fun k ↦ (C / (2 * R) ^ k) / Real.sqrt I.card)
    (fun k ↦ div_nonneg (div_nonneg hC (pow_nonneg (mul_nonneg (by norm_num) hR.le) _))
      (Real.sqrt_nonneg _)) hbsum hcl2
  convert hmain using 1
  congr 2
  rw [show (fun k ↦ (C / (2 * R) ^ k / Real.sqrt ↑I.card) * R ^ k) =
      fun k ↦ (C / Real.sqrt I.card) * (1 / 2 : ℝ) ^ k by
    funext k
    have hR0 : R ≠ 0 := hR.ne'
    field_simp
    have ht : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by
      rw [one_div, inv_pow, inv_mul_cancel₀]
      positivity
    calc
      C * R ^ k = C * R ^ k * 1 := by ring
      _ = C * R ^ k * ((1 / 2 : ℝ) ^ k * 2 ^ k) := by rw [ht]
      _ = _ := by ring]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  ring

/-- Take a [nonempty block of sample indices](hyp:hI), a [measurable
weight](hyp:hW) and a [measurable exponent variable](hyp:hV), a [disk of positive
radius](hyp:hR), and assume the [envelope given by the absolute weight times the
exponential of twice the radius times the absolute exponent variable has second
moment no larger than the square of a](hyp:henv) [nonnegative constant](hyp:hC).
Then at every [argument of modulus at most the radius](hyp:hz) the [block average
of the weight times the exponential of the argument times the exponent variable,
minus the population weighted transform, equals the power series whose `k`-th
coefficient is the block average of the centered factorial statistic — weight
times exponent variable to the power `k` over `k` factorial, minus its population
mean](goal).

This is the exact coefficient-series identity behind the uniform disk bound: the
centered empirical transform is literally the sum of its centered factorial
coefficients against powers of the argument. -/
theorem weighted_empirical_sub_eq_centered_factorial_series
    {X : Type*} [MeasurableSpace X] {P : Measure X} [IsProbabilityMeasure P]
    {n : ℕ} (I : Finset (Fin n)) (hI : I.Nonempty)
    (W V : X → ℝ) (hW : Measurable W) (hV : Measurable V)
    (R : ℝ) (hR : 0 < R) (C : ℝ) (hC : 0 ≤ C)
    (henv : ∫⁻ o, ENNReal.ofReal
        ((|W o| * Real.exp (2 * R * |V o|)) ^ 2) ∂P ≤ ENNReal.ofReal (C ^ 2))
    (data : Fin n → X) (z : ℂ) (hz : ‖z‖ ≤ R) :
    (I.card : ℂ)⁻¹ * ∑ i ∈ I, (W (data i) : ℂ) * Complex.exp (z * V (data i)) -
        weightedTransform P W V z =
      ∑' k : ℕ, (((I.card : ℝ)⁻¹ * ∑ i ∈ I,
          (W (data i) * V (data i) ^ k / k.factorial -
            ∫ o, W o * V o ^ k / k.factorial ∂P) : ℝ) : ℂ) * z ^ k := by
  let f : ℕ → X → ℝ := fun k o ↦ W o * V o ^ k / k.factorial
  have hf (k : ℕ) : MemLp (f k) 2 P ∧
      eLpNorm (f k) 2 P ≤ ENNReal.ofReal (C / (2 * R) ^ k) := by
    simpa [f] using factorial_coefficient_memLp_two P W V hW hV R hR C hC henv k
  have hdom : Integrable (fun o ↦ |W o| * Real.exp (2 * ‖z‖ * |V o|)) P := by
    let E : X → ℝ := fun o ↦ |W o| * Real.exp (2 * R * |V o|)
    have hEmeas : Measurable E := hW.abs.mul
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul hV.abs))
    have hEmem := memLp_two_and_eLpNorm_le_of_sq_lintegral_le P hEmeas hC henv |>.1
    apply (hEmem.integrable (by norm_num)).mono'
      ((hW.abs.fun_mul (Real.continuous_exp.measurable.comp
        (measurable_const.fun_mul hV.abs))).aestronglyMeasurable)
    filter_upwards [] with o
    simp only [Function.comp_apply, E, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by gcongr)) (abs_nonneg _)
  have hpop := weighted_exp_integral_eq_moment_tsum P W V hW hV z hdom
  have hmean_bound (k : ℕ) : |∫ o, f k o ∂P| ≤ C / (2 * R) ^ k := by
    have hle := Causalean.Stat.abs_integral_le_eLpNorm_two (hf k).1
    exact hle.trans ((ENNReal.toReal_mono ENNReal.ofReal_ne_top (hf k).2).trans_eq
      (ENNReal.toReal_ofReal
        (div_nonneg hC (pow_nonneg (mul_nonneg (by norm_num) hR.le) _))))
  let r : ℕ → ℂ := fun k ↦ ((∫ o, f k o ∂P : ℝ) : ℂ) * z ^ k
  have hr : Summable r := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) (fun k ↦ ?_)
      ((summable_geometric_of_norm_lt_one
        (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left C)
    dsimp [r]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    calc
      |∫ o, f k o ∂P| * ‖z‖ ^ k ≤ (C / (2 * R) ^ k) * R ^ k := by
        exact mul_le_mul (hmean_bound k) (pow_le_pow_left₀ (norm_nonneg z) hz k)
          (pow_nonneg (norm_nonneg z) k)
          (div_nonneg hC (pow_nonneg (mul_nonneg (by norm_num) hR.le) k))
      _ = C * (1 / 2 : ℝ) ^ k := by
        have hR0 : R ≠ 0 := hR.ne'
        field_simp
        have ht : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by
          rw [one_div, inv_pow, inv_mul_cancel₀]
          positivity
        calc
          C * R ^ k = C * R ^ k * 1 := by ring
          _ = C * R ^ k * ((1 / 2 : ℝ) ^ k * 2 ^ k) := by rw [ht]
          _ = _ := by ring
  let q : Fin n → ℕ → ℂ := fun i k ↦ (f k (data i) : ℂ) * z ^ k
  have hq (i : Fin n) : Summable (q i) := by
    have hs := (NormedSpace.expSeries_div_summable (z * (V (data i) : ℂ))).mul_left
      (W (data i) : ℂ)
    refine hs.congr (fun k ↦ ?_)
    symm
    simp [q, f]
    push_cast
    ring
  have hqsum : ∀ s : Finset (Fin n), Summable (fun k ↦ ∑ i ∈ s, q i k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp_rw [Finset.sum_insert hi]
        exact (hq i).add ih
  have hsum_tsum : ∀ s : Finset (Fin n),
      (∑ i ∈ s, ∑' k, q i k) = ∑' k, ∑ i ∈ s, q i k := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp_rw [Finset.sum_insert hi]
        rw [ih]
        exact ((hq i).tsum_add (hqsum s)).symm
  let e : ℕ → ℂ := fun k ↦ (I.card : ℂ)⁻¹ * (∑ i ∈ I, q i k)
  have he : Summable e := (hqsum I).mul_left _
  have hemp : (I.card : ℂ)⁻¹ * ∑ i ∈ I,
      (W (data i) : ℂ) * Complex.exp (z * V (data i)) = ∑' k, e k := by
    dsimp [e]
    rw [tsum_mul_left, ← hsum_tsum I]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [q]
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div, ← tsum_mul_left]
    apply tsum_congr
    intro k
    simp [f]
    push_cast
    ring
  rw [hemp]
  rw [show weightedTransform P W V z = ∑' k, r k by
    rw [weightedTransform, hpop]
    apply tsum_congr
    intro k
    dsimp [r, f]
    rw [integral_div]
    push_cast
    ring]
  rw [← he.tsum_sub hr]
  apply tsum_congr
  intro k
  dsimp [e, q, r, f]
  rw [integral_div]
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hc : (I.card : ℂ) ≠ 0 := by exact_mod_cast hI.card_pos.ne'
  field_simp
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    ring
  · ring

/-- The explicit constant in the uniform disk bound for the empirical
transforms: four times the sum of two envelope factors. The first is twice the
exponential of eight times the search radius times the treatment-regression
bound, plus four times the squared radius times the squared treatment
sub-Gaussian scale. The second adds to a fourth-moment term — sixty-four times the sum of the
fourth power of the outcome-regression bound, four times the fourth power of the
treatment-effect bound times the fourth power of the treatment scale, and four
times the fourth power of the outcome sub-Gaussian scale — twice the exponential
of sixteen times the radius times the
treatment-regression bound plus sixteen times the squared radius times the
squared treatment scale. -/
def empiricalTransformL2Constant
    (Ctheta Cg Cq psieta psixi R1 : ℝ) : ℝ :=
  let AF := 2 * Real.exp (8 * R1 * Cg + 4 * R1 ^ 2 * psieta ^ 2)
  let AG := 64 * (Cq ^ 4 + 4 * Ctheta ^ 4 * psieta ^ 4 + 4 * psixi ^ 4) +
    2 * Real.exp (16 * R1 * Cg + 16 * R1 ^ 2 * psieta ^ 2)
  4 * ((Real.sqrt AF) ^ 2 + (Real.sqrt AG) ^ 2)

/-- The explicit constant in the uniform disk bound for the empirical transforms
[is strictly positive for any values of the model constants and the search
radius](goal). -/
lemma empiricalTransformL2Constant_pos
    (Ctheta Cg Cq psieta psixi R1 : ℝ) :
    0 < empiricalTransformL2Constant Ctheta Cg Cq psieta psixi R1 := by
  dsimp [empiricalTransformL2Constant]
  positivity

/-- Explicit-constant form of the uniform split-fold transform bound. -/
lemma empirical_transform_uniform_l2_explicit
    {Xspace : Type*} [MeasurableSpace Xspace]
    (Ctheta Cg Cq psieta psixi R1 : ℝ) :
      ∀ (p : Parameters), p.Ctheta = Ctheta → p.Cg = Cg → p.Cq = Cq →
        p.psieta = psieta → p.psixi = psixi → searchRadius p = R1 → 2 ≤ p.n →
      ∀ (m : Model (Xspace := Xspace) p), NonGaussianClass p p.n m →
      IidSampling p.n m.P (iidLaw m p.n) →
      ∀ a : Fin 2, (inferenceFold p.n a).Nonempty →
        (∫⁻ data, ENNReal.ofReal
          ((transformSupError
            (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n a) z)
            (residualMGF p m p.n) R1 data) ^ 2) ∂iidLaw m p.n) +
        (∫⁻ data, ENNReal.ofReal
          ((transformSupError
            (fun data z ↦ empiricalG p m p.n data (inferenceFold p.n a) z)
            (outcomeResidualTransform p m p.n) R1 data) ^ 2) ∂iidLaw m p.n) ≤
          ENNReal.ofReal (empiricalTransformL2Constant Ctheta Cg Cq psieta psixi R1 /
            (inferenceFold p.n a).card) := by
  let AF := 2 * Real.exp (8 * R1 * Cg + 4 * R1 ^ 2 * psieta ^ 2)
  let AG := 64 * (Cq ^ 4 + 4 * Ctheta ^ 4 * psieta ^ 4 + 4 * psixi ^ 4) +
    2 * Real.exp (16 * R1 * Cg + 16 * R1 ^ 2 * psieta ^ 2)
  let CF := Real.sqrt AF
  let CG := Real.sqrt AG
  let K := 4 * (CF ^ 2 + CG ^ 2)
  have hAF : 0 < AF := by dsimp [AF]; positivity
  have hAG : 0 < AG := by dsimp [AG]; positivity
  have hCF : 0 < CF := Real.sqrt_pos.2 hAF
  have hCG : 0 < CG := Real.sqrt_pos.2 hAG
  change ∀ (p : Parameters), p.Ctheta = Ctheta → p.Cg = Cg → p.Cq = Cq →
      p.psieta = psieta → p.psixi = psixi → searchRadius p = R1 → 2 ≤ p.n →
    ∀ (m : Model (Xspace := Xspace) p), NonGaussianClass p p.n m →
    IidSampling p.n m.P (iidLaw m p.n) →
    ∀ a : Fin 2, (inferenceFold p.n a).Nonempty →
      (∫⁻ data, ENNReal.ofReal
        ((transformSupError
          (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n a) z)
          (residualMGF p m p.n) R1 data) ^ 2) ∂iidLaw m p.n) +
      (∫⁻ data, ENNReal.ofReal
        ((transformSupError
          (fun data z ↦ empiricalG p m p.n data (inferenceFold p.n a) z)
          (outcomeResidualTransform p m p.n) R1 data) ^ 2) ∂iidLaw m p.n) ≤
        ENNReal.ofReal (K / (inferenceFold p.n a).card)
  intro p hpθ hpg hpq hpη hpξ hpR hn m hclass _hiid a hI
  subst Ctheta
  subst Cg
  subst Cq
  subst psieta
  subst psixi
  subst R1
  let I := inferenceFold p.n a
  have hR : 0 < searchRadius p := by
    have hR0 : 0 ≤ zeroRadius p := by
      unfold zeroRadius Ak
      apply mul_nonneg
      · exact Real.rpow_nonneg (by positivity) _
      · exact Real.rpow_nonneg
          (div_nonneg (sq_nonneg _) p.constants_pos.2.2.2.2.2.1.le) _
    unfold searchRadius
    linarith
  have hFenv : ∫⁻ o, ENNReal.ofReal
      ((|(1 : ℝ)| * Real.exp (2 * searchRadius p * |learnedResidual p m p.n o|)) ^ 2)
      ∂m.P ≤ ENNReal.ofReal (CF ^ 2) := by
    have h := learnedResidual_exp_abs_sq_lintegral_le p m p.n hclass
      (searchRadius p) hR.le
    have hCFsq : CF ^ 2 = AF := Real.sq_sqrt hAF.le
    rw [hCFsq]
    simpa [AF, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using h
  have hGenv : ∫⁻ o, ENNReal.ofReal
      ((|outcome o| * Real.exp (2 * searchRadius p * |learnedResidual p m p.n o|)) ^ 2)
      ∂m.P ≤ ENNReal.ofReal (CG ^ 2) := by
    have h := outcome_exp_abs_sq_lintegral_le p m p.n hclass
      (searchRadius p) hR.le
    have hCGsq : CG ^ 2 = AG := Real.sq_sqrt hAG.le
    rw [hCGsq]
    exact h
  let cF : (Fin p.n → Obs Xspace) → ℕ → ℝ := fun data k ↦
    (I.card : ℝ)⁻¹ * ∑ i ∈ I,
      (learnedResidual p m p.n (data i) ^ k / k.factorial -
        ∫ o, learnedResidual p m p.n o ^ k / k.factorial ∂m.P)
  let cG : (Fin p.n → Obs Xspace) → ℕ → ℝ := fun data k ↦
    (I.card : ℝ)⁻¹ * ∑ i ∈ I,
      (outcome (data i) * learnedResidual p m p.n (data i) ^ k / k.factorial -
        ∫ o, outcome o * learnedResidual p m p.n o ^ k / k.factorial ∂m.P)
  have hZmeas : Measurable (learnedResidual p m p.n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      (((m.gcode_measurable p.n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  have hFbound := centered_factorial_empirical_disk_l2 I hI
    (fun _ : Obs Xspace ↦ (1 : ℝ)) (learnedResidual p m p.n)
    measurable_const hZmeas (searchRadius p) hR CF hCF.le hFenv
  have hGbound := centered_factorial_empirical_disk_l2 I hI
    outcome (learnedResidual p m p.n) measurable_snd.snd hZmeas
    (searchRadius p) hR CG hCG.le hGenv
  have hFerr : ∀ data,
      transformSupError (fun data z ↦ empiricalF p m p.n data I z)
          (residualMGF p m p.n) (searchRadius p) data =
        diskSupNorm (fun data z ↦ ∑' k, (cF data k : ℂ) * z ^ k)
          (searchRadius p) data := by
    intro data
    rw [transformSupError_eq_diskSupNorm, diskSupNorm_eq_sSup_image,
      diskSupNorm_eq_sSup_image]
    apply congrArg sSup
    ext x
    constructor <;> rintro ⟨z, hz, rfl⟩ <;> refine ⟨z, hz, ?_⟩
    · congr 1
      symm
      have hs := weighted_empirical_sub_eq_centered_factorial_series I hI
        (fun _ : Obs Xspace ↦ (1 : ℝ)) (learnedResidual p m p.n)
        measurable_const hZmeas (searchRadius p) hR CF hCF.le hFenv data z hz
      exact congrArg norm (by simpa [cF, empiricalF, residualMGF, weightedTransform,
        ProbabilityTheory.complexMGF] using hs)
    · congr 1
      have hs := weighted_empirical_sub_eq_centered_factorial_series I hI
        (fun _ : Obs Xspace ↦ (1 : ℝ)) (learnedResidual p m p.n)
        measurable_const hZmeas (searchRadius p) hR CF hCF.le hFenv data z hz
      exact congrArg norm (by simpa [cF, empiricalF, residualMGF, weightedTransform,
        ProbabilityTheory.complexMGF] using hs)
  have hGerr : ∀ data,
      transformSupError (fun data z ↦ empiricalG p m p.n data I z)
          (outcomeResidualTransform p m p.n) (searchRadius p) data =
        diskSupNorm (fun data z ↦ ∑' k, (cG data k : ℂ) * z ^ k)
          (searchRadius p) data := by
    intro data
    rw [transformSupError_eq_diskSupNorm, diskSupNorm_eq_sSup_image,
      diskSupNorm_eq_sSup_image]
    apply congrArg sSup
    ext x
    constructor <;> rintro ⟨z, hz, rfl⟩ <;> refine ⟨z, hz, ?_⟩
    · congr 1
      symm
      exact congrArg norm (by simpa [cG, empiricalG, outcomeResidualTransform] using
        (weighted_empirical_sub_eq_centered_factorial_series I hI outcome
          (learnedResidual p m p.n) measurable_snd.snd hZmeas
          (searchRadius p) hR CG hCG.le hGenv data z hz))
    · congr 1
      exact congrArg norm (by simpa [cG, empiricalG, outcomeResidualTransform] using
        (weighted_empirical_sub_eq_centered_factorial_series I hI outcome
          (learnedResidual p m p.n) measurable_snd.snd hZmeas
          (searchRadius p) hR CG hCG.le hGenv data z hz))
  have htotal :
      (∫⁻ data, ENNReal.ofReal
        ((transformSupError (fun data z ↦ empiricalF p m p.n data I z)
          (residualMGF p m p.n) (searchRadius p) data) ^ 2)
        ∂Measure.pi (fun _ : Fin p.n ↦ m.P)) +
      (∫⁻ data, ENNReal.ofReal
        ((transformSupError (fun data z ↦ empiricalG p m p.n data I z)
          (outcomeResidualTransform p m p.n) (searchRadius p) data) ^ 2)
        ∂Measure.pi (fun _ : Fin p.n ↦ m.P)) ≤ ENNReal.ofReal (K / I.card) := by
    simp_rw [hFerr, hGerr]
    have hFbound' :
        (∫⁻ data, ENNReal.ofReal
          ((diskSupNorm (fun data z ↦ ∑' k, (cF data k : ℂ) * z ^ k)
            (searchRadius p) data) ^ 2) ∂Measure.pi (fun _ : Fin p.n ↦ m.P)) ≤
          ENNReal.ofReal ((2 * CF / Real.sqrt I.card) ^ 2) := by
      simpa [cF] using hFbound
    have hGbound' :
        (∫⁻ data, ENNReal.ofReal
          ((diskSupNorm (fun data z ↦ ∑' k, (cG data k : ℂ) * z ^ k)
            (searchRadius p) data) ^ 2) ∂Measure.pi (fun _ : Fin p.n ↦ m.P)) ≤
          ENNReal.ofReal ((2 * CG / Real.sqrt I.card) ^ 2) := by
      simpa [cG] using hGbound
    calc
    _ ≤ ENNReal.ofReal ((2 * CF / Real.sqrt I.card) ^ 2) +
        ENNReal.ofReal ((2 * CG / Real.sqrt I.card) ^ 2) := add_le_add hFbound' hGbound'
    _ = ENNReal.ofReal (K / I.card) := by
      rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      congr 1
      have hcard : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
      dsimp [K]
      rw [div_pow, div_pow, Real.sq_sqrt hcard.le]
      field_simp
      ring
  simpa [I, iidLaw] using htotal

/-- Both split-fold analytic transforms have uniform mean-square error of
order inverse fold size. -/
-- @node: lem:empirical-transform-uniform-l2
lemma empirical_transform_uniform_l2
    {Xspace : Type*} [MeasurableSpace Xspace]
    (Ctheta Cg Cq psieta psixi R1 : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (p : Parameters), p.Ctheta = Ctheta → p.Cg = Cg → p.Cq = Cq →
        p.psieta = psieta → p.psixi = psixi → searchRadius p = R1 → 2 ≤ p.n →
      ∀ (m : Model (Xspace := Xspace) p), NonGaussianClass p p.n m →
      IidSampling p.n m.P (iidLaw m p.n) →
      ∀ a : Fin 2, (inferenceFold p.n a).Nonempty →
        (∫⁻ data, ENNReal.ofReal
          ((transformSupError
            (fun data z ↦ empiricalF p m p.n data (inferenceFold p.n a) z)
            (residualMGF p m p.n) R1 data) ^ 2) ∂iidLaw m p.n) +
        (∫⁻ data, ENNReal.ofReal
          ((transformSupError
            (fun data z ↦ empiricalG p m p.n data (inferenceFold p.n a) z)
            (outcomeResidualTransform p m p.n) R1 data) ^ 2) ∂iidLaw m p.n) ≤
          ENNReal.ofReal (K / (inferenceFold p.n a).card) := by
  refine ⟨empiricalTransformL2Constant Ctheta Cg Cq psieta psixi R1,
    empiricalTransformL2Constant_pos _ _ _ _ _ _, ?_⟩
  exact empirical_transform_uniform_l2_explicit Ctheta Cg Cq psieta psixi R1



end CausalSmith.Stat.SaPlmCumulantConverse
