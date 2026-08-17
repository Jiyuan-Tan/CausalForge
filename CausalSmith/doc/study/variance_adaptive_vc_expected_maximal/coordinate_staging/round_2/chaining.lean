import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.EmpiricalCover
import Causalean.Stat.Concentration.Covering.DudleyEntropy
import Causalean.Stat.Concentration.Covering.SqrtLogIntegral
import Causalean.Stat.Concentration.Covering.VCLocalizedRegime
import Causalean.Stat.Concentration.Rademacher.Contraction
import Causalean.Stat.Concentration.Rademacher.Symmetrization
import Causalean.Mathlib.Analysis.ClipInterval

/-!
# Variance-adaptive Rademacher chaining

This module supplies the deterministic chaining half of the countable-class
maximal inequality.  It combines empirical `L²` polynomial covers with the
existing Dudley bound to control a fixed-sample Rademacher supremum by an
empirical radius and the population `L²` radius.

The statement follows the constant-envelope specialization of the maximal
inequality recorded as Corollary 5.1 in Chernozhukov, Chetverikov, and Kato,
*Gaussian approximation of suprema of empirical processes* (2014).  In that
corollary the empirical process is scaled by `sqrt n`; a constant envelope
has population `L²` norm and sample maximum both bounded by `U`, so dividing
their conclusion by `sqrt n` gives exactly the two terms below.  The
canonical normalization there is `A ≥ exp 1` and `v ≥ 1`.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory

universe u v

variable {𝒳 : Type u} [MeasurableSpace 𝒳] {ι : Type v}

private noncomputable def anchoredClass (F : ι → 𝒳 → ℝ) (i₀ : ι) :
    ι → 𝒳 → ℝ := fun i x => F i x - F i₀ x

private lemma anchoredClass_measurable
    (F : ι → 𝒳 → ℝ) (i₀ : ι) (hmeas : ∀ i, Measurable (F i)) :
    ∀ i, Measurable (anchoredClass F i₀ i) :=
  fun i => (hmeas i).sub (hmeas i₀)

private lemma anchoredClass_empiricalDist
    (F : ι → 𝒳 → ℝ) (i₀ i j : ι) {n : ℕ} (S : Fin n → 𝒳) :
    empiricalDist S (anchoredClass F i₀ i) (anchoredClass F i₀ j) =
      empiricalDist S (F i) (F j) := by
  simp only [empiricalDist]
  congr 1
  funext x
  simp [anchoredClass]

private lemma HasPolynomialEmpiricalL2Cover.anchoredClass
    {F : ι → 𝒳 → ℝ} {U A p : ℝ}
    (hcover : HasPolynomialEmpiricalL2Cover F U A p)
    (i₀ : ι) (hmeas : ∀ i, Measurable (F i)) :
    HasPolynomialEmpiricalL2Cover (anchoredClass F i₀) U A p := by
  intro m S hm ε hε hε1
  obtain ⟨C, hC, hcard⟩ := hcover S hm ε hε hε1
  refine ⟨C, ?_, hcard⟩
  intro i
  obtain ⟨j, hj, hij⟩ := hC i
  refine ⟨j, hj, ?_⟩
  rw [measureL2Dist_finiteSampleMeasure_eq_empiricalDist S hm
      (anchoredClass_measurable F i₀ hmeas i)
      (anchoredClass_measurable F i₀ hmeas j),
    anchoredClass_empiricalDist]
  rwa [← measureL2Dist_finiteSampleMeasure_eq_empiricalDist S hm (hmeas i) (hmeas j)]

private lemma HasPolynomialEmpiricalL2Cover.neg
    {F : ι → 𝒳 → ℝ} {U A p : ℝ}
    (hcover : HasPolynomialEmpiricalL2Cover F U A p)
    (hmeas : ∀ i, Measurable (F i)) :
    HasPolynomialEmpiricalL2Cover (fun i x => -F i x) U A p := by
  intro m S hm ε hε hε1
  obtain ⟨C, hC, hcard⟩ := hcover S hm ε hε hε1
  refine ⟨C, ?_, hcard⟩
  intro i
  obtain ⟨j, hj, hij⟩ := hC i
  refine ⟨j, hj, ?_⟩
  rw [measureL2Dist_finiteSampleMeasure_eq_empiricalDist S hm
      (hmeas i).neg (hmeas j).neg]
  have heq : empiricalDist S (fun x => -F i x) (fun x => -F j x) =
      empiricalDist S (F i) (F j) := by
    unfold empiricalDist empiricalNorm
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    change (-F i (S k) - -F j (S k)) ^ 2 = (F i (S k) - F j (S k)) ^ 2
    ring
  rw [heq]
  rwa [← measureL2Dist_finiteSampleMeasure_eq_empiricalDist S hm (hmeas i) (hmeas j)]

private lemma empiricalNorm_le_of_envelope
    (F : ι → 𝒳 → ℝ) {U : ℝ} (hU : 0 ≤ U)
    (henvelope : ∀ i x, |F i x| ≤ U)
    {n : ℕ} (S : Fin n → 𝒳) (i : ι) : empiricalNorm S (F i) ≤ U := by
  unfold empiricalNorm
  rw [Real.sqrt_le_iff]
  constructor
  · exact hU
  · by_cases hn : n = 0
    · subst n
      simp [hU]
    · have hnR : 0 < (n : ℝ) := by positivity
      calc
        (1 / (n : ℝ)) * ∑ k : Fin n, F i (S k) ^ 2
            ≤ (1 / (n : ℝ)) * ∑ _k : Fin n, U ^ 2 := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
              rw [sq_le_sq]
              simpa [abs_of_nonneg hU] using henvelope i (S k)
        _ = U ^ 2 := by
              simp [Finset.sum_const, nsmul_eq_mul]
              field_simp

private lemma empiricalNorm_anchored_le
    (F : ι → 𝒳 → ℝ) (i₀ : ι) {n : ℕ} (S : Fin n → 𝒳)
    {R : ℝ} (hR : ∀ i, empiricalNorm S (F i) ≤ R) (i : ι) :
    empiricalNorm S (anchoredClass F i₀ i) ≤ 2 * R := by
  letI := empiricalPMet S
  calc
    empiricalNorm S (anchoredClass F i₀ i) = dist (F i) (F i₀) := by
      rfl
    _ ≤ dist (F i) 0 + dist 0 (F i₀) := dist_triangle _ _ _
    _ = empiricalNorm S (F i) + empiricalNorm S (F i₀) := by
      simp only [dist_comm (0 : 𝒳 → ℝ)]
      change empiricalNorm S (F i - 0) + empiricalNorm S (F i₀ - 0) = _
      simp
    _ ≤ R + R := add_le_add (hR i) (hR i₀)
    _ = 2 * R := by ring

private lemma intervalIntegrable_sqrt_log_ratio_positive
    {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ) :
    IntervalIntegrable (fun x : ℝ => Real.sqrt (Real.log (δ / x))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hdiv : ContinuousOn (fun x : ℝ => δ / x) (Set.Icc a b) :=
    continuousOn_const.div continuousOn_id (fun x hx => by linarith [hx.1])
  simpa [Set.uIcc_of_le hab] using Real.continuous_sqrt.comp_continuousOn
    (hdiv.log (fun x hx => div_ne_zero hδ.ne' (by linarith [hx.1])))

/-- A logarithmic square-root kernel contributes at most its numerator even
when the integration interval extends beyond that numerator (where Lean's
real square root of the nonpositive logarithm is zero). -/
private lemma sqrtLog_partial_integral_le
    {ε R σ : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (hσ : 0 < σ) :
    (∫ x in ε..R, Real.sqrt (Real.log (σ / x))) ≤ σ := by
  have hint := intervalIntegrable_sqrt_log_ratio_positive (δ := σ) hε hεR hσ
  by_cases hRσ : R ≤ σ
  · have hmono :
        (∫ x in ε..R, Real.sqrt (Real.log (σ / x))) ≤
          ∫ x in ε..σ, Real.sqrt (Real.log (σ / x)) := by
      exact intervalIntegral.integral_mono_interval le_rfl hεR hRσ
        (by filter_upwards; intro x; exact Real.sqrt_nonneg _)
        (intervalIntegrable_sqrt_log_div hε (hεR.trans hRσ))
    exact hmono.trans ((sqrtLog_integral_le hε (hεR.trans hRσ)).trans (by linarith))
  · have hσR : σ < R := lt_of_not_ge hRσ
    by_cases hεσ : ε ≤ σ
    · have hi1 := intervalIntegrable_sqrt_log_div hε hεσ
      have hi2 := intervalIntegrable_sqrt_log_ratio_positive (δ := σ) hσ hσR.le hσ
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
      have hzero : (∫ x in σ..R, Real.sqrt (Real.log (σ / x))) = 0 := by
        rw [← intervalIntegral.integral_zero]
        apply intervalIntegral.integral_congr
        intro x hx
        have hxIcc : x ∈ Set.Icc σ R := by
          simpa [Set.uIcc_of_le hσR.le] using hx
        have hxpos : 0 < x := lt_of_lt_of_le hσ hxIcc.1
        have hratio : σ / x ≤ 1 := (div_le_one hxpos).2 hxIcc.1
        exact Real.sqrt_eq_zero_of_nonpos (Real.log_nonpos (by positivity) hratio)
      rw [hzero, add_zero]
      exact (sqrtLog_integral_le hε hεσ).trans (by linarith)
    · have hσε : σ < ε := lt_of_not_ge hεσ
      have hzero : (∫ x in ε..R, Real.sqrt (Real.log (σ / x))) = 0 := by
        rw [← intervalIntegral.integral_zero]
        apply intervalIntegral.integral_congr
        intro x hx
        have hxIcc : x ∈ Set.Icc ε R := by
          simpa [Set.uIcc_of_le hεR] using hx
        have hxpos : 0 < x := lt_of_lt_of_le hε hxIcc.1
        have hratio : σ / x ≤ 1 := (div_le_one hxpos).2 (hσε.le.trans hxIcc.1)
        exact Real.sqrt_eq_zero_of_nonpos (Real.log_nonpos (by positivity) hratio)
      rw [hzero]
      exact hσ.le

private lemma polynomialCover_entropyIntegral_le
    [Nonempty ι]
    {F : ι → 𝒳 → ℝ} {U σ A p ε R : ℝ}
    (hcover : HasPolynomialEmpiricalL2Cover F U A p)
    (hmeas : ∀ i, Measurable (F i))
    (hU : 0 < U) (hσ : 0 < σ) (hσU : σ < U)
    (hA : Real.exp 1 ≤ A) (hp : 1 ≤ p)
    {n : ℕ} (S : Fin n → 𝒳) (hn : 0 < n)
    (hε : 0 < ε) (hεR : ε ≤ R) (hRU : R ≤ U) :
    let htot := hcover.totallyBounded hmeas hU S hn
    (∫ x in ε..R, Real.sqrt (Real.log (coveringNumber htot x))) ≤
      R * Real.sqrt (p * vcMaximalLog A U σ) +
        σ * Real.sqrt p := by
  dsimp only
  let htot := hcover.totallyBounded hmeas hU S hn
  letI : Nonempty (EmpiricalFunctionSpace F S) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty ι)⟩⟩
  have hA0 : 0 < A := lt_of_lt_of_le (Real.exp_pos 1) hA
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hratio : Real.exp 1 < A * U / σ := by
    have hUσ : 1 < U / σ := (one_lt_div₀ hσ).2 hσU
    calc
      Real.exp 1 ≤ A := hA
      _ < A * (U / σ) := by nlinarith
      _ = A * U / σ := by ring
  have hlog : vcMaximalLog A U σ = Real.log (A * U / σ) := by
    simp [vcMaximalLog, max_eq_right hratio.le]
  have hL0 : 0 ≤ vcMaximalLog A U σ := by
    rw [hlog]
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by
      simpa using (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num))
    exact Real.log_nonneg (he1.trans hratio.le)
  have hpoint : ∀ x ∈ Set.Icc ε R,
      Real.sqrt (Real.log (coveringNumber htot x)) ≤
        Real.sqrt (p * vcMaximalLog A U σ) +
          Real.sqrt p * Real.sqrt (Real.log (σ / x)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hε hx.1
    have hxU : x / U ≤ 1 := (div_le_one hU).2 (hx.2.trans hRU)
    have hxU0 : 0 < x / U := div_pos hx0 hU
    have hcov := hcover.coveringNumber_le hmeas hU S hn (x / U) hxU0 hxU
    have hbase : 0 < A * U / x := by positivity
    have hcard0 : 0 < (coveringNumber htot x : ℝ) := by
      exact_mod_cast coveringNumber_nonzero Set.univ_nonempty htot hx0
    have hcard : (coveringNumber htot x : ℝ) ≤ Real.rpow (A * U / x) p := by
      convert hcov using 1 <;> field_simp <;> ring
    have hlogcov : Real.log (coveringNumber htot x) ≤ p * Real.log (A * U / x) := by
      calc
        Real.log (coveringNumber htot x) ≤ Real.log (Real.rpow (A * U / x) p) :=
          Real.log_le_log hcard0 hcard
        _ = p * Real.log (A * U / x) := Real.log_rpow hbase p
    have hmain : Real.sqrt (Real.log (coveringNumber htot x)) ≤
        Real.sqrt (p * Real.log (A * U / x)) :=
      Real.sqrt_le_sqrt hlogcov
    by_cases hxσ : x ≤ σ
    · have hσx : 1 ≤ σ / x := (one_le_div hx0).2 hxσ
      have hlogsx : 0 ≤ Real.log (σ / x) := Real.log_nonneg hσx
      have hsplit : Real.log (A * U / x) =
          vcMaximalLog A U σ + Real.log (σ / x) := by
        rw [hlog]
        rw [← Real.log_mul (by positivity : A * U / σ ≠ 0) (by positivity : σ / x ≠ 0)]
        congr 1
        field_simp
      have ha : 0 ≤ p * vcMaximalLog A U σ := mul_nonneg hp0 hL0
      have hb : 0 ≤ p * Real.log (σ / x) := mul_nonneg hp0 hlogsx
      have hsqrtadd : Real.sqrt (p * vcMaximalLog A U σ +
          p * Real.log (σ / x)) ≤
          Real.sqrt (p * vcMaximalLog A U σ) +
            Real.sqrt (p * Real.log (σ / x)) := by
        have hsq1 := Real.sq_sqrt ha
        have hsq2 := Real.sq_sqrt hb
        have hsq12 := Real.sq_sqrt (add_nonneg ha hb)
        nlinarith [Real.sqrt_nonneg (p * vcMaximalLog A U σ),
          Real.sqrt_nonneg (p * Real.log (σ / x))]
      calc
        _ ≤ Real.sqrt (p * Real.log (A * U / x)) := hmain
        _ = Real.sqrt (p * vcMaximalLog A U σ + p * Real.log (σ / x)) := by
          rw [hsplit]
          ring_nf
        _ ≤ Real.sqrt (p * vcMaximalLog A U σ) +
            Real.sqrt (p * Real.log (σ / x)) := hsqrtadd
        _ = _ := by rw [Real.sqrt_mul hp0, Real.sqrt_mul hp0]
    · have hσx : σ < x := lt_of_not_ge hxσ
      have hlogle : Real.log (A * U / x) ≤ vcMaximalLog A U σ := by
        rw [hlog]
        apply Real.log_le_log (by positivity)
        exact div_le_div_of_nonneg_left (mul_nonneg hA0.le hU.le) hσ hσx.le
      have hple : p * Real.log (A * U / x) ≤ p * vcMaximalLog A U σ :=
        mul_le_mul_of_nonneg_left hlogle hp0
      have hzero : Real.sqrt (Real.log (σ / x)) = 0 := by
        apply Real.sqrt_eq_zero_of_nonpos
        exact Real.log_nonpos (by positivity) ((div_le_one hx0).2 hσx.le)
      rw [hzero, mul_zero, add_zero]
      exact hmain.trans (Real.sqrt_le_sqrt hple)
  have hintLeft : IntervalIntegrable
      (fun x : ℝ => Real.sqrt (Real.log (coveringNumber htot x))) volume ε R := by
    apply AntitoneOn.intervalIntegrable
    refine antitoneOn_iff_forall_lt.mpr ?_
    intro a ha b hb hab
    apply Real.sqrt_le_sqrt
    apply Real.log_le_log
    · exact_mod_cast coveringNumber_nonzero Set.univ_nonempty htot (by
        have : b ∈ Set.Icc ε R := by simpa [Set.uIcc_of_le hεR] using hb
        exact lt_of_lt_of_le hε this.1)
    · norm_cast
      apply coveringNumber_antitone
      · have : a ∈ Set.Icc ε R := by simpa [Set.uIcc_of_le hεR] using ha
        exact lt_of_lt_of_le hε this.1
      · have : b ∈ Set.Icc ε R := by simpa [Set.uIcc_of_le hεR] using hb
        exact lt_of_lt_of_le hε this.1
      · exact hab.le
  have hintConst : IntervalIntegrable
      (fun _x : ℝ => Real.sqrt (p * vcMaximalLog A U σ)) volume ε R :=
    intervalIntegral.intervalIntegrable_const
  have hintKernel : IntervalIntegrable
      (fun x : ℝ => Real.sqrt p * Real.sqrt (Real.log (σ / x))) volume ε R :=
    (intervalIntegrable_sqrt_log_ratio_positive hε hεR hσ).const_mul _
  have hintRight : IntervalIntegrable
      (fun x : ℝ => Real.sqrt (p * vcMaximalLog A U σ) +
        Real.sqrt p * Real.sqrt (Real.log (σ / x))) volume ε R := by
    exact hintConst.add hintKernel
  have hmono := intervalIntegral.integral_mono_on hεR hintLeft hintRight hpoint
  have hkernel := sqrtLog_partial_integral_le hε hεR hσ
  calc
    (∫ x in ε..R, Real.sqrt (Real.log (coveringNumber htot x)))
        ≤ ∫ x in ε..R, (Real.sqrt (p * vcMaximalLog A U σ) +
          Real.sqrt p * Real.sqrt (Real.log (σ / x))) := hmono
    _ = (R - ε) * Real.sqrt (p * vcMaximalLog A U σ) +
          Real.sqrt p * (∫ x in ε..R, Real.sqrt (Real.log (σ / x))) := by
      rw [intervalIntegral.integral_add hintConst hintKernel]
      rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
      simp [smul_eq_mul]
    _ ≤ R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p := by
      have hs1 : (R - ε) * Real.sqrt (p * vcMaximalLog A U σ) ≤
          R * Real.sqrt (p * vcMaximalLog A U σ) := by
        nlinarith [Real.sqrt_nonneg (p * vcMaximalLog A U σ)]
      have hs2 : Real.sqrt p * (∫ x in ε..R, Real.sqrt (Real.log (σ / x))) ≤
          Real.sqrt p * σ := mul_le_mul_of_nonneg_left hkernel (Real.sqrt_nonneg _)
      nlinarith
    _ = _ := by ring

private lemma empiricalRademacherComplexity_le_signed_add_neg_of_zero
    [Nonempty ι]
    (H : ι → 𝒳 → ℝ) (i₀ : ι) (hzero : ∀ x, H i₀ x = 0)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i x, |H i x| ≤ M)
    (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n H S ≤
      empiricalRademacherComplexity_without_abs n H S +
        empiricalRademacherComplexity_without_abs n (fun i x => -H i x) S := by
  classical
  unfold empiricalRademacherComplexity empiricalRademacherComplexity_without_abs
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) (by positivity)
  let z : ι → ℝ := fun i =>
    (n : ℝ)⁻¹ * ∑ k : Fin n, (τ k : ℝ) * H i (S k)
  have hz0 : z i₀ = 0 := by simp [z, hzero]
  have hbddAbs : BddAbove (Set.range fun i => |z i|) := by
    simpa [z] using absInner_bddAbove H hM0 hM n S τ
  have hbdd : BddAbove (Set.range z) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (le_abs_self _).trans (absInner_le_of_bound H hM0 hM n S τ i)
  have hbddNeg : BddAbove (Set.range fun i => -z i) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (neg_le_abs _).trans (absInner_le_of_bound H hM0 hM n S τ i)
  have hsup0 : 0 ≤ ⨆ i, z i := by
    rw [← hz0]
    exact le_ciSup hbdd i₀
  have hsupNeg0 : 0 ≤ ⨆ i, -z i := by
    rw [← show -z i₀ = 0 by rw [hz0]; simp]
    exact le_ciSup hbddNeg i₀
  have hpoint : (⨆ i, |z i|) ≤ (⨆ i, z i) + (⨆ i, -z i) := by
    refine ciSup_le fun i => ?_
    by_cases hi : 0 ≤ z i
    · rw [abs_of_nonneg hi]
      linarith [le_ciSup hbdd i]
    · rw [abs_of_neg (lt_of_not_ge hi)]
      linarith [le_ciSup hbddNeg i]
  have hneg : (⨆ i, -z i) =
      ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (τ k : ℝ) * (-H i (S k)) := by
    refine iSup_congr fun i => ?_
    calc
      -z i = (n : ℝ)⁻¹ * (-(∑ k : Fin n, (τ k : ℝ) * H i (S k))) := by
        simp only [z]
        ring
      _ = (n : ℝ)⁻¹ * ∑ k : Fin n, -((τ k : ℝ) * H i (S k)) := by
        rw [Finset.sum_neg_distrib]
      _ = (n : ℝ)⁻¹ * ∑ k : Fin n, (τ k : ℝ) * (-H i (S k)) := by
        congr 1
        refine Finset.sum_congr rfl fun k _ => by ring
  simpa [z, hneg] using hpoint

private lemma constantClass_empiricalRademacher_le
    [Nonempty ι] (g : 𝒳 → ℝ) {n : ℕ} (hn : 0 < n) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun _i : ι => g) S ≤
      2 * empiricalNorm S g / Real.sqrt (n : ℝ) := by
  classical
  let H : Unit → 𝒳 → ℝ := fun _ => g
  have hradius : ∀ i ∈ (Finset.univ : Finset Unit),
      Real.sqrt (∑ k : Fin n, ((n : ℝ)⁻¹ * |H i (S k)|) ^ 2) ≤
        empiricalNorm S g / Real.sqrt (n : ℝ) := by
    intro i hi
    exact (sqrt_sum_inv_abs_sq_eq_empiricalNorm_div_sqrt hn S g).le
  have hmass := empiricalRademacher_withAbs_finiteClass_le hn H S
    (Finset.univ : Finset Unit) (by simp) (empiricalNorm S g / Real.sqrt (n : ℝ)) hradius
  rw [empiricalRademacherComplexity_F_on_univ_eq] at hmass
  have hlog2 : Real.sqrt (2 * Real.log (2 * ((Finset.univ : Finset Unit).card : ℝ))) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · simp only [Finset.card_univ, Fintype.card_unit, Nat.cast_one, mul_one]
      nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hnonneg : 0 ≤ empiricalNorm S g / Real.sqrt (n : ℝ) :=
    div_nonneg (by unfold empiricalNorm; positivity) (Real.sqrt_nonneg _)
  have hunit : empiricalRademacherComplexity n H S =
      empiricalRademacherComplexity n (fun _i : ι => g) S := by
    unfold empiricalRademacherComplexity
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp [H, hn.ne']
  rw [← hunit]
  exact hmass.trans (by
    calc
      _ ≤ (empiricalNorm S g / Real.sqrt (n : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hlog2 hnonneg
      _ = _ := by ring)

/-- A bounded countable class with polynomial empirical `L²` entropy has
conditional Rademacher complexity controlled by its empirical `L²` radius
and its population `L²` radius at the corresponding logarithmic entropy
rate. -/
theorem empiricalRademacher_conditional_le
    [Nonempty ι]
    (F : ι → 𝒳 → ℝ) {U σ A p R : ℝ}
    (hσ : 0 < σ) (hσU : σ < U) (hA : Real.exp 1 ≤ A) (hp : 1 ≤ p)
    (hmeas : ∀ i, Measurable (F i))
    (henvelope : ∀ i x, |F i x| ≤ U)
    (hcover : HasPolynomialEmpiricalL2Cover F U A p)
    {n : ℕ} (hn : 0 < n) (S : Fin n → 𝒳)
    (hR : ∀ i, empiricalNorm S (F i) ≤ R) (hR0 : 0 < R) (hRU : R ≤ U) :
    empiricalRademacherComplexity n F S ≤
      26 / Real.sqrt (n : ℝ) * Real.sqrt (p * vcMaximalLog A U σ) * (R + σ) := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  let H := anchoredClass F i₀
  have hU : 0 < U := hσ.trans hσU
  have hU0 : 0 ≤ U := hU.le
  have hHmeas : ∀ i, Measurable (H i) := anchoredClass_measurable F i₀ hmeas
  have hHenv : ∀ i x, |H i x| ≤ 2 * U := by
    intro i x
    exact (abs_sub (F i x) (F i₀ x)).trans (by linarith [henvelope i x, henvelope i₀ x])
  have hHnorm : ∀ i, empiricalNorm S (H i) ≤ 2 * R :=
    empiricalNorm_anchored_le F i₀ S hR
  have hHcover : HasPolynomialEmpiricalL2Cover H U A p := by
    change HasPolynomialEmpiricalL2Cover (anchoredClass F i₀) U A p
    exact hcover.anchoredClass i₀ hmeas
  have htot := hHcover.totallyBounded hHmeas hU S hn
  have hnegCover : HasPolynomialEmpiricalL2Cover (fun i x => -H i x) U A p := by
    exact hHcover.neg hHmeas
  have hnegMeas : ∀ i, Measurable (fun x => -H i x) := fun i => (hHmeas i).neg
  have htotNeg := hnegCover.totallyBounded hnegMeas hU S hn
  have hHsigned :
      empiricalRademacherComplexity_without_abs n H S +
          empiricalRademacherComplexity_without_abs n (fun i x => -H i x) S ≤
        24 / Real.sqrt (n : ℝ) *
          (R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p) := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let ε := min (R / 2) (δ / 8)
    have hε : 0 < ε := lt_min (by positivity) (by positivity)
    have hεR : ε ≤ R := (min_le_left _ _).trans (by linarith)
    have hεltR : ε < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdudley := dudley_entropy_integral_bound (F := H) hε htot hn hHnorm (by
      simpa using hεltR)
    have hnegNorm : ∀ i, empiricalNorm S (fun x => -H i x) ≤ 2 * R := by
      intro i
      simpa [empiricalNorm] using hHnorm i
    have hdudleyNeg := dudley_entropy_integral_bound (F := fun i x => -H i x)
      hε htotNeg hn hnegNorm (by simpa using hεltR)
    have hdudley' := hdudley
    have hdudleyNeg' := hdudleyNeg
    simp only [show (2 * R) / 2 = R by ring] at hdudley' hdudleyNeg'
    have hint := polynomialCover_entropyIntegral_le hHcover hHmeas hU hσ hσU
      hA hp S hn hε hεR hRU
    have hintNeg := polynomialCover_entropyIntegral_le hnegCover hnegMeas hU hσ hσU
      hA hp S hn hε hεR hRU
    have hint' : (∫ x in ε..R,
        Real.sqrt (Real.log (coveringNumber htot x))) ≤
          R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p := by
      simpa [htot] using hint
    have hintNeg' : (∫ x in ε..R,
        Real.sqrt (Real.log (coveringNumber htotNeg x))) ≤
          R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p := by
      simpa [htotNeg] using hintNeg
    have hεsmall : 8 * ε ≤ δ := by
      dsimp [ε]
      have := min_le_right (R / 2) (δ / 8)
      linarith
    exact (add_le_add hdudley' hdudleyNeg').trans (by
        have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        have hdiv0 : 0 ≤ 12 / Real.sqrt (n : ℝ) := div_nonneg (by norm_num) hsqrt0
        have hmul1 := mul_le_mul_of_nonneg_left hint' hdiv0
        have hmul2 := mul_le_mul_of_nonneg_left hintNeg' hdiv0
        have hcoef : 24 / Real.sqrt (n : ℝ) = 2 * (12 / Real.sqrt (n : ℝ)) := by ring
        calc
          (4 * ε + 12 / Real.sqrt (n : ℝ) *
                (∫ x in ε..R, Real.sqrt (Real.log (coveringNumber htot x)))) +
              (4 * ε + 12 / Real.sqrt (n : ℝ) *
                (∫ x in ε..R, Real.sqrt (Real.log (coveringNumber htotNeg x))))
              ≤ 8 * ε + 24 / Real.sqrt (n : ℝ) *
                (R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p) := by
                  rw [hcoef]
                  linarith
          _ ≤ 24 / Real.sqrt (n : ℝ) *
                (R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p) + δ := by
                  linarith)
  have hHzero : ∀ x, H i₀ x = 0 := by simp [H, anchoredClass]
  have hHabs := empiricalRademacherComplexity_le_signed_add_neg_of_zero
    H i₀ hHzero (mul_nonneg (by norm_num) hU0) hHenv n S
  have hdecomp : empiricalRademacherComplexity n F S ≤
      empiricalRademacherComplexity n H S +
        empiricalRademacherComplexity n (fun _i : ι => F i₀) S := by
    have hsub := empiricalRademacherComplexity_sub_le H (fun _i : ι => fun x => -F i₀ x)
      (mul_nonneg (by norm_num) hU0) hU0 hHenv
      (fun _ x => by simpa using henvelope i₀ x) n S
    have hcongr : empiricalRademacherComplexity n F S =
        empiricalRademacherComplexity n
          (fun i x => H i x - (-F i₀ x)) S := by
      apply empiricalRademacherComplexity_congr_sample
      intro i k
      simp [H, anchoredClass]
    rw [hcongr]
    have hnegConst : empiricalRademacherComplexity n (fun _i : ι => fun x => -F i₀ x) S =
        empiricalRademacherComplexity n (fun _i : ι => F i₀) S := by
      simpa using empiricalRademacherComplexity_smul_class
        (fun _i : ι => F i₀) (-1) n S
    rwa [hnegConst] at hsub
  have hanchor := constantClass_empiricalRademacher_le (ι := ι) (F i₀) hn S
  have hbasic : empiricalRademacherComplexity n F S ≤
      24 / Real.sqrt (n : ℝ) *
          (R * Real.sqrt (p * vcMaximalLog A U σ) + σ * Real.sqrt p) +
        2 * R / Real.sqrt (n : ℝ) := by
    have hanchorR : empiricalRademacherComplexity n (fun _i : ι => F i₀) S ≤
        2 * R / Real.sqrt (n : ℝ) := hanchor.trans (by
      gcongr
      exact hR i₀)
    exact hdecomp.trans (add_le_add (hHabs.trans hHsigned) hanchorR)
  have hratio : Real.exp 1 < A * U / σ := by
    have hUσ : 1 < U / σ := (one_lt_div₀ hσ).2 hσU
    calc
      Real.exp 1 ≤ A := hA
      _ < A * (U / σ) := by nlinarith [Real.exp_pos 1]
      _ = A * U / σ := by ring
  have hL1 : 1 ≤ vcMaximalLog A U σ := by
    rw [vcMaximalLog, max_eq_right hratio.le, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hratio.le
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hq1 : 1 ≤ Real.sqrt (p * vcMaximalLog A U σ) := by
    have hs := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ p * vcMaximalLog A U σ by nlinarith)
    simpa using hs
  have hsqrtp : Real.sqrt p ≤ Real.sqrt (p * vcMaximalLog A U σ) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hRnonneg : 0 ≤ R := hR0.le
  have hnroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  calc
    empiricalRademacherComplexity n F S ≤ _ := hbasic
    _ ≤ 26 / Real.sqrt (n : ℝ) * Real.sqrt (p * vcMaximalLog A U σ) * (R + σ) := by
      have h1 := mul_le_mul_of_nonneg_left hsqrtp hσ.le
      have h2 := mul_le_mul_of_nonneg_left hq1 hRnonneg
      field_simp
      nlinarith [Real.sqrt_nonneg (p * vcMaximalLog A U σ)]

end Causalean.Stat.Concentration
