import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.EmpiricalCover
import Causalean.Stat.Concentration.Covering.DudleyEntropy
import Causalean.Stat.Concentration.Covering.SqrtLogIntegral
import Causalean.Stat.Concentration.Covering.VCLocalizedRegime
import Causalean.Stat.Concentration.Rademacher.Contraction
import Causalean.Stat.Concentration.Rademacher.Symmetrization
import Causalean.Mathlib.Analysis.ClipInterval

/-!
# Variance-adaptive Rademacher chaining

This module contains the chaining core of the countable-class maximal
inequality.  It combines empirical `L²` polynomial covers with Dudley
chaining and a self-bounding empirical-radius argument, retaining the
population `L²` radius in the leading term.

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

private lemma empiricalRademacher_conditional_le
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

private lemma empiricalRademacherComplexity_measurable_countable
    [Countable ι] (F : ι → 𝒳 → ℝ) (hmeas : ∀ i, Measurable (F i)) (n : ℕ) :
    Measurable (fun S : Fin n → 𝒳 => empiricalRademacherComplexity n F S) := by
  unfold empiricalRademacherComplexity
  fun_prop

private lemma empiricalRademacherComplexity_mem_Icc
    [Nonempty ι]
    (F : ι → 𝒳 → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i x, |F i x| ≤ M)
    (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n F S ∈ Set.Icc 0 M := by
  classical
  letI : Nonempty (Signs n) := ⟨fun _ => ⟨1, by simp⟩⟩
  unfold empiricalRademacherComplexity
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun τ _ => by
      let i₀ : ι := Classical.choice inferInstance
      exact (abs_nonneg _).trans (le_ciSup (absInner_bddAbove F hM0 hM n S τ) i₀))
  · calc
      (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ τ : Signs n, ⨆ i, |(n : ℝ)⁻¹ * ∑ k, (τ k : ℝ) * F i (S k)|
          ≤ (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ _τ : Signs n, M := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) (by positivity)
            exact ciSup_le fun i => absInner_le_of_bound F hM0 hM n S τ i
      _ = M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcNat : 0 < Fintype.card (Signs n) := Fintype.card_pos
        have hc : (Fintype.card (Signs n) : ℝ) ≠ 0 := by exact_mod_cast hcNat.ne'
        field_simp

private noncomputable def empiricalL2Radius
    (F : ι → 𝒳 → ℝ) {n : ℕ} (S : Fin n → 𝒳) : ℝ :=
  ⨆ i, empiricalNorm S (F i)

private lemma empiricalL2Radius_measurable
    [Countable ι] (F : ι → 𝒳 → ℝ) (hmeas : ∀ i, Measurable (F i)) (n : ℕ) :
    Measurable (fun S : Fin n → 𝒳 => empiricalL2Radius F S) := by
  unfold empiricalL2Radius empiricalNorm
  fun_prop

private lemma empiricalL2Radius_mem_Icc
    [Nonempty ι]
    (F : ι → 𝒳 → ℝ) {U : ℝ} (hU0 : 0 ≤ U) (henvelope : ∀ i x, |F i x| ≤ U)
    {n : ℕ} (S : Fin n → 𝒳) : empiricalL2Radius F S ∈ Set.Icc 0 U := by
  have hbdd : BddAbove (Set.range fun i => empiricalNorm S (F i)) :=
    ⟨U, by rintro _ ⟨i, rfl⟩; exact empiricalNorm_le_of_envelope F hU0 henvelope S i⟩
  constructor
  · let i₀ : ι := Classical.choice inferInstance
    exact (by unfold empiricalNorm; positivity : 0 ≤ empiricalNorm S (F i₀)) |>.trans
      (le_ciSup hbdd i₀)
  · exact ciSup_le fun i => empiricalNorm_le_of_envelope F hU0 henvelope S i

private lemma clippedSquare_lipschitzAt0 {U : ℝ} (hU0 : 0 ≤ U) :
    LipschitzAt0 (fun x => (Causalean.Mathlib.Analysis.clipIcc (-U) U x) ^ 2) (2 * U) := by
  open Causalean.Mathlib.Analysis in
  constructor
  · simp [clipIcc, hU0]
  · intro x y
    let a := clipIcc (-U) U x
    let b := clipIcc (-U) U y
    have ha : |a| ≤ U := abs_clipIcc_neg_le hU0 x
    have hb : |b| ≤ U := abs_clipIcc_neg_le hU0 y
    have hab : |a - b| ≤ |x - y| := abs_clipIcc_sub_clipIcc_le (-U) U x y
    have habsum : |a + b| ≤ 2 * U := by
      calc |a + b| ≤ |a| + |b| := abs_add_le _ _
        _ ≤ 2 * U := by linarith
    rw [sq_sub_sq, abs_mul]
    calc
      |a + b| * |a - b| ≤ (2 * U) * |x - y| :=
        mul_le_mul habsum hab (abs_nonneg _) (by positivity)

private lemma empiricalL2Radius_sq_le_uniformDeviation
    [Nonempty ι]
    (P : Measure 𝒳) [IsProbabilityMeasure P]
    (F : ι → 𝒳 → ℝ) {U σ : ℝ}
    (hσ : 0 < σ) (hσU : σ < U)
    (hmeas : ∀ i, Measurable (F i))
    (henvelope : ∀ i x, |F i x| ≤ U)
    (hL2 : ∀ i, measureL2Dist P (F i) (fun _ => 0) ≤ σ)
    {n : ℕ} (hn : 0 < n) (S : Fin n → 𝒳) :
    empiricalL2Radius F S ^ 2 ≤ σ ^ 2 +
      uniformDeviation n (fun i x => F i x ^ 2) P id S := by
  classical
  have hU : 0 < U := hσ.trans hσU
  have hpop : ∀ i, ∫ x, F i x ^ 2 ∂P ≤ σ ^ 2 := by
    intro i
    have hi0 : 0 ≤ ∫ x, F i x ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    have hi := hL2 i
    unfold measureL2Dist at hi
    simp only [sub_zero] at hi
    calc
      (∫ x, F i x ^ 2 ∂P) = Real.sqrt (∫ x, F i x ^ 2 ∂P) ^ 2 :=
        (Real.sq_sqrt hi0).symm
      _ ≤ σ ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hσ.le).2 hi
  have havg : ∀ i, 0 ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 ∧
      (n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 ≤ U ^ 2 := by
    intro i
    constructor
    · positivity
    · calc
        (n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2
            ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, U ^ 2 := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
              rw [sq_le_sq]
              simpa [abs_of_pos hU] using henvelope i (S k)
        _ = U ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
          simp only [Fintype.card_fin]
          field_simp
  have hdevBdd : BddAbove (Set.range fun i =>
      |(n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 - ∫ x, F i x ^ 2 ∂P|) := by
    refine ⟨2 * U ^ 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    have hpop0 : 0 ≤ ∫ x, F i x ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    have hσU2 : σ ^ 2 ≤ U ^ 2 := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith [havg i, hpop i]
  let D := uniformDeviation n (fun i x => F i x ^ 2) P id S
  have hD0 : 0 ≤ D := by
    let i₀ : ι := Classical.choice inferInstance
    exact (abs_nonneg _).trans (le_ciSup hdevBdd i₀)
  have hnormsq : ∀ i, empiricalNorm S (F i) ^ 2 ≤ σ ^ 2 + D := by
    intro i
    have hdev : |(n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 - ∫ x, F i x ^ 2 ∂P| ≤ D :=
      le_ciSup hdevBdd i
    have heq : empiricalNorm S (F i) ^ 2 =
        (n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 := by
      unfold empiricalNorm
      simpa [one_div] using Real.sq_sqrt (havg i |>.1)
    rw [heq]
    linarith [le_abs_self ((n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) ^ 2 -
      ∫ x, F i x ^ 2 ∂P), hpop i]
  have hrad := empiricalL2Radius_mem_Icc F hU.le henvelope S
  have hB0 : 0 ≤ σ ^ 2 + D := add_nonneg (sq_nonneg _) hD0
  have hradle : empiricalL2Radius F S ≤ Real.sqrt (σ ^ 2 + D) := by
    unfold empiricalL2Radius
    refine ciSup_le fun i => ?_
    have hs := Real.sqrt_le_sqrt (hnormsq i)
    have hnorm0 : 0 ≤ empiricalNorm S (F i) := by unfold empiricalNorm; positivity
    rw [Real.sqrt_sq hnorm0] at hs
    exact hs
  change empiricalL2Radius F S ^ 2 ≤ σ ^ 2 + D
  nlinarith [Real.sq_sqrt hB0, hrad.1]

set_option maxHeartbeats 800000 in
/-- The expected absolute signed Rademacher supremum of a countable bounded
class with population `L²` radius `σ` and polynomial empirical `L²` entropy
is bounded by half the universal maximal-inequality constant times the
variance-adaptive two-term rate. -/
theorem varianceAdaptiveRademacherComplexity_le
    [Nonempty ι] [Countable ι]
    (P : Measure 𝒳) [IsProbabilityMeasure P]
    (F : ι → 𝒳 → ℝ) {U σ A v : ℝ}
    (hσ : 0 < σ) (hσU : σ < U) (hA : Real.exp 1 ≤ A) (hv : 1 ≤ v)
    (hmeas : ∀ i, Measurable (F i))
    (henvelope : ∀ i x, |F i x| ≤ U)
    (hL2 : ∀ i, measureL2Dist P (F i) (fun _ => 0) ≤ σ)
    (hcover : HasPolynomialEmpiricalL2Cover F U A v)
    (n : ℕ) (hn : 0 < n) :
    rademacherComplexity n F P id ≤
      (varianceAdaptiveVCConstant / 2) *
        vcExpectedMaximalRate U σ A v n := by
  /-
  Proof route:

  1. Anchor at one index and apply the existing signed Dudley theorem to the
     increment class (which contains zero).  Bound the anchor directly by
     its empirical `L²` norm.  This is the countable absolute-Dudley bridge;
     it avoids treating the signed theorem as if it already had an outer
     absolute value.
  2. Conditional on a sample, use `hcover` and
     `measureL2Dist_finiteSampleMeasure_eq_empiricalDist` to bound every
     empirical covering number at envelope-relative scales.
  3. Truncate Dudley's integral at a variable lower scale and at the random
     empirical radius `R_S = sup_f ‖f‖_{L²(Pₙ)}`.  Integrate the polynomial
     entropy bound to obtain a conditional estimate proportional to
     `R_S * sqrt (v * log (max e (A*U/R_S)) / n)` plus the truncation term.
  4. In the bounded-envelope specialization, symmetrization of the square
     class followed by `empiricalRademacherComplexity_contraction_abs_of_bddAbove`
     gives directly `E R_S² ≤ σ² + 8 U R_n(F)`; unlike the unbounded-envelope
     source proof, no Hoffmann–Jørgensen second-moment step is needed.  Solve the
     resulting quadratic inequality, producing the leading `σ` term and the
     second-order `U/n` term.

  All constants may be rounded upward to `varianceAdaptiveVCConstant / 2`.
  -/
  classical
  let μn : Measure (Fin n → 𝒳) := Measure.pi (fun _ : Fin n => P)
  have hU : 0 < U := hσ.trans hσU
  have hU0 : 0 ≤ U := hU.le
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 : 1 ≤ vcMaximalLog A U σ := by
    have hratio : Real.exp 1 < A * U / σ := by
      have hUσ : 1 < U / σ := (one_lt_div₀ hσ).2 hσU
      calc
        Real.exp 1 ≤ A := hA
        _ < A * (U / σ) := by nlinarith [Real.exp_pos 1]
        _ = A * U / σ := by ring
    rw [vcMaximalLog, max_eq_right hratio.le, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hratio.le
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hvL1 : 1 ≤ v * vcMaximalLog A U σ := by nlinarith
  let rad : (Fin n → 𝒳) → ℝ := fun S => empiricalRademacherComplexity n F S
  let radius : (Fin n → 𝒳) → ℝ := fun S => empiricalL2Radius F S
  let floorRadius : ℝ := U / (n : ℝ)
  let radius' : (Fin n → 𝒳) → ℝ := fun S => max (radius S) floorRadius
  have hradMeas : Measurable rad := empiricalRademacherComplexity_measurable_countable F hmeas n
  have hradiusMeas : Measurable radius := empiricalL2Radius_measurable F hmeas n
  have hradius'Meas : Measurable radius' := hradiusMeas.max measurable_const
  have hradMem : ∀ S, rad S ∈ Set.Icc 0 U := fun S =>
    empiricalRademacherComplexity_mem_Icc F hU0 henvelope n S
  have hradiusMem : ∀ S, radius S ∈ Set.Icc 0 U := fun S =>
    empiricalL2Radius_mem_Icc F hU0 henvelope S
  have hfloor0 : 0 < floorRadius := div_pos hU hnR
  have hfloorU : floorRadius ≤ U := by
    dsimp [floorRadius]
    apply (div_le_iff₀ hnR).2
    nlinarith
  have hradius'Mem : ∀ S, radius' S ∈ Set.Icc 0 U := by
    intro S
    exact ⟨le_max_of_le_right hfloor0.le, max_le (hradiusMem S).2 hfloorU⟩
  have hradInt : Integrable rad μn :=
    (integrable_const U).mono' hradMeas.aestronglyMeasurable
      (ae_of_all _ fun S => by simpa [Real.norm_eq_abs, abs_of_nonneg (hradMem S).1] using (hradMem S).2)
  have hradiusInt : Integrable radius μn :=
    (integrable_const U).mono' hradiusMeas.aestronglyMeasurable
      (ae_of_all _ fun S => by simpa [Real.norm_eq_abs, abs_of_nonneg (hradiusMem S).1] using (hradiusMem S).2)
  have hradius'Int : Integrable radius' μn :=
    (integrable_const U).mono' hradius'Meas.aestronglyMeasurable
      (ae_of_all _ fun S => by simpa [Real.norm_eq_abs, abs_of_nonneg (hradius'Mem S).1] using (hradius'Mem S).2)
  let q : ℝ := Real.sqrt (v * vcMaximalLog A U σ / (n : ℝ))
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hconditional : ∀ S, rad S ≤ 26 * q * (radius' S + σ) := by
    intro S
    have hri : ∀ i, empiricalNorm S (F i) ≤ radius' S := by
      intro i
      have hbdd : BddAbove (Set.range fun j => empiricalNorm S (F j)) :=
        ⟨U, by rintro _ ⟨j, rfl⟩; exact empiricalNorm_le_of_envelope F hU0 henvelope S j⟩
      exact (le_ciSup hbdd i).trans (le_max_left _ _)
    have hc := empiricalRademacher_conditional_le F hσ hσU hA hv hmeas henvelope
      hcover hn S hri (lt_of_lt_of_le hfloor0 (le_max_right _ _)) (hradius'Mem S).2
    have hsqrt : Real.sqrt (v * vcMaximalLog A U σ) / Real.sqrt (n : ℝ) = q := by
      dsimp [q]
      rw [Real.sqrt_div (mul_nonneg hv0 (zero_le_one.trans hL1))]
    calc
      rad S ≤ 26 / Real.sqrt (n : ℝ) * Real.sqrt (v * vcMaximalLog A U σ) *
          (radius' S + σ) := hc
      _ = 26 * q * (radius' S + σ) := by rw [← hsqrt]; ring
  have hrhsInt : Integrable (fun S => 26 * q * (radius' S + σ)) μn :=
    (hradius'Int.add (integrable_const σ)).const_mul _
  have hxchain : rademacherComplexity n F P id ≤
      26 * q * ((∫ S, radius' S ∂μn) + σ) := by
    unfold rademacherComplexity
    change (∫ S, rad S ∂μn) ≤ _
    calc
      (∫ S, rad S ∂μn) ≤ ∫ S, 26 * q * (radius' S + σ) ∂μn :=
        integral_mono hradInt hrhsInt hconditional
      _ = 26 * q * ((∫ S, radius' S ∂μn) + σ) := by
        rw [integral_const_mul]
        rw [integral_add hradius'Int (integrable_const σ)]
        simp [μn, smul_eq_mul]
  have hradius'Expectation : (∫ S, radius' S ∂μn) ≤
      (∫ S, radius S ∂μn) + floorRadius := by
    have hsumInt := hradiusInt.add (integrable_const floorRadius)
    calc
      (∫ S, radius' S ∂μn) ≤ ∫ S, radius S + floorRadius ∂μn := by
        apply integral_mono hradius'Int hsumInt
        intro S
        exact max_le_add_of_nonneg (hradiusMem S).1 hfloor0.le
      _ = (∫ S, radius S ∂μn) + floorRadius := by
        rw [integral_add hradiusInt (integrable_const floorRadius)]
        simp [μn]
  let sqF : ι → 𝒳 → ℝ := fun i x => F i x ^ 2
  have hsqMeas : ∀ i, Measurable (sqF i) := fun i => (hmeas i).pow_const 2
  have hsqEnv : ∀ i x, |sqF i x| ≤ U ^ 2 := by
    intro i x
    rw [abs_of_nonneg (sq_nonneg _), sq_le_sq]
    simpa [abs_of_pos hU] using henvelope i x
  have hsymm := uniform_deviation_expectation_le_two_smul_rademacher_complexity
    (μ := P) (f := sqF) hn id hsqMeas (sq_nonneg U) hsqEnv
  let φ : ℝ → ℝ := fun x => (Causalean.Mathlib.Analysis.clipIcc (-U) U x) ^ 2
  have hφeq : ∀ i x, φ (F i x) = sqF i x := by
    intro i x
    simp [φ, sqF, Causalean.Mathlib.Analysis.clipIcc_neg_eq_self (henvelope i x)]
  have hφMeas : ∀ i, Measurable (fun x => φ (F i x)) := fun i => by
    simpa [hφeq i] using hsqMeas i
  have hcontractPoint : ∀ S,
      empiricalRademacherComplexity n sqF S ≤ 4 * U * rad S := by
    intro S
    have hc := empiricalRademacherComplexity_contraction_abs_of_bddAbove φ
      (clippedSquare_lipschitzAt0 hU0) F hU0 henvelope n S
    have heq := empiricalRademacherComplexity_congr_sample n sqF (fun i x => φ (F i x)) S
      (fun i k => (hφeq i (S k)).symm)
    rw [heq]
    calc
      empiricalRademacherComplexity n (fun i x => φ (F i x)) S ≤
          2 * (2 * U) * empiricalRademacherComplexity n F S := hc
      _ = 4 * U * rad S := by simp only [rad]; ring
  have hsqRadMeas := empiricalRademacherComplexity_measurable_countable sqF hsqMeas n
  have hsqRadInt : Integrable (fun S => empiricalRademacherComplexity n sqF S) μn :=
    (integrable_const (U ^ 2)).mono' hsqRadMeas.aestronglyMeasurable
      (ae_of_all _ fun S => by
        have hm := empiricalRademacherComplexity_mem_Icc sqF (sq_nonneg U) hsqEnv n S
        simpa [Real.norm_eq_abs, abs_of_nonneg hm.1] using hm.2)
  have hcontractPop : rademacherComplexity n sqF P id ≤
      4 * U * rademacherComplexity n F P id := by
    unfold rademacherComplexity
    change (∫ S, empiricalRademacherComplexity n sqF S ∂μn) ≤
      4 * U * ∫ S, rad S ∂μn
    rw [← integral_const_mul]
    exact integral_mono hsqRadInt (hradInt.const_mul _) hcontractPoint
  have hdevExpectation :
      (∫ S, uniformDeviation n sqF P id S ∂μn) ≤
        8 * U * rademacherComplexity n F P id := by
    have hsymm' : (∫ S, uniformDeviation n sqF P id S ∂μn) ≤
        2 * rademacherComplexity n sqF P id := by
      simpa [μn, two_smul ℝ] using hsymm
    have hs := hsymm'.trans (mul_le_mul_of_nonneg_left hcontractPop
      (show (0 : ℝ) ≤ 2 by norm_num))
    convert hs using 1 <;> ring
  have hradiusSqMeas : Measurable (fun S => radius S ^ 2) := hradiusMeas.pow_const 2
  have hradiusSqInt : Integrable (fun S => radius S ^ 2) μn :=
    (integrable_const (U ^ 2)).mono' hradiusSqMeas.aestronglyMeasurable
      (ae_of_all _ fun S => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (sq_le_sq₀ (hradiusMem S).1 hU0).2 (hradiusMem S).2)
  have hdevMeas : Measurable (fun S => uniformDeviation n sqF P id S) :=
    uniformDeviation_measurable id hsqMeas
  have hdevInt : Integrable (fun S => uniformDeviation n sqF P id S) μn := by
    have hsqInt : ∀ i, Integrable (sqF i) P := fun i =>
      (integrable_const (U ^ 2)).mono' (hsqMeas i).aestronglyMeasurable
        (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hsqEnv i x)
    have hsqPop : ∀ i, (∫ x, sqF i x ∂P) ∈ Set.Icc 0 (U ^ 2) := by
      intro i
      constructor
      · exact integral_nonneg fun x => by exact sq_nonneg (F i x)
      · calc
          (∫ x, sqF i x ∂P) ≤ ∫ _x, U ^ 2 ∂P :=
            integral_mono (hsqInt i) (integrable_const (U ^ 2)) (fun x => by
              have := hsqEnv i x
              simpa [abs_of_nonneg (sq_nonneg (F i x)), sqF] using this)
          _ = U ^ 2 := by simp
    have hsqAvg : ∀ (T : Fin n → 𝒳) (i : ι),
        ((n : ℝ)⁻¹ * ∑ k : Fin n, sqF i (T k)) ∈ Set.Icc 0 (U ^ 2) := by
      intro T i
      constructor
      · positivity
      · dsimp [sqF]
        calc
          _ ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, U ^ 2 := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity)
            exact (sq_le_sq).2 (by simpa [abs_of_pos hU] using henvelope i (T k))
          _ = U ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            simp only [Fintype.card_fin]
            field_simp
    have hdevBound : ∀ S, uniformDeviation n sqF P id S ∈ Set.Icc 0 (2 * U ^ 2) := by
      intro S
      have hbdd : BddAbove (Set.range fun i =>
          |(n : ℝ)⁻¹ * ∑ k : Fin n, sqF i (S k) - ∫ x, sqF i x ∂P|) := by
        refine ⟨2 * U ^ 2, ?_⟩
        rintro _ ⟨i, rfl⟩
        have havg := hsqAvg S i
        have hpop := hsqPop i
        rw [abs_le]
        constructor <;> nlinarith [havg.1, havg.2, hpop.1, hpop.2, sq_nonneg U]
      constructor
      · let i₀ : ι := Classical.choice inferInstance
        unfold uniformDeviation
        exact (abs_nonneg _).trans (le_ciSup hbdd i₀)
      ·
        unfold uniformDeviation
        exact ciSup_le fun i => by
          have havg := hsqAvg S i
          have hpop := hsqPop i
          simp only [Function.comp_apply, id_eq]
          rw [abs_le]
          constructor <;> nlinarith [havg.1, havg.2, hpop.1, hpop.2, sq_nonneg U]
    exact (integrable_const (2 * U ^ 2)).mono' hdevMeas.aestronglyMeasurable
      (ae_of_all _ fun S => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (hdevBound S).1] using (hdevBound S).2)
  have hradiusSecond : (∫ S, radius S ^ 2 ∂μn) ≤
      σ ^ 2 + 8 * U * rademacherComplexity n F P id := by
    have hpoint := fun S => empiricalL2Radius_sq_le_uniformDeviation P F hσ hσU
      hmeas henvelope hL2 hn S
    calc
      (∫ S, radius S ^ 2 ∂μn) ≤ ∫ S, σ ^ 2 + uniformDeviation n sqF P id S ∂μn := by
        exact integral_mono hradiusSqInt ((integrable_const (σ ^ 2)).add hdevInt) hpoint
      _ = σ ^ 2 + ∫ S, uniformDeviation n sqF P id S ∂μn := by
        rw [integral_add (integrable_const (σ ^ 2)) hdevInt]
        simp [μn]
      _ ≤ _ := by linarith
  have hradiusExpectationNonneg : 0 ≤ ∫ S, radius S ∂μn :=
    integral_nonneg fun S => (hradiusMem S).1
  have hradiusVariance : (∫ S, radius S ∂μn) ^ 2 ≤ ∫ S, radius S ^ 2 ∂μn := by
    have hcenter0 : 0 ≤ ∫ S, (radius S - ∫ T, radius T ∂μn) ^ 2 ∂μn :=
      integral_nonneg fun S => sq_nonneg (radius S - ∫ T, radius T ∂μn)
    let c : ℝ := ∫ T, radius T ∂μn
    have hlinearInt : Integrable (fun S => (2 * c) * radius S) μn :=
      hradiusInt.const_mul (2 * c)
    have hsubInt : Integrable (fun S => radius S ^ 2 - (2 * c) * radius S) μn :=
      hradiusSqInt.sub hlinearInt
    have hexpand : (∫ S, (radius S - ∫ T, radius T ∂μn) ^ 2 ∂μn) =
        (∫ S, radius S ^ 2 ∂μn) - (∫ S, radius S ∂μn) ^ 2 := by
      change (∫ S, (radius S - c) ^ 2 ∂μn) =
        (∫ S, radius S ^ 2 ∂μn) - c ^ 2
      calc
        (∫ S, (radius S - c) ^ 2 ∂μn) =
            ∫ S, (radius S ^ 2 - (2 * c) * radius S) + c ^ 2 ∂μn := by
              apply integral_congr_ae
              filter_upwards
              intro S
              ring
        _ = (∫ S, radius S ^ 2 - (2 * c) * radius S ∂μn) +
              ∫ _S, c ^ 2 ∂μn := integral_add hsubInt (integrable_const _)
        _ = ((∫ S, radius S ^ 2 ∂μn) - ∫ S, (2 * c) * radius S ∂μn) +
              ∫ _S, c ^ 2 ∂μn := by rw [integral_sub hradiusSqInt hlinearInt]
        _ = (∫ S, radius S ^ 2 ∂μn) - c ^ 2 := by
              rw [integral_const_mul]
              simp [μn]
              ring
    rw [hexpand] at hcenter0
    linarith
  have hradiusExpectation : (∫ S, radius S ∂μn) ≤
      Real.sqrt (σ ^ 2 + 8 * U * rademacherComplexity n F P id) := by
    have hs := Real.sqrt_le_sqrt (hradiusVariance.trans hradiusSecond)
    rw [Real.sqrt_sq hradiusExpectationNonneg] at hs
    exact hs
  have hxNonneg : 0 ≤ rademacherComplexity n F P id := by
    unfold rademacherComplexity
    exact integral_nonneg fun S => (hradMem S).1
  have hself : rademacherComplexity n F P id ≤
      26 * q * (Real.sqrt (σ ^ 2 + 8 * U * rademacherComplexity n F P id) + σ + floorRadius) := by
    have hsum := add_le_add hradius'Expectation (le_refl σ)
    have hsum2 := add_le_add (add_le_add hradiusExpectation (le_refl floorRadius)) (le_refl σ)
    exact hxchain.trans (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by norm_num) hq0))
  have hsqrtSelf : Real.sqrt (σ ^ 2 + 8 * U * rademacherComplexity n F P id) ≤
      σ + Real.sqrt (8 * U * rademacherComplexity n F P id) := by
    have ha := sq_nonneg σ
    have hb : 0 ≤ 8 * U * rademacherComplexity n F P id :=
      mul_nonneg (mul_nonneg (by norm_num) hU0) hxNonneg
    have hs := Real.sqrt_le_sqrt (show σ ^ 2 + 8 * U * rademacherComplexity n F P id ≤
        (σ + Real.sqrt (8 * U * rademacherComplexity n F P id)) ^ 2 by
      nlinarith [Real.sq_sqrt hb, Real.sqrt_nonneg (8 * U * rademacherComplexity n F P id)])
    have hsum0 : 0 ≤ σ + Real.sqrt (8 * U * rademacherComplexity n F P id) := by positivity
    rw [Real.sqrt_sq hsum0] at hs
    exact hs
  have hyoung : 26 * q * Real.sqrt (8 * U * rademacherComplexity n F P id) ≤
      rademacherComplexity n F P id / 2 + 2704 * U * q ^ 2 := by
    have hsqrtprod : Real.sqrt (8 * U * rademacherComplexity n F P id) =
        Real.sqrt (8 * U) * Real.sqrt (rademacherComplexity n F P id) := by
      rw [Real.sqrt_mul (show 0 ≤ 8 * U by positivity)]
    rw [hsqrtprod]
    nlinarith [sq_nonneg (Real.sqrt (rademacherComplexity n F P id) -
      26 * q * Real.sqrt (8 * U)), Real.sq_sqrt hxNonneg,
      Real.sq_sqrt (show 0 ≤ 8 * U by positivity)]
  have hsolved : rademacherComplexity n F P id ≤
      104 * σ * q + 5408 * U * q ^ 2 + 52 * q * floorRadius := by
    have hinside : Real.sqrt (σ ^ 2 + 8 * U * rademacherComplexity n F P id) + σ + floorRadius ≤
        2 * σ + Real.sqrt (8 * U * rademacherComplexity n F P id) + floorRadius := by
      linarith [hsqrtSelf]
    have hs := hself.trans (mul_le_mul_of_nonneg_left hinside
      (mul_nonneg (by norm_num) hq0))
    nlinarith [hyoung]
  have hqSq : q ^ 2 = v * vcMaximalLog A U σ / (n : ℝ) := by
    dsimp [q]
    rw [Real.sq_sqrt]
    positivity
  have hfloorTerm : 52 * q * floorRadius ≤
      52 * U * (v * vcMaximalLog A U σ / (n : ℝ)) := by
    have hqle : q ≤ v * vcMaximalLog A U σ := by
      have hs := Real.sqrt_le_sqrt (show v * vcMaximalLog A U σ / (n : ℝ) ≤
          (v * vcMaximalLog A U σ) ^ 2 by
        have : 1 ≤ v * vcMaximalLog A U σ := hvL1
        apply (div_le_iff₀ hnR).2
        nlinarith)
      simpa [q, Real.sqrt_sq (zero_le_one.trans hvL1)] using hs
    dsimp [floorRadius]
    have hmul := mul_le_mul_of_nonneg_left hqle
      (show 0 ≤ 52 * U / (n : ℝ) by positivity)
    convert hmul using 1 <;> ring
  have hrate : rademacherComplexity n F P id ≤
      104 * (σ * q) + 5460 * (v * U * vcMaximalLog A U σ / (n : ℝ)) := by
    rw [hqSq] at hsolved
    have halg : 5408 * U * (v * vcMaximalLog A U σ / (n : ℝ)) +
        52 * U * (v * vcMaximalLog A U σ / (n : ℝ)) =
          5460 * (v * U * vcMaximalLog A U σ / (n : ℝ)) := by ring
    linarith
  unfold varianceAdaptiveVCConstant vcExpectedMaximalRate
  have hqdef : q = Real.sqrt (v * vcMaximalLog A U σ / (n : ℝ)) := rfl
  rw [← hqdef]
  have hlead0 : 0 ≤ σ * q := mul_nonneg hσ.le hq0
  have hsecond0 : 0 ≤ v * U * vcMaximalLog A U σ / (n : ℝ) := by positivity
  apply hrate.trans
  calc
    104 * (σ * q) + 5460 * (v * U * vcMaximalLog A U σ / (n : ℝ)) ≤
        8192 * (σ * q) + 8192 * (v * U * vcMaximalLog A U σ / (n : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_right (by norm_num) hlead0)
        (mul_le_mul_of_nonneg_right (by norm_num) hsecond0)
    _ = 16384 / 2 *
        (σ * q + v * U * vcMaximalLog A U σ / (n : ℝ)) := by ring

end Causalean.Stat.Concentration
