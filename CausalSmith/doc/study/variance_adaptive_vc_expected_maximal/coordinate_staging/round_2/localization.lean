import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.Chaining

/-!
# Variance-adaptive Rademacher localization

This module localizes the chaining bound through the empirical `L²` radius.
It combines symmetrization of the squared class with a contraction argument
to derive the variance-sensitive expected Rademacher maximal inequality.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory
open scoped BigOperators

universe u v

variable {𝒳 : Type u} [MeasurableSpace 𝒳] {ι : Type v}

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
