import Causalean.Stat.Concentration.TailBounds.BinomialCount
import Causalean.Stat.Sample

/-!
# Sharp relative concentration for bounded functions

A direct bounded-`[0,1]` Chernoff argument gives simultaneous two-sided
relative comparisons for a finite class.  The moment-generating-function chain
it rests on lives in `Causalean.Stat.Concentration`
(`exp_mul_le_secant`, `mgf_le_of_mem_Icc_zero_one`,
`boundedCount_mgf_le_integral`); this file only adds the union bound and the
finite-class packaging.
-/

noncomputable section

namespace CausalSmith.Substrate

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- The logarithmic part of the sharp relative-comparison remainder. -/
def relativeLogRemainder (n : ℕ) (N zeta : ℝ) : ℝ :=
  8 / (3 * n) * Real.log (2 * N / zeta)

private lemma sampleMean_nonneg
    (S : Causalean.Stat.IIDSample Ω X μ P)
    {f : X → ℝ} (h01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (ω : Ω) :
    0 ≤ S.sampleMean f n ω := by
  unfold Causalean.Stat.IIDSample.sampleMean
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => (h01 (S.Z i ω)).1)

/-- For a measurable `[0,1]`-valued function, either relative comparison can
fail with probability at most `exp(-3*n*a/8)` when `a≥0`. -/
theorem relative_fixed_function_bad_le
    (S : Causalean.Stat.IIDSample Ω X μ P)
    {f : X → ℝ} (hf : Measurable f)
    (h01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a) :
    μ.real
      ({ω | 2 * S.sampleMean f n ω + a < ∫ x, f x ∂P} ∪
       {ω | 2 * (∫ x, f x ∂P) + a < S.sampleMean f n ω}) ≤
      2 * Real.exp (-(3 * n * a / 8)) := by
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let m : ℝ := ∫ x, f x ∂P
  have hm0 : 0 ≤ m := integral_nonneg_of_ae
    (ae_of_all _ fun x => (h01 x).1)
  have hlog0 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hlog38 : (3 : ℝ) / 8 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hsum_meas :
      Measurable (fun ω => ∑ i ∈ Finset.range n, f (S.Z i ω)) :=
    Finset.measurable_fun_sum _ fun i _ => hf.comp (S.meas i)
  have hupper :
      μ.real {ω | 2 * m + a < S.sampleMean f n ω} ≤
        Real.exp (-(3 * n * a / 8)) := by
    let q : ℝ := (n : ℝ) * (2 * m + a)
    have hint : Integrable
        (fun ω => Real.exp (Real.log 2 *
          ∑ i ∈ Finset.range n, f (S.Z i ω))) μ := by
      refine Integrable.of_bound
        ((hsum_meas.const_mul _).exp.aestronglyMeasurable)
        (Real.exp (Real.log 2 * n)) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hlog0
      calc
        (∑ i ∈ Finset.range n, f (S.Z i ω)) ≤
            ∑ _i ∈ Finset.range n, (1 : ℝ) := by
          gcongr with i hi
          exact (h01 (S.Z i ω)).2
        _ = n := by simp
    have hmgf := Causalean.Stat.Concentration.boundedCount_mgf_le_integral
      S hf h01 n (Real.log 2)
    unfold Causalean.Stat.Concentration.bernoulliCount at hmgf
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hmgf
    have hmgf' :
        mgf (fun ω => ∑ i ∈ Finset.range n, f (S.Z i ω)) μ
            (Real.log 2) ≤ Real.exp ((n : ℝ) * m) := by
      calc
        _ ≤ Real.exp ((n : ℝ) * (m * ((2 : ℝ) - 1))) := by
          simpa [m] using hmgf
        _ = Real.exp ((n : ℝ) * m) := by congr 1 <;> ring
    have hsubset :
        {ω | 2 * m + a < S.sampleMean f n ω} ⊆
          {ω | q ≤ ∑ i ∈ Finset.range n, f (S.Z i ω)} := by
      intro ω hω
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      unfold Causalean.Stat.IIDSample.sampleMean at hω
      change 2 * m + a <
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (S.Z i ω) at hω
      dsimp [q]
      have hmul : 0 < (n : ℝ) *
          ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (S.Z i ω) -
            (2 * m + a)) :=
        mul_pos hnR (sub_pos.mpr hω)
      have heq :
          (n : ℝ) * ((n : ℝ)⁻¹ *
            ∑ i ∈ Finset.range n, f (S.Z i ω)) =
            ∑ i ∈ Finset.range n, f (S.Z i ω) := by
        field_simp
      nlinarith
    calc
      μ.real {ω | 2 * m + a < S.sampleMean f n ω} ≤
          μ.real {ω | q ≤ ∑ i ∈ Finset.range n, f (S.Z i ω)} :=
        measureReal_mono hsubset
      _ ≤ Real.exp (-Real.log 2 * q) *
          mgf (fun ω => ∑ i ∈ Finset.range n, f (S.Z i ω)) μ
            (Real.log 2) :=
        measure_ge_le_exp_mul_mgf q hlog0 hint
      _ ≤ Real.exp (-Real.log 2 * q) *
          Real.exp ((n : ℝ) * m) := by
        exact mul_le_mul_of_nonneg_left hmgf' (Real.exp_pos _).le
      _ = Real.exp (-Real.log 2 * q + (n : ℝ) * m) := by
        rw [← Real.exp_add]
      _ ≤ Real.exp (-(3 * n * a / 8)) := by
        apply Real.exp_le_exp.mpr
        dsimp [q]
        have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        have hc : 1 - 2 * Real.log 2 ≤ 0 := by
          linarith [Real.log_two_gt_d9]
        have hcm : (1 - 2 * Real.log 2) * m ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hc hm0
        have hloga : (3 / 8 : ℝ) * a ≤ Real.log 2 * a :=
          mul_le_mul_of_nonneg_right hlog38 ha
        nlinarith
  have hlower :
      μ.real {ω | 2 * S.sampleMean f n ω + a < m} ≤
        Real.exp (-(3 * n * a / 8)) := by
    by_cases hma : m ≤ a
    · have hempty : {ω | 2 * S.sampleMean f n ω + a < m} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hω
        linarith [sampleMean_nonneg S h01 n ω]
      rw [hempty, measureReal_empty]
      positivity
    · have ham : a < m := lt_of_not_ge hma
      let q : ℝ := (n : ℝ) * (m - a) / 2
      have hlogneg : -Real.log (2 : ℝ) ≤ 0 := neg_nonpos.mpr hlog0
      have hint : Integrable
          (fun ω => Real.exp (-Real.log 2 *
            ∑ i ∈ Finset.range n, f (S.Z i ω))) μ := by
        refine Integrable.of_bound
          ((hsum_meas.const_mul _).exp.aestronglyMeasurable)
          1 (ae_of_all _ fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc
          Real.exp (-Real.log 2 *
              ∑ i ∈ Finset.range n, f (S.Z i ω)) ≤ Real.exp 0 := by
            apply Real.exp_le_exp.mpr
            exact mul_nonpos_of_nonpos_of_nonneg hlogneg
              (Finset.sum_nonneg fun i _ => (h01 (S.Z i ω)).1)
          _ = 1 := Real.exp_zero
      have hmgf := Causalean.Stat.Concentration.boundedCount_mgf_le_integral
        S hf h01 n (-Real.log 2)
      unfold Causalean.Stat.Concentration.bernoulliCount at hmgf
      have hexp : Real.exp (-Real.log (2 : ℝ)) = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [hexp] at hmgf
      have hmgf' :
          mgf (fun ω => ∑ i ∈ Finset.range n, f (S.Z i ω)) μ
              (-Real.log 2) ≤ Real.exp (-((n : ℝ) * m) / 2) := by
        calc
          _ ≤ Real.exp ((n : ℝ) * (m * ((1 : ℝ) / 2 - 1))) := by
            simpa [m] using hmgf
          _ = Real.exp (-((n : ℝ) * m) / 2) := by congr 1 <;> ring
      have hsubset :
          {ω | 2 * S.sampleMean f n ω + a < m} ⊆
            {ω | (∑ i ∈ Finset.range n, f (S.Z i ω)) ≤ q} := by
        intro ω hω
        have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
        unfold Causalean.Stat.IIDSample.sampleMean at hω
        change 2 * ((n : ℝ)⁻¹ *
          ∑ i ∈ Finset.range n, f (S.Z i ω)) + a < m at hω
        dsimp [q]
        have hpre :
            2 * ((n : ℝ)⁻¹ *
              ∑ i ∈ Finset.range n, f (S.Z i ω)) < m - a := by
          linarith
        have hmul : 0 < (n : ℝ) *
            ((m - a) - 2 * ((n : ℝ)⁻¹ *
              ∑ i ∈ Finset.range n, f (S.Z i ω))) :=
          mul_pos hnR (sub_pos.mpr hpre)
        have heq :
            (n : ℝ) * ((n : ℝ)⁻¹ *
              ∑ i ∈ Finset.range n, f (S.Z i ω)) =
              ∑ i ∈ Finset.range n, f (S.Z i ω) := by
          field_simp
        nlinarith
      calc
        μ.real {ω | 2 * S.sampleMean f n ω + a < m} ≤
            μ.real {ω |
              (∑ i ∈ Finset.range n, f (S.Z i ω)) ≤ q} :=
          measureReal_mono hsubset
        _ ≤ Real.exp (-(-Real.log 2) * q) *
            mgf (fun ω => ∑ i ∈ Finset.range n, f (S.Z i ω)) μ
              (-Real.log 2) :=
          measure_le_le_exp_mul_mgf q hlogneg hint
        _ ≤ Real.exp (-(-Real.log 2) * q) *
            Real.exp (-((n : ℝ) * m) / 2) := by
          exact mul_le_mul_of_nonneg_left hmgf' (Real.exp_pos _).le
        _ = Real.exp
            (-(-Real.log 2) * q - ((n : ℝ) * m) / 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-(3 * n * a / 8)) := by
          apply Real.exp_le_exp.mpr
          dsimp [q]
          have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
          have hc : Real.log 2 - 1 ≤ 0 := by
            linarith [Real.log_two_lt_d9]
          have hcm :
              (Real.log 2 - 1) * (m - a) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hc (sub_nonneg.mpr ham.le)
          nlinarith
  calc
    μ.real
        ({ω | 2 * S.sampleMean f n ω + a < m} ∪
         {ω | 2 * m + a < S.sampleMean f n ω}) ≤
        μ.real {ω | 2 * S.sampleMean f n ω + a < m} +
        μ.real {ω | 2 * m + a < S.sampleMean f n ω} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-(3 * n * a / 8)) +
        Real.exp (-(3 * n * a / 8)) := add_le_add hlower hupper
    _ = 2 * Real.exp (-(3 * n * a / 8)) := by ring

/-- A finite class of measurable `[0,1]`-valued functions satisfies both
relative comparisons with logarithmic remainder `8/(3n) log(2N/zeta)`.
The case `zeta≥1` is discharged directly. -/
theorem finite_relative_comparison_core
    (S : Causalean.Stat.IIDSample Ω X μ P)
    (H : Finset (X → ℝ))
    (hmeas : ∀ h ∈ H, Measurable h)
    (h01 : ∀ h ∈ H, ∀ x, h x ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (hn : 0 < n) (zeta : ℝ) (hzeta : 0 < zeta) :
    μ.real {ω | ∀ h ∈ H,
      (∫ x, h x ∂P) ≤
          2 * S.sampleMean h n ω +
            relativeLogRemainder n H.card zeta ∧
      S.sampleMean h n ω ≤
          2 * (∫ x, h x ∂P) +
            relativeLogRemainder n H.card zeta} ≥
      1 - zeta := by
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let a := relativeLogRemainder n H.card zeta
  by_cases hz1 : 1 ≤ zeta
  · exact le_trans (by linarith) (measureReal_nonneg)
  by_cases hH : H = ∅
  · subst H
    simp [probReal_univ]
    exact hzeta.le
  have hcard : 0 < H.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hH)
  have hratio : 1 < 2 * (H.card : ℝ) / zeta := by
    have hzlt : zeta < 1 := lt_of_not_ge hz1
    have hcardR : 1 ≤ (H.card : ℝ) := by exact_mod_cast hcard
    apply (lt_div_iff₀ hzeta).2
    nlinarith
  have ha : 0 ≤ a := by
    unfold a relativeLogRemainder
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    exact mul_nonneg (by positivity)
      (Real.log_nonneg (le_of_lt hratio))
  let bad : (X → ℝ) → Set Ω := fun h =>
    {ω | 2 * S.sampleMean h n ω + a < ∫ x, h x ∂P} ∪
    {ω | 2 * (∫ x, h x ∂P) + a < S.sampleMean h n ω}
  have hbad (h : X → ℝ) (hh : h ∈ H) :
      μ.real (bad h) ≤ zeta / H.card := by
    calc
      μ.real (bad h) ≤ 2 * Real.exp (-(3 * n * a / 8)) :=
        relative_fixed_function_bad_le S (hmeas h hh) (h01 h hh)
          n hn a ha
      _ = zeta / H.card := by
        unfold a relativeLogRemainder
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        have hzN : (2 * (H.card : ℝ) / zeta) ≠ 0 := by positivity
        rw [show -(3 * (n : ℝ) *
            (8 / (3 * (n : ℝ)) *
              Real.log (2 * (H.card : ℝ) / zeta)) / 8) =
            -Real.log (2 * (H.card : ℝ) / zeta) by field_simp]
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  have hunion :
      μ.real (⋃ h ∈ H, bad h) ≤ zeta := by
    calc
      μ.real (⋃ h ∈ H, bad h) ≤ ∑ h ∈ H, μ.real (bad h) :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _h ∈ H, zeta / H.card := by
        gcongr with h hh
        exact hbad h hh
      _ = zeta := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcR : (H.card : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
        field_simp
  have hbadmeas : MeasurableSet (⋃ h ∈ H, bad h) := by
    exact H.measurableSet_biUnion fun h hh => by
      change MeasurableSet
        ({ω | 2 * S.sampleMean h n ω + a < ∫ x, h x ∂P} ∪
         {ω | 2 * (∫ x, h x ∂P) + a < S.sampleMean h n ω})
      have hsm : Measurable (S.sampleMean h n) := by
        unfold Causalean.Stat.IIDSample.sampleMean
        exact (Finset.measurable_sum _
          (fun i _ => (hmeas h hh).comp (S.meas i))).const_mul _
      apply MeasurableSet.union
      · exact measurableSet_lt
          (hsm.const_mul 2 |>.add_const a) measurable_const
      · exact measurableSet_lt measurable_const
          hsm
  have hgood :
      {ω | ∀ h ∈ H,
        (∫ x, h x ∂P) ≤ 2 * S.sampleMean h n ω + a ∧
        S.sampleMean h n ω ≤ 2 * (∫ x, h x ∂P) + a} =
      (⋃ h ∈ H, bad h)ᶜ := by
    ext ω
    simp [bad, not_lt, and_comm, and_left_comm, and_assoc]
  rw [show relativeLogRemainder n H.card zeta = a from rfl, hgood,
    measureReal_compl hbadmeas, probReal_univ]
  linarith

/-- Exact finite-union form with the requested additional `3/n` slack. -/
theorem finite_relative_comparison
    (S : Causalean.Stat.IIDSample Ω X μ P)
    (H : Finset (X → ℝ))
    (hmeas : ∀ h ∈ H, Measurable h)
    (h01 : ∀ h ∈ H, ∀ x, h x ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (hn : 0 < n) (zeta : ℝ) (hzeta : 0 < zeta) :
    μ.real {ω | ∀ h ∈ H,
      (∫ x, h x ∂P) ≤
          2 * S.sampleMean h n ω +
            relativeLogRemainder n H.card zeta + 3 / n ∧
      S.sampleMean h n ω ≤
          2 * (∫ x, h x ∂P) +
            relativeLogRemainder n H.card zeta + 3 / n} ≥
      1 - zeta := by
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hcore :=
    finite_relative_comparison_core S H hmeas h01 n hn zeta hzeta
  apply hcore.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω h hh
  have hn0 : 0 ≤ (3 : ℝ) / n := by positivity
  exact ⟨(hω h hh).1.trans (by linarith),
    (hω h hh).2.trans (by linarith)⟩

end CausalSmith.Substrate
