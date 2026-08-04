/-
# Regular-cell risk engine

Leaf lemmas for the honesty and variance half of the regular finite-cell
attainment argument.  The ambient covariate carrier remains arbitrary: every
finite calculation is scoped to the injected support supplied by
`RegularFiniteCellClass`.
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.InversionRisk
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.Witness
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_CompactCausalRange
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part1
import Causalean.Stat.Sample.EmpiricalMass

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ## Statistics and deterministic constants -/
/-- For the source-sample average weighted by target cell masses, this result gives its mean, an upper bound on its variance, and square integrability. The mean is the target-mass-weighted sum of the cell means. -/
lemma weighted_iid_average_mean_variance
    (P : TransportedArray 𝒳) (n : ℕ) (hn : 0 < n)
    [IsProbabilityMeasure (sourceObsLaw P n)]
    {m : ℕ} (cell : Fin m ↪ 𝒳)
    (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : sourceXLaw P n (Set.range cell) = 1)
    (targetMass : 𝒳 → ℝ) (G : SourceObs 𝒳 → ℝ)
    (a : 𝒳 → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hG : MemLp G 2 (sourceObsLaw P n))
    (hGbound : ∀ᵐ o ∂sourceObsLaw P n, |G o| ≤ C)
    (hqpos : ∀ i, 0 < sourceCellMass P n (cell i))
    (hmean : ∀ i,
      (∫ o in {o | o.1 = cell i}, G o ∂sourceObsLaw P n) /
          sourceCellMass P n (cell i) = a (cell i)) :
    let F := fun o : SourceObs 𝒳 =>
      (targetMass o.1 / sourceCellMass P n o.1) * G o
    (∫ sample : SourceSample 𝒳 n,
        (n : ℝ)⁻¹ * ∑ i, F (sample i)
        ∂Measure.pi (fun _ : Fin n => sourceObsLaw P n)) =
        ∑ i, targetMass (cell i) * a (cell i) ∧
    variance
        (fun sample : SourceSample 𝒳 n =>
          (n : ℝ)⁻¹ * ∑ i, F (sample i))
        (Measure.pi (fun _ : Fin n => sourceObsLaw P n)) ≤
      C ^ 2 / n * ∑ i,
        targetMass (cell i) ^ 2 / sourceCellMass P n (cell i) ∧
    MemLp
        (fun sample : SourceSample 𝒳 n =>
          (n : ℝ)⁻¹ * ∑ i, F (sample i)) 2
        (Measure.pi (fun _ : Fin n => sourceObsLaw P n)) := by
  classical
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  let μ := sourceObsLaw P n
  let q := sourceCellMass P n
  let coeff : Fin m → ℝ := fun i => targetMass (cell i) / q (cell i)
  let S : Fin m → Set (SourceObs 𝒳) := fun i => {o | o.1 = cell i}
  let F : SourceObs 𝒳 → ℝ := fun o => (targetMass o.1 / q o.1) * G o
  let B : SourceObs 𝒳 → ℝ := fun o =>
    ∑ i, coeff i * (S i).indicator G o
  have hS (i : Fin m) : MeasurableSet (S i) := by
    exact hcell i |>.preimage measurable_fst
  have hBmem : MemLp B 2 μ := by
    dsimp only [B]
    apply memLp_finset_sum
    intro i hi
    exact (hG.indicator (hS i)).const_mul (coeff i)
  have hrangeAE : ∀ᵐ o ∂μ, o.1 ∈ Set.range cell := by
    have hx : ∀ᵐ x ∂sourceXLaw P n, x ∈ Set.range cell := by
      change Set.range cell ∈ ae (sourceXLaw P n)
      rw [mem_ae_iff]
      have hrangeMeas : MeasurableSet (Set.range cell) := by
        rw [show Set.range cell = ⋃ i, {cell i} by
          ext x
          simp]
        exact MeasurableSet.iUnion hcell
      rw [measure_compl hrangeMeas (measure_ne_top _ _), hrange,
        measure_univ]
      simp
    unfold sourceXLaw at hx
    exact ae_of_ae_map measurable_fst.aemeasurable hx
  have hFB : F =ᵐ[μ] B := by
    filter_upwards [hrangeAE] with o ho
    obtain ⟨i, hi⟩ := ho
    dsimp only [F, B, coeff, S]
    rw [← hi]
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (show
          o ∈ {z : SourceObs 𝒳 | z.1 = cell i} by exact hi.symm)]
    · intro j hj hji
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      have hne : cell i ≠ cell j :=
        fun h => hji (cell.injective h.symm)
      have hneO : o.1 ≠ cell j := fun h => hne (hi.trans h)
      simp [hneO]
    · simp
  have hFmem : MemLp F 2 μ := by
    refine ⟨hBmem.1.congr hFB.symm, ?_⟩
    rw [eLpNorm_congr_ae hFB]
    exact hBmem.2
  have hBsq (o : SourceObs 𝒳) :
      B o ^ 2 =
        ∑ i, coeff i ^ 2 * (S i).indicator (fun z => G z ^ 2) o := by
    by_cases ho : o.1 ∈ Set.range cell
    · obtain ⟨i, hi⟩ := ho
      have hoi : o.1 = cell i := hi.symm
      dsimp only [B, coeff, S]
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single i]
        · simp only [Set.indicator_of_mem, Set.mem_setOf_eq, hoi]
          ring
        · intro j hj hji
          simp only [Set.indicator_apply, Set.mem_setOf_eq]
          have hne : o.1 ≠ cell j := fun h =>
            hji (cell.injective (hoi.symm.trans h).symm)
          simp [hne]
        · simp
      · intro j hj hji
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
        have hne : o.1 ≠ cell j := fun h =>
          hji (cell.injective (hoi.symm.trans h).symm)
        simp [hne]
      · simp
    · have hnot (i : Fin m) : o ∉ S i := by
        intro hi
        exact ho ⟨i, hi.symm⟩
      simp [B, hnot]
  have hsetMeasure (i : Fin m) :
      (μ (S i)).toReal = q (cell i) := by
    change
      (sourceObsLaw P n {o | o.1 = cell i}).toReal =
        (sourceXLaw P n {cell i}).toReal
    unfold sourceXLaw
    rw [Measure.map_apply measurable_fst (hcell i)]
    rfl
  have hsetSquare (i : Fin m) :
      (∫ o in S i, G o ^ 2 ∂μ) ≤ C ^ 2 * q (cell i) := by
    calc
      (∫ o in S i, G o ^ 2 ∂μ) ≤ ∫ _o in S i, C ^ 2 ∂μ := by
        apply integral_mono_ae
        · exact hG.integrable_sq.integrableOn
        · exact integrableOn_const
        · filter_upwards [ae_restrict_of_ae hGbound] with o ho
          have habs := (abs_le.mp ho)
          nlinarith [sq_nonneg (G o)]
      _ = C ^ 2 * q (cell i) := by
        rw [setIntegral_const]
        change (μ (S i)).toReal * C ^ 2 = C ^ 2 * q (cell i)
        rw [hsetMeasure]
        ring
  have hBsqInt :
      (∫ o, B o ^ 2 ∂μ) ≤
        C ^ 2 * ∑ i, targetMass (cell i) ^ 2 / q (cell i) := by
    simp_rw [hBsq]
    rw [integral_finset_sum]
    · calc
        ∑ i, ∫ o, coeff i ^ 2 *
              (S i).indicator (fun z => G z ^ 2) o ∂μ
            = ∑ i, coeff i ^ 2 * ∫ o in S i, G o ^ 2 ∂μ := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [integral_const_mul, integral_indicator (hS i)]
        _ ≤ ∑ i, coeff i ^ 2 * (C ^ 2 * q (cell i)) := by
              gcongr with i
              exact hsetSquare i
        _ = C ^ 2 * ∑ i,
              targetMass (cell i) ^ 2 / q (cell i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              dsimp only [coeff]
              field_simp [(hqpos i).ne']
              <;> ring
    · intro i hi
      exact
        ((hG.integrable_sq.indicator (hS i)).const_mul (coeff i ^ 2))
  have hFmean :
      (∫ o, F o ∂μ) = ∑ i, targetMass (cell i) * a (cell i) := by
    rw [integral_congr_ae hFB]
    dsimp only [B]
    rw [integral_finset_sum]
    · calc
        ∑ i, ∫ o, coeff i * (S i).indicator G o ∂μ =
            ∑ i, coeff i * ∫ o in S i, G o ∂μ := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [integral_const_mul, integral_indicator (hS i)]
        _ = ∑ i, targetMass (cell i) * a (cell i) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hm := hmean i
              dsimp only [coeff, q, S] at hm ⊢
              rw [div_eq_iff (hqpos i).ne'] at hm
              change targetMass (cell i) / sourceCellMass P n (cell i) *
                  (∫ o in {o | o.1 = cell i}, G o ∂sourceObsLaw P n) =
                targetMass (cell i) * a (cell i)
              rw [hm]
              field_simp [(hqpos i).ne']
    · intro i hi
      exact ((hG.integrable (by norm_num)).indicator (hS i)).const_mul (coeff i)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [F] using
      (iid_average_integral μ n hn F hFmem).trans hFmean
  · rw [iid_average_variance μ n hn F hFmem]
    calc
      (n : ℝ)⁻¹ * variance F μ ≤
          (n : ℝ)⁻¹ * ∫ o, F o ^ 2 ∂μ := by
        gcongr
        exact variance_le_expectation_sq hFmem.aestronglyMeasurable
      _ = (n : ℝ)⁻¹ * ∫ o, B o ^ 2 ∂μ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hFB] with o ho
        rw [ho]
      _ ≤ (n : ℝ)⁻¹ *
          (C ^ 2 * ∑ i, targetMass (cell i) ^ 2 / q (cell i)) := by
        gcongr
      _ = C ^ 2 / n *
          ∑ i, targetMass (cell i) ^ 2 / q (cell i) := by ring
  · apply MemLp.const_mul
    apply memLp_finset_sum
    intro i hi
    exact hFmem.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => μ) i)

/-- The second moment of a cell's empirical target mass equals the squared population cell mass plus its binomial sampling correction. -/
lemma integral_targetEmpiricalMass_sq
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m)
    (a : 𝒳) (ha : MeasurableSet {a}) :
    (∫ target : Fin m → 𝒳, targetEmpiricalMass target a ^ 2
        ∂Measure.pi (fun _ : Fin m => μ)) =
      μ.real {a} ^ 2 + (m : ℝ)⁻¹ * (μ.real {a} - μ.real {a} ^ 2) := by
  exact Causalean.Stat.integral_empiricalMass_sq μ hm a ha

/-- Conditional on a fixed target sample, the source mean and variance have
the paper's finite-cell expressions. -/
lemma regularCell_source_conditional_mean_variance_for_witness
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus theta : ℝ) (n : ℕ)
    (target : TargetSample 𝒳 (N n))
    (hn : 0 < n)
    (hIV : TransportedIVClass P N k c epsilon n)
    (hk : 0 < k n) (hcm : 0 < cminus)
    (hcmOne : cminus ≤ 1) (hcp : 1 ≤ cplus)
    (cell : Fin (k n) ↪ 𝒳)
    (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : sourceXLaw P n (Set.range cell) = 1)
    (hmass : ∀ i,
      cminus / (k n : ℝ) ≤ (sourceXLaw P n {cell i}).toReal ∧
      (sourceXLaw P n {cell i}).toReal ≤ cplus / (k n : ℝ))
    (htheta : theta ∈ parameterSpace) :
    let q := sourceCellMass P n
    let e := P.propensity n
    (∫ source, regularCellContrastMoment q e theta source target
        ∂Measure.pi (fun _ : Fin n => sourceObsLaw P n)) =
      ∑ i, targetEmpiricalMass target (cell i) *
        regularCellScoreMean P n theta (cell i) ∧
    variance
        (fun source => regularCellContrastMoment q e theta source target)
        (Measure.pi (fun _ : Fin n => sourceObsLaw P n)) ≤
      4 / (epsilon ^ 2 * n) *
        ∑ i, targetEmpiricalMass target (cell i) ^ 2 / q (cell i) ∧
    MemLp
        (fun source => regularCellContrastMoment q e theta source target) 2
        (Measure.pi (fun _ : Fin n => sourceObsLaw P n)) ∧
    (∀ i,
      (∫ o in {o | o.1 = cell i},
        regularCellScore e theta o ∂sourceObsLaw P n) / q (cell i) =
          regularCellScoreMean P n theta (cell i)) ∧
    MemLp (regularCellScore e theta) 2 (sourceObsLaw P n) ∧
    (∀ᵐ o ∂sourceObsLaw P n,
      |regularCellScore e theta o| ≤ 2 / epsilon) := by
  classical
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hqpos (i : Fin (k n)) :
      0 < sourceCellMass P n (cell i) := by
    exact lt_of_lt_of_le
      (div_pos hcm (by exact_mod_cast hk)) (hmass i).1
  have hInstrumentMeasurable : Measurable (instrumentScore P n) := by
    have hz : Measurable fun o : SourceObs 𝒳 => o.2.1 := by fun_prop
    have he : Measurable fun o : SourceObs 𝒳 => P.propensity n o.1 :=
      (P.propensity_measurable n).comp measurable_fst
    unfold instrumentScore
    exact Measurable.ite (hz (MeasurableSet.singleton true))
      (measurable_const.div he)
      (measurable_const.neg.div (measurable_const.sub he))
  have hInstrumentBound : ∀ᵐ o ∂sourceObsLaw P n,
      |instrumentScore P n o| ≤ 1 / epsilon := by
    have hOverlapObs : ∀ᵐ o ∂sourceObsLaw P n,
        epsilon ≤ P.propensity n o.1 ∧
          P.propensity n o.1 ≤ 1 - epsilon := by
      have hx := hIV.instrumentOverlap.2.2
      unfold sourceXLaw at hx
      exact ae_of_ae_map measurable_fst.aemeasurable hx
    filter_upwards [hOverlapObs] with o ho
    rcases o with ⟨x, z, d, y⟩
    cases z
    · simp only [instrumentScore, Bool.false_eq_true, ↓reduceIte, abs_neg,
        abs_div, abs_one]
      rw [abs_of_pos (sub_pos.mpr (lt_of_le_of_lt ho.2
        (by linarith [hIV.instrumentOverlap.1])))]
      exact one_div_le_one_div_of_le hIV.instrumentOverlap.1
        (by linarith [ho.2])
    · simp only [instrumentScore, ↓reduceIte, abs_div, abs_one]
      rw [abs_of_pos (lt_of_lt_of_le hIV.instrumentOverlap.1 ho.1)]
      exact one_div_le_one_div_of_le hIV.instrumentOverlap.1 ho.1
  have hBoolMeasurable :
      Measurable (fun o : SourceObs 𝒳 => boolReal o.2.2.1) := by
    unfold boolReal
    have hd : Measurable fun o : SourceObs 𝒳 => o.2.2.1 := by fun_prop
    exact Measurable.ite (hd (MeasurableSet.singleton true))
      measurable_const measurable_const
  have hOutcomeScoreIntegrable :
      Integrable (fun o => instrumentScore P n o * o.2.2.2)
        (sourceObsLaw P n) := by
    refine Integrable.of_bound
      (hInstrumentMeasurable.mul (by fun_prop)).aestronglyMeasurable
      (1 / epsilon) ?_
    filter_upwards [hInstrumentBound, (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.1]
      with o hs hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hy.1]
    exact (mul_le_mul hs hy.2 hy.1
      (one_div_nonneg.mpr hIV.instrumentOverlap.1.le)).trans_eq (mul_one _)
  have hReceiptScoreIntegrable :
      Integrable (fun o =>
        instrumentScore P n o * boolReal o.2.2.1)
        (sourceObsLaw P n) := by
    refine Integrable.of_bound
      (hInstrumentMeasurable.mul hBoolMeasurable).aestronglyMeasurable
      (1 / epsilon) ?_
    filter_upwards [hInstrumentBound] with o hs
    have hd : |boolReal o.2.2.1| ≤ 1 := by
      cases o.2.2.1 <;> simp [boolReal]
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul hs hd (abs_nonneg _)
      (one_div_nonneg.mpr hIV.instrumentOverlap.1.le)).trans_eq (mul_one _)
  have hmean (i : Fin (k n)) :
      (∫ o in {o | o.1 = cell i},
        regularCellScore (P.propensity n) theta o ∂sourceObsLaw P n) /
          sourceCellMass P n (cell i) =
        regularCellScoreMean P n theta (cell i) := by
    have hOutcomeSet :=
      (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.1
        ({cell i} : Set 𝒳) (hcell i)
    have hReceiptSet :=
      (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.2.1
        ({cell i} : Set 𝒳) (hcell i)
    have hscore :
        (∫ o in {o | o.1 = cell i},
          regularCellScore (P.propensity n) theta o ∂sourceObsLaw P n) =
          (∫ o in {o | o.1 ∈ ({cell i} : Set 𝒳)},
            instrumentScore P n o * o.2.2.2 ∂sourceObsLaw P n) -
          theta * (∫ o in {o | o.1 ∈ ({cell i} : Set 𝒳)},
            instrumentScore P n o * boolReal o.2.2.1
              ∂sourceObsLaw P n) := by
      change
        (∫ o in {o | o.1 ∈ ({cell i} : Set 𝒳)},
          instrumentScore P n o *
            (o.2.2.2 - theta * boolReal o.2.2.1)
            ∂sourceObsLaw P n) = _
      rw [show (fun o : SourceObs 𝒳 =>
          instrumentScore P n o *
            (o.2.2.2 - theta * boolReal o.2.2.1)) =
          (fun o => instrumentScore P n o * o.2.2.2 -
            theta * (instrumentScore P n o * boolReal o.2.2.1)) by
        funext o
        ring]
      rw [integral_sub hOutcomeScoreIntegrable.integrableOn
        (hReceiptScoreIntegrable.const_mul theta).integrableOn,
        integral_const_mul]
    rw [hscore, hOutcomeSet, hReceiptSet,
      integral_singleton' (P.deltaY_measurable n).stronglyMeasurable,
      integral_singleton' (P.deltaD_measurable n).stronglyMeasurable]
    change
      (sourceCellMass P n (cell i) * P.deltaY n (cell i) -
        theta * (sourceCellMass P n (cell i) * P.deltaD n (cell i))) /
          sourceCellMass P n (cell i) =
        P.deltaY n (cell i) - theta * P.deltaD n (cell i)
    field_simp [(hqpos i).ne']
  have hScoreMeas :
      Measurable (regularCellScore (P.propensity n) theta) := by
    change Measurable (fun o : SourceObs 𝒳 =>
      instrumentScore P n o *
        (o.2.2.2 - theta * boolReal o.2.2.1))
    have hyMeas : Measurable (fun o : SourceObs 𝒳 => o.2.2.2) := by
      fun_prop
    exact hInstrumentMeasurable.mul
      (hyMeas.sub (measurable_const.mul hBoolMeasurable))
  have hScoreBound : ∀ᵐ o ∂sourceObsLaw P n,
      |regularCellScore (P.propensity n) theta o| ≤ 2 / epsilon := by
    have hOverlapObs : ∀ᵐ o ∂sourceObsLaw P n,
        epsilon ≤ P.propensity n o.1 ∧
          P.propensity n o.1 ≤ 1 - epsilon := by
      have hx := hIV.instrumentOverlap.2.2
      unfold sourceXLaw at hx
      exact ae_of_ae_map measurable_fst.aemeasurable hx
    filter_upwards [hOverlapObs, (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.1] with o he hy
    exact abs_regularCellScore_le (P.propensity n) epsilon theta o
      hIV.instrumentOverlap.1 he htheta hy
  have hScoreMem :
      MemLp (regularCellScore (P.propensity n) theta) 2
        (sourceObsLaw P n) :=
    MemLp.of_bound hScoreMeas.aestronglyMeasurable (2 / epsilon)
      (hScoreBound.mono fun o ho => by simpa [Real.norm_eq_abs] using ho)
  obtain ⟨hMean, hVar, hSourceMem⟩ :=
    weighted_iid_average_mean_variance P n hn cell hcell hrange
      (targetEmpiricalMass target)
      (regularCellScore (P.propensity n) theta)
      (regularCellScoreMean P n theta) (2 / epsilon)
      (div_nonneg (by norm_num) hIV.instrumentOverlap.1.le)
      hScoreMem hScoreBound hqpos hmean
  refine ⟨?_, ?_, ?_, hmean, hScoreMem, hScoreBound⟩
  · simpa only [regularCell_crossAverage_identity] using hMean
  · simp only [regularCell_crossAverage_identity]
    calc
      variance
          (fun source : SourceSample 𝒳 n =>
            (n : ℝ)⁻¹ * ∑ i,
              (targetEmpiricalMass target (source i).1 /
                  sourceCellMass P n (source i).1) *
                regularCellScore (P.propensity n) theta (source i))
          (Measure.pi (fun _ : Fin n => sourceObsLaw P n)) ≤
          (2 / epsilon) ^ 2 / n *
            ∑ i, targetEmpiricalMass target (cell i) ^ 2 /
              sourceCellMass P n (cell i) := hVar
      _ = 4 / (epsilon ^ 2 * n) *
            ∑ i, targetEmpiricalMass target (cell i) ^ 2 /
              sourceCellMass P n (cell i) := by
          congr 1
          field_simp [hIV.instrumentOverlap.1.ne']
          <;> ring
  · simpa only [regularCell_crossAverage_identity] using hSourceMem

/-- Conditional on a fixed target sample, the source mean and variance have
the paper's finite-cell expressions. -/
lemma regularCell_source_conditional_mean_variance
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus theta : ℝ) (n : ℕ)
    (target : TargetSample 𝒳 (N n))
    (hn : 0 < n)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n)
    (htheta : theta ∈ parameterSpace) :
    let q := sourceCellMass P n
    let e := P.propensity n
    ∃ cell : Fin (k n) ↪ 𝒳,
      (∫ source, regularCellContrastMoment q e theta source target
          ∂Measure.pi (fun _ : Fin n => sourceObsLaw P n)) =
        ∑ i, targetEmpiricalMass target (cell i) *
          regularCellScoreMean P n theta (cell i) ∧
      variance
          (fun source => regularCellContrastMoment q e theta source target)
          (Measure.pi (fun _ : Fin n => sourceObsLaw P n)) ≤
        4 / (epsilon ^ 2 * n) *
          ∑ i, targetEmpiricalMass target (cell i) ^ 2 / q (cell i) := by
  rcases hP with
    ⟨hIV, hk, hcminus, hcminus_one, hcplus, cell, hcell, hrange, hmass⟩
  have h := regularCell_source_conditional_mean_variance_for_witness
    P N k c epsilon cminus cplus theta n target hn hIV hk hcminus
    hcminus_one hcplus cell hcell hrange hmass htheta
  exact ⟨cell, h.1, h.2.1⟩

end CausalSmith.Stat.TransportedLateStrengthFrontier
