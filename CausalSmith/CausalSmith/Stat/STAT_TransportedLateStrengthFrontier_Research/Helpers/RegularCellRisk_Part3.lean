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
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part2
import Causalean.Mathlib.Probability.VarianceProd

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ## Statistics and deterministic constants -/
/-- At the target CACE, randomness of the target empirical score mean
contributes at most `4 / N`. -/
lemma regularCell_target_score_mean_variance_for_witness
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hIV : TransportedIVClass P N k c epsilon n)
    (hk : 0 < k n) (hcminus : 0 < cminus)
    (hcminus_one : cminus ≤ 1) (hcplus : 1 ≤ cplus)
    (cell : Fin (k n) ↪ 𝒳)
    (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : sourceXLaw P n (Set.range cell) = 1)
    (hmass : ∀ i,
      cminus / (k n : ℝ) ≤ (sourceXLaw P n {cell i}).toReal ∧
      (sourceXLaw P n {cell i}).toReal ≤ cplus / (k n : ℝ)) :
    variance
      (fun target : TargetSample 𝒳 (N n) =>
        ∑ i, targetEmpiricalMass target (cell i) *
          regularCellScoreMean P n (targetCACE P n) (cell i))
      (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) ≤
        4 / (N n : ℝ) ∧
    MemLp
      (fun target : TargetSample 𝒳 (N n) =>
        ∑ i, targetEmpiricalMass target (cell i) *
          regularCellScoreMean P n (targetCACE P n) (cell i)) 2
      (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) ∧
    (∫ target : TargetSample 𝒳 (N n),
        ∑ i, targetEmpiricalMass target (cell i) *
          regularCellScoreMean P n (targetCACE P n) (cell i)
        ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) = 0 := by
  classical
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hIV.twoSampleArray.2.2.1 n
  have hAssignmentInt :
      Integrable (P.assignmentContrast n true) (sourceXLaw P n) :=
    integrable_of_finite_support (sourceXLaw P n) cell hcell hrange
      _ (P.assignmentContrast_measurable n true).stronglyMeasurable
  have hReceiptInt :
      Integrable (P.receiptContrast n true) (sourceXLaw P n) :=
    integrable_of_finite_support (sourceXLaw P n) cell hcell hrange
      _ (P.receiptContrast_measurable n true).stronglyMeasurable
  rcases compact_causal_range P N k c epsilon n
      hAssignmentInt hReceiptInt hIV with
    ⟨hDeltaYEq, hDeltaDEq, hOutcomeEq, hFirstEq, hRatio, hTheta⟩
  have hsourcePos (i : Fin (k n)) :
      0 < (sourceXLaw P n {cell i}).toReal := by
    exact lt_of_lt_of_le
      (div_pos hcminus (by exact_mod_cast hk)) (hmass i).1
  have hcellBound (i : Fin (k n)) :
      |regularCellScoreMean P n (targetCACE P n) (cell i)| ≤ 2 := by
    have hy := property_at_of_ae_of_singleton_pos
      (sourceXLaw P n) (fun x => P.deltaY n x ∈ Set.Icc (-1 : ℝ) 1)
      (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.1 (hsourcePos i)
    have hd := property_at_of_ae_of_singleton_pos
      (sourceXLaw P n) (fun x => P.deltaD n x ∈ Set.Icc (0 : ℝ) 1)
      (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.2.2 (hsourcePos i)
    have hthetaAbs : |targetCACE P n| ≤ 1 := (abs_le).2 hTheta
    have hyAbs : |P.deltaY n (cell i)| ≤ 1 := (abs_le).2 hy
    have hdAbs : |P.deltaD n (cell i)| ≤ 1 := by
      rw [abs_of_nonneg hd.1]
      exact hd.2
    unfold regularCellScoreMean
    calc
      |P.deltaY n (cell i) -
          targetCACE P n * P.deltaD n (cell i)| ≤
          |P.deltaY n (cell i)| +
            |targetCACE P n| * |P.deltaD n (cell i)| := by
        simpa [abs_mul] using
          (abs_sub (P.deltaY n (cell i))
            (targetCACE P n * P.deltaD n (cell i)))
      _ ≤ 1 + 1 * 1 := by gcongr
      _ = 2 := by norm_num
  let B : 𝒳 → ℝ := fun x =>
    if hx : x ∈ Set.range cell
    then regularCellScoreMean P n (targetCACE P n) x else 0
  have hrangeMeas : MeasurableSet (Set.range cell) := by
    rw [show Set.range cell = ⋃ i, {cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion hcell
  have hBMeas : Measurable B := by
    dsimp [B]
    exact Measurable.ite hrangeMeas
      ((P.deltaY_measurable n).sub
        (measurable_const.mul (P.deltaD_measurable n)))
      measurable_const
  have hBBound : ∀ x, |B x| ≤ 2 := by
    intro x
    by_cases hx : x ∈ Set.range cell
    · obtain ⟨i, rfl⟩ := hx
      simpa [B] using hcellBound i
    · simp only [B, dif_neg hx, abs_zero]
      norm_num
  have hBMem : MemLp B 2 (targetXLaw P n) :=
    MemLp.of_bound hBMeas.aestronglyMeasurable 2
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hBBound x)
  by_cases hNzero : N n = 0
  · rw [hNzero]
    refine ⟨?_, ?_, ?_⟩
    · simp [targetEmpiricalMass, Causalean.Stat.empiricalMass, variance, evariance]
    · simp [targetEmpiricalMass, Causalean.Stat.empiricalMass]
    · simp [targetEmpiricalMass, Causalean.Stat.empiricalMass]
  have hNpos : 0 < N n := Nat.pos_of_ne_zero hNzero
  have hstat :
      (fun target : TargetSample 𝒳 (N n) =>
        ∑ i, targetEmpiricalMass target (cell i) *
          regularCellScoreMean P n (targetCACE P n) (cell i)) =
      (fun target => (N n : ℝ)⁻¹ * ∑ j, B (target j)) := by
    funext target
    unfold targetEmpiricalMass Causalean.Stat.empiricalMass
    calc
      _ =
          ∑ i, ∑ j, (N n : ℝ)⁻¹ *
            (if target j = cell i then 1 else 0) *
            regularCellScoreMean P n (targetCACE P n) (cell i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ j, ∑ i, (N n : ℝ)⁻¹ *
            (if target j = cell i then 1 else 0) *
            regularCellScoreMean P n (targetCACE P n) (cell i) := by
        rw [Finset.sum_comm]
      _ = ∑ j, (N n : ℝ)⁻¹ * B (target j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        congr 1
        by_cases hx : target j ∈ Set.range cell
        · obtain ⟨i, hi⟩ := hx
          rw [← hi]
          rw [Finset.sum_eq_single i]
          · simp [B]
          · intro i' hi' hne
            have htargetne : target j ≠ cell i' := by
              rw [← hi]
              exact fun h => hne (cell.injective h.symm)
            have hcellne : cell i ≠ cell i' :=
              fun h => hne (cell.injective h).symm
            rw [if_neg hcellne]
            simp
          · simp
        · have hne : ∀ i, target j ≠ cell i := by
            intro i hEq
            exact hx ⟨i, hEq.symm⟩
          have hne' : ∀ i, cell i ≠ target j :=
            fun i hEq => hne i hEq.symm
          simp [B, hx, hne, hne']
      _ = (N n : ℝ)⁻¹ * ∑ j, B (target j) := by
        rw [Finset.mul_sum]
  have hAvgMem :
      MemLp (fun target : TargetSample 𝒳 (N n) =>
        (N n : ℝ)⁻¹ * ∑ j, B (target j)) 2
        (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) := by
    apply MemLp.const_mul
    apply memLp_finset_sum
    intro j hj
    exact hBMem.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin (N n) => targetXLaw P n) j)
  refine ⟨?_, ?_, ?_⟩
  · rw [hstat, iid_average_variance
      (targetXLaw P n) (N n) hNpos B hBMem]
    calc
      (N n : ℝ)⁻¹ * variance B (targetXLaw P n) ≤
          (N n : ℝ)⁻¹ *
            ∫ x, B x ^ 2 ∂targetXLaw P n := by
        gcongr
        exact variance_le_expectation_sq hBMeas.aestronglyMeasurable
      _ ≤ (N n : ℝ)⁻¹ * 4 := by
        gcongr
        calc
          (∫ x, B x ^ 2 ∂targetXLaw P n) ≤ ∫ _x, (4 : ℝ)
              ∂targetXLaw P n := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun x => sq_nonneg (B x)
            · exact integrable_const 4
            · exact Filter.Eventually.of_forall fun x => by
                have hb := (abs_le).1 (hBBound x)
                nlinarith
          _ = 4 := by simp
      _ = 4 / (N n : ℝ) := by ring
  · rw [hstat]
    exact hAvgMem
  · rw [hstat, iid_average_integral
      (targetXLaw P n) (N n) hNpos B hBMem]
    have hrangeCompl : sourceXLaw P n (Set.range cell)ᶜ = 0 := by
      rw [measure_compl hrangeMeas (measure_ne_top _ _), hrange, measure_univ]
      simp
    have htargetRange :
        ∀ᵐ x ∂targetXLaw P n, x ∈ Set.range cell := by
      have hc := hIV.transportDomination hrangeCompl
      change Set.range cell ∈ ae (targetXLaw P n)
      rw [mem_ae_iff]
      exact hc
    have hBScore :
        B =ᵐ[targetXLaw P n]
          regularCellScoreMean P n (targetCACE P n) := by
      filter_upwards [htargetRange] with x hx
      dsimp only [B]
      rw [dif_pos hx]
    rw [integral_congr_ae hBScore]
    have hDeltaYTargetInt :
        Integrable (P.deltaY n) (targetXLaw P n) := by
      refine Integrable.of_bound
        (P.deltaY_measurable n).aestronglyMeasurable 1 ?_
      apply hIV.transportDomination.ae_le
      filter_upwards [(sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.1] with x hx
      simpa [Real.norm_eq_abs] using (show |P.deltaY n x| ≤ 1 from
        (abs_le).2 hx)
    have hDeltaDTargetInt :
        Integrable (P.deltaD n) (targetXLaw P n) := by
      refine Integrable.of_bound
        (P.deltaD_measurable n).aestronglyMeasurable 1 ?_
      apply hIV.transportDomination.ae_le
      filter_upwards [(sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.2.2] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    have hOutcomeTarget :
        (∫ x, P.deltaY n x ∂targetXLaw P n) =
          transportedOutcomeITT P n := by
      simpa [transportedOutcomeITT, transportWeight, smul_eq_mul] using
        (integral_rnDeriv_smul
          (μ := targetXLaw P n) (ν := sourceXLaw P n)
          (f := P.deltaY n) hIV.transportDomination).symm
    have hFirstTarget :
        (∫ x, P.deltaD n x ∂targetXLaw P n) =
          transportedFirstStage P n := by
      rw [transportedFirstStage_eq_weighted_deltaD P k epsilon n
        (sourceObservationFacts_of_class P N k c epsilon n hIV)
        hIV.instrumentOverlap hIV.weightEnvelope]
      simpa [transportWeight, smul_eq_mul] using
        (integral_rnDeriv_smul
          (μ := targetXLaw P n) (ν := sourceXLaw P n)
          (f := P.deltaD n) hIV.transportDomination).symm
    simp only [regularCellScoreMean]
    rw [integral_sub hDeltaYTargetInt
        (hDeltaDTargetInt.const_mul (targetCACE P n)),
      integral_const_mul, hOutcomeTarget, hFirstTarget]
    have hfirstPos : 0 < transportedFirstStage P n := by
      rw [hFirstEq]
      exact hIV.targetComplierPositivity
    rw [div_eq_iff hfirstPos.ne'] at hRatio
    linarith

/-- At the target CACE, randomness of the target empirical score mean
contributes at most `4 / N`. -/
lemma regularCell_target_score_mean_variance
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    ∃ cell : Fin (k n) ↪ 𝒳,
      variance
        (fun target : TargetSample 𝒳 (N n) =>
          ∑ i, targetEmpiricalMass target (cell i) *
            regularCellScoreMean P n (targetCACE P n) (cell i))
        (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) ≤
          4 / (N n : ℝ) := by
  rcases hP with
    ⟨hIV, hk, hcminus, hcminus_one, hcplus, cell, hcell, hrange, hmass⟩
  exact ⟨cell, (regularCell_target_score_mean_variance_for_witness
    P N k c epsilon cminus cplus n hIV hk hcminus hcminus_one hcplus
    cell hcell hrange hmass).1⟩

/-- Exact multinomial second moment and its regular-cell upper bound. -/
lemma regularCell_multinomial_second_moment_for_witness
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hNpos : 0 < N n)
    (hIV : TransportedIVClass P N k c epsilon n)
    (hk : 0 < k n) (hcminus : 0 < cminus)
    (hcminus_one : cminus ≤ 1) (hcplus : 1 ≤ cplus)
    (cell : Fin (k n) ↪ 𝒳)
    (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : sourceXLaw P n (Set.range cell) = 1)
    (hmass : ∀ i,
      cminus / (k n : ℝ) ≤ (sourceXLaw P n {cell i}).toReal ∧
      (sourceXLaw P n {cell i}).toReal ≤ cplus / (k n : ℝ)) :
    (∫ target : TargetSample 𝒳 (N n),
        ∑ i, targetEmpiricalMass target (cell i) ^ 2 /
          sourceCellMass P n (cell i)
        ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) =
      kishDispersion P n +
        (N n : ℝ)⁻¹ *
          ∑ i, ((targetXLaw P n {cell i}).toReal -
              (targetXLaw P n {cell i}).toReal ^ 2) /
            sourceCellMass P n (cell i) ∧
    (∫ target : TargetSample 𝒳 (N n),
        ∑ i, targetEmpiricalMass target (cell i) ^ 2 /
          sourceCellMass P n (cell i)
        ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) ≤
      kishDispersion P n +
        (k n : ℝ) / (cminus * (N n : ℝ)) ∧
    Integrable
      (fun target : TargetSample 𝒳 (N n) =>
        ∑ i, targetEmpiricalMass target (cell i) ^ 2 /
          sourceCellMass P n (cell i))
      (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) := by
  classical
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hIV.twoSampleArray.2.2.1 n
  let μTarget :=
    Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
  have hsourcePos (i : Fin (k n)) :
      0 < sourceCellMass P n (cell i) := by
    exact lt_of_lt_of_le
      (div_pos hcminus (by exact_mod_cast hk)) (hmass i).1
  have hphatMem (i : Fin (k n)) :
      MemLp (fun target : TargetSample 𝒳 (N n) =>
        targetEmpiricalMass target (cell i)) 2 μTarget := by
    unfold targetEmpiricalMass Causalean.Stat.empiricalMass
    apply MemLp.const_mul
    apply memLp_finset_sum
    intro j hj
    refine MemLp.of_bound ?_ 1 ?_
    · have hjmeas : Measurable fun target :
          TargetSample 𝒳 (N n) => target j :=
        measurable_pi_apply j
      exact
        (Measurable.ite (hjmeas (hcell i))
          measurable_const measurable_const).aestronglyMeasurable
    · filter_upwards with target
      split_ifs <;> simp
  have hintegrable (i : Fin (k n)) :
      Integrable (fun target : TargetSample 𝒳 (N n) =>
        targetEmpiricalMass target (cell i) ^ 2 /
          sourceCellMass P n (cell i)) μTarget := by
    have hsquare := (hphatMem i).integrable_sq
    have hmul := hsquare.const_mul
      (sourceCellMass P n (cell i))⁻¹
    simpa [div_eq_mul_inv, mul_comm] using hmul
  have hmoment :
      (∫ target : TargetSample 𝒳 (N n),
          ∑ i, targetEmpiricalMass target (cell i) ^ 2 /
            sourceCellMass P n (cell i) ∂μTarget) =
        ∑ i, ((targetXLaw P n {cell i}).toReal ^ 2 +
          (N n : ℝ)⁻¹ *
            ((targetXLaw P n {cell i}).toReal -
              (targetXLaw P n {cell i}).toReal ^ 2)) /
            sourceCellMass P n (cell i) := by
    rw [integral_finset_sum _ (fun i _ => hintegrable i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_div,
      integral_targetEmpiricalMass_sq (targetXLaw P n) hNpos
        (cell i) (hcell i)]
    simp [measureReal_def]
  have hrnStrong :
      StronglyMeasurable
        (fun x => ((targetXLaw P n).rnDeriv (sourceXLaw P n) x).toReal) :=
    (Measure.measurable_rnDeriv (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
      |>.stronglyMeasurable
  have hratio (i : Fin (k n)) :
      transportWeight P n (cell i) =
        (targetXLaw P n {cell i}).toReal /
          sourceCellMass P n (cell i) := by
    have hRN :=
      Measure.setIntegral_toReal_rnDeriv'
        hIV.transportDomination (hcell i)
    rw [integral_singleton' hrnStrong] at hRN
    apply (eq_div_iff (hsourcePos i).ne').2
    simpa [transportWeight, sourceCellMass, measureReal_def, mul_comm] using hRN
  have hmeasure :
      sourceXLaw P n =
        ∑ i, sourceXLaw P n {cell i} • Measure.dirac (cell i) :=
    measure_eq_fin_sum_smul_dirac_of_range
      (sourceXLaw P n) cell hcell hrange
  have hweightStrong :
      StronglyMeasurable (fun x => (transportWeight P n x) ^ 2) :=
    ((Measure.measurable_rnDeriv (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
      |>.pow_const 2).stronglyMeasurable
  have hkish :
      kishDispersion P n =
        ∑ i, (targetXLaw P n {cell i}).toReal ^ 2 /
          sourceCellMass P n (cell i) := by
    rw [kishDispersion, hmeasure, integral_finset_sum_measure]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_smul_measure, integral_dirac' _ _ hweightStrong]
      simp only [smul_eq_mul]
      change
        sourceCellMass P n (cell i) * transportWeight P n (cell i) ^ 2 =
          (targetXLaw P n {cell i}).toReal ^ 2 /
            sourceCellMass P n (cell i)
      rw [hratio i]
      field_simp [(hsourcePos i).ne']
    · intro i hi
      exact
        (integrable_dirac' hweightStrong (by simp)).smul_measure
          (measure_ne_top (sourceXLaw P n) {cell i})
  have hsplit :
      (∑ i, ((targetXLaw P n {cell i}).toReal ^ 2 +
          (N n : ℝ)⁻¹ *
            ((targetXLaw P n {cell i}).toReal -
              (targetXLaw P n {cell i}).toReal ^ 2)) /
            sourceCellMass P n (cell i)) =
        (∑ i, (targetXLaw P n {cell i}).toReal ^ 2 /
          sourceCellMass P n (cell i)) +
        (N n : ℝ)⁻¹ *
          ∑ i, ((targetXLaw P n {cell i}).toReal -
            (targetXLaw P n {cell i}).toReal ^ 2) /
              sourceCellMass P n (cell i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [(hsourcePos i).ne']
  refine ⟨?_, ?_, ?_⟩
  · rw [hmoment, hsplit, ← hkish]
  · rw [hmoment, hsplit, ← hkish]
    have hrangeMeas : MeasurableSet (Set.range cell) := by
      rw [show Set.range cell = ⋃ i, {cell i} by
        ext x
        simp]
      exact MeasurableSet.iUnion hcell
    have hsourceCompl : sourceXLaw P n (Set.range cell)ᶜ = 0 := by
      rw [measure_compl hrangeMeas (measure_ne_top _ _), hrange, measure_univ]
      simp
    have htargetCompl : targetXLaw P n (Set.range cell)ᶜ = 0 :=
      hIV.transportDomination hsourceCompl
    have htargetRange : targetXLaw P n (Set.range cell) = 1 :=
      (measure_of_measure_compl_eq_zero htargetCompl).trans measure_univ
    have hpsum :
        ∑ i, (targetXLaw P n {cell i}).toReal = 1 := by
      have htargetMeasure :=
        measure_eq_fin_sum_smul_dirac_of_range
          (targetXLaw P n) cell hcell htargetRange
      have hu := congrArg (fun μ : Measure 𝒳 => μ Set.univ)
        htargetMeasure
      simp only [measure_univ, Measure.finset_sum_apply,
        Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
        Set.mem_univ, if_true, Pi.one_apply, mul_one] at hu
      have hu' : (1 : ENNReal) =
          ∑ i, targetXLaw P n {cell i} := by
        simpa [Set.indicator_of_mem, smul_eq_mul] using hu
      have huReal := congrArg ENNReal.toReal hu'
      rw [ENNReal.toReal_sum
        (fun _ _ => measure_ne_top (targetXLaw P n) _)] at huReal
      simpa using huReal.symm
    have hcorr :
        ∑ i, ((targetXLaw P n {cell i}).toReal -
            (targetXLaw P n {cell i}).toReal ^ 2) /
          sourceCellMass P n (cell i) ≤
        (k n : ℝ) / cminus := by
      calc
        _ ≤ ∑ i, (targetXLaw P n {cell i}).toReal *
            ((k n : ℝ) / cminus) := by
          apply Finset.sum_le_sum
          intro i hi
          have hp0 : 0 ≤ (targetXLaw P n {cell i}).toReal :=
            ENNReal.toReal_nonneg
          have hp1 : (targetXLaw P n {cell i}).toReal ≤ 1 :=
            measureReal_le_one
          have hnum :
              (targetXLaw P n {cell i}).toReal -
                  (targetXLaw P n {cell i}).toReal ^ 2 ≤
                (targetXLaw P n {cell i}).toReal := by
            nlinarith [sq_nonneg (targetXLaw P n {cell i}).toReal]
          rw [div_le_iff₀ (hsourcePos i)]
          have hkreal : 0 < (k n : ℝ) := by exact_mod_cast hk
          have hq := (hmass i).1
          have hkq :
              cminus ≤ (k n : ℝ) *
                sourceCellMass P n (cell i) := by
            change cminus ≤ (k n : ℝ) *
              (sourceXLaw P n {cell i}).toReal
            rw [div_le_iff₀ hkreal] at hq
            nlinarith
          have hone :
              1 ≤ ((k n : ℝ) / cminus) *
                sourceCellMass P n (cell i) := by
            calc
              1 ≤ ((k n : ℝ) *
                    sourceCellMass P n (cell i)) / cminus := by
                exact (le_div_iff₀ hcminus).2 (by simpa using hkq)
              _ = ((k n : ℝ) / cminus) *
                    sourceCellMass P n (cell i) := by ring
          calc
            (targetXLaw P n {cell i}).toReal -
                (targetXLaw P n {cell i}).toReal ^ 2 ≤
                (targetXLaw P n {cell i}).toReal := hnum
            _ ≤ (targetXLaw P n {cell i}).toReal *
                (((k n : ℝ) / cminus) *
                  sourceCellMass P n (cell i)) :=
              by simpa using mul_le_mul_of_nonneg_left hone hp0
            _ = (targetXLaw P n {cell i}).toReal *
                ((k n : ℝ) / cminus) *
                  sourceCellMass P n (cell i) := by ring
        _ = (k n : ℝ) / cminus := by rw [← Finset.sum_mul, hpsum, one_mul]
    calc
      kishDispersion P n + (N n : ℝ)⁻¹ *
          ∑ i, ((targetXLaw P n {cell i}).toReal -
            (targetXLaw P n {cell i}).toReal ^ 2) /
              sourceCellMass P n (cell i) ≤
          kishDispersion P n + (N n : ℝ)⁻¹ *
          ((k n : ℝ) / cminus) := by
        gcongr
      _ = kishDispersion P n +
          (k n : ℝ) / (cminus * (N n : ℝ)) := by
        field_simp [hcminus.ne', (Nat.cast_pos.mpr hNpos).ne']
  · exact integrable_finset_sum _ (fun i _ => hintegrable i)

/-- Exact multinomial second moment and its regular-cell upper bound. -/
lemma regularCell_multinomial_second_moment
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hNpos : 0 < N n)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    ∃ cell : Fin (k n) ↪ 𝒳,
      (∫ target : TargetSample 𝒳 (N n),
          ∑ i, targetEmpiricalMass target (cell i) ^ 2 /
            sourceCellMass P n (cell i)
          ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) =
        kishDispersion P n +
          (N n : ℝ)⁻¹ *
            ∑ i, ((targetXLaw P n {cell i}).toReal -
                (targetXLaw P n {cell i}).toReal ^ 2) /
              sourceCellMass P n (cell i) ∧
      (∫ target : TargetSample 𝒳 (N n),
          ∑ i, targetEmpiricalMass target (cell i) ^ 2 /
            sourceCellMass P n (cell i)
          ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) ≤
        kishDispersion P n +
          (k n : ℝ) / (cminus * (N n : ℝ)) := by
  rcases hP with
    ⟨hIV, hk, hcminus, hcminus_one, hcplus, cell, hcell, hrange, hmass⟩
  have h := regularCell_multinomial_second_moment_for_witness
    P N k c epsilon cminus cplus n hNpos hIV hk hcminus hcminus_one
    hcplus cell hcell hrange hmass
  exact ⟨cell, h.1, h.2.1⟩

/-! ## R1.7: eventual uniform two-sample variance -/

/-- The variance of a statistic based on two independent samples equals its average conditional variance given the second sample plus the variance of its conditional mean. -/
lemma variance_prod_eq_integral_variance_add
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (μ : Measure Ω) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω × T → ℝ) (m : T → ℝ)
    (hF : MemLp F 2 (μ.prod ν))
    (hsection : ∀ t, MemLp (fun s => F (s, t)) 2 μ)
    (hm : MemLp m 2 ν)
    (hmean : ∀ t, (∫ s, F (s, t) ∂μ) = m t) :
    variance F (μ.prod ν) =
      (∫ t, variance (fun s => F (s, t)) μ ∂ν) +
        variance m ν := by
  exact Causalean.Mathlib.Probability.variance_prod_eq_integral_variance_add
    μ ν F m hF (Filter.Eventually.of_forall hsection) hm
    (Filter.Eventually.of_forall hmean)

/-- The weighted cross-sample average is almost-everywhere strongly measurable under the joint two-sample distribution. -/
lemma weighted_cross_aestronglyMeasurable
    (P : TransportedArray 𝒳) (N : ℕ → ℕ) (n : ℕ)
    [IsProbabilityMeasure (sourceObsLaw P n)]
    [IsProbabilityMeasure (targetXLaw P n)]
    {m : ℕ} (cell : Fin m ↪ 𝒳)
    (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : sourceXLaw P n (Set.range cell) = 1)
    (G : SourceObs 𝒳 → ℝ) (hG : Measurable G) :
    AEStronglyMeasurable
      (fun s : TwoSample 𝒳 n (N n) =>
        (n : ℝ)⁻¹ * ∑ r,
          (targetEmpiricalMass s.2 (s.1 r).1 /
            sourceCellMass P n (s.1 r).1) * G (s.1 r))
      (twoSampleLaw P N n) := by
  classical
  let μS := Measure.pi (fun _ : Fin n => sourceObsLaw P n)
  let μT := Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
  let q := sourceCellMass P n
  let S : Fin m → Set (SourceObs 𝒳) := fun i => {o | o.1 = cell i}
  let B : TwoSample 𝒳 n (N n) → ℝ := fun s =>
    (n : ℝ)⁻¹ * ∑ r, ∑ i,
      (targetEmpiricalMass s.2 (cell i) / q (cell i)) *
        (S i).indicator G (s.1 r)
  have hS (i : Fin m) : MeasurableSet (S i) :=
    (hcell i).preimage measurable_fst
  have hphat (i : Fin m) :
      Measurable (fun target : TargetSample 𝒳 (N n) =>
        targetEmpiricalMass target (cell i)) := by
    unfold targetEmpiricalMass Causalean.Stat.empiricalMass
    apply measurable_const.mul
    refine Finset.measurable_fun_sum Finset.univ fun j hj => ?_
    have hjm : Measurable fun target : TargetSample 𝒳 (N n) => target j :=
      measurable_pi_apply j
    exact Measurable.ite (hjm (hcell i)) measurable_const measurable_const
  have hB : Measurable B := by
    dsimp only [B]
    apply measurable_const.mul
    refine Finset.measurable_fun_sum Finset.univ fun r hr => ?_
    refine Finset.measurable_fun_sum Finset.univ fun i hi => ?_
    have ht : Measurable (fun s : TwoSample 𝒳 n (N n) =>
        targetEmpiricalMass s.2 (cell i) / q (cell i)) :=
      ((hphat i).comp measurable_snd).div measurable_const
    have heval : Measurable (fun s : TwoSample 𝒳 n (N n) => s.1 r) :=
      (measurable_pi_apply r).comp measurable_fst
    exact ht.mul ((hG.indicator (hS i)).comp heval)
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hRangeObs : ∀ᵐ o ∂sourceObsLaw P n, o.1 ∈ Set.range cell := by
    have hx : ∀ᵐ x ∂sourceXLaw P n, x ∈ Set.range cell := by
      change Set.range cell ∈ ae (sourceXLaw P n)
      rw [mem_ae_iff]
      have hm : MeasurableSet (Set.range cell) := by
        rw [show Set.range cell = ⋃ i, {cell i} by
          ext x
          simp]
        exact MeasurableSet.iUnion hcell
      rw [measure_compl hm (measure_ne_top _ _), hrange, measure_univ]
      simp
    unfold sourceXLaw at hx
    exact ae_of_ae_map measurable_fst.aemeasurable hx
  have hRangeSample :
      ∀ᵐ source ∂μS, ∀ r, (source r).1 ∈ Set.range cell := by
    rw [ae_all_iff]
    intro r
    have hx : ∀ᵐ o ∂Measure.map (fun source : SourceSample 𝒳 n => source r) μS,
        o.1 ∈ Set.range cell := by
      rw [(measurePreserving_eval
        (fun _ : Fin n => sourceObsLaw P n) r).map_eq]
      exact hRangeObs
    exact ae_of_ae_map (measurable_pi_apply r).aemeasurable hx
  have hEqSource : ∀ᵐ source ∂μS, ∀ target,
      (n : ℝ)⁻¹ * ∑ r,
          (targetEmpiricalMass target (source r).1 / q (source r).1) *
            G (source r) =
        B (source, target) := by
    filter_upwards [hRangeSample] with source hs
    intro target
    dsimp only [B]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    obtain ⟨i, hi⟩ := hs r
    rw [← hi]
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (show source r ∈ S i by
        change (source r).1 = cell i
        exact hi.symm)]
    · intro j hj hji
      simp only [Set.indicator_apply]
      have hnot : source r ∉ S j := by
        intro hmem
        exact hji (cell.injective (show cell j = cell i by
          exact hmem.symm.trans hi.symm))
      simp [hnot]
    · simp
  have hEqProd :
      (fun s : TwoSample 𝒳 n (N n) =>
        (n : ℝ)⁻¹ * ∑ r,
          (targetEmpiricalMass s.2 (s.1 r).1 / q (s.1 r).1) *
            G (s.1 r)) =ᵐ[μS.prod μT] B := by
    have hx : ∀ᵐ source ∂Measure.map
        (fun s : TwoSample 𝒳 n (N n) => s.1) (μS.prod μT),
        ∀ target, (n : ℝ)⁻¹ * ∑ r,
          (targetEmpiricalMass target (source r).1 / q (source r).1) *
            G (source r) = B (source, target) := by
      rw [(show MeasurePreserving
          (fun s : TwoSample 𝒳 n (N n) => s.1) (μS.prod μT) μS from
        measurePreserving_fst).map_eq]
      exact hEqSource
    filter_upwards
      [ae_of_ae_map measurable_fst.aemeasurable hx] with s hs
    exact hs s.2
  unfold twoSampleLaw
  exact hB.aestronglyMeasurable.congr hEqProd.symm

end CausalSmith.Stat.TransportedLateStrengthFrontier
