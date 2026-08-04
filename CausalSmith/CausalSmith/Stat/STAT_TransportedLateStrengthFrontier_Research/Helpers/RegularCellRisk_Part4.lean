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
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part3
import Causalean.Stat.Sample.EmpiricalMass

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ## Statistics and deterministic constants -/
/-- For a transported-IV distribution supported on the regular cells, the Kish dispersion of the transport weights is at least one. -/
lemma one_le_regularCell_kish
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon : ℝ) (n : ℕ)
    (hIV : TransportedIVClass P N k c epsilon n)
    {m : ℕ} (cell : Fin m ↪ 𝒳)
    (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : sourceXLaw P n (Set.range cell) = 1) :
    1 ≤ kishDispersion P n := by
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hIV.twoSampleArray.2.2.1 n
  have hwStrong : StronglyMeasurable (transportWeight P n) := by
    exact
      (Measure.measurable_rnDeriv (targetXLaw P n)
        (sourceXLaw P n)).ennreal_toReal.stronglyMeasurable
  have hwSqInt :
      Integrable (fun x => transportWeight P n x ^ 2) (sourceXLaw P n) :=
    integrable_of_finite_support (sourceXLaw P n) cell hcell hrange _
      (hwStrong.pow 2)
  have hwMem : MemLp (transportWeight P n) 2 (sourceXLaw P n) :=
    (memLp_two_iff_integrable_sq hwStrong.aestronglyMeasurable).2 hwSqInt
  have hwMean :
      (∫ x, transportWeight P n x ∂sourceXLaw P n) = 1 := by
    simpa [transportWeight, measureReal_def] using
      Measure.integral_toReal_rnDeriv hIV.transportDomination
  have hv := variance_nonneg (transportWeight P n) (sourceXLaw P n)
  rw [variance_eq_sub hwMem, hwMean] at hv
  simpa [kishDispersion] using hv

/-- The weighted cross-sample average has variance bounded by its source-sampling contribution plus its target-sampling contribution, and its expectation equals the stated target mean. -/
lemma weighted_two_sample_variance
    (P : TransportedArray 𝒳) (N : ℕ → ℕ) (n : ℕ)
    (hn : 0 < n)
    [IsProbabilityMeasure (sourceObsLaw P n)]
    [IsProbabilityMeasure (targetXLaw P n)]
    {m : ℕ} (cell : Fin m ↪ 𝒳)
    (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : sourceXLaw P n (Set.range cell) = 1)
    (G : SourceObs 𝒳 → ℝ) (a : 𝒳 → ℝ) (C V R mean : ℝ)
    (hC : 0 ≤ C)
    (hGmeas : Measurable G)
    (hGmem : MemLp G 2 (sourceObsLaw P n))
    (hGbound : ∀ᵐ o ∂sourceObsLaw P n, |G o| ≤ C)
    (hqpos : ∀ i, 0 < sourceCellMass P n (cell i))
    (hcellMean : ∀ i,
      (∫ o in {o | o.1 = cell i}, G o ∂sourceObsLaw P n) /
          sourceCellMass P n (cell i) = a (cell i))
    (hTargetMem : MemLp
      (fun target : TargetSample 𝒳 (N n) =>
        ∑ i, targetEmpiricalMass target (cell i) * a (cell i)) 2
      (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)))
    (hTargetVar :
      variance
        (fun target : TargetSample 𝒳 (N n) =>
          ∑ i, targetEmpiricalMass target (cell i) * a (cell i))
        (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) ≤ V)
    (hTargetMean :
      (∫ target : TargetSample 𝒳 (N n),
          ∑ i, targetEmpiricalMass target (cell i) * a (cell i)
          ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) = mean)
    (hMassInt : Integrable
      (fun target : TargetSample 𝒳 (N n) =>
        ∑ i, targetEmpiricalMass target (cell i) ^ 2 /
          sourceCellMass P n (cell i))
      (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)))
    (hMassBound :
      (∫ target : TargetSample 𝒳 (N n),
          ∑ i, targetEmpiricalMass target (cell i) ^ 2 /
            sourceCellMass P n (cell i)
          ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) ≤
        kishDispersion P n + R) :
    let F := fun s : TwoSample 𝒳 n (N n) =>
      (n : ℝ)⁻¹ * ∑ r,
        (targetEmpiricalMass s.2 (s.1 r).1 /
          sourceCellMass P n (s.1 r).1) * G (s.1 r)
    variance F (twoSampleLaw P N n) ≤
        C ^ 2 / n * (kishDispersion P n + R) + V ∧
      (∫ s, F s ∂twoSampleLaw P N n) = mean := by
  classical
  let μS := Measure.pi (fun _ : Fin n => sourceObsLaw P n)
  let μT := Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
  let mass : TargetSample 𝒳 (N n) → ℝ := fun target =>
    ∑ i, targetEmpiricalMass target (cell i) ^ 2 /
      sourceCellMass P n (cell i)
  let M : TargetSample 𝒳 (N n) → ℝ := fun target =>
    ∑ i, targetEmpiricalMass target (cell i) * a (cell i)
  let F : TwoSample 𝒳 n (N n) → ℝ := fun s =>
    (n : ℝ)⁻¹ * ∑ r,
      (targetEmpiricalMass s.2 (s.1 r).1 /
        sourceCellMass P n (s.1 r).1) * G (s.1 r)
  have hcond (target : TargetSample 𝒳 (N n)) :=
    weighted_iid_average_mean_variance P n hn cell hcell hrange
      (targetEmpiricalMass target) G a C hC hGmem hGbound hqpos hcellMean
  have hFae : AEStronglyMeasurable F (μS.prod μT) := by
    dsimp only [F]
    simpa only [twoSampleLaw] using
      weighted_cross_aestronglyMeasurable P N n cell hcell hrange G hGmeas
  have hFSqAE :
      AEStronglyMeasurable (fun z => F z ^ 2) (μS.prod μT) :=
    hFae.pow 2
  have hInnerAE :
      AEStronglyMeasurable
        (fun target => ∫ source, F (source, target) ^ 2 ∂μS) μT :=
    hFSqAE.prod_swap.integral_prod_right'
  have hInnerEq (target : TargetSample 𝒳 (N n)) :
      (∫ source, F (source, target) ^ 2 ∂μS) =
        variance (fun source => F (source, target)) μS + M target ^ 2 := by
    have hv := variance_eq_sub (hcond target).2.2
    have hm := (hcond target).1
    have hv' :
        variance (fun source => F (source, target)) μS =
          (∫ source, F (source, target) ^ 2 ∂μS) - M target ^ 2 := by
      simpa only [F, M, μS, Pi.pow_apply, hm] using hv
    linarith [hv']
  have hInnerBound (target : TargetSample 𝒳 (N n)) :
      (∫ source, F (source, target) ^ 2 ∂μS) ≤
        (C ^ 2 / n) * mass target + M target ^ 2 := by
    rw [hInnerEq]
    exact add_le_add (hcond target).2.1 le_rfl
  have hDomInt :
      Integrable (fun target => (C ^ 2 / n) * mass target + M target ^ 2)
        μT := by
    exact (hMassInt.const_mul (C ^ 2 / n)).add hTargetMem.integrable_sq
  have hInnerInt :
      Integrable (fun target => ∫ source, F (source, target) ^ 2 ∂μS)
        μT := by
    apply Integrable.mono' hDomInt hInnerAE
    filter_upwards with target
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hInnerBound target
    · exact integral_nonneg fun _ => sq_nonneg _
  have hFSqInt : Integrable (fun z => F z ^ 2) (μS.prod μT) := by
    apply (integrable_prod_iff' hFSqAE).2
    constructor
    · exact Filter.Eventually.of_forall fun target =>
        (hcond target).2.2.integrable_sq
    · have heq :
          (fun target => ∫ source, ‖F (source, target) ^ 2‖ ∂μS) =
            fun target => ∫ source, F (source, target) ^ 2 ∂μS := by
        funext target
        apply integral_congr_ae
        filter_upwards with source
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [heq]
      exact hInnerInt
  have hFmem : MemLp F 2 (μS.prod μT) :=
    (memLp_two_iff_integrable_sq hFae).2 hFSqInt
  have hVarFunInt :
      Integrable (fun target => variance (fun source => F (source, target)) μS)
        μT := by
    have heq : (fun target =>
        variance (fun source => F (source, target)) μS) =
        fun target => (∫ source, F (source, target) ^ 2 ∂μS) - M target ^ 2 := by
      funext target
      rw [hInnerEq]
      ring
    rw [heq]
    exact hInnerInt.sub hTargetMem.integrable_sq
  have hVarIntegral :
      (∫ target, variance (fun source => F (source, target)) μS ∂μT) ≤
        (C ^ 2 / n) *
          (kishDispersion P n + R) := by
    calc
      _ ≤ ∫ target, (C ^ 2 / n) * mass target ∂μT := by
        apply integral_mono hVarFunInt (hMassInt.const_mul _)
        intro target
        simpa only [F, mass, μS] using (hcond target).2.1
      _ = (C ^ 2 / n) * ∫ target, mass target ∂μT := by
        rw [integral_const_mul]
      _ ≤ (C ^ 2 / n) * (kishDispersion P n + R) := by
        gcongr
  have hTotal :=
    variance_prod_eq_integral_variance_add μS μT F M hFmem
      (fun target => (hcond target).2.2) hTargetMem
      (fun target => (hcond target).1)
  constructor
  · unfold twoSampleLaw
    rw [hTotal]
    exact add_le_add hVarIntegral hTargetVar
  · unfold twoSampleLaw
    rw [integral_prod_symm _ (hFmem.integrable (by norm_num))]
    calc
      (∫ target, ∫ source, F (source, target) ∂μS ∂μT) =
          ∫ target, M target ∂μT := by
        apply integral_congr_ae
        filter_upwards with target
        simpa only [F, M, μS] using (hcond target).1
      _ = mean := by
        simpa only [M, μT] using hTargetMean

/-- For the witness construction, the empirical target receipt contrast has the stated mean and variance bound determined by the target cell distribution. -/
lemma target_receipt_mean_variance_for_witness
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ) (hNpos : 0 < N n)
    (hIV : TransportedIVClass P N k c epsilon n)
    (hk : 0 < k n) (hcm : 0 < cminus)
    (cell : Fin (k n) ↪ 𝒳)
    (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : sourceXLaw P n (Set.range cell) = 1)
    (hmass : ∀ i,
      cminus / (k n : ℝ) ≤ (sourceXLaw P n {cell i}).toReal ∧
      (sourceXLaw P n {cell i}).toReal ≤ cplus / (k n : ℝ)) :
    let M := fun target : TargetSample 𝒳 (N n) =>
      ∑ i, targetEmpiricalMass target (cell i) * P.deltaD n (cell i)
    variance M (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) ≤
        1 / (N n : ℝ) ∧
      MemLp M 2 (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) ∧
      (∫ target, M target
        ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) =
          transportedFirstStage P n := by
  classical
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hIV.twoSampleArray.2.2.1 n
  have hsourcePos (i : Fin (k n)) :
      0 < (sourceXLaw P n {cell i}).toReal :=
    lt_of_lt_of_le (div_pos hcm (by exact_mod_cast hk)) (hmass i).1
  have hcellBound (i : Fin (k n)) :
      |P.deltaD n (cell i)| ≤ 1 := by
    have hd := property_at_of_ae_of_singleton_pos
      (sourceXLaw P n) (fun x => P.deltaD n x ∈ Set.Icc (0 : ℝ) 1)
      (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.2.2 (hsourcePos i)
    rw [abs_of_nonneg hd.1]
    exact hd.2
  let B : 𝒳 → ℝ := fun x =>
    if x ∈ Set.range cell then P.deltaD n x else 0
  have hrangeMeas : MeasurableSet (Set.range cell) := by
    rw [show Set.range cell = ⋃ i, {cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion hcell
  have hBMeas : Measurable B := by
    dsimp only [B]
    exact Measurable.ite hrangeMeas (P.deltaD_measurable n) measurable_const
  have hBBound : ∀ x, |B x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ Set.range cell
    · obtain ⟨i, rfl⟩ := hx
      simpa [B] using hcellBound i
    · have hzero : B x = 0 := by
        dsimp only [B]
        rw [if_neg hx]
      rw [hzero]
      norm_num
  have hBMem : MemLp B 2 (targetXLaw P n) :=
    MemLp.of_bound hBMeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hBBound x)
  have hstat :
      (fun target : TargetSample 𝒳 (N n) =>
        ∑ i, targetEmpiricalMass target (cell i) * P.deltaD n (cell i)) =
      (fun target => (N n : ℝ)⁻¹ * ∑ j, B (target j)) := by
    funext target
    unfold targetEmpiricalMass Causalean.Stat.empiricalMass
    calc
      _ = ∑ i, ∑ j, (N n : ℝ)⁻¹ *
            (if target j = cell i then 1 else 0) * P.deltaD n (cell i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ j, ∑ i, (N n : ℝ)⁻¹ *
            (if target j = cell i then 1 else 0) * P.deltaD n (cell i) := by
        rw [Finset.sum_comm]
      _ = ∑ j, (N n : ℝ)⁻¹ * B (target j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        congr 1
        by_cases hx : target j ∈ Set.range cell
        · obtain ⟨i, hi⟩ := hx
          rw [← hi, Finset.sum_eq_single i]
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
  have hrangeCompl : sourceXLaw P n (Set.range cell)ᶜ = 0 := by
    rw [measure_compl hrangeMeas (measure_ne_top _ _), hrange, measure_univ]
    simp
  have htargetRange :
      ∀ᵐ x ∂targetXLaw P n, x ∈ Set.range cell := by
    have hc := hIV.transportDomination hrangeCompl
    change Set.range cell ∈ ae (targetXLaw P n)
    rw [mem_ae_iff]
    exact hc
  have hBDelta : B =ᵐ[targetXLaw P n] P.deltaD n := by
    filter_upwards [htargetRange] with x hx
    dsimp only [B]
    rw [if_pos hx]
  have hDeltaTargetInt :
      Integrable (P.deltaD n) (targetXLaw P n) := by
    refine Integrable.of_bound (P.deltaD_measurable n).aestronglyMeasurable 1 ?_
    apply hIV.transportDomination.ae_le
    filter_upwards [(sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.2.2] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
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
  refine ⟨?_, ?_, ?_⟩
  · rw [hstat, iid_average_variance
      (targetXLaw P n) (N n) hNpos B hBMem]
    calc
      (N n : ℝ)⁻¹ * variance B (targetXLaw P n) ≤
          (N n : ℝ)⁻¹ * ∫ x, B x ^ 2 ∂targetXLaw P n := by
        gcongr
        exact variance_le_expectation_sq hBMeas.aestronglyMeasurable
      _ ≤ (N n : ℝ)⁻¹ * 1 := by
        gcongr
        calc
          (∫ x, B x ^ 2 ∂targetXLaw P n) ≤ ∫ _x, (1 : ℝ)
              ∂targetXLaw P n := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun x => sq_nonneg (B x)
            · exact integrable_const 1
            · exact Filter.Eventually.of_forall fun x => by
                have hb := (abs_le).1 (hBBound x)
                nlinarith
          _ = 1 := by simp
      _ = 1 / (N n : ℝ) := by ring
  · rw [hstat]
    exact hAvgMem
  · rw [hstat, iid_average_integral
      (targetXLaw P n) (N n) hNpos B hBMem]
    rw [integral_congr_ae hBDelta, hFirstTarget]

end CausalSmith.Stat.TransportedLateStrengthFrontier
