/-
# Transported LATE identification and compact causal range
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Basic
import Causalean.PO.ID.Exact.LATE
import Causalean.Mathlib.MeasureTheory.SetIntegralRecovery

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open MeasureTheory

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The map from assigned full data to the observed source-data record is measurable. -/
lemma measurable_observeSource :
    Measurable (observeSource : AssignedFullData 𝒳 → SourceObs 𝒳) := by
    have hx : Measurable fun q : AssignedFullData 𝒳 => q.1.2.1 := by
      fun_prop
    have hz : Measurable fun q : AssignedFullData 𝒳 => q.2 := by
      fun_prop
    have hd : Measurable fun q : AssignedFullData 𝒳 =>
        if q.2 then q.1.2.2.2.1 else q.1.2.2.1 := by
      exact Measurable.ite
        (hz (MeasurableSet.singleton true)) (by fun_prop) (by fun_prop)
    have hy : Measurable fun q : AssignedFullData 𝒳 =>
        if (if q.2 then q.1.2.2.2.1 else q.1.2.2.1)
          then q.1.2.2.2.2.2 else q.1.2.2.2.2.1 := by
      exact Measurable.ite
        (hd (MeasurableSet.singleton true)) (by fun_prop) (by fun_prop)
    exact hx.prodMk (hz.prodMk (hd.prodMk hy))

/-- Under the source-observation conditions, the source covariate distribution equals the source population covariate distribution. -/
lemma sourceXLaw_eq_populationXLaw_source
    (P : TransportedArray 𝒳) (n : ℕ)
    (hSourceFacts : SourceObservationFacts P n) :
    sourceXLaw P n = populationXLaw P n true := by
  have hObserve :
      Measurable (observeSource : AssignedFullData 𝒳 → SourceObs 𝒳) :=
    measurable_observeSource
  have hFullX : Measurable (fullX : FullData 𝒳 → 𝒳) := by
    unfold fullX
    fun_prop
  rw [sourceXLaw, sourceObsLaw, Measure.map_map measurable_fst hObserve]
  rw [populationXLaw, ← hSourceFacts.2.2.2.1]
  rw [Measure.map_map hFullX measurable_fst]
  congr 1

/-- A finite measure equals the measure obtained by weighting another measure when its mass on every measurable set is the corresponding integral of a nonnegative integrable weight. -/
lemma measure_eq_withDensity_of_toReal_setIntegral
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [IsFiniteMeasure ν]
    {w : α → ℝ} (hwmeas : Measurable w) (hwint : Integrable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hν : ∀ A, MeasurableSet A →
      (ν A).toReal = ∫ x in A, w x ∂μ) :
    ν = μ.withDensity (fun x => ENNReal.ofReal (w x)) := by
  exact Causalean.Mathlib.MeasureTheory.measure_eq_withDensity_of_toReal_setIntegral
    hwint hν

/-- Under IV randomization and overlap, the full-data distribution conditional on each instrument value is the source population law reweighted by that instrument's propensity probability. -/
lemma ivRandomization_slice_eq_withDensity
    (P : TransportedArray 𝒳) (n : ℕ) (epsilon : ℝ)
    (hSourceFacts : SourceObservationFacts P n)
    (hRandom : IVRandomization P n)
    (hOverlap : InstrumentOverlap P n epsilon)
    (z : Bool) :
    ((P.assignedSourceLaw n).restrict {q | q.2 = z}).map Prod.fst =
      (populationLaw P n true).withDensity (fun o =>
        ENNReal.ofReal
          (if z then P.propensity n (fullX o)
            else 1 - P.propensity n (fullX o))) := by
  let μ := populationLaw P n true
  let ν := ((P.assignedSourceLaw n).restrict {q | q.2 = z}).map Prod.fst
  let w : FullData 𝒳 → ℝ := fun o =>
    if z then P.propensity n (fullX o)
      else 1 - P.propensity n (fullX o)
  have hFullX : Measurable (fullX : FullData 𝒳 → 𝒳) := by
    unfold fullX
    fun_prop
  have hwmeas : Measurable w := by
    have hecomp : Measurable fun o : FullData 𝒳 =>
        P.propensity n (fullX o) :=
      (P.propensity_measurable n).comp hFullX
    cases z
    · simpa [w] using measurable_const.sub hecomp
    · simpa [w] using hecomp
  have hsourceX := sourceXLaw_eq_populationXLaw_source P n hSourceFacts
  have hoverlapPop : ∀ᵐ o ∂μ,
      epsilon ≤ P.propensity n (fullX o) ∧
        P.propensity n (fullX o) ≤ 1 - epsilon := by
    have hx := hOverlap.2.2
    rw [hsourceX] at hx
    exact ae_of_ae_map hFullX.aemeasurable hx
  have hw0 : ∀ᵐ o ∂μ, 0 ≤ w o := by
    filter_upwards [hoverlapPop] with o ho
    unfold w
    cases z
    · simp
      linarith [hOverlap.1]
    · simpa using (le_trans hOverlap.1.le ho.1)
  have hwle : ∀ᵐ o ∂μ, w o ≤ 1 := by
    filter_upwards [hoverlapPop] with o ho
    unfold w
    cases z
    · simp
      linarith [ho.1, hOverlap.1]
    · simpa using ho.2.trans (sub_le_self 1 hOverlap.1.le)
  haveI : IsProbabilityMeasure (P.assignedSourceLaw n) := hSourceFacts.1
  haveI : IsProbabilityMeasure μ := by
    unfold μ
    rw [← hSourceFacts.2.2.2.1]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hwint : Integrable w μ := by
    refine Integrable.of_bound hwmeas.aestronglyMeasurable 1 ?_
    filter_upwards [hw0, hwle] with o h0 h1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  haveI : IsFiniteMeasure ν := by
    unfold ν
    exact Measure.isFiniteMeasure_map
      ((P.assignedSourceLaw n).restrict {q | q.2 = z}) Prod.fst
  apply measure_eq_withDensity_of_toReal_setIntegral hwmeas hwint hw0
  intro A hA
  rw [Measure.map_apply measurable_fst hA]
  rw [Measure.restrict_apply (hA.preimage measurable_fst)]
  rw [show Prod.fst ⁻¹' A ∩ {q | q.2 = z} =
      {q | q.1 ∈ A ∧ q.2 = z} by
    ext q
    simp]
  simpa [μ, w] using hRandom A hA z

/-- Under IV randomization and overlap, the inverse-propensity-weighted contrast over a covariate set equals the source-population integral of the difference between the two full-data outcomes. -/
lemma ivRandomization_ipw_contrast
    (P : TransportedArray 𝒳) (n : ℕ) (epsilon : ℝ)
    (hSourceFacts : SourceObservationFacts P n)
    (hRandom : IVRandomization P n)
    (hOverlap : InstrumentOverlap P n epsilon)
    (F0 F1 : FullData 𝒳 → ℝ)
    (hF0 : Measurable F0) (hF1 : Measurable F1)
    (hF0int : Integrable F0 (populationLaw P n true))
    (hF1int : Integrable F1 (populationLaw P n true))
    (hInt : Integrable (fun q : AssignedFullData 𝒳 =>
      if q.2 then
        (1 / P.propensity n (fullX q.1)) * F1 q.1
      else
        (-1 / (1 - P.propensity n (fullX q.1))) * F0 q.1)
      (P.assignedSourceLaw n))
    (A : Set 𝒳) (hA : MeasurableSet A) :
    (∫ q in {q | fullX q.1 ∈ A},
      (if q.2 then
        (1 / P.propensity n (fullX q.1)) * F1 q.1
      else
        (-1 / (1 - P.propensity n (fullX q.1))) * F0 q.1)
      ∂P.assignedSourceLaw n) =
      ∫ o in {o | fullX o ∈ A}, (F1 o - F0 o)
        ∂populationLaw P n true := by
  let μ := populationLaw P n true
  let e : FullData 𝒳 → ℝ := fun o => P.propensity n (fullX o)
  let S : Set (AssignedFullData 𝒳) := {q | fullX q.1 ∈ A}
  let E : Set (AssignedFullData 𝒳) := {q | q.2 = true}
  let W : AssignedFullData 𝒳 → ℝ := fun q =>
    if q.2 then (1 / e q.1) * F1 q.1
      else (-1 / (1 - e q.1)) * F0 q.1
  have hFullX : Measurable (fullX : FullData 𝒳 → 𝒳) := by
    unfold fullX
    fun_prop
  have hS : MeasurableSet S :=
    hA.preimage (hFullX.comp measurable_fst)
  have hE : MeasurableSet E :=
    measurable_snd (MeasurableSet.singleton true)
  have hsplit := integral_add_compl
    (μ := (P.assignedSourceLaw n).restrict S) hE hInt.integrableOn
  have hemeas : Measurable e :=
    (P.propensity_measurable n).comp hFullX
  have hoverlapPop : ∀ᵐ o ∂μ,
      epsilon ≤ e o ∧ e o ≤ 1 - epsilon := by
    have hx := hOverlap.2.2
    rw [sourceXLaw_eq_populationXLaw_source P n hSourceFacts] at hx
    exact ae_of_ae_map hFullX.aemeasurable hx
  have htrue :
      (∫ q in S ∩ E, W q ∂P.assignedSourceLaw n) =
        ∫ o in {o | fullX o ∈ A}, F1 o ∂μ := by
    have hslice :=
      ivRandomization_slice_eq_withDensity P n epsilon hSourceFacts hRandom
        hOverlap true
    have hmap :
        (∫ o in {o | fullX o ∈ A}, (1 / e o) * F1 o
            ∂(((P.assignedSourceLaw n).restrict E).map Prod.fst)) =
          ∫ q in S ∩ E, W q ∂P.assignedSourceLaw n := by
      calc
        _ = ∫ q in Prod.fst ⁻¹' {o | fullX o ∈ A},
              (1 / e q.1) * F1 q.1
              ∂(P.assignedSourceLaw n).restrict E :=
          setIntegral_map (μ := (P.assignedSourceLaw n).restrict E)
            (hA.preimage hFullX)
            ((measurable_const.div hemeas).mul hF1).aestronglyMeasurable
            measurable_fst.aemeasurable
        _ = _ := by
          change (∫ q, (1 / e q.1) * F1 q.1
            ∂((P.assignedSourceLaw n).restrict E).restrict
              (Prod.fst ⁻¹' {o | fullX o ∈ A})) =
                ∫ q in S ∩ E, W q ∂P.assignedSourceLaw n
          rw [Measure.restrict_restrict' hE]
          change (∫ q in S ∩ E, (1 / e q.1) * F1 q.1
            ∂P.assignedSourceLaw n) =
              ∫ q in S ∩ E, W q ∂P.assignedSourceLaw n
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (hS.inter hE)] with q hq
          have hqtrue : q.2 = true := hq.2
          simp [W, hqtrue]
    rw [← hmap, hslice]
    change (∫ o in {o | fullX o ∈ A}, (1 / e o) * F1 o
      ∂μ.withDensity (fun o => ENNReal.ofReal (e o))) =
        ∫ o in {o | fullX o ∈ A}, F1 o ∂μ
    calc
      _ = ∫ o in {o | fullX o ∈ A},
          (ENNReal.ofReal (e o)).toReal • ((1 / e o) * F1 o) ∂μ :=
        setIntegral_withDensity_eq_setIntegral_toReal_smul
          (ENNReal.measurable_ofReal.comp hemeas)
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
          (fun o => (1 / e o) * F1 o) (hA.preimage hFullX)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hoverlapPop] with o ho
        have hepos : 0 < e o := lt_of_lt_of_le hOverlap.1 ho.1
        simp [ENNReal.toReal_ofReal hepos.le, smul_eq_mul, hepos.ne']
  have hfalse :
      (∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n) =
        ∫ o in {o | fullX o ∈ A}, -F0 o ∂μ := by
    have hslice :=
      ivRandomization_slice_eq_withDensity P n epsilon hSourceFacts hRandom
        hOverlap false
    have hmap :
        (∫ o in {o | fullX o ∈ A}, (-1 / (1 - e o)) * F0 o
            ∂(((P.assignedSourceLaw n).restrict {q | q.2 = false}).map
              Prod.fst)) =
          ∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n := by
      calc
        _ = ∫ q in Prod.fst ⁻¹' {o | fullX o ∈ A},
              (-1 / (1 - e q.1)) * F0 q.1
              ∂(P.assignedSourceLaw n).restrict {q | q.2 = false} :=
          setIntegral_map
            (μ := (P.assignedSourceLaw n).restrict {q | q.2 = false})
            (hA.preimage hFullX)
            ((measurable_const.neg.div (measurable_const.sub hemeas)).mul
              hF0).aestronglyMeasurable
            measurable_fst.aemeasurable
        _ = _ := by
          have hEf : {q : AssignedFullData 𝒳 | q.2 = false} = Eᶜ := by
            ext q
            cases q.2 <;> simp [E]
          rw [hEf]
          change (∫ q, (-1 / (1 - e q.1)) * F0 q.1
            ∂((P.assignedSourceLaw n).restrict Eᶜ).restrict
              (Prod.fst ⁻¹' {o | fullX o ∈ A})) =
                ∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n
          rw [Measure.restrict_restrict' hE.compl]
          change (∫ q in S ∩ Eᶜ, (-1 / (1 - e q.1)) * F0 q.1
            ∂P.assignedSourceLaw n) =
              ∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (hS.inter hE.compl)] with q hq
          have hqfalse : q.2 = false := by
            cases hqz : q.2
            · rfl
            · exfalso
              exact hq.2 (by simp [E, hqz])
          simp [W, hqfalse]
    rw [← hmap, hslice]
    change (∫ o in {o | fullX o ∈ A}, (-1 / (1 - e o)) * F0 o
      ∂μ.withDensity (fun o => ENNReal.ofReal (1 - e o))) =
        ∫ o in {o | fullX o ∈ A}, -F0 o ∂μ
    calc
      _ = ∫ o in {o | fullX o ∈ A},
          (ENNReal.ofReal (1 - e o)).toReal •
            ((-1 / (1 - e o)) * F0 o) ∂μ :=
        setIntegral_withDensity_eq_setIntegral_toReal_smul
          (ENNReal.measurable_ofReal.comp (measurable_const.sub hemeas))
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
          (fun o => (-1 / (1 - e o)) * F0 o) (hA.preimage hFullX)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hoverlapPop] with o ho
        have hden : 0 < 1 - e o := by
          linarith [ho.2, hOverlap.1]
        rw [ENNReal.toReal_ofReal hden.le]
        simp only [smul_eq_mul]
        field_simp [hden.ne']
  have hsplitW :
      (∫ q in S ∩ E, W q ∂P.assignedSourceLaw n) +
        (∫ q in S ∩ Eᶜ, W q ∂P.assignedSourceLaw n) =
          ∫ q in S, W q ∂P.assignedSourceLaw n := by
    rw [Measure.restrict_restrict hE,
      Measure.restrict_restrict hE.compl] at hsplit
    simpa [S, E, W, e, Set.inter_comm] using hsplit
  change (∫ q in S, W q ∂P.assignedSourceLaw n) =
    ∫ o in {o | fullX o ∈ A}, F1 o - F0 o ∂μ
  rw [← hsplitW, htrue, hfalse]
  calc
    (∫ o in {o | fullX o ∈ A}, F1 o ∂μ) +
        ∫ o in {o | fullX o ∈ A}, -F0 o ∂μ =
        ∫ o in {o | fullX o ∈ A}, F1 o + -F0 o ∂μ := by
      simpa only [Pi.neg_apply] using
        (integral_add hF1int.integrableOn hF0int.neg.integrableOn).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with o
      ring

-- @node: prop:compact-causal-range
/-- Source randomization identifies the two conditional contrasts; transport
identifies their target means; their Wald ratio is the target CACE and belongs
to the forced interval `[-1,1]`. -/
theorem compact_causal_range
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ) (c epsilon : ℝ) (n : ℕ)
    (hAssignmentContrastIntegrable :
      Integrable (P.assignmentContrast n true) (sourceXLaw P n))
    (hReceiptContrastIntegrable :
      Integrable (P.receiptContrast n true) (sourceXLaw P n))
    (hP : TransportedIVClass P N k c epsilon n) :
    OutcomeContrastRepresentation P n (P.deltaY n) ∧
    ReceiptContrastRepresentation P n (P.deltaD n) ∧
    transportedOutcomeITT P n =
      ∫ o, (fullY1 o - fullY0 o) *
        (if fullD1 o = true ∧ fullD0 o = false then 1 else 0)
        ∂populationLaw P n false ∧
    transportedFirstStage P n = targetComplierShare P n ∧
    transportedOutcomeITT P n / transportedFirstStage P n =
      targetCACE P n ∧
    targetCACE P n ∈ parameterSpace := by
  have hSourceFacts :=
    sourceObservationFacts_of_class P N k c epsilon n hP
  have hSupport := hP.fullDataSupport
  have hPresence := hP.populationPresence
  have hTwo := hP.twoSampleArray
  have hOverlap := hP.instrumentOverlap
  have hRandom := hP.ivRandomization
  have hExclusion := hP.ivExclusion
  have hMono := hP.ivMonotonicity
  have hOutcome := hP.outcomeTransport
  have hReceipt := hP.receiptTransport
  have hPositive := hP.targetComplierPositivity
  have hDom := hP.transportDomination
  letI : IsProbabilityMeasure (sourceObsLaw P n) := hSourceFacts.2.1
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hOverlapObs : ∀ᵐ o ∂sourceObsLaw P n,
      epsilon ≤ P.propensity n o.1 ∧
        P.propensity n o.1 ≤ 1 - epsilon := by
    have hx := hOverlap.2.2
    unfold sourceXLaw at hx
    exact ae_of_ae_map measurable_fst.aemeasurable hx
  have hInstrumentScoreMeasurable :
      Measurable (instrumentScore P n) := by
    have hz : Measurable fun o : SourceObs 𝒳 => o.2.1 := by
      fun_prop
    have he : Measurable fun o : SourceObs 𝒳 => P.propensity n o.1 :=
      (P.propensity_measurable n).comp measurable_fst
    unfold instrumentScore
    exact Measurable.ite (hz (MeasurableSet.singleton true))
      (measurable_const.div he)
      (measurable_const.neg.div (measurable_const.sub he))
  have hInstrumentScoreBound : ∀ᵐ o ∂sourceObsLaw P n,
      |instrumentScore P n o| ≤ 1 / epsilon := by
    filter_upwards [hOverlapObs] with o ho
    rcases o with ⟨x, z, d, y⟩
    cases z
    · simp only [instrumentScore, Bool.false_eq_true, ↓reduceIte, abs_neg,
        abs_div, abs_one]
      rw [abs_of_pos (sub_pos.mpr (lt_of_le_of_lt ho.2
        (by linarith [hOverlap.1])))]
      exact one_div_le_one_div_of_le hOverlap.1 (by linarith [ho.2])
    · simp only [instrumentScore, ↓reduceIte, abs_div, abs_one]
      rw [abs_of_pos (lt_of_lt_of_le hOverlap.1 ho.1)]
      exact one_div_le_one_div_of_le hOverlap.1 ho.1
  have hScoreIntegrable
      (G : SourceObs 𝒳 → ℝ) (hGmeas : Measurable G)
      (hGbound : ∀ᵐ o ∂sourceObsLaw P n, |G o| ≤ 1) :
      Integrable (fun o => instrumentScore P n o * G o)
        (sourceObsLaw P n) := by
    refine Integrable.of_bound
      ((hInstrumentScoreMeasurable.mul hGmeas).aestronglyMeasurable)
      (1 / epsilon) ?_
    filter_upwards [hInstrumentScoreBound, hGbound] with o hs hG
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |instrumentScore P n o| * |G o| ≤
          (1 / epsilon) * 1 :=
        mul_le_mul hs hG (abs_nonneg _)
          (one_div_nonneg.mpr hOverlap.1.le)
      _ = 1 / epsilon := mul_one _
  have hOutcomeScoreIntegrable :
      Integrable (fun o => instrumentScore P n o * o.2.2.2)
        (sourceObsLaw P n) := by
    apply hScoreIntegrable (fun o => o.2.2.2) (by fun_prop)
    filter_upwards [hSourceFacts.2.2.1] with o ho
    rw [abs_of_nonneg ho.1]
    exact ho.2
  have hReceiptScoreIntegrable :
      Integrable (fun o => instrumentScore P n o * boolReal o.2.2.1)
        (sourceObsLaw P n) := by
    apply hScoreIntegrable (fun o => boolReal o.2.2.1)
      (by
        unfold boolReal
        have hd : Measurable fun o : SourceObs 𝒳 => o.2.2.1 := by
          fun_prop
        exact Measurable.ite (hd (MeasurableSet.singleton true))
          measurable_const measurable_const)
    filter_upwards with o
    cases o.2.2.1 <;> simp [boolReal]
  have hDeltaY :
      P.deltaY n =ᵐ[sourceXLaw P n] P.assignmentContrast n true := by
    have hDeltaYint : Integrable (P.deltaY n) (sourceXLaw P n) := by
      refine Integrable.of_bound
        (P.deltaY_measurable n).aestronglyMeasurable 1 ?_
      filter_upwards [hSourceFacts.2.2.2.2.2.2.1] with x hx
      rw [Real.norm_eq_abs]
      exact (abs_le).2 hx
    refine Integrable.ae_eq_of_forall_setIntegral_eq
      (P.deltaY n) (P.assignmentContrast n true) hDeltaYint
      hAssignmentContrastIntegrable ?_
    intro A hA hAfin
    have hFullX : Measurable (fullX : FullData 𝒳 → 𝒳) := by
      unfold fullX
      fun_prop
    have hDerivedMeas (z : Bool) :
        Measurable (fun o : FullData 𝒳 => derivedAssignmentOutcome o z) := by
      have hd : Measurable fun o : FullData 𝒳 => potentialReceipt o z := by
        cases z
        · have hd0 : Measurable (fullD0 : FullData 𝒳 → Bool) := by
            unfold fullD0
            fun_prop
          simpa [potentialReceipt] using hd0
        · have hd1 : Measurable (fullD1 : FullData 𝒳 → Bool) := by
            unfold fullD1
            fun_prop
          simpa [potentialReceipt] using hd1
      unfold derivedAssignmentOutcome potentialOutcome
      have hy0 : Measurable (fullY0 : FullData 𝒳 → ℝ) := by
        unfold fullY0
        fun_prop
      have hy1 : Measurable (fullY1 : FullData 𝒳 → ℝ) := by
        unfold fullY1
        fun_prop
      exact Measurable.ite (hd (MeasurableSet.singleton true)) hy1 hy0
    haveI : IsProbabilityMeasure (P.assignedSourceLaw n) := hSourceFacts.1
    haveI : IsProbabilityMeasure (populationLaw P n true) := by
      rw [← hSourceFacts.2.2.2.1]
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have hSupportSource : ∀ᵐ o ∂populationLaw P n true,
        fullY0 o ∈ Set.Icc (0 : ℝ) 1 ∧ fullY1 o ∈ Set.Icc (0 : ℝ) 1 :=
      ProbabilityTheory.cond_absolutelyContinuous.ae_le hSupport.2
    have hDerivedBound (z : Bool) :
        ∀ᵐ o ∂populationLaw P n true,
          |derivedAssignmentOutcome o z| ≤ 1 := by
      filter_upwards [hSupportSource] with o ho
      unfold derivedAssignmentOutcome potentialOutcome potentialReceipt
      cases z <;> cases fullD0 o <;> cases fullD1 o <;>
        simp [abs_of_nonneg ho.1.1, abs_of_nonneg ho.2.1, ho.1.2, ho.2.2]
    have hF0int :
        Integrable (fun o : FullData 𝒳 => derivedAssignmentOutcome o false)
          (populationLaw P n true) := by
      exact Integrable.of_bound (hDerivedMeas false).aestronglyMeasurable 1
        (hDerivedBound false)
    have hF1int :
        Integrable (fun o : FullData 𝒳 => derivedAssignmentOutcome o true)
          (populationLaw P n true) := by
      exact Integrable.of_bound (hDerivedMeas true).aestronglyMeasurable 1
        (hDerivedBound true)
    have hpull :
        Integrable (fun q : AssignedFullData 𝒳 =>
          instrumentScore P n (observeSource q) * (observeSource q).2.2.2)
          (P.assignedSourceLaw n) := by
      unfold sourceObsLaw at hOutcomeScoreIntegrable
      exact hOutcomeScoreIntegrable.comp_measurable measurable_observeSource
    have hWint :
        Integrable (fun q : AssignedFullData 𝒳 =>
          if q.2 then
            (1 / P.propensity n (fullX q.1)) *
              derivedAssignmentOutcome q.1 true
          else
            (-1 / (1 - P.propensity n (fullX q.1))) *
              derivedAssignmentOutcome q.1 false)
          (P.assignedSourceLaw n) := by
      apply hpull.congr
      filter_upwards with q
      cases hz : q.2 <;>
        cases hd0 : fullD0 q.1 <;> cases hd1 : fullD1 q.1 <;>
          simp [observeSource, instrumentScore, derivedAssignmentOutcome,
            potentialOutcome, potentialReceipt, hz, hd0, hd1]
    calc
      (∫ x in A, P.deltaY n x ∂sourceXLaw P n) =
          ∫ o in {o | o.1 ∈ A},
            instrumentScore P n o * o.2.2.2 ∂sourceObsLaw P n :=
        (hSourceFacts.2.2.2.2.2.1 A hA).symm
      _ = ∫ q in {q | fullX q.1 ∈ A},
          (if q.2 then
            (1 / P.propensity n (fullX q.1)) *
              derivedAssignmentOutcome q.1 true
          else
            (-1 / (1 - P.propensity n (fullX q.1))) *
              derivedAssignmentOutcome q.1 false)
            ∂P.assignedSourceLaw n := by
        unfold sourceObsLaw
        calc
          _ = ∫ q in observeSource ⁻¹' {o | o.1 ∈ A},
              instrumentScore P n (observeSource q) *
                (observeSource q).2.2.2 ∂P.assignedSourceLaw n :=
            setIntegral_map (μ := P.assignedSourceLaw n)
              (hA.preimage measurable_fst)
              (hInstrumentScoreMeasurable.mul (by fun_prop)).aestronglyMeasurable
              measurable_observeSource.aemeasurable
          _ = _ := by
            apply integral_congr_ae
            filter_upwards with q
            cases hz : q.2 <;>
              cases hd0 : fullD0 q.1 <;> cases hd1 : fullD1 q.1 <;>
                simp [observeSource, instrumentScore, derivedAssignmentOutcome,
                  potentialOutcome, potentialReceipt, fullX, hz, hd0, hd1]
      _ = ∫ o in {o | fullX o ∈ A},
          (derivedAssignmentOutcome o true -
            derivedAssignmentOutcome o false) ∂populationLaw P n true :=
        ivRandomization_ipw_contrast P n epsilon hSourceFacts hRandom hOverlap
          (fun o => derivedAssignmentOutcome o false)
          (fun o => derivedAssignmentOutcome o true)
          (hDerivedMeas false) (hDerivedMeas true) hF0int hF1int hWint A hA
      _ = ∫ o in {o | fullX o ∈ A},
          (P.assignmentOutcome n true o -
            P.assignmentOutcome n false o) ∂populationLaw P n true := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (hExclusion true true),
          ae_restrict_of_ae (hExclusion true false)]
          with o h1 h0
        rw [h1, h0]
      _ = ∫ x in A, P.assignmentContrast n true x ∂sourceXLaw P n := by
        rw [sourceXLaw_eq_populationXLaw_source P n hSourceFacts]
        simpa using hOutcome.1 true A hA
  have hDeltaD :
      P.deltaD n =ᵐ[sourceXLaw P n] P.receiptContrast n true := by
    have hDeltaDint : Integrable (P.deltaD n) (sourceXLaw P n) := by
      refine Integrable.of_bound
        (P.deltaD_measurable n).aestronglyMeasurable 1 ?_
      filter_upwards [hSourceFacts.2.2.2.2.2.2.2.2] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    refine Integrable.ae_eq_of_forall_setIntegral_eq
      (P.deltaD n) (P.receiptContrast n true) hDeltaDint
      hReceiptContrastIntegrable ?_
    intro A hA hAfin
    have hFullX : Measurable (fullX : FullData 𝒳 → 𝒳) := by
      unfold fullX
      fun_prop
    have hD0meas : Measurable fun o : FullData 𝒳 => boolReal (fullD0 o) := by
      unfold boolReal
      have hd : Measurable (fullD0 : FullData 𝒳 → Bool) := by
        unfold fullD0
        fun_prop
      exact Measurable.ite (hd (MeasurableSet.singleton true))
        measurable_const measurable_const
    have hD1meas : Measurable fun o : FullData 𝒳 => boolReal (fullD1 o) := by
      unfold boolReal
      have hd : Measurable (fullD1 : FullData 𝒳 → Bool) := by
        unfold fullD1
        fun_prop
      exact Measurable.ite (hd (MeasurableSet.singleton true))
        measurable_const measurable_const
    haveI : IsProbabilityMeasure (P.assignedSourceLaw n) := hSourceFacts.1
    haveI : IsProbabilityMeasure (populationLaw P n true) := by
      rw [← hSourceFacts.2.2.2.1]
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have hD0int :
        Integrable (fun o : FullData 𝒳 => boolReal (fullD0 o))
          (populationLaw P n true) := by
      refine Integrable.of_bound hD0meas.aestronglyMeasurable 1 ?_
      filter_upwards with o
      cases fullD0 o <;> simp [boolReal]
    have hD1int :
        Integrable (fun o : FullData 𝒳 => boolReal (fullD1 o))
          (populationLaw P n true) := by
      refine Integrable.of_bound hD1meas.aestronglyMeasurable 1 ?_
      filter_upwards with o
      cases fullD1 o <;> simp [boolReal]
    have hpull :
        Integrable (fun q : AssignedFullData 𝒳 =>
          instrumentScore P n (observeSource q) *
            boolReal (observeSource q).2.2.1)
          (P.assignedSourceLaw n) := by
      unfold sourceObsLaw at hReceiptScoreIntegrable
      exact hReceiptScoreIntegrable.comp_measurable measurable_observeSource
    have hWint :
        Integrable (fun q : AssignedFullData 𝒳 =>
          if q.2 then
            (1 / P.propensity n (fullX q.1)) * boolReal (fullD1 q.1)
          else
            (-1 / (1 - P.propensity n (fullX q.1))) *
              boolReal (fullD0 q.1))
          (P.assignedSourceLaw n) := by
      apply hpull.congr
      filter_upwards with q
      cases hz : q.2 <;>
        cases hd0 : fullD0 q.1 <;> cases hd1 : fullD1 q.1 <;>
          simp [observeSource, instrumentScore, potentialReceipt, boolReal,
            hz, hd0, hd1]
    calc
      (∫ x in A, P.deltaD n x ∂sourceXLaw P n) =
          ∫ o in {o | o.1 ∈ A},
            instrumentScore P n o * boolReal o.2.2.1
              ∂sourceObsLaw P n :=
        (hSourceFacts.2.2.2.2.2.2.2.1 A hA).symm
      _ = ∫ q in {q | fullX q.1 ∈ A},
          (if q.2 then
            (1 / P.propensity n (fullX q.1)) * boolReal (fullD1 q.1)
          else
            (-1 / (1 - P.propensity n (fullX q.1))) *
              boolReal (fullD0 q.1)) ∂P.assignedSourceLaw n := by
        unfold sourceObsLaw
        calc
          _ = ∫ q in observeSource ⁻¹' {o | o.1 ∈ A},
              instrumentScore P n (observeSource q) *
                boolReal (observeSource q).2.2.1
                ∂P.assignedSourceLaw n :=
            setIntegral_map (μ := P.assignedSourceLaw n)
              (hA.preimage measurable_fst)
              (hInstrumentScoreMeasurable.mul
                (by
                  unfold boolReal
                  have hd : Measurable fun o : SourceObs 𝒳 => o.2.2.1 := by
                    fun_prop
                  exact Measurable.ite (hd (MeasurableSet.singleton true))
                    measurable_const measurable_const)).aestronglyMeasurable
              measurable_observeSource.aemeasurable
          _ = _ := by
            apply integral_congr_ae
            filter_upwards with q
            cases hz : q.2 <;>
              cases hd0 : fullD0 q.1 <;> cases hd1 : fullD1 q.1 <;>
                simp [observeSource, instrumentScore, potentialReceipt, boolReal,
                  fullX, hz, hd0, hd1]
      _ = ∫ o in {o | fullX o ∈ A},
          (boolReal (fullD1 o) - boolReal (fullD0 o))
            ∂populationLaw P n true :=
        ivRandomization_ipw_contrast P n epsilon hSourceFacts hRandom hOverlap
          (fun o => boolReal (fullD0 o)) (fun o => boolReal (fullD1 o))
          hD0meas hD1meas hD0int hD1int hWint A hA
      _ = ∫ x in A, P.receiptContrast n true x ∂sourceXLaw P n := by
        rw [sourceXLaw_eq_populationXLaw_source P n hSourceFacts]
        simpa using hReceipt.1 true A hA
  constructor
  · exact ⟨P.deltaY_measurable n, hSourceFacts.2.2.2.2.2.1⟩
  constructor
  · exact ⟨P.deltaD_measurable n, hSourceFacts.2.2.2.2.2.2.2.1⟩
  have hOutcomeEq :
      transportedOutcomeITT P n =
        ∫ o, (fullY1 o - fullY0 o) *
          (if fullD1 o = true ∧ fullD0 o = false then 1 else 0)
          ∂populationLaw P n false := by
    haveI : IsProbabilityMeasure (sourceObsLaw P n) := hTwo.2.1 n
    haveI : IsProbabilityMeasure (sourceXLaw P n) := by
      unfold sourceXLaw
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    haveI : IsProbabilityMeasure (targetXLaw P n) := hTwo.2.2.1 n
    calc
      transportedOutcomeITT P n =
          ∫ x, transportWeight P n x *
            P.assignmentContrast n true x ∂sourceXLaw P n := by
        unfold transportedOutcomeITT
        exact integral_congr_ae
          (hDeltaY.mono fun x hx => by
            simpa using congrArg (fun z => transportWeight P n x * z) hx)
      _ = ∫ x, P.assignmentContrast n true x ∂targetXLaw P n := by
        unfold transportWeight
        simpa only [smul_eq_mul] using
          (integral_rnDeriv_smul
            (μ := targetXLaw P n) (ν := sourceXLaw P n)
            (f := P.assignmentContrast n true) hDom)
      _ = ∫ x, P.assignmentContrast n false x ∂targetXLaw P n := by
        exact integral_congr_ae hOutcome.2.symm
      _ = ∫ o, (P.assignmentOutcome n true o -
            P.assignmentOutcome n false o) ∂populationLaw P n false := by
        simpa using (hOutcome.1 false Set.univ MeasurableSet.univ).symm
      _ = ∫ o, (derivedAssignmentOutcome o true -
            derivedAssignmentOutcome o false) ∂populationLaw P n false := by
        apply integral_congr_ae
        filter_upwards [hExclusion false true, hExclusion false false]
          with o h1 h0
        rw [h1, h0]
      _ = ∫ o, (fullY1 o - fullY0 o) *
          (if fullD1 o = true ∧ fullD0 o = false then 1 else 0)
            ∂populationLaw P n false := by
        apply integral_congr_ae
        filter_upwards [hMono false] with o ho
        cases h0 : fullD0 o <;> cases h1 : fullD1 o <;>
          simp [derivedAssignmentOutcome, potentialOutcome, potentialReceipt,
            boolReal, h0, h1] at ho ⊢ <;> norm_num at ho
  have hFirstEq :
      transportedFirstStage P n = targetComplierShare P n := by
    letI : IsProbabilityMeasure (targetXLaw P n) := hTwo.2.2.1 n
    have hWeightMeasurable : Measurable (transportWeight P n) :=
      (Measure.measurable_rnDeriv
        (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
    have hWeightBoundObs : ∀ᵐ o ∂sourceObsLaw P n,
        0 ≤ transportWeight P n o.1 ∧
          transportWeight P n o.1 ≤ 2 * (k n : ℝ) := by
      have hx := hP.weightEnvelope
      unfold sourceXLaw at hx
      exact ae_of_ae_map measurable_fst.aemeasurable hx
    have hWeightedScoreIntegrable :
        Integrable (fun o => transportWeight P n o.1 *
          (instrumentScore P n o * boolReal o.2.2.1))
          (sourceObsLaw P n) := by
      refine Integrable.of_bound
        (((hWeightMeasurable.comp measurable_fst).mul
          (hInstrumentScoreMeasurable.mul (by
            unfold boolReal
            have hd : Measurable fun o : SourceObs 𝒳 => o.2.2.1 := by
              fun_prop
            exact Measurable.ite (hd (MeasurableSet.singleton true))
              measurable_const measurable_const))).aestronglyMeasurable)
        ((2 * (k n : ℝ)) * (1 / epsilon)) ?_
      filter_upwards [hWeightBoundObs, hInstrumentScoreBound] with o hw hs
      have hbool : |boolReal o.2.2.1| ≤ 1 := by
        cases o.2.2.1 <;> simp [boolReal]
      have hscoreReceipt :
          |instrumentScore P n o * boolReal o.2.2.1| ≤ 1 / epsilon := by
        rw [abs_mul]
        calc
          |instrumentScore P n o| * |boolReal o.2.2.1| ≤
              (1 / epsilon) * 1 :=
            mul_le_mul hs hbool (abs_nonneg _)
              (one_div_nonneg.mpr hOverlap.1.le)
          _ = 1 / epsilon := mul_one _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1]
      exact mul_le_mul hw.2 hscoreReceipt (abs_nonneg _)
        (mul_nonneg (by positivity) (Nat.cast_nonneg _))
    have hDeltaDIntegrable :
        Integrable (P.deltaD n) (sourceXLaw P n) := by
      refine Integrable.of_bound
        (P.deltaD_measurable n).aestronglyMeasurable 1 ?_
      filter_upwards [hSourceFacts.2.2.2.2.2.2.2.2] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2
    have hWeightedDeltaDIntegrable :
        Integrable (fun x => transportWeight P n x * P.deltaD n x)
          (sourceXLaw P n) := by
      refine Integrable.of_bound
        ((hWeightMeasurable.mul (P.deltaD_measurable n)).aestronglyMeasurable)
        (2 * (k n : ℝ)) ?_
      filter_upwards [hP.weightEnvelope,
        hSourceFacts.2.2.2.2.2.2.2.2] with x hw hd
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1,
        abs_of_nonneg hd.1]
      calc
        transportWeight P n x * P.deltaD n x ≤
            (2 * (k n : ℝ)) * 1 :=
          mul_le_mul hw.2 hd.2 hd.1
            (mul_nonneg (by positivity) (Nat.cast_nonneg _))
        _ = 2 * (k n : ℝ) := mul_one _
    calc
      transportedFirstStage P n =
          ∫ x, transportWeight P n x * P.deltaD n x
            ∂sourceXLaw P n := by
        exact transportedFirstStage_eq_weighted_deltaD
          P k epsilon n hSourceFacts hOverlap hP.weightEnvelope
      _ = ∫ x, transportWeight P n x *
            P.receiptContrast n true x ∂sourceXLaw P n := by
        exact integral_congr_ae
          (hDeltaD.mono fun x hx => by
            simpa using congrArg (fun z => transportWeight P n x * z) hx)
      _ = ∫ x, P.receiptContrast n true x ∂targetXLaw P n := by
        unfold transportWeight
        simpa only [smul_eq_mul] using
          (integral_rnDeriv_smul
            (μ := targetXLaw P n) (ν := sourceXLaw P n)
            (f := P.receiptContrast n true) hDom)
      _ = ∫ x, P.receiptContrast n false x ∂targetXLaw P n :=
        hReceipt.2.symm
      _ = ∫ o, (boolReal (fullD1 o) - boolReal (fullD0 o))
            ∂populationLaw P n false := by
        simpa using (hReceipt.1 false Set.univ MeasurableSet.univ).symm
      _ = ∫ o, (if fullD1 o = true ∧ fullD0 o = false
            then (1 : ℝ) else 0) ∂populationLaw P n false := by
        apply integral_congr_ae
        filter_upwards [hMono false] with o ho
        cases h0 : fullD0 o <;> cases h1 : fullD1 o <;>
          simp [boolReal, h0, h1] at ho ⊢ <;> norm_num at ho
      _ = targetComplierShare P n := by
        unfold targetComplierShare
        have hd1 : Measurable (fullD1 : FullData 𝒳 → Bool) := by
          unfold fullD1
          fun_prop
        have hd0 : Measurable (fullD0 : FullData 𝒳 → Bool) := by
          unfold fullD0
          fun_prop
        have hC : MeasurableSet
            {o : FullData 𝒳 | fullD1 o = true ∧ fullD0 o = false} :=
          (hd1 (MeasurableSet.singleton true)).inter
            (hd0 (MeasurableSet.singleton false))
        simpa [Set.indicator, Measure.real] using
          (integral_indicator_const
            (μ := populationLaw P n false) (1 : ℝ) hC)
  refine ⟨hOutcomeEq, hFirstEq, ?_, ?_⟩
  · unfold targetCACE
    rw [hOutcomeEq, hFirstEq]
  · unfold targetCACE parameterSpace
    let μ := populationLaw P n false
    let C : Set (FullData 𝒳) :=
      {o | fullD1 o = true ∧ fullD0 o = false}
    have hC : MeasurableSet C := by
      have hd1 : Measurable (fullD1 : FullData 𝒳 → Bool) := by
        change Measurable fun o :
          Bool × (𝒳 × (Bool × (Bool × (ℝ × ℝ)))) => o.2.2.2.1
        fun_prop
      have hd0 : Measurable (fullD0 : FullData 𝒳 → Bool) := by
        change Measurable fun o :
          Bool × (𝒳 × (Bool × (Bool × (ℝ × ℝ)))) => o.2.2.1
        fun_prop
      exact (hd1 (MeasurableSet.singleton true)).inter
        (hd0 (MeasurableSet.singleton false))
    have hμac : μ ≪ P.fullLaw n := by
      exact ProbabilityTheory.cond_absolutelyContinuous
    have hbounds : ∀ᵐ o ∂μ,
        -1 ≤ fullY1 o - fullY0 o ∧ fullY1 o - fullY0 o ≤ 1 := by
      filter_upwards [hμac.ae_le hSupport.2] with o ho
      constructor <;> linarith [ho.1.1, ho.1.2, ho.2.1, ho.2.2]
    have hμprob : IsProbabilityMeasure μ := by
      letI : IsProbabilityMeasure (P.fullLaw n) := hSupport.1
      apply ProbabilityTheory.cond_isProbabilityMeasure
      intro hz
      have hz' : (P.fullLaw n {o | fullS o = false}).toReal = 0 := by
        rw [hz]
        simp
      linarith [hPresence false]
    letI : IsProbabilityMeasure μ := hμprob
    have hmeasY : Measurable fun o : FullData 𝒳 =>
        fullY1 o - fullY0 o := by
      dsimp [fullY1, fullY0]
      fun_prop
    have hfint : Integrable (fun o : FullData 𝒳 =>
        (fullY1 o - fullY0 o) * C.indicator (fun _ => (1 : ℝ)) o) μ := by
      refine Integrable.of_bound
        ((hmeasY.mul (measurable_const.indicator hC)).aestronglyMeasurable) 1 ?_
      filter_upwards [hbounds] with o ho
      by_cases hoc : o ∈ C
      · simp only [Set.indicator_of_mem hoc, mul_one, Real.norm_eq_abs]
        rw [abs_le]
        exact ho
      · simp [Set.indicator_of_notMem hoc]
    have honeint : Integrable (C.indicator (fun _ => (1 : ℝ))) μ := by
      refine Integrable.of_bound
        (measurable_const.indicator hC).aestronglyMeasurable 1 ?_
      filter_upwards with o
      by_cases hoc : o ∈ C
      · simp [Set.indicator_of_mem hoc]
      · simp [Set.indicator_of_notMem hoc]
    have hnumUpper :
        (∫ o, (fullY1 o - fullY0 o) *
          C.indicator (fun _ => (1 : ℝ)) o ∂μ) ≤
          ∫ o, C.indicator (fun _ => (1 : ℝ)) o ∂μ := by
      apply integral_mono_ae hfint honeint
      filter_upwards [hbounds] with o ho
      by_cases hoc : o ∈ C
      · simp [Set.indicator_of_mem hoc, ho.2]
      · simp [Set.indicator_of_notMem hoc]
    have hnumLower :
        -(∫ o, C.indicator (fun _ => (1 : ℝ)) o ∂μ) ≤
          ∫ o, (fullY1 o - fullY0 o) *
            C.indicator (fun _ => (1 : ℝ)) o ∂μ := by
      rw [← integral_neg]
      apply integral_mono_ae honeint.neg hfint
      filter_upwards [hbounds] with o ho
      by_cases hoc : o ∈ C
      · simp [Set.indicator_of_mem hoc, ho.1]
      · simp [Set.indicator_of_notMem hoc]
    have hindicator :
        (∫ o, C.indicator (fun _ => (1 : ℝ)) o ∂μ) =
          (μ C).toReal := by
      simpa [Measure.real] using
        (integral_indicator_const (μ := μ) (1 : ℝ) hC)
    have hpos : 0 < (μ C).toReal := hPositive
    have hif (o : FullData 𝒳) :
        (if fullD1 o = true ∧ fullD0 o = false then (1 : ℝ) else 0) =
          C.indicator (fun _ => (1 : ℝ)) o := by
      by_cases ho : fullD1 o = true ∧ fullD0 o = false
      · simp [ho, C]
      · simp [ho, C]
    change
      (∫ o, (fullY1 o - fullY0 o) *
        (if fullD1 o = true ∧ fullD0 o = false then 1 else 0) ∂μ) /
          (μ C).toReal ∈ Set.Icc (-1 : ℝ) 1
    simp_rw [hif]
    constructor
    · rw [le_div_iff₀ hpos]
      rw [← hindicator]
      simpa using hnumLower
    · rw [div_le_iff₀ hpos]
      rw [← hindicator]
      simpa using hnumUpper

end CausalSmith.Stat.TransportedLateStrengthFrontier
