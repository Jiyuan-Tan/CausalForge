/-
# Frontier order assembly

The two monotonicity steps the source's converse takes: a globally honest
procedure restricts to a slice-honest one, and the conditional minimax value is
bounded by each globally honest procedure's risk.  These live downstream of
`Helpers.Witness` because they consume `fixedGeometrySlice_eventually_inhabited`
(the slice must be nonempty, or the infimum defining slice honesty collapses).
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.Witness
import Causalean.Stat.Minimax.HonestConfidenceSet

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory
open scoped ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]
variable (N k : ℕ → ℕ) (c epsilon alpha : ℝ)

/-- On an inhabited row, `coverageInfOrOne` is the ordinary infimum. -/
lemma coverageInfOrOne_of_nonempty {ι : Sort*} [Nonempty ι] (f : ι → ℝ) :
    coverageInfOrOne f = ⨅ i, f i := by
  exact Causalean.Stat.coverageInfOrOne_of_nonempty f

/-- On an empty row, `coverageInfOrOne` has its declared vacuous value. -/
lemma coverageInfOrOne_of_isEmpty {ι : Sort*} [IsEmpty ι] (f : ι → ℝ) :
    coverageInfOrOne f = 1 := by
  exact Causalean.Stat.coverageInfOrOne_of_isEmpty f

/-- The full representative-fiber coverage infimum is bounded by evaluation at
the canonical representative of any particular class member. -/
lemma oracleCoverageClassInf_le_canonical
    (C : OracleProcedure 𝒳 N k c epsilon) (P : TransportedArray 𝒳) (n : ℕ)
    (hP : TransportedIVClass P N k c epsilon n) :
    oracleCoverageClassInf N k c epsilon C n ≤ oracleCoverage C P n := by
  letI : Nonempty
      {Q : TransportedArray 𝒳 //
        TransportedIVClass Q N k c epsilon n} :=
    ⟨⟨P, hP⟩⟩
  have hbounded :
      BddBelow (Set.range (fun Q :
          {Q : TransportedArray 𝒳 //
            TransportedIVClass Q N k c epsilon n} =>
        oracleCoverage C Q n)) :=
    ⟨0, by
      rintro y ⟨Q, rfl⟩
      exact ENNReal.toReal_nonneg⟩
  rw [oracleCoverageClassInf, coverageInfOrOne_of_nonempty]
  exact ciInf_le hbounded ⟨P, hP⟩

/-- Every rowwise full-fiber coverage infimum is nonnegative. -/
lemma oracleCoverageClassInf_nonneg
    (C : OracleProcedure 𝒳 N k c epsilon) (n : ℕ)
    (h : ∃ P : TransportedArray 𝒳,
      TransportedIVClass P N k c epsilon n) :
    0 ≤ oracleCoverageClassInf N k c epsilon C n := by
  let P := h.choose
  letI : Nonempty
      {Q : TransportedArray 𝒳 //
        TransportedIVClass Q N k c epsilon n} :=
    ⟨⟨P, h.choose_spec⟩⟩
  rw [oracleCoverageClassInf, coverageInfOrOne_of_nonempty]
  exact le_ciInf (fun q => ENNReal.toReal_nonneg)

/-- The full representative-fiber risk row dominates canonical evaluation at
every member above the strength threshold. -/
lemma oracleExpectedLength_le_frontierRiskRow
    (C : OracleProcedure 𝒳 N k c epsilon) (P : TransportedArray 𝒳) (n : ℕ) (t0 : ℝ)
    (hP : TransportedIVClass P N k c epsilon n)
    (ht : t0 ≤ effectiveStrength P n) :
    oracleExpectedLength C P n ≤ frontierRiskRow N k c epsilon C t0 n := by
  have hsetLength_le_two : ∀ A : Set ℝ, setLength A ≤ 2 := by
    intro A
    unfold setLength parameterSpace
    calc
      (volume (A ∩ Set.Icc (-1 : ℝ) 1)).toReal ≤
          (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Icc])
          (measure_mono Set.inter_subset_right)
      _ = 2 := by
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
        norm_num
  have hbounded :
      BddAbove (Set.range (fun Q :
          {Q : TransportedArray 𝒳 //
            TransportedIVClass Q N k c epsilon n ∧
              t0 ≤ effectiveStrength Q n} =>
        oracleExpectedLength C Q n)) :=
    ⟨2, by
      rintro y ⟨Q, rfl⟩
      letI : IsProbabilityMeasure (sourceObsLaw Q.1 n) :=
        Q.property.1.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (targetXLaw Q.1 n) :=
        Q.property.1.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw Q.1 N n) := by
        unfold twoSampleLaw
        infer_instance
      exact (integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        (integrable_const 2)
        (Filter.Eventually.of_forall fun s =>
          hsetLength_le_two
            (oracleSet C Q.1 n s))).trans_eq (by simp)⟩
  unfold frontierRiskRow
  exact le_ciSup hbounded ⟨P, hP, ht⟩

/-- Canonical evaluation at a finite-cell row is bounded by the full
representative-fiber finite-cell risk row. -/
lemma oracleExpectedLength_le_finiteCellOracleRiskRow
    (C : OracleProcedure 𝒳 N k c epsilon) (P : TransportedArray 𝒳) (n : ℕ) (t0 : ℝ)
    (hP : FiniteCellClass P N k c epsilon n)
    (ht : t0 ≤ effectiveStrength P n) :
    oracleExpectedLength C P n ≤
      finiteCellOracleRiskRow N k c epsilon C t0 n := by
  have hsetLength_le_two : ∀ A : Set ℝ, setLength A ≤ 2 := by
    intro A
    unfold setLength parameterSpace
    calc
      (volume (A ∩ Set.Icc (-1 : ℝ) 1)).toReal ≤
          (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Icc])
          (measure_mono Set.inter_subset_right)
      _ = 2 := by
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
        norm_num
  have hbounded :
      BddAbove (Set.range (fun Q :
          {Q : TransportedArray 𝒳 //
            FiniteCellClass Q N k c epsilon n ∧
              t0 ≤ effectiveStrength Q n} =>
        oracleExpectedLength C Q n)) :=
    ⟨2, by
      rintro y ⟨Q, rfl⟩
      letI : IsProbabilityMeasure (sourceObsLaw Q.1 n) :=
        Q.property.1.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (targetXLaw Q.1 n) :=
        Q.property.1.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw Q.1 N n) := by
        unfold twoSampleLaw
        infer_instance
      exact (integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        (integrable_const 2)
        (Filter.Eventually.of_forall fun s =>
          hsetLength_le_two
            (oracleSet C Q.1 n s))).trans_eq (by simp)⟩
  unfold finiteCellOracleRiskRow
  exact le_ciSup hbounded ⟨P, hP, ht⟩

/-- Full-fiber finite-cell oracle risk rows retain the diameter-two bound. -/
lemma finiteCellOracleRiskRow_le_two
    (C : OracleProcedure 𝒳 N k c epsilon) (n : ℕ) (t0 : ℝ) :
    finiteCellOracleRiskRow N k c epsilon C t0 n ≤ 2 := by
  cases isEmpty_or_nonempty
      {P : TransportedArray 𝒳 //
        FiniteCellClass P N k c epsilon n ∧
          t0 ≤ effectiveStrength P n} with
  | inl h =>
      letI := h
      simp [finiteCellOracleRiskRow]
  | inr h =>
      letI := h
      unfold finiteCellOracleRiskRow
      refine ciSup_le (fun q => ?_)
      letI : IsProbabilityMeasure (sourceObsLaw q.1 n) :=
        q.property.1.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (targetXLaw q.1 n) :=
        q.property.1.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw q.1 N n) := by
        unfold twoSampleLaw
        infer_instance
      have hsetLength_le_two : ∀ A : Set ℝ, setLength A ≤ 2 := by
        intro A
        unfold setLength parameterSpace
        calc
          (volume (A ∩ Set.Icc (-1 : ℝ) 1)).toReal ≤
              (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
            ENNReal.toReal_mono (by simp [Real.volume_Icc])
              (measure_mono Set.inter_subset_right)
          _ = 2 := by
            rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
            norm_num
      exact (integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        (integrable_const 2)
        (Filter.Eventually.of_forall fun s =>
          hsetLength_le_two
            (oracleSet C q.1 n s))).trans_eq (by simp)

/-- A globally honest procedure restricts to every fixed geometry because the
geometry's declared weight is itself a member of each row's full version
fiber. -/
lemma OracleHonest.fixedGeometry
    (C : OracleProcedure 𝒳 N k c epsilon)
    (hC : OracleHonest N k c epsilon alpha C)
    (g : Geometry 𝒳) (t0 : ℝ)
    (hc : 0 < c) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2) (ht0 : 0 < t0)
    (hg : AdmissibleGeometry g k epsilon)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n) atTop (𝓝 0)) :
    ∃ D : OracleProcedure 𝒳 N k c epsilon,
      FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ D ∧
      fixedGeometryRisk N k c epsilon g D t0 ≤
        frontierRiskTotal N k c epsilon C t0 := by
  classical
  let D : OracleProcedure 𝒳 N k c epsilon := C
  have hgeometryWeightInput_eq (n : ℕ) :
      (geometryWeightInput g n : 𝒳 → ℝ) = g.weight n := by
    simp [geometryWeightInput, fun x => (hg.2.2.2.2.2.1 n x).1]
  let geometryVersion (n : ℕ) (P : TransportedArray 𝒳)
      (hP : fixedGeometrySlice P g N k c epsilon n) :
      TransportWeightVersion P n :=
    ⟨geometryWeightInput g n,
      by simpa [hgeometryWeightInput_eq n] using g.weight_measurable n,
      by simpa only [hgeometryWeightInput_eq n] using hP.2.2.2.1.symm⟩
  have hset_eq (n : ℕ) (P : TransportedArray 𝒳)
      (hP : fixedGeometrySlice P g N k c epsilon n)
      (s : TwoSample 𝒳 n (N n)) :
      fixedGeometryOracleSet D g n s =
        oracleSetAtWeight C P n (geometryVersion n P hP) s := by
    simp only [D, fixedGeometryOracleSet, oracleSetAtWeight,
      geometryVersion, hP.2.2.2.2]
  have hcoverage_eq (n : ℕ) (P : TransportedArray 𝒳)
      (hP : fixedGeometrySlice P g N k c epsilon n) :
      fixedGeometryOracleCoverage D g P n =
        oracleCoverage C P n := by
    unfold fixedGeometryOracleCoverage oracleCoverage
    congr 1
    apply measure_congr
    filter_upwards [
      C.weightAEInvariant n P hP.1 (geometryVersion n P hP)
        (canonicalTransportWeightVersion P n)
    ] with s hs
    simpa only [hset_eq n P hP, oracleSet, oracleSetAtWeight] using
      congrArg (fun A : Set ℝ => targetCACE P n ∈ A) hs
  have hexpectedLength_eq (n : ℕ) (P : TransportedArray 𝒳)
      (hP : fixedGeometrySlice P g N k c epsilon n) :
      fixedGeometryOracleExpectedLength D g P n =
        oracleExpectedLength C P n := by
    unfold fixedGeometryOracleExpectedLength oracleExpectedLength
    apply integral_congr_ae
    filter_upwards [
      C.weightAEInvariant n P hP.1 (geometryVersion n P hP)
        (canonicalTransportWeightVersion P n)
    ] with s hs
    simpa only [hset_eq n P hP, oracleSet, oracleSetAtWeight] using
      congrArg setLength hs
  have hcoverage_nonneg (E : OracleProcedure 𝒳 N k c epsilon)
      (P : TransportedArray 𝒳) (n : ℕ) :
      0 ≤ oracleCoverage E P n := by
    exact ENNReal.toReal_nonneg
  have hcoverage_le_one (E : OracleProcedure 𝒳 N k c epsilon)
      (P : TransportedArray 𝒳) (n : ℕ)
      (hP : TransportedIVClass P N k c epsilon n) :
      oracleCoverage E P n ≤ 1 := by
    letI : IsProbabilityMeasure (sourceObsLaw P n) :=
      hP.twoSampleArray.2.1 n
    letI : IsProbabilityMeasure (targetXLaw P n) :=
      hP.twoSampleArray.2.2.1 n
    letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
      unfold twoSampleLaw
      infer_instance
    exact measureReal_le_one
  have hsetLength_nonneg : ∀ A : Set ℝ, 0 ≤ setLength A :=
    fun _ => ENNReal.toReal_nonneg
  have hsetLength_le_two : ∀ A : Set ℝ, setLength A ≤ 2 := by
    intro A
    unfold setLength parameterSpace
    calc
      (volume (A ∩ Set.Icc (-1 : ℝ) 1)).toReal ≤
          (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Icc])
          (measure_mono Set.inter_subset_right)
      _ = 2 := by
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
        norm_num
  have hexpectedLength_le_two (E : OracleProcedure 𝒳 N k c epsilon)
      (P : TransportedArray 𝒳) (n : ℕ)
      (hP : TransportedIVClass P N k c epsilon n) :
      oracleExpectedLength E P n ≤ 2 := by
    letI : IsProbabilityMeasure (sourceObsLaw P n) :=
      hP.twoSampleArray.2.1 n
    letI : IsProbabilityMeasure (targetXLaw P n) :=
      hP.twoSampleArray.2.2.1 n
    letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
      unfold twoSampleLaw
      infer_instance
    exact (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      (integrable_const 2)
      (Filter.Eventually.of_forall fun s =>
        hsetLength_le_two (oracleSet E P n s))).trans_eq (by simp)
  have hinhabited :
      ∀ᶠ n in atTop, ∃ P : TransportedArray 𝒳,
        fixedGeometrySlice P g N k c epsilon n ∧
        t0 ≤ effectiveStrength P n :=
    fixedGeometrySlice_eventually_inhabited g N k c epsilon t0 hc
      hepsilon ht0 hg hN hkPos hkInf hkRoot
  have hcoverage_rows :
      ∀ᶠ n in atTop,
        oracleCoverageClassInf N k c epsilon C n ≤
        coverageInfOrOne (fun P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n} =>
          fixedGeometryOracleCoverage D g P n) := by
    filter_upwards [hinhabited] with n hn
    obtain ⟨P₀, hP₀, _ht₀⟩ := hn
    letI : Nonempty {P : TransportedArray 𝒳 //
        fixedGeometrySlice P g N k c epsilon n} :=
      ⟨⟨P₀, hP₀⟩⟩
    letI : Nonempty {P : TransportedArray 𝒳 //
        TransportedIVClass P N k c epsilon n} :=
      ⟨⟨P₀, hP₀.1⟩⟩
    rw [coverageInfOrOne_of_nonempty]
    refine le_ciInf (fun P => ?_)
    have hglobal_bdd :
        BddBelow (Set.range (fun Q :
            {Q : TransportedArray 𝒳 //
              TransportedIVClass Q N k c epsilon n} =>
          oracleCoverage C Q n)) :=
      ⟨0, by
        rintro y ⟨Q, rfl⟩
        exact hcoverage_nonneg C Q n⟩
    rw [oracleCoverageClassInf, coverageInfOrOne_of_nonempty]
    exact (ciInf_le hglobal_bdd
      ⟨P, P.property.1⟩).trans_eq
      (hcoverage_eq n P P.property).symm
  have hglobal_coverage_nonneg :
      ∀ᶠ n in atTop,
        0 ≤ oracleCoverageClassInf N k c epsilon C n := by
    filter_upwards [hinhabited] with n hn
    obtain ⟨P₀, hP₀, _ht₀⟩ := hn
    letI : Nonempty
        {P : TransportedArray 𝒳 //
          TransportedIVClass P N k c epsilon n} :=
      ⟨⟨P₀, hP₀.1⟩⟩
    rw [oracleCoverageClassInf, coverageInfOrOne_of_nonempty]
    exact le_ciInf (fun Q => hcoverage_nonneg C Q n)
  have hslice_coverage_le_one :
      ∀ᶠ n in atTop,
        coverageInfOrOne (fun P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n} =>
          fixedGeometryOracleCoverage D g P n) ≤ 1 := by
    filter_upwards [hinhabited] with n hn
    obtain ⟨P₀, hP₀, _ht₀⟩ := hn
    letI : Nonempty {P : TransportedArray 𝒳 //
        fixedGeometrySlice P g N k c epsilon n} :=
      ⟨⟨P₀, hP₀⟩⟩
    rw [coverageInfOrOne_of_nonempty]
    have hslice_bdd :
        BddBelow (Set.range (fun P :
            {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n} =>
          fixedGeometryOracleCoverage D g P n)) :=
      ⟨0, by
        rintro y ⟨P, rfl⟩
        change 0 ≤ fixedGeometryOracleCoverage D g P n
        rw [hcoverage_eq n P P.property]
        exact hcoverage_nonneg C P n⟩
    exact (ciInf_le hslice_bdd ⟨P₀, hP₀⟩).trans
      ((hcoverage_eq n P₀ hP₀).le.trans
        (hcoverage_le_one C P₀ n hP₀.1))
  have hglobal_coverage_bounded :
      IsBoundedUnder (· ≥ ·) atTop
        (oracleCoverageClassInf N k c epsilon C) := by
    change ∃ b, ∀ᶠ n in atTop, b ≤ _
    exact ⟨0, hglobal_coverage_nonneg⟩
  have hslice_coverage_cobounded :
      IsCoboundedUnder (· ≥ ·) atTop
        (fun n => coverageInfOrOne (fun P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n} =>
          fixedGeometryOracleCoverage D g P n)) := by
    change ∃ b, ∀ a, (∀ᶠ n in atTop, a ≤ _) → a ≤ b
    refine ⟨1, fun a ha => ?_⟩
    have ha_one :=
      (ha.and hslice_coverage_le_one).exists.choose_spec
    exact ha_one.1.trans ha_one.2
  have hD_honest :
      FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ D := by
    refine ⟨hC.1, hC.2.1, hC.2.2.trans ?_⟩
    exact Filter.liminf_le_liminf hcoverage_rows
      hglobal_coverage_bounded hslice_coverage_cobounded
  have hfixed_risk_rows_nonneg : ∀ n,
      0 ≤ (⨆ P : {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n},
        fixedGeometryOracleExpectedLength D g P n) := by
    intro n
    cases isEmpty_or_nonempty
        {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n} with
    | inl h =>
        letI := h
        calc
          0 ≤ (0 : ℝ) := le_rfl
          _ = (⨆ P : {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n ∧
                t0 ≤ effectiveStrength P n},
              fixedGeometryOracleExpectedLength D g P n) :=
            ((iSup_of_empty' _).trans Real.sSup_empty).symm
    | inr h =>
        let P := Classical.choice h
        refine le_trans ?_ (le_ciSup ?_ P)
        · exact integral_nonneg (fun s =>
            hsetLength_nonneg (fixedGeometryOracleSet D g n s))
        · exact ⟨2, by
            rintro y ⟨Q, rfl⟩
            change fixedGeometryOracleExpectedLength D g Q n ≤ 2
            rw [hexpectedLength_eq n Q Q.property.1]
            exact hexpectedLength_le_two C Q n Q.property.1.1⟩
  have hglobal_risk_rows_le_two : ∀ n,
      frontierRiskRow N k c epsilon C t0 n ≤ 2 := by
    intro n
    cases isEmpty_or_nonempty
        {P : TransportedArray 𝒳 //
          TransportedIVClass P N k c epsilon n ∧
            t0 ≤ effectiveStrength P n} with
    | inl h =>
        letI := h
        unfold frontierRiskRow
        calc
          (⨆ P : {P : TransportedArray 𝒳 //
                TransportedIVClass P N k c epsilon n ∧
                  t0 ≤ effectiveStrength P n},
              oracleExpectedLength C P n) =
              0 := (iSup_of_empty' _).trans Real.sSup_empty
          _ ≤ 2 := by norm_num
    | inr h =>
        letI := h
        unfold frontierRiskRow
        refine ciSup_le (fun q =>
          hexpectedLength_le_two C q n q.property.1)
  have hrisk_rows :
      ∀ᶠ n in atTop,
        (⨆ P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n},
          fixedGeometryOracleExpectedLength D g P n) ≤
        frontierRiskRow N k c epsilon C t0 n := by
    filter_upwards [hinhabited] with n hn
    obtain ⟨P₀, hP₀, htP₀⟩ := hn
    letI : Nonempty {P : TransportedArray 𝒳 //
        fixedGeometrySlice P g N k c epsilon n ∧
          t0 ≤ effectiveStrength P n} :=
      ⟨⟨P₀, hP₀, htP₀⟩⟩
    refine ciSup_le (fun P => ?_)
    have hglobal_bdd :
        BddAbove (Set.range (fun Q :
            {Q : TransportedArray 𝒳 //
              TransportedIVClass Q N k c epsilon n ∧
                t0 ≤ effectiveStrength Q n} =>
          oracleExpectedLength C Q n)) :=
      ⟨2, by
        rintro y ⟨Q, rfl⟩
        exact hexpectedLength_le_two C Q n Q.property.1⟩
    unfold frontierRiskRow
    exact (hexpectedLength_eq n P P.property.1).le.trans
      (le_ciSup hglobal_bdd
        ⟨P, P.property.1.1, P.property.2⟩)
  have hfixed_risk_cobounded :
      IsCoboundedUnder (· ≤ ·) atTop
        (fun n => ⨆ P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n},
          fixedGeometryOracleExpectedLength D g P n) := by
    change ∃ b, ∀ a, (∀ᶠ n in atTop, _ ≤ a) → b ≤ a
    refine ⟨0, fun a ha => ?_⟩
    have hzero_a :=
      ((Filter.Eventually.of_forall hfixed_risk_rows_nonneg).and
        ha).exists.choose_spec
    exact hzero_a.1.trans hzero_a.2
  have hglobal_risk_bounded :
      IsBoundedUnder (· ≤ ·) atTop
        (frontierRiskRow N k c epsilon C t0) := by
    change ∃ b, ∀ᶠ n in atTop, _ ≤ b
    exact ⟨2, Filter.Eventually.of_forall hglobal_risk_rows_le_two⟩
  refine ⟨D, hD_honest, ?_⟩
  exact Filter.limsup_le_limsup hrisk_rows
    hfixed_risk_cobounded hglobal_risk_bounded

/-- Consequently the conditional minimax value is bounded by the risk of each
globally honest procedure, without identifying a.e.-equal weight versions
pointwise. -/
lemma fixedGeometryValue_le_frontierRisk
    (g : Geometry 𝒳) (C : OracleProcedure 𝒳 N k c epsilon)
    (hC : OracleHonest N k c epsilon alpha C) (t0 : ℝ)
    (hc : 0 < c) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2) (ht0 : 0 < t0)
    (hg : AdmissibleGeometry g k epsilon)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n) atTop (𝓝 0)) :
    fixedGeometryValueTotal N k c epsilon alpha ⟨g, hg⟩ t0 ≤
      frontierRiskTotal N k c epsilon C t0 := by
  classical
  obtain ⟨D, hD, hDC⟩ :=
    OracleHonest.fixedGeometry (N := N) (k := k) (c := c)
      (epsilon := epsilon) (alpha := alpha) C hC g t0
      hc hepsilon ht0 hg hN hkPos hkInf hkRoot
  have hsetLength_nonneg : ∀ A : Set ℝ, 0 ≤ setLength A :=
    fun _ => ENNReal.toReal_nonneg
  have hsetLength_le_two : ∀ A : Set ℝ, setLength A ≤ 2 := by
    intro A
    unfold setLength parameterSpace
    calc
      (volume (A ∩ Set.Icc (-1 : ℝ) 1)).toReal ≤
          (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono (by simp [Real.volume_Icc])
          (measure_mono Set.inter_subset_right)
      _ = 2 := by
        rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
        norm_num
  have hrisk_nonneg : ∀ E : OracleProcedure 𝒳 N k c epsilon,
      0 ≤ fixedGeometryRisk N k c epsilon g E t0 := by
    intro E
    letI : (atTop : Filter ℕ).NeBot := inferInstance
    have hrow_nonneg : ∀ n,
        0 ≤ (⨆ P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n},
          fixedGeometryOracleExpectedLength E g P n) := by
      intro n
      cases isEmpty_or_nonempty
          {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n} with
      | inl h =>
          simp
      | inr h =>
          let P := Classical.choice h
          refine le_trans ?_ (le_ciSup ?_ P)
          · exact integral_nonneg (fun s =>
              hsetLength_nonneg (fixedGeometryOracleSet E g n s))
          · exact ⟨2, by
              rintro y ⟨Q, rfl⟩
              change fixedGeometryOracleExpectedLength E g Q n ≤ 2
              letI : IsProbabilityMeasure
                  (sourceObsLaw (Q : TransportedArray 𝒳) n) :=
                Q.property.1.1.twoSampleArray.2.1 n
              letI : IsProbabilityMeasure
                  (targetXLaw (Q : TransportedArray 𝒳) n) :=
                Q.property.1.1.twoSampleArray.2.2.1 n
              letI : IsProbabilityMeasure
                  (twoSampleLaw (Q : TransportedArray 𝒳) N n) := by
                unfold twoSampleLaw
                infer_instance
              exact (integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
                (integrable_const 2)
                (Filter.Eventually.of_forall fun s =>
                  hsetLength_le_two
                    (fixedGeometryOracleSet E g n s))).trans_eq (by simp)⟩
    have hrow_le_two : ∀ n,
        (⨆ P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n},
          fixedGeometryOracleExpectedLength E g P n) ≤ 2 := by
      intro n
      cases isEmpty_or_nonempty
          {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n} with
      | inl h =>
          simp
      | inr h =>
          refine ciSup_le (fun P => ?_)
          letI : IsProbabilityMeasure
              (sourceObsLaw (P : TransportedArray 𝒳) n) :=
            P.property.1.1.twoSampleArray.2.1 n
          letI : IsProbabilityMeasure
              (targetXLaw (P : TransportedArray 𝒳) n) :=
            P.property.1.1.twoSampleArray.2.2.1 n
          letI : IsProbabilityMeasure
              (twoSampleLaw (P : TransportedArray 𝒳) N n) := by
            unfold twoSampleLaw
            infer_instance
          exact (integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
            (integrable_const 2)
            (Filter.Eventually.of_forall fun s =>
              hsetLength_le_two
                (fixedGeometryOracleSet E g n s))).trans_eq (by simp)
    have hzero_cobounded :
        IsCoboundedUnder (· ≤ ·) atTop (fun _ : ℕ => (0 : ℝ)) := by
      change ∃ b, ∀ a, (∀ᶠ _n : ℕ in atTop, (0 : ℝ) ≤ a) → b ≤ a
      exact ⟨0, fun a ha => ha.exists.choose_spec⟩
    have hrow_bounded :
        IsBoundedUnder (· ≤ ·) atTop
          (fun n => ⨆ P : {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n ∧
                t0 ≤ effectiveStrength P n},
            fixedGeometryOracleExpectedLength E g P n) := by
      change ∃ b, ∀ᶠ n in atTop, _ ≤ b
      exact ⟨2, Filter.Eventually.of_forall hrow_le_two⟩
    change 0 ≤ Filter.limsup _ atTop
    rw [← Filter.limsup_const (f := (atTop : Filter ℕ)) (0 : ℝ)]
    exact Filter.limsup_le_limsup
      (Filter.Eventually.of_forall hrow_nonneg)
      hzero_cobounded hrow_bounded
  have hvalues_bdd :
      BddBelow (Set.range (fun E :
          {E : OracleProcedure 𝒳 N k c epsilon //
            FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ E} =>
        fixedGeometryRisk N k c epsilon g E.1 t0)) :=
    ⟨0, by
      rintro y ⟨E, rfl⟩
      exact hrisk_nonneg E⟩
  exact (ciInf_le hvalues_bdd ⟨D, hD⟩).trans hDC

end CausalSmith.Stat.TransportedLateStrengthFrontier
