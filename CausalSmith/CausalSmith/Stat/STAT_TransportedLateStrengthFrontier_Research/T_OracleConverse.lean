/-
# Global and finite-cell oracle converse
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_NoShiftReduction

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory
open scoped Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

set_option maxHeartbeats 2000000 in
-- The proof compares nested full-fiber suprema and infima over model rows.
-- @node: thm:oracle-converse
/-- Universal lower-frontier constants apply both globally and to the
finite-cell oracle submodel and are invariant to the decomposition of effective
strength into first stage and Kish dispersion. -/
theorem oracle_converse
    (epsilon alpha c : ℝ)
    (hc : 0 < c)
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (halpha : 0 < alpha ∧ alpha < 1) :
      -- @realizes \alpha(noncoverage in (0,1))
    ∃ c0 tc : ℝ,
      0 < c0 ∧ -- @realizes c_0(positive lower-frontier constant)
      0 < tc ∧ -- @realizes t_c(positive transition threshold)
      ∀ {𝒳 : Type*} [MeasurableSpace 𝒳]
        (N k : ℕ → ℕ)
        (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
          -- @realizes N_n(N_n/n→c)
        (hkPos : ∀ n, 0 < k n)
        (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
        (hkRoot : Tendsto (fun n : ℕ =>
          (k n : ℝ) / Real.sqrt n) atTop (𝓝 0))
          -- @realizes k_n(positive, diverging, and o(√n))
        (hCarrier : ∀ n, ∃ cell : Fin (k n) ↪ 𝒳, ∀ i, MeasurableSet {cell i})
        (hFullData : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → FullDataSupport P n)
        (hPresence : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → PopulationPresence P n)
        (hTwo : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → TwoSampleArray P N c)
        (hOverlap : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → InstrumentOverlap P n epsilon)
        (hObservation : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n →
            SourceAssignmentConsistency P n)
        (hRandomization : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → IVRandomization P n)
        (hExclusion : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → IVExclusion P n)
        (hMonotonicity : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → IVMonotonicity P n)
        (hOutcomeTransport : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → OutcomeTransport P n)
        (hReceiptTransport : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → ReceiptTransport P n)
        (hComplierPositive : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → TargetComplierPositivity P n)
        (hDomination : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → TransportDomination P n)
        (hEnvelope : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → WeightEnvelope P k n)
        (hSecond : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → WeightSecondMoment P k n)
        (hDegrade : ∀ n (P : TransportedArray 𝒳),
          TransportedIVClass P N k c epsilon n → DegradingArray P k)
        (hFiniteCell : ∀ n (P : TransportedArray 𝒳),
          FiniteCellClass P N k c epsilon n → FiniteCellSource P k n)
        (t0 : ℝ), ∀ ht0 : 0 < t0, -- @realizes t_0(positive frontier threshold)
          c0 * min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
            oracleValue (𝒳 := 𝒳) N k c epsilon alpha ⟨t0, ht0⟩ ∧
          c0 * min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
            finiteCellOracleValue (𝒳 := 𝒳) N k c epsilon alpha ⟨t0, ht0⟩ ∧
          (t0 ≤ tc →
            c0 ≤ oracleValue (𝒳 := 𝒳) N k c epsilon alpha ⟨t0, ht0⟩) := by
  refine ⟨3 * (1 - alpha) ^ 2 / 16, 1, ?_, by norm_num, ?_⟩
  · have : 0 < 1 - alpha := sub_pos.mpr halpha.2
    positivity
  intro 𝒳 _ N k hN hkPos hkInf hkRoot hCarrier hFullData hPresence
    hTwo hOverlap hObservation hRandomization hExclusion hMonotonicity
    hOutcomeTransport hReceiptTransport hComplierPositive hDomination hEnvelope
    hSecond hDegrade hFiniteCell t0 ht0
  have hFiniteInhabited :=
    finiteCellClass_inhabited N k c epsilon hCarrier hc hepsilon hN hkPos hkInf
      hkRoot
  have hMainInhabited :=
    transportedIVClass_inhabited N k c epsilon hCarrier hc hepsilon hN hkPos
      hkInf hkRoot
  classical
  choose cell hcell using hCarrier
  let μ : ℕ → Measure 𝒳 := fun n =>
    ∑ i : Fin (k n), (k n : ENNReal)⁻¹ • Measure.dirac (cell n i)
  have hkinv (n : ℕ) : (k n : ENNReal) * (k n : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hkPos n)))
      (ENNReal.natCast_ne_top (k n))
  have hμ : ∀ n, IsProbabilityMeasure (μ n) := by
    intro n
    rw [isProbabilityMeasure_iff]
    simp [μ, hkinv n]
  let g : Geometry 𝒳 :=
    { sourceX := μ
      targetX := μ
      weight := fun _ _ => 1
      propensity := fun _ _ => 1 / 2
      weight_measurable := fun _ => measurable_const
      propensity_measurable := fun _ => measurable_const }
  have hg : AdmissibleGeometry g k epsilon := by
    refine ⟨hμ, hμ, hepsilon.1, hepsilon.2, ?_, ?_, ?_, ?_, ?_⟩
    · intro n x
      dsimp [g]
      constructor
      · exact hepsilon.2.le
      · linarith [hepsilon.2]
    · intro n x
      dsimp [g]
      constructor
      · norm_num
      · have hk1 : (1 : ℝ) ≤ k n := by exact_mod_cast hkPos n
        linarith
    · intro n
      letI : IsProbabilityMeasure (μ n) := hμ n
      simp [g]
    · intro n
      letI : IsProbabilityMeasure (μ n) := hμ n
      have hk1 : (1 : ℝ) ≤ k n := by exact_mod_cast hkPos n
      simpa [g] using hk1
    · intro n A hA
      letI : IsProbabilityMeasure (μ n) := hμ n
      simpa [g] using (ofReal_setIntegral_one (μ n) A).symm
  have hSliceFinite : ∀ n (P : TransportedArray 𝒳),
      fixedGeometrySlice P g N k c epsilon n →
        FiniteCellClass P N k c epsilon n := by
    intro n P hP
    refine { hP.1 with finiteCellSource := ?_ }
    refine ⟨hkPos n, ?_, cell n, hcell n, ?_, ?_, ?_, ?_⟩
    · rw [hP.2.1]
      exact hμ n
    · rw [hP.2.1]
      rw [show Set.range (cell n) = ⋃ i, {cell n i} by
        ext x
        simp]
      simp only [g, μ, Measure.finset_sum_apply, Measure.smul_apply]
      simp [Measure.dirac_apply_of_mem, hkinv n]
    · intro i
      rw [hP.2.1]
      simp only [g, μ, Measure.finset_sum_apply, Measure.smul_apply]
      rw [Finset.sum_eq_single i]
      · simp [ENNReal.toReal_inv]
      · intro j _ hji
        have hne : cell n j ≠ cell n i :=
          fun h => hji ((cell n).injective h)
        rw [Measure.dirac_apply' _ (hcell n i)]
        simp [hne]
      · simp
    · rw [hP.2.1]
      rfl
    · filter_upwards with x
      rw [hP.2.2.2.2]
  let Dfull : OracleProcedure 𝒳 N k c epsilon :=
    { set := fun _ _ => parameterSpace
      subset := fun _ _ => Set.Subset.rfl
      measurableGraph := by
        intro _ _ _ _ _
        exact measurableSet_Icc.preimage measurable_snd
      weightAEInvariant := by
        intro _ _ _ _ _
        exact Filter.Eventually.of_forall (fun _ => rfl) }
  have hfullCoverage : ∀ n P,
      TransportedIVClass P N k c epsilon n →
        oracleCoverage Dfull P n = 1 := by
    intro n P hP
    letI : IsProbabilityMeasure (sourceObsLaw P n) :=
      hP.twoSampleArray.2.1 n
    letI : IsProbabilityMeasure (targetXLaw P n) :=
      hP.twoSampleArray.2.2.1 n
    letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
      unfold twoSampleLaw
      infer_instance
    have htheta : targetCACE P n ∈ parameterSpace :=
      (scoreRiskClass_compact_causal_range
        (transportedIVScoreRiskAtoms N k c epsilon) hP).2.2.2.2.2
    simp [oracleCoverage, oracleSet, Dfull, htheta]
  have hfullCoverageClassInf : ∀ n,
      oracleCoverageClassInf N k c epsilon Dfull n = 1 := by
    intro n
    let P := (hMainInhabited n).choose
    letI : Nonempty
        {Q : TransportedArray 𝒳 //
          TransportedIVClass Q N k c epsilon n} :=
      ⟨⟨P, (hMainInhabited n).choose_spec⟩⟩
    apply le_antisymm
    · exact (oracleCoverageClassInf_le_canonical N k c epsilon Dfull P n
        (hMainInhabited n).choose_spec).trans_eq
          (hfullCoverage n P (hMainInhabited n).choose_spec)
    · rw [oracleCoverageClassInf, coverageInfOrOne_of_nonempty]
      refine le_ciInf (fun Q => ?_)
      rw [hfullCoverage n Q.1 Q.2]
  have hDfullHonest :
      OracleHonest N k c epsilon alpha Dfull := by
    refine ⟨halpha.1, halpha.2, ?_⟩
    rw [show oracleCoverageClassInf N k c epsilon Dfull =
        fun _ => 1 by
      funext n
      exact hfullCoverageClassInf n]
    rw [liminf_const]
    exact sub_le_self 1 (le_of_lt halpha.1)
  letI : Nonempty {C : OracleProcedure 𝒳 N k c epsilon //
      OracleHonest N k c epsilon alpha C} :=
    ⟨⟨Dfull, hDfullHonest⟩⟩
  have hFixedLower : ∀ t0 : ℝ, 0 < t0 →
      3 * (1 - alpha) ^ 2 / 16 * min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
        fixedGeometryValueTotal N k c epsilon alpha ⟨g, hg⟩ t0 := by
    intro t0 ht0
    have hw : ∀ n, g.weight n =ᵐ[g.sourceX n] fun _ => 1 := by
      intro n
      filter_upwards with x
      rfl
    exact (no_shift_reduction N k c epsilon alpha g hc hepsilon halpha hN
      hkPos hkInf hkRoot hg hw).2.2 t0 ht0 |>.1
  have hOracleLower : ∀ t0 : ℝ, 0 < t0 →
      3 * (1 - alpha) ^ 2 / 16 * min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
        oracleValueTotal (𝒳 := 𝒳) N k c epsilon alpha t0 := by
    intro t0 ht0
    unfold oracleValueTotal
    apply le_ciInf
    intro C
    exact (hFixedLower t0 ht0).trans
      (fixedGeometryValue_le_frontierRisk N k c epsilon alpha g C.1 C.2 t0
        hc hepsilon ht0 hg hN hkPos hkInf hkRoot)
  have hFiniteLower : ∀ t0 : ℝ, 0 < t0 →
      3 * (1 - alpha) ^ 2 / 16 * min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
        finiteCellOracleValueTotal (𝒳 := 𝒳) N k c epsilon alpha t0 := by
    intro t0 ht0
    have hSliceInhabited :
        ∀ᶠ n in atTop, ∃ P : TransportedArray 𝒳,
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n :=
      fixedGeometrySlice_eventually_inhabited g N k c epsilon t0 hc
        hepsilon ht0 hg hN hkPos hkInf hkRoot
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
    have hfixedRisk_nonneg : ∀ E : OracleProcedure 𝒳 N k c epsilon,
        0 ≤ fixedGeometryRisk N k c epsilon g E t0 := by
      intro E
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
        refine ⟨2, Filter.Eventually.of_forall fun n => ?_⟩
        cases isEmpty_or_nonempty
            {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n ∧
                t0 ≤ effectiveStrength P n} with
        | inl h => simp
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
      change 0 ≤ Filter.limsup _ atTop
      rw [← Filter.limsup_const (f := (atTop : Filter ℕ)) (0 : ℝ)]
      exact Filter.limsup_le_limsup
        (Filter.Eventually.of_forall hrow_nonneg)
        hzero_cobounded hrow_bounded
    unfold finiteCellOracleValueTotal
    apply le_ciInf
    intro C
    let canonicalWeight (n : ℕ) : NonnegativeWeight 𝒳 :=
      ⟨fun x => ((g.targetX n).rnDeriv (g.sourceX n) x).toReal,
        fun _ => ENNReal.toReal_nonneg⟩
    have hcanonicalWeight_measurable :
        ∀ n, Measurable (canonicalWeight n : 𝒳 → ℝ) := by
      intro n
      exact (Measure.measurable_rnDeriv
        (g.targetX n) (g.sourceX n)).ennreal_toReal
    let D : OracleProcedure 𝒳 N k c epsilon :=
      { set := fun n input =>
          C.1.set n (input.1, canonicalWeight n, g.propensity n)
        subset := by
          intro n input
          exact C.1.subset n
            (input.1, canonicalWeight n, g.propensity n)
        measurableGraph := by
          intro n _w _e _hw _he
          exact C.1.measurableGraph n (canonicalWeight n) (g.propensity n)
            (hcanonicalWeight_measurable n) (g.propensity_measurable n)
        weightAEInvariant := by
          intro _ _ _ _ _
          exact Filter.Eventually.of_forall (fun _ => rfl) }
    have hset_eq (n : ℕ) (P : TransportedArray 𝒳)
        (hP : fixedGeometrySlice P g N k c epsilon n)
        (s : TwoSample 𝒳 n (N n)) :
        fixedGeometryOracleSet D g n s =
          oracleSet C.1 P n s := by
      simp only [D, fixedGeometryOracleSet, oracleSet,
        hP.2.2.2.2]
      congr 2
      apply Prod.ext
      · apply Subtype.ext
        funext x
        change ((g.targetX n).rnDeriv (g.sourceX n) x).toReal =
          ((targetXLaw P n).rnDeriv (sourceXLaw P n) x).toReal
        rw [hP.2.1, hP.2.2.1]
      · rfl
    have hcoverage_eq (n : ℕ) (P : TransportedArray 𝒳)
        (hP : fixedGeometrySlice P g N k c epsilon n) :
        fixedGeometryOracleCoverage D g P n =
          oracleCoverage C.1 P n := by
      unfold fixedGeometryOracleCoverage oracleCoverage
      simp_rw [hset_eq n P hP]
    have hexpectedLength_eq (n : ℕ) (P : TransportedArray 𝒳)
        (hP : fixedGeometrySlice P g N k c epsilon n) :
        fixedGeometryOracleExpectedLength D g P n =
          oracleExpectedLength C.1 P n := by
      unfold fixedGeometryOracleExpectedLength
        oracleExpectedLength
      simp_rw [hset_eq n P hP]
    have hcoverage_nonneg (E : OracleProcedure 𝒳 N k c epsilon)
        (P : TransportedArray 𝒳) (n : ℕ) :
        0 ≤ oracleCoverage E P n := ENNReal.toReal_nonneg
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
    have hcoverage_rows :
        ∀ᶠ n in atTop,
          oracleCoverageClassInf N k c epsilon C.1 n ≤
          coverageInfOrOne (fun P : {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n} =>
            fixedGeometryOracleCoverage D g P n) := by
      filter_upwards [hSliceInhabited] with n hn
      obtain ⟨P₀, hP₀, _⟩ := hn
      letI : Nonempty {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n} :=
        ⟨⟨P₀, hP₀⟩⟩
      rw [coverageInfOrOne_of_nonempty]
      refine le_ciInf (fun P => ?_)
      exact (oracleCoverageClassInf_le_canonical
          N k c epsilon C.1 P n P.property.1).trans_eq
        (hcoverage_eq n P P.property).symm
    have hglobal_coverage_nonneg :
        ∀ᶠ n in atTop,
          0 ≤ oracleCoverageClassInf N k c epsilon C.1 n := by
      filter_upwards with n
      exact oracleCoverageClassInf_nonneg N k c epsilon C.1 n
        (hMainInhabited n)
    have hslice_coverage_le_one :
        ∀ᶠ n in atTop,
          coverageInfOrOne (fun P : {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n} =>
            fixedGeometryOracleCoverage D g P n) ≤ 1 := by
      filter_upwards [hSliceInhabited] with n hn
      obtain ⟨P₀, hP₀, _⟩ := hn
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
          exact hcoverage_nonneg C.1 P n⟩
      exact (ciInf_le hslice_bdd ⟨P₀, hP₀⟩).trans
        ((hcoverage_eq n P₀ hP₀).le.trans
          (hcoverage_le_one C.1 P₀ n hP₀.1))
    have hglobal_coverage_bounded :
        IsBoundedUnder (· ≥ ·) atTop
          (oracleCoverageClassInf N k c epsilon C.1) :=
      ⟨0, hglobal_coverage_nonneg⟩
    have hslice_coverage_cobounded :
        IsCoboundedUnder (· ≥ ·) atTop
          (fun n => coverageInfOrOne (fun P : {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n} =>
            fixedGeometryOracleCoverage D g P n)) := by
      change ∃ b, ∀ a, (∀ᶠ n in atTop, a ≤ _) → a ≤ b
      refine ⟨1, fun a ha => ?_⟩
      exact (ha.and hslice_coverage_le_one).exists.choose_spec.1.trans
        (ha.and hslice_coverage_le_one).exists.choose_spec.2
    have hD : FixedGeometryOracleHonest
        N k c epsilon alpha ⟨g, hg⟩ D := by
      refine ⟨C.2.1, C.2.2.1, C.2.2.2.trans ?_⟩
      exact Filter.liminf_le_liminf hcoverage_rows
        hglobal_coverage_bounded hslice_coverage_cobounded
    have hfixed_rows_nonneg : ∀ n,
        0 ≤ (⨆ P : {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n},
          fixedGeometryOracleExpectedLength D g P n) := by
      intro n
      cases isEmpty_or_nonempty
          {P : TransportedArray 𝒳 //
            fixedGeometrySlice P g N k c epsilon n ∧
              t0 ≤ effectiveStrength P n} with
      | inl h => simp
      | inr h =>
          let P := Classical.choice h
          refine le_trans ?_ (le_ciSup ?_ P)
          · exact integral_nonneg (fun s =>
              hsetLength_nonneg (fixedGeometryOracleSet D g n s))
          · exact ⟨2, by
              rintro y ⟨Q, rfl⟩
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
                    (fixedGeometryOracleSet D g n s))).trans_eq (by simp)⟩
    have hfinite_rows_le_two : ∀ n,
        finiteCellOracleRiskRow N k c epsilon C.1 t0 n ≤ 2 := by
      intro n
      exact finiteCellOracleRiskRow_le_two N k c epsilon C.1 n t0
    have hrisk_rows :
        ∀ᶠ n in atTop,
          (⨆ P : {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n ∧
                t0 ≤ effectiveStrength P n},
            fixedGeometryOracleExpectedLength D g P n) ≤
          finiteCellOracleRiskRow N k c epsilon C.1 t0 n := by
      filter_upwards [hSliceInhabited] with n hn
      obtain ⟨P₀, hP₀, htP₀⟩ := hn
      letI : Nonempty {P : TransportedArray 𝒳 //
          fixedGeometrySlice P g N k c epsilon n ∧
            t0 ≤ effectiveStrength P n} :=
        ⟨⟨P₀, hP₀, htP₀⟩⟩
      refine ciSup_le (fun P => ?_)
      exact (hexpectedLength_eq n P P.property.1).le.trans
        (oracleExpectedLength_le_finiteCellOracleRiskRow
          N k c epsilon C.1 P n t0
          (hSliceFinite n P P.property.1) P.property.2)
    have hfixed_cobounded :
        IsCoboundedUnder (· ≤ ·) atTop
          (fun n => ⨆ P : {P : TransportedArray 𝒳 //
              fixedGeometrySlice P g N k c epsilon n ∧
                t0 ≤ effectiveStrength P n},
            fixedGeometryOracleExpectedLength D g P n) := by
      change ∃ b, ∀ a, (∀ᶠ n in atTop, _ ≤ a) → b ≤ a
      refine ⟨0, fun a ha => ?_⟩
      exact ((Filter.Eventually.of_forall hfixed_rows_nonneg).and
        ha).exists.choose_spec.1.trans
          ((Filter.Eventually.of_forall hfixed_rows_nonneg).and
            ha).exists.choose_spec.2
    have hfinite_bounded :
        IsBoundedUnder (· ≤ ·) atTop
          (finiteCellOracleRiskRow N k c epsilon C.1 t0) := by
      change ∃ b, ∀ᶠ n in atTop, _ ≤ b
      exact ⟨2, Filter.Eventually.of_forall hfinite_rows_le_two⟩
    have hRisk :
        fixedGeometryRisk N k c epsilon g D t0 ≤
          finiteCellOracleRisk N k c epsilon C.1 t0 :=
      Filter.limsup_le_limsup hrisk_rows hfixed_cobounded hfinite_bounded
    have hvalues_bdd :
        BddBelow (Set.range (fun E :
              {E : OracleProcedure 𝒳 N k c epsilon //
              FixedGeometryOracleHonest N k c epsilon alpha ⟨g, hg⟩ E} =>
          fixedGeometryRisk N k c epsilon g E.1 t0)) :=
      ⟨0, by
        rintro y ⟨E, rfl⟩
        exact hfixedRisk_nonneg E⟩
    exact (hFixedLower t0 ht0).trans
      ((ciInf_le hvalues_bdd ⟨D, hD⟩).trans hRisk)
  refine ⟨hOracleLower t0 ht0, ?_, ?_⟩
  · exact hFiniteLower t0 ht0
  · intro ht1
    have hone : min 1 (t0 ^ (-1 / 2 : ℝ)) = 1 := by
      rw [min_eq_left]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by norm_num)
    simpa [hone] using hOracleLower t0 ht0

end CausalSmith.Stat.TransportedLateStrengthFrontier
