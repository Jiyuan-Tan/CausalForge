/-
# Oracle score-inversion attainment
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.ScoreInversion
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_FixedGeometryFrontier
import Causalean.Stat.Sample.EffectiveSampleSize

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

set_option maxHeartbeats 3000000

-- @node: thm:oracle-score-inversion-attainment
/-- One oracle transported-score inversion sequence is honest and attains the
frontier simultaneously at every fixed positive strength threshold. -/
theorem oracle_score_inversion_attainment
    (N k : ℕ → ℕ) (c epsilon alpha : ℝ)
    (hc : 0 < c)
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (halpha : 0 < alpha ∧ alpha < 1) -- @realizes \alpha(noncoverage in (0,1))
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
      -- @realizes N_n(N_n/n→c)
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ =>
      (k n : ℝ) / Real.sqrt n) atTop (𝓝 0))
      -- @realizes k_n(positive, diverging, and o(√n))
    (hGeometry : ∃ g : Geometry 𝒳, AdmissibleGeometry g k epsilon)
      -- the carrier admits the paper's own deterministic geometry
    (hTwo : ∀ n (P : TransportedArray 𝒳),
      TransportedIVClass P N k c epsilon n →
      TwoSampleArray P N c)
    (hOverlap : ∀ n (P : TransportedArray 𝒳),
      TransportedIVClass P N k c epsilon n →
      InstrumentOverlap P n epsilon)
    (hEnvelope : ∀ n (P : TransportedArray 𝒳),
      TransportedIVClass P N k c epsilon n →
      WeightEnvelope P k n)
    (hSecond : ∀ n (P : TransportedArray 𝒳),
      TransportedIVClass P N k c epsilon n →
      WeightSecondMoment P k n)
    (hDegrade : ∀ n (P : TransportedArray 𝒳),
      TransportedIVClass P N k c epsilon n →
      DegradingArray P k) :
    let Lalpha := Real.sqrt (8 / (alpha * epsilon ^ 2))
    let C0 := max 2 (4 * Lalpha + 8 / epsilon ^ 2)
      -- @realizes C_0(max{2,4L_alpha+8/epsilon^2})
    0 < C0 ∧
    ∃ C : OracleProcedure 𝒳 N k c epsilon,
      (∀ n x, C.set n x =
        inversionHandle x.2.1.1 x.2.2 n Lalpha x.1.1) ∧
      OracleHonest N k c epsilon alpha C ∧
      ∀ (t0 : ℝ) (ht0 : 0 < t0), -- @realizes t_0(positive frontier threshold)
        frontierRisk N k c epsilon C ⟨t0, ht0⟩ ≤
          C0 * min 1 (t0 ^ (-1 / 2 : ℝ)) ∧
        3 * (1 - alpha) ^ 2 / 16 *
            min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
          oracleValue (𝒳 := 𝒳) N k c epsilon alpha ⟨t0, ht0⟩ ∧
        oracleValue (𝒳 := 𝒳) N k c epsilon alpha ⟨t0, ht0⟩ ≤
          C0 * min 1 (t0 ^ (-1 / 2 : ℝ)) ∧
        ∀ (g : Geometry 𝒳) (hg : AdmissibleGeometry g k epsilon),
          3 * (1 - alpha) ^ 2 / 16 *
              min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
            fixedGeometryValue N k c epsilon alpha ⟨g, hg⟩
              ⟨t0, ht0⟩ ∧
          fixedGeometryValue N k c epsilon alpha ⟨g, hg⟩
              ⟨t0, ht0⟩ ≤
            C0 * min 1 (t0 ^ (-1 / 2 : ℝ)) := by
  obtain ⟨g, hg⟩ := hGeometry
  have hClass : ∀ t0 : ℝ, 0 < t0 →
      ∀ᶠ n in atTop, ∃ P : TransportedArray 𝒳,
        TransportedIVClass P N k c epsilon n := by
    intro t0 ht0
    filter_upwards [
      fixedGeometrySlice_eventually_inhabited
        g N k c epsilon t0 hc hepsilon ht0 hg hN hkPos hkInf hkRoot
    ] with n hn
    obtain ⟨P, hP, _⟩ := hn
    exact ⟨P, hP.1⟩
  dsimp only
  have hC0pos :
      0 < max 2
        (4 * Real.sqrt (8 / (alpha * epsilon ^ 2)) +
          8 / epsilon ^ 2) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨hC0pos, ?_⟩
  classical
  let L : ℝ := Real.sqrt (8 / (alpha * epsilon ^ 2))
  let C : OracleProcedure 𝒳 N k c epsilon :=
    { set := fun n x =>
        inversionHandle x.2.1.1 x.2.2 n L x.1.1
      subset := by
        intro n x theta htheta
        exact htheta.1
      measurableGraph := by
        intro n w e hw he
        have hscore : Measurable (oracleInstrumentScore e) := by
          have he' : Measurable (fun o : SourceObs 𝒳 => e o.1) :=
            he.comp measurable_fst
          unfold oracleInstrumentScore
          exact Measurable.ite (by measurability)
            (measurable_const.div he')
            (measurable_const.neg.div (measurable_const.sub he'))
        have hA : Measurable (fun s : SourceSample 𝒳 n =>
            scoreOutcomeMean w e n s) := by
          unfold scoreOutcomeMean
          fun_prop
        have hB : Measurable (fun s : SourceSample 𝒳 n =>
            scoreReceiptMean w e n s) := by
          unfold scoreReceiptMean
          fun_prop
        have hK : Measurable (fun s : SourceSample 𝒳 n =>
            empiricalKish w n s) := by
          unfold empiricalKish Causalean.Stat.empiricalKishDispersion
          fun_prop
        unfold inversionHandle
        refine (measurableSet_Icc.preimage measurable_snd).inter ?_
        exact measurableSet_le
          ((hA.comp (measurable_fst.fst)).sub
            (measurable_snd.mul
              (hB.comp (measurable_fst.fst)))).abs
          (measurable_const.mul
            ((hK.comp (measurable_fst.fst)).div measurable_const).sqrt)
      weightAEInvariant := by
        intro n P hP w w'
        letI : IsProbabilityMeasure (sourceObsLaw P n) :=
          hP.twoSampleArray.2.1 n
        letI : IsProbabilityMeasure (targetXLaw P n) :=
          hP.twoSampleArray.2.2.1 n
        let μS := Measure.pi (fun _ : Fin n => sourceObsLaw P n)
        let μT := Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
        have hmap : Measure.map Prod.fst (μS.prod μT) = μS := by
          simp [μS, μT]
        have hpull (v : TransportWeightVersion P n) :
            (fun z : TwoSample 𝒳 n (N n) =>
              inversionHandle v.1.1 (P.propensity n) n L z.1) =ᵐ[
                twoSampleLaw P N n]
            (fun z : TwoSample 𝒳 n (N n) =>
              inversionHandle (transportWeight P n) (P.propensity n) n L z.1) := by
          have hv := inversionHandle_weight_version_ae_eq P n v L
          have hv' :
              (fun s : SourceSample 𝒳 n =>
                inversionHandle v.1.1 (P.propensity n) n L s) =ᵐ[
                  Measure.map Prod.fst (μS.prod μT)]
              (fun s : SourceSample 𝒳 n =>
                inversionHandle (transportWeight P n) (P.propensity n) n L s) := by
            rw [hmap]
            exact hv
          simpa only [twoSampleLaw, μS, μT, Function.comp_apply] using
            (MeasureTheory.ae_eq_comp measurable_fst.aemeasurable hv')
        exact (hpull w).trans (hpull w').symm }
  have hCset : ∀ n x, C.set n x =
      inversionHandle x.2.1.1 x.2.2 n L x.1.1 := by
    intro n x
    rfl
  have hUpper :
      OracleHonest N k c epsilon alpha C ∧
      ∀ t0 : ℝ, 0 < t0 →
        frontierRiskTotal N k c epsilon C t0 ≤
          max 2 (4 * L + 8 / epsilon ^ 2) *
            min 1 (t0 ^ (-1 / 2 : ℝ)) := by
    have atoms :=
      transportedIVScoreRiskAtoms (𝒳 := 𝒳) N k c epsilon
    have pullout
        (P : TransportedArray 𝒳) (n : ℕ)
        (F : SourceObs 𝒳 → ℝ) (d w : 𝒳 → ℝ)
        (hprob : IsProbabilityMeasure (sourceObsLaw P n))
        (hF : Integrable F (sourceObsLaw P n))
        (hd : Integrable d (sourceXLaw P n))
        (hdmeas : Measurable d)
        (hw : Measurable w)
        (hWF : Integrable (fun o => w o.1 * F o) (sourceObsLaw P n))
        (hwd : Integrable (fun x => w x * d x) (sourceXLaw P n))
        (hset : ∀ A, MeasurableSet A →
          ∫ o in {o | o.1 ∈ A}, F o ∂sourceObsLaw P n =
            ∫ x in A, d x ∂sourceXLaw P n) :
        (∫ o, w o.1 * F o ∂sourceObsLaw P n) =
          ∫ x, w x * d x ∂sourceXLaw P n := by
      let m0 : MeasurableSpace (SourceObs 𝒳) := inferInstance
      let mX : MeasurableSpace (SourceObs 𝒳) :=
        MeasurableSpace.comap (fun o => o.1)
          (inferInstance : MeasurableSpace 𝒳)
      letI : MeasurableSpace (SourceObs 𝒳) := m0
      letI : IsProbabilityMeasure (sourceObsLaw P n) := hprob
      have hfst :
          @Measurable (SourceObs 𝒳) 𝒳 m0 inferInstance (fun o => o.1) :=
        measurable_fst
      have hm : mX ≤ m0 :=
        hfst.comap_le
      have hfstM :
          @Measurable (SourceObs 𝒳) 𝒳 mX inferInstance (fun o => o.1) := by
        intro A hA
        exact MeasurableSpace.measurableSet_comap.mpr ⟨A, hA, rfl⟩
      have hdcomp : Integrable (fun o => d o.1) (sourceObsLaw P n) := by
        have hdmap : Integrable d
            (Measure.map (fun o : SourceObs 𝒳 => o.1) (sourceObsLaw P n)) := by
          simpa [sourceXLaw] using hd
        simpa [Function.comp_def] using
          (integrable_map_measure hdmap.1 hfst.aemeasurable).mp hdmap
      have hcond : (fun o => d o.1) =ᵐ[sourceObsLaw P n]
          (sourceObsLaw P n)[F | mX] := by
        refine ae_eq_condExp_of_forall_setIntegral_eq
          (μ := sourceObsLaw P n) (f := F) (g := fun o => d o.1)
          hm hF ?_ ?_ ?_
        · intro s hs _hfin
          exact hdcomp.integrableOn
        · intro s hs _hfin
          rcases MeasurableSpace.measurableSet_comap.mp hs with
            ⟨A, hA, rfl⟩
          calc
            (∫ x in (fun o : SourceObs 𝒳 => o.1) ⁻¹' A,
                d x.1 ∂sourceObsLaw P n) =
                ∫ x in A, d x ∂sourceXLaw P n := by
              rw [sourceXLaw]
              exact (setIntegral_map hA hd.1 hfst.aemeasurable).symm
            _ = ∫ x in (fun o : SourceObs 𝒳 => o.1) ⁻¹' A,
                F x ∂sourceObsLaw P n := (hset A hA).symm
        · exact (hdmeas.comp hfstM).aestronglyMeasurable
      have hwM : @StronglyMeasurable (SourceObs 𝒳) ℝ _ mX
          (fun o => w o.1) :=
        (hw.comp hfstM).stronglyMeasurable
      have hpull := condExp_mul_of_stronglyMeasurable_left
        (m := mX) (μ := sourceObsLaw P n) hwM hWF hF
      have hpull' :
          (sourceObsLaw P n)[(fun o => w o.1 * F o) | mX] =ᵐ[
            sourceObsLaw P n]
              fun o => w o.1 * (sourceObsLaw P n)[F | mX] o := by
        simpa only [Pi.mul_apply] using hpull
      calc
        (∫ o, w o.1 * F o ∂sourceObsLaw P n) =
            ∫ o, (sourceObsLaw P n)[(fun o => w o.1 * F o) | mX] o
              ∂sourceObsLaw P n := (integral_condExp hm).symm
        _ = ∫ o, w o.1 * d o.1 ∂sourceObsLaw P n := by
          apply integral_congr_ae
          filter_upwards [hpull', hcond] with o hp hc
          rw [hp, ← hc]
        _ = ∫ x, w x * d x ∂sourceXLaw P n := by
          rw [sourceXLaw]
          exact (integral_map measurable_fst.aemeasurable hwd.1).symm
    have hRiskPoint : ∀ n P, 0 < n →
        TransportedIVClass P N k c epsilon n →
        oracleExpectedLength C P n ≤
          max 2 (4 * L + 8 / epsilon ^ 2) *
            min 1 (effectiveStrength P n ^ (-1 / 2 : ℝ)) := by
      intro n P hn hP
      have hIV := atoms.toTransportedIVClass hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hIV.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (sourceXLaw P n) := by
        unfold sourceXLaw
        exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hIV.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      have hcompact := scoreRiskClass_compact_causal_range atoms hP
      have htheta : targetCACE P n ∈ parameterSpace :=
        hcompact.2.2.2.2.2
      have hfirstEq :
          transportedFirstStage P n = targetComplierShare P n :=
        hcompact.2.2.2.1
      have hmu : 0 < transportedFirstStage P n := by
        rw [hfirstEq]
        exact hIV.targetComplierPositivity
      have hweightMeas : Measurable (transportWeight P n) := by
        exact (Measure.measurable_rnDeriv
          (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
      have hweightMem :
          MemLp (transportWeight P n) 2 (sourceXLaw P n) := by
        refine MemLp.of_bound hweightMeas.aestronglyMeasurable
          (2 * (k n : ℝ)) ?_
        filter_upwards [hIV.weightEnvelope] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact hx.2
      have hweightMean :
          (∫ x, transportWeight P n x ∂sourceXLaw P n) = 1 := by
        have hchange := integral_rnDeriv_smul
          (μ := targetXLaw P n) (ν := sourceXLaw P n)
          (f := fun _ => (1 : ℝ)) hIV.transportDomination
        simpa [transportWeight] using hchange
      have hkappaOne : 1 ≤ kishDispersion P n := by
        simpa [kishDispersion] using
          one_le_secondMoment_of_mean_one
            (sourceXLaw P n) (transportWeight P n)
            hweightMem hweightMean
      have hkappa : 0 < kishDispersion P n :=
        lt_of_lt_of_le zero_lt_one hkappaOne
      rcases sourceObservationFacts_of_class P N k c epsilon n hIV with
        ⟨_hAssigned, _hSource, hYObs, _hMap, _hProp,
          _hYScore, _hDeltaY, hDScore, hDeltaD⟩
      have hoverObs : ∀ᵐ o ∂sourceObsLaw P n,
          epsilon ≤ P.propensity n o.1 ∧
            P.propensity n o.1 ≤ 1 - epsilon := by
        have hover := hIV.instrumentOverlap.2.2
        rw [sourceXLaw] at hover
        exact (ae_map_iff measurable_fst.aemeasurable
          (measurableSet_Icc.preimage
            (P.propensity_measurable n))).mp hover
      have hDMeas : Measurable (fun o : SourceObs 𝒳 =>
          oracleInstrumentScore (P.propensity n) o *
            boolReal o.2.2.1) := by
        have he : Measurable (fun o : SourceObs 𝒳 =>
            P.propensity n o.1) :=
          (P.propensity_measurable n).comp measurable_fst
        have hscore : Measurable
            (oracleInstrumentScore (P.propensity n)) := by
          unfold oracleInstrumentScore
          exact Measurable.ite (by measurability)
            (measurable_const.div he)
            (measurable_const.neg.div (measurable_const.sub he))
        have hd : Measurable (fun o : SourceObs 𝒳 =>
            boolReal o.2.2.1) := by
          unfold boolReal
          exact Measurable.ite (by measurability)
            measurable_const measurable_const
        exact hscore.mul hd
      have hDInt : Integrable (fun o : SourceObs 𝒳 =>
          oracleInstrumentScore (P.propensity n) o *
            boolReal o.2.2.1) (sourceObsLaw P n) := by
        refine Integrable.of_bound hDMeas.aestronglyMeasurable
          (1 / epsilon) ?_
        filter_upwards [hoverObs] with o ho
        have hscore :
            |oracleInstrumentScore (P.propensity n) o| ≤ 1 / epsilon := by
          unfold oracleInstrumentScore
          split
          · rw [abs_div, abs_one,
              abs_of_pos (lt_of_lt_of_le hepsilon.1 ho.1)]
            exact one_div_le_one_div_of_le hepsilon.1 ho.1
          · have hden : 0 < 1 - P.propensity n o.1 := by linarith
            rw [abs_div, abs_neg, abs_one, abs_of_pos hden]
            exact one_div_le_one_div_of_le hepsilon.1 (by linarith)
        rw [Real.norm_eq_abs, abs_mul]
        have hd : |boolReal o.2.2.1| ≤ 1 := by
          cases o.2.2.1 <;> simp [boolReal]
        calc
          |oracleInstrumentScore (P.propensity n) o| *
              |boolReal o.2.2.1| ≤ (1 / epsilon) * 1 := by
            exact mul_le_mul hscore hd (abs_nonneg _)
              (div_nonneg zero_le_one hepsilon.1.le)
          _ = 1 / epsilon := mul_one _
      have hdeltaDInt : Integrable (P.deltaD n) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (P.deltaD_measurable n).aestronglyMeasurable 1 ?_
        filter_upwards [hDeltaD] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact hx.2
      have hweightedDMeas : Measurable (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 *
            (oracleInstrumentScore (P.propensity n) o *
              boolReal o.2.2.1)) :=
        (hweightMeas.comp measurable_fst).mul hDMeas
      have hweightedDBound : ∀ᵐ o : SourceObs 𝒳 ∂sourceObsLaw P n,
          ‖transportWeight P n o.1 *
            (oracleInstrumentScore (P.propensity n) o *
              boolReal o.2.2.1)‖ ≤ 2 * (k n : ℝ) / epsilon := by
        filter_upwards [hoverObs,
          (ae_map_iff measurable_fst.aemeasurable
            (measurableSet_Icc.preimage hweightMeas)).mp
              (by simpa only [Set.mem_setOf_eq] using hIV.weightEnvelope)
        ] with o ho hw
        have hscore :
            |oracleInstrumentScore (P.propensity n) o| ≤ 1 / epsilon := by
          unfold oracleInstrumentScore
          split
          · rw [abs_div, abs_one,
              abs_of_pos (lt_of_lt_of_le hepsilon.1 ho.1)]
            exact one_div_le_one_div_of_le hepsilon.1 ho.1
          · have hden : 0 < 1 - P.propensity n o.1 := by linarith
            rw [abs_div, abs_neg, abs_one, abs_of_pos hden]
            exact one_div_le_one_div_of_le hepsilon.1 (by linarith)
        have hd : |boolReal o.2.2.1| ≤ 1 := by
          cases o.2.2.1 <;> simp [boolReal]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw.1]
        calc
          transportWeight P n o.1 *
              (|oracleInstrumentScore (P.propensity n) o| *
                |boolReal o.2.2.1|) ≤
              (2 * (k n : ℝ)) * ((1 / epsilon) * 1) := by
            exact mul_le_mul hw.2
              (mul_le_mul hscore hd (abs_nonneg _)
                (div_nonneg zero_le_one hepsilon.1.le))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          _ = 2 * (k n : ℝ) / epsilon := by ring
      have hweightedDMem : MemLp (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 *
            (oracleInstrumentScore (P.propensity n) o *
              boolReal o.2.2.1)) 2 (sourceObsLaw P n) :=
        MemLp.of_bound hweightedDMeas.aestronglyMeasurable
          (2 * (k n : ℝ) / epsilon) hweightedDBound
      have hweightedDInt := hweightedDMem.integrable (by norm_num)
      have hweightDeltaDInt : Integrable (fun x =>
          transportWeight P n x * P.deltaD n x) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (hweightMeas.mul (P.deltaD_measurable n)).aestronglyMeasurable
          (2 * (k n : ℝ)) ?_
        filter_upwards [hIV.weightEnvelope, hDeltaD] with x hw hd
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1,
          abs_of_nonneg hd.1]
        exact (mul_le_mul hw.2 hd.2 hd.1
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))).trans_eq
          (mul_one _)
      have hDMean : (∫ o,
          transportWeight P n o.1 *
            (oracleInstrumentScore (P.propensity n) o *
              boolReal o.2.2.1) ∂sourceObsLaw P n) =
          transportedFirstStage P n := by
        rw [pullout P n
          (fun o => oracleInstrumentScore (P.propensity n) o *
            boolReal o.2.2.1)
          (P.deltaD n) (transportWeight P n)
          (inferInstance : IsProbabilityMeasure (sourceObsLaw P n))
          hDInt hdeltaDInt (P.deltaD_measurable n) hweightMeas
          hweightedDInt hweightDeltaDInt]
        · exact
            (transportedFirstStage_eq_weighted_deltaD P k epsilon n
              (sourceObservationFacts_of_class P N k c epsilon n hIV)
              hIV.instrumentOverlap hIV.weightEnvelope).symm
        · intro A hA
          simpa [instrumentScore, oracleInstrumentScore] using hDScore A hA
      have hweightSqObsInt : Integrable (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 ^ 2) (sourceObsLaw P n) := by
        have hmap : Integrable (fun x => transportWeight P n x ^ 2)
            (Measure.map (fun o : SourceObs 𝒳 => o.1)
              (sourceObsLaw P n)) := by
          simpa [sourceXLaw] using hweightMem.integrable_sq
        simpa [Function.comp_def] using
          (integrable_map_measure hmap.1 measurable_fst.aemeasurable).mp hmap
      have hDVar : variance (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 *
            (oracleInstrumentScore (P.propensity n) o *
              boolReal o.2.2.1)) (sourceObsLaw P n) ≤
          kishDispersion P n / epsilon ^ 2 := by
        calc
          variance (fun o : SourceObs 𝒳 =>
              transportWeight P n o.1 *
                (oracleInstrumentScore (P.propensity n) o *
                  boolReal o.2.2.1)) (sourceObsLaw P n) ≤
              ∫ o, (transportWeight P n o.1 *
                (oracleInstrumentScore (P.propensity n) o *
                  boolReal o.2.2.1)) ^ 2 ∂sourceObsLaw P n :=
            variance_le_expectation_sq
              hweightedDMeas.aestronglyMeasurable
          _ ≤ ∫ o, transportWeight P n o.1 ^ 2 / epsilon ^ 2
                ∂sourceObsLaw P n := by
            apply integral_mono_ae hweightedDMem.integrable_sq
              (hweightSqObsInt.div_const _)
            filter_upwards [hoverObs] with o ho
            have hscore :
                |oracleInstrumentScore (P.propensity n) o| ≤
                  1 / epsilon := by
              unfold oracleInstrumentScore
              split
              · rw [abs_div, abs_one,
                  abs_of_pos (lt_of_lt_of_le hepsilon.1 ho.1)]
                exact one_div_le_one_div_of_le hepsilon.1 ho.1
              · have hden : 0 < 1 - P.propensity n o.1 := by linarith
                rw [abs_div, abs_neg, abs_one, abs_of_pos hden]
                exact one_div_le_one_div_of_le hepsilon.1 (by linarith)
            have hd : |boolReal o.2.2.1| ≤ 1 := by
              cases o.2.2.1 <;> simp [boolReal]
            have hprod :
                |oracleInstrumentScore (P.propensity n) o *
                  boolReal o.2.2.1| ≤ 1 / epsilon := by
              rw [abs_mul]
              calc
                _ ≤ (1 / epsilon) * 1 :=
                  mul_le_mul hscore hd (abs_nonneg _)
                    (div_nonneg zero_le_one hepsilon.1.le)
                _ = 1 / epsilon := mul_one _
            have hsquare :
                (oracleInstrumentScore (P.propensity n) o *
                  boolReal o.2.2.1) ^ 2 ≤ (1 / epsilon) ^ 2 := by
              rw [← sq_abs]
              exact (sq_le_sq₀ (abs_nonneg _)
                (div_nonneg zero_le_one hepsilon.1.le)).2 hprod
            rw [mul_pow]
            calc
              transportWeight P n o.1 ^ 2 *
                  (oracleInstrumentScore (P.propensity n) o *
                    boolReal o.2.2.1) ^ 2 ≤
                  transportWeight P n o.1 ^ 2 * (1 / epsilon) ^ 2 := by
                gcongr
              _ = transportWeight P n o.1 ^ 2 / epsilon ^ 2 := by ring
          _ = kishDispersion P n / epsilon ^ 2 := by
            rw [integral_div]
            congr 1
            have hmap := integral_map measurable_fst.aemeasurable
              hweightMem.integrable_sq.1
            simpa [kishDispersion, sourceXLaw] using hmap.symm
      let QS : Measure (SourceSample 𝒳 n) :=
        Measure.pi (fun _ : Fin n => sourceObsLaw P n)
      let B : SourceSample 𝒳 n → ℝ := fun sample =>
        scoreReceiptMean (transportWeight P n) (P.propensity n) n sample
      have hBeq : B = fun sample : SourceSample 𝒳 n =>
          (n : ℝ)⁻¹ * ∑ i,
            transportWeight P n (sample i).1 *
              (oracleInstrumentScore (P.propensity n) (sample i) *
                boolReal (sample i).2.2.1) := by
        funext sample
        simp only [B, scoreReceiptMean]
        apply congrArg ((n : ℝ)⁻¹ * ·)
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hBmom := iid_empiricalAverage_mean_variance
        (sourceObsLaw P n) n hn
        (fun o => transportWeight P n o.1 *
          (oracleInstrumentScore (P.propensity n) o *
            boolReal o.2.2.1)) hweightedDMem
      have hBmean : (∫ sample, B sample ∂QS) =
          transportedFirstStage P n := by
        rw [hBeq]
        exact hBmom.1.trans hDMean
      have hBvar : variance B QS ≤
          kishDispersion P n / (epsilon ^ 2 * n) := by
        rw [hBeq, hBmom.2]
        calc
          (n : ℝ)⁻¹ * variance (fun o : SourceObs 𝒳 =>
              transportWeight P n o.1 *
                (oracleInstrumentScore (P.propensity n) o *
                  boolReal o.2.2.1)) (sourceObsLaw P n) ≤
              (n : ℝ)⁻¹ * (kishDispersion P n / epsilon ^ 2) := by
            gcongr
          _ = kishDispersion P n / (epsilon ^ 2 * n) := by ring
      have hBmem : MemLp B 2 QS := by
        rw [hBeq]
        have heval (i : Fin n) :
            MeasurePreserving (fun sample : SourceSample 𝒳 n => sample i)
              QS (sourceObsLaw P n) := by
          refine ⟨measurable_pi_apply i, ?_⟩
          dsimp [QS]
          rw [Measure.pi_map_eval]
          simp
        have hcoord (i : Fin n) : MemLp
            (fun sample : SourceSample 𝒳 n =>
              transportWeight P n (sample i).1 *
                (oracleInstrumentScore (P.propensity n) (sample i) *
                  boolReal (sample i).2.2.1)) 2 QS := by
          simpa [Function.comp_def] using
            hweightedDMem.comp_measurePreserving (heval i)
        exact (memLp_finset_sum Finset.univ
          (fun i _hi => hcoord i)).const_mul _
      have hbadS := scoreReceiptMean_bad_probability
        QS B n epsilon (transportedFirstStage P n)
        (kishDispersion P n) (effectiveStrength P n)
        hn hepsilon.1 hmu hkappa hBmem hBmean hBvar rfl
      let K : SourceSample 𝒳 n → ℝ := fun sample =>
        empiricalKish (transportWeight P n) n sample
      have hweightSqObsMem : MemLp (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 ^ 2) 2 (sourceObsLaw P n) := by
        refine MemLp.of_bound
          ((hweightMeas.comp measurable_fst).pow_const 2).aestronglyMeasurable
          ((2 * (k n : ℝ)) ^ 2) ?_
        filter_upwards [
          (ae_map_iff measurable_fst.aemeasurable
            (measurableSet_Icc.preimage hweightMeas)).mp
              (by simpa only [Set.mem_setOf_eq] using hIV.weightEnvelope)
        ] with o hw
        rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hw.1]
        exact pow_le_pow_left₀ hw.1 hw.2 2
      have hKmeanS : (∫ sample, K sample ∂QS) =
          kishDispersion P n := by
        calc
          (∫ sample, K sample ∂QS) =
              ∫ o : SourceObs 𝒳, transportWeight P n o.1 ^ 2
                ∂sourceObsLaw P n := by
            simpa [K, QS] using
              empiricalKish_mean (sourceObsLaw P n)
                (transportWeight P n) n hn hweightSqObsMem
          _ = kishDispersion P n := by
            have hmap := integral_map measurable_fst.aemeasurable
              hweightMem.integrable_sq.1
            simpa [kishDispersion, sourceXLaw] using hmap.symm
      have hKmem : MemLp K 2 QS := by
        have heval (i : Fin n) :
            MeasurePreserving (fun sample : SourceSample 𝒳 n => sample i)
              QS (sourceObsLaw P n) := by
          refine ⟨measurable_pi_apply i, ?_⟩
          dsimp [QS]
          rw [Measure.pi_map_eval]
          simp
        have hcoord (i : Fin n) : MemLp
            (fun sample : SourceSample 𝒳 n =>
              transportWeight P n (sample i).1 ^ 2) 2 QS := by
          simpa [Function.comp_def] using
            hweightSqObsMem.comp_measurePreserving (heval i)
        unfold K empiricalKish Causalean.Stat.empiricalKishDispersion
        exact (memLp_finset_sum Finset.univ
          (fun i _hi => hcoord i)).const_mul _
      let A₂ : TwoSample 𝒳 n (N n) → ℝ := fun s =>
        scoreOutcomeMean (transportWeight P n) (P.propensity n) n s.1
      let B₂ : TwoSample 𝒳 n (N n) → ℝ := fun s => B s.1
      let K₂ : TwoSample 𝒳 n (N n) → ℝ := fun s => K s.1
      let QT : Measure (TargetSample 𝒳 (N n)) :=
        Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
      have hK₂mem : MemLp K₂ 2 (twoSampleLaw P N n) := by
        simpa [K₂, QS, QT, twoSampleLaw] using hKmem.comp_fst QT
      have hK₂mean : (∫ s, K₂ s ∂twoSampleLaw P N n) =
          kishDispersion P n := by
        unfold twoSampleLaw
        rw [integral_prod_symm _ (hK₂mem.integrable (by norm_num))]
        simp [K₂, QS, QT, hKmeanS]
      have hbad₂ :
          (twoSampleLaw P N n
            {s | transportedFirstStage P n / 2 <
              |B₂ s - transportedFirstStage P n|}).toReal ≤
            4 / (epsilon ^ 2 * effectiveStrength P n) := by
        let bad : Set (SourceSample 𝒳 n) :=
          {s | transportedFirstStage P n / 2 <
            |B s - transportedFirstStage P n|}
        have hset :
            {s : TwoSample 𝒳 n (N n) |
              transportedFirstStage P n / 2 <
                |B₂ s - transportedFirstStage P n|} =
              bad ×ˢ Set.univ := by
          ext s
          simp [bad, B₂]
        rw [hset, twoSampleLaw, Measure.prod_prod]
        simpa [bad, QS] using hbadS
      have hfront := scoreInversion_expectedLength_frontier_le
        (twoSampleLaw P N n) A₂ B₂ K₂ n L
        (transportedFirstStage P n) (kishDispersion P n)
        (4 / (epsilon ^ 2 * effectiveStrength P n))
        epsilon (effectiveStrength P n)
        (Real.sqrt_nonneg _) hmu hn
        (fun s => by
          unfold K₂ K empiricalKish Causalean.Stat.empiricalKishDispersion
          exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
            (Finset.sum_nonneg fun i _ => sq_nonneg _))
        (hK₂mem.integrable (by norm_num)) hK₂mean
        hbad₂ hkappa hepsilon.1 le_rfl rfl
      simpa [oracleExpectedLength, oracleSet,
        C, L, A₂, B₂, B, K₂, K,
        inversionHandle_eq_affineInversionSet] using hfront
    let delta : ℕ → ℝ := fun n =>
      if n = 0 then 1 else 16 * (k n : ℝ) ^ 2 / n
    have hdelta : Tendsto delta atTop (𝓝 0) := by
      have hsquare := hkRoot.pow 2
      have hraw : Tendsto (fun n : ℕ =>
          16 * ((k n : ℝ) / Real.sqrt n) ^ 2) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hsquare)
      apply hraw.congr'
      filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hn)
      have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
      simp only [delta, hn0, ↓reduceIte]
      rw [div_pow]
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      ring
    have hCoveragePoint : ∀ n P,
        TransportedIVClass P N k c epsilon n →
        1 - alpha - delta n ≤ oracleCoverage C P n := by
      intro n P hP
      by_cases hn0 : n = 0
      · subst n
        have hcov0 : 0 ≤ oracleCoverage C P 0 :=
          ENNReal.toReal_nonneg
        simp only [delta, ↓reduceIte]
        linarith [halpha.1]
      have hn : 0 < n := Nat.pos_of_ne_zero hn0
      have hIV := atoms.toTransportedIVClass hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hIV.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (sourceXLaw P n) := by
        unfold sourceXLaw
        exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hIV.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      have hcompact := scoreRiskClass_compact_causal_range atoms hP
      have htheta : targetCACE P n ∈ parameterSpace :=
        hcompact.2.2.2.2.2
      have hfirstEq :
          transportedFirstStage P n = targetComplierShare P n :=
        hcompact.2.2.2.1
      have hmu : 0 < transportedFirstStage P n := by
        rw [hfirstEq]
        exact hIV.targetComplierPositivity
      have hratio :
          transportedOutcomeITT P n / transportedFirstStage P n =
            targetCACE P n :=
        hcompact.2.2.2.2.1
      have hweightMeas : Measurable (transportWeight P n) :=
        (Measure.measurable_rnDeriv
          (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
      have hweightMem :
          MemLp (transportWeight P n) 2 (sourceXLaw P n) := by
        refine MemLp.of_bound hweightMeas.aestronglyMeasurable
          (2 * (k n : ℝ)) ?_
        filter_upwards [hIV.weightEnvelope] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact hx.2
      have hweightMean :
          (∫ x, transportWeight P n x ∂sourceXLaw P n) = 1 := by
        have hchange := integral_rnDeriv_smul
          (μ := targetXLaw P n) (ν := sourceXLaw P n)
          (f := fun _ => (1 : ℝ)) hIV.transportDomination
        simpa [transportWeight] using hchange
      have hkappaOne : 1 ≤ kishDispersion P n := by
        simpa [kishDispersion] using
          one_le_secondMoment_of_mean_one
            (sourceXLaw P n) (transportWeight P n)
            hweightMem hweightMean
      have hkappa : 0 < kishDispersion P n :=
        lt_of_lt_of_le zero_lt_one hkappaOne
      rcases sourceObservationFacts_of_class P N k c epsilon n hIV with
        ⟨_hAssigned, _hSource, hYObs, _hMap, _hProp,
          hYScore, hDeltaY, hDScore, hDeltaD⟩
      have hoverObs : ∀ᵐ o ∂sourceObsLaw P n,
          epsilon ≤ P.propensity n o.1 ∧
            P.propensity n o.1 ≤ 1 - epsilon := by
        have hover := hIV.instrumentOverlap.2.2
        rw [sourceXLaw] at hover
        exact (ae_map_iff measurable_fst.aemeasurable
          (measurableSet_Icc.preimage
            (P.propensity_measurable n))).mp hover
      have hweightObs : ∀ᵐ o ∂sourceObsLaw P n,
          0 ≤ transportWeight P n o.1 ∧
            transportWeight P n o.1 ≤ 2 * (k n : ℝ) := by
        exact (ae_map_iff measurable_fst.aemeasurable
          (measurableSet_Icc.preimage hweightMeas)).mp
            (by simpa only [Set.mem_setOf_eq] using hIV.weightEnvelope)
      have hInstMeas : Measurable
          (oracleInstrumentScore (P.propensity n)) := by
        have he : Measurable (fun o : SourceObs 𝒳 =>
            P.propensity n o.1) :=
          (P.propensity_measurable n).comp measurable_fst
        unfold oracleInstrumentScore
        exact Measurable.ite (by measurability)
          (measurable_const.div he)
          (measurable_const.neg.div (measurable_const.sub he))
      have hBoolMeas : Measurable (fun o : SourceObs 𝒳 =>
          boolReal o.2.2.1) := by
        unfold boolReal
        exact Measurable.ite (by measurability)
          measurable_const measurable_const
      have hinstBound : ∀ᵐ o ∂sourceObsLaw P n,
          |oracleInstrumentScore (P.propensity n) o| ≤ 1 / epsilon := by
        filter_upwards [hoverObs] with o ho
        unfold oracleInstrumentScore
        split
        · rw [abs_div, abs_one,
            abs_of_pos (lt_of_lt_of_le hepsilon.1 ho.1)]
          exact one_div_le_one_div_of_le hepsilon.1 ho.1
        · have hden : 0 < 1 - P.propensity n o.1 := by linarith
          rw [abs_div, abs_neg, abs_one, abs_of_pos hden]
          exact one_div_le_one_div_of_le hepsilon.1 (by linarith)
      let FY : SourceObs 𝒳 → ℝ := fun o =>
        oracleInstrumentScore (P.propensity n) o * o.2.2.2
      let FD : SourceObs 𝒳 → ℝ := fun o =>
        oracleInstrumentScore (P.propensity n) o * boolReal o.2.2.1
      have hFYMeas : Measurable FY :=
        hInstMeas.mul (by fun_prop)
      have hFDMeas : Measurable FD :=
        hInstMeas.mul hBoolMeas
      have hFYInt : Integrable FY (sourceObsLaw P n) := by
        refine Integrable.of_bound hFYMeas.aestronglyMeasurable
          (1 / epsilon) ?_
        filter_upwards [hinstBound, hYObs] with o hs hy
        simp only [FY]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hy.1]
        exact (mul_le_mul hs hy.2 hy.1
          (div_nonneg zero_le_one hepsilon.1.le)).trans_eq (mul_one _)
      have hFDInt : Integrable FD (sourceObsLaw P n) := by
        refine Integrable.of_bound hFDMeas.aestronglyMeasurable
          (1 / epsilon) ?_
        filter_upwards [hinstBound] with o hs
        simp only [FD]
        rw [Real.norm_eq_abs, abs_mul]
        have hd : |boolReal o.2.2.1| ≤ 1 := by
          cases o.2.2.1 <;> simp [boolReal]
        exact (mul_le_mul hs hd (abs_nonneg _)
          (div_nonneg zero_le_one hepsilon.1.le)).trans_eq (mul_one _)
      have hdeltaYInt : Integrable (P.deltaY n) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (P.deltaY_measurable n).aestronglyMeasurable 1 ?_
        filter_upwards [hDeltaY] with x hx
        rw [Real.norm_eq_abs]
        exact (abs_le).2 hx
      have hdeltaDInt : Integrable (P.deltaD n) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (P.deltaD_measurable n).aestronglyMeasurable 1 ?_
        filter_upwards [hDeltaD] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact hx.2
      have hweightFYMem : MemLp (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 * FY o) 2 (sourceObsLaw P n) := by
        refine MemLp.of_bound
          ((hweightMeas.comp measurable_fst).mul hFYMeas).aestronglyMeasurable
          (2 * (k n : ℝ) / epsilon) ?_
        filter_upwards [hweightObs, hinstBound, hYObs] with o hw hs hy
        simp only [FY]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1,
          abs_mul, abs_of_nonneg hy.1]
        calc
          transportWeight P n o.1 *
              (|oracleInstrumentScore (P.propensity n) o| * o.2.2.2) ≤
              (2 * (k n : ℝ)) * ((1 / epsilon) * 1) := by
            exact mul_le_mul hw.2
              (mul_le_mul hs hy.2 hy.1
                (div_nonneg zero_le_one hepsilon.1.le))
              (mul_nonneg (abs_nonneg _) hy.1)
              (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          _ = 2 * (k n : ℝ) / epsilon := by ring
      have hweightFDMem : MemLp (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 * FD o) 2 (sourceObsLaw P n) := by
        refine MemLp.of_bound
          ((hweightMeas.comp measurable_fst).mul hFDMeas).aestronglyMeasurable
          (2 * (k n : ℝ) / epsilon) ?_
        filter_upwards [hweightObs, hinstBound] with o hw hs
        simp only [FD]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1, abs_mul]
        have hd : |boolReal o.2.2.1| ≤ 1 := by
          cases o.2.2.1 <;> simp [boolReal]
        calc
          transportWeight P n o.1 *
              (|oracleInstrumentScore (P.propensity n) o| *
                |boolReal o.2.2.1|) ≤
              (2 * (k n : ℝ)) * ((1 / epsilon) * 1) := by
            exact mul_le_mul hw.2
              (mul_le_mul hs hd (abs_nonneg _)
                (div_nonneg zero_le_one hepsilon.1.le))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          _ = 2 * (k n : ℝ) / epsilon := by ring
      have hweightDeltaYInt : Integrable (fun x =>
          transportWeight P n x * P.deltaY n x) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (hweightMeas.mul (P.deltaY_measurable n)).aestronglyMeasurable
          (2 * (k n : ℝ)) ?_
        filter_upwards [hIV.weightEnvelope, hDeltaY] with x hw hy
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1]
        exact (mul_le_mul hw.2 ((abs_le).2 hy)
          (abs_nonneg _) (mul_nonneg (by norm_num)
            (Nat.cast_nonneg _))).trans_eq (mul_one _)
      have hweightDeltaDInt : Integrable (fun x =>
          transportWeight P n x * P.deltaD n x) (sourceXLaw P n) := by
        refine Integrable.of_bound
          (hweightMeas.mul (P.deltaD_measurable n)).aestronglyMeasurable
          (2 * (k n : ℝ)) ?_
        filter_upwards [hIV.weightEnvelope, hDeltaD] with x hw hd
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw.1,
          abs_of_nonneg hd.1]
        exact (mul_le_mul hw.2 hd.2 hd.1
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _))).trans_eq
          (mul_one _)
      have hYMean : (∫ o, transportWeight P n o.1 * FY o
          ∂sourceObsLaw P n) = transportedOutcomeITT P n := by
        rw [pullout P n FY (P.deltaY n) (transportWeight P n)
          (inferInstance : IsProbabilityMeasure (sourceObsLaw P n))
          hFYInt hdeltaYInt (P.deltaY_measurable n) hweightMeas
          (hweightFYMem.integrable (by norm_num)) hweightDeltaYInt]
        · rfl
        · intro A hA
          simpa [FY, instrumentScore, oracleInstrumentScore] using hYScore A hA
      have hDMean : (∫ o, transportWeight P n o.1 * FD o
          ∂sourceObsLaw P n) = transportedFirstStage P n := by
        rw [pullout P n FD (P.deltaD n) (transportWeight P n)
          (inferInstance : IsProbabilityMeasure (sourceObsLaw P n))
          hFDInt hdeltaDInt (P.deltaD_measurable n) hweightMeas
          (hweightFDMem.integrable (by norm_num)) hweightDeltaDInt]
        · exact
            (transportedFirstStage_eq_weighted_deltaD P k epsilon n
              (sourceObservationFacts_of_class P N k c epsilon n hIV)
              hIV.instrumentOverlap hIV.weightEnvelope).symm
        · intro A hA
          simpa [FD, instrumentScore, oracleInstrumentScore] using hDScore A hA
      let theta := targetCACE P n
      let Z : SourceObs 𝒳 → ℝ :=
        oracleAffineScore (transportWeight P n) (P.propensity n) theta
      have hZMeas : Measurable Z := by
        unfold Z oracleAffineScore
        have hyMeas : Measurable (fun o : SourceObs 𝒳 => o.2.2.2) := by
          fun_prop
        exact ((hweightMeas.comp measurable_fst).mul hInstMeas).mul
          (hyMeas.sub (measurable_const.mul hBoolMeas))
      have hZMem : MemLp Z 2 (sourceObsLaw P n) := by
        refine MemLp.of_bound hZMeas.aestronglyMeasurable
          (4 * (k n : ℝ) / epsilon) ?_
        filter_upwards [hweightObs, hoverObs, hYObs] with o hw ho hy
        have hres := abs_oracleInstrumentScore_residual_le
          (P.propensity n) epsilon theta o hepsilon.1 ho htheta hy
        have hres' :
            |oracleInstrumentScore (P.propensity n) o| *
                |o.2.2.2 - theta * boolReal o.2.2.1| ≤ 2 / epsilon := by
          simpa [abs_mul] using hres
        simp only [Z]
        rw [oracleAffineScore, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg hw.1, mul_assoc]
        calc
          transportWeight P n o.1 *
              (|oracleInstrumentScore (P.propensity n) o| *
                |o.2.2.2 - theta * boolReal o.2.2.1|) ≤
              (2 * (k n : ℝ)) * (2 / epsilon) := by
            exact mul_le_mul hw.2 hres'
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          _ = 4 * (k n : ℝ) / epsilon := by ring
      have hZMean : (∫ o, Z o ∂sourceObsLaw P n) = 0 := by
        apply oracleAffineScore_mean_zero
          (sourceObsLaw P n) (transportWeight P n) (P.propensity n)
          theta (transportedOutcomeITT P n) (transportedFirstStage P n)
        · simpa [FY, mul_assoc] using
            hweightFYMem.integrable (by norm_num)
        · simpa [FD, mul_assoc] using
            hweightFDMem.integrable (by norm_num)
        · simpa [FY, mul_assoc] using hYMean
        · simpa [FD, mul_assoc] using hDMean
        · exact hmu.ne'
        · exact hratio
      have hweightSqObsInt : Integrable (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 ^ 2) (sourceObsLaw P n) := by
        have hmap : Integrable (fun x => transportWeight P n x ^ 2)
            (Measure.map (fun o : SourceObs 𝒳 => o.1)
              (sourceObsLaw P n)) := by
          simpa [sourceXLaw] using hweightMem.integrable_sq
        simpa [Function.comp_def] using
          (integrable_map_measure hmap.1 measurable_fst.aemeasurable).mp hmap
      have hkappaObs :
          (∫ o : SourceObs 𝒳, transportWeight P n o.1 ^ 2
              ∂sourceObsLaw P n) = kishDispersion P n := by
        have hmap := integral_map measurable_fst.aemeasurable
          hweightMem.integrable_sq.1
        simpa [kishDispersion, sourceXLaw] using hmap.symm
      have hZVar : variance Z (sourceObsLaw P n) ≤
          4 * kishDispersion P n / epsilon ^ 2 := by
        calc
          variance Z (sourceObsLaw P n) ≤
              ∫ o, Z o ^ 2 ∂sourceObsLaw P n :=
            variance_le_expectation_sq hZMeas.aestronglyMeasurable
          _ ≤ ∫ o, 4 * transportWeight P n o.1 ^ 2 / epsilon ^ 2
                ∂sourceObsLaw P n := by
            apply integral_mono_ae hZMem.integrable_sq
              ((hweightSqObsInt.const_mul 4).div_const _)
            filter_upwards [hoverObs, hYObs] with o ho hy
            exact oracleAffineScore_sq_le
              (transportWeight P n) (P.propensity n)
              epsilon theta o hepsilon.1 ho htheta hy
          _ = 4 * kishDispersion P n / epsilon ^ 2 := by
            rw [integral_div, integral_const_mul, hkappaObs]
      let QS : Measure (SourceSample 𝒳 n) :=
        Measure.pi (fun _ : Fin n => sourceObsLaw P n)
      let S : SourceSample 𝒳 n → ℝ := fun sample =>
        scoreOutcomeMean (transportWeight P n) (P.propensity n) n sample -
          theta * scoreReceiptMean
            (transportWeight P n) (P.propensity n) n sample
      have hSeq : S = fun sample : SourceSample 𝒳 n =>
          (n : ℝ)⁻¹ * ∑ i, Z (sample i) := by
        funext sample
        exact scoreOutcomeMean_sub_receiptMean
          (transportWeight P n) (P.propensity n) theta n sample
      have hSmom := iid_empiricalAverage_mean_variance
        (sourceObsLaw P n) n hn Z hZMem
      have hSmean : (∫ sample, S sample ∂QS) = 0 := by
        rw [hSeq]
        exact hSmom.1.trans hZMean
      have hSvar : variance S QS ≤
          4 * kishDispersion P n / (epsilon ^ 2 * n) := by
        rw [hSeq, hSmom.2]
        calc
          (n : ℝ)⁻¹ * variance Z (sourceObsLaw P n) ≤
              (n : ℝ)⁻¹ *
                (4 * kishDispersion P n / epsilon ^ 2) := by
            gcongr
          _ = 4 * kishDispersion P n / (epsilon ^ 2 * n) := by
            ring
      have hSmem : MemLp S 2 QS := by
        rw [hSeq]
        have heval (i : Fin n) :
            MeasurePreserving (fun sample : SourceSample 𝒳 n => sample i)
              QS (sourceObsLaw P n) := by
          refine ⟨measurable_pi_apply i, ?_⟩
          dsimp [QS]
          rw [Measure.pi_map_eval]
          simp
        have hcoord (i : Fin n) :
            MemLp (fun sample : SourceSample 𝒳 n => Z (sample i)) 2 QS := by
          simpa [Function.comp_def] using
            hZMem.comp_measurePreserving (heval i)
        exact (memLp_finset_sum Finset.univ
          (fun i _hi => hcoord i)).const_mul _
      let K : SourceSample 𝒳 n → ℝ := fun sample =>
        empiricalKish (transportWeight P n) n sample
      have hweightSqObsMem : MemLp (fun o : SourceObs 𝒳 =>
          transportWeight P n o.1 ^ 2) 2 (sourceObsLaw P n) := by
        refine MemLp.of_bound
          ((hweightMeas.comp measurable_fst).pow_const 2).aestronglyMeasurable
          ((2 * (k n : ℝ)) ^ 2) ?_
        filter_upwards [hweightObs] with o hw
        rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hw.1]
        exact pow_le_pow_left₀ hw.1 hw.2 2
      have hKmean : (∫ sample, K sample ∂QS) =
          kishDispersion P n := by
        calc
          (∫ sample, K sample ∂QS) =
              ∫ o : SourceObs 𝒳, transportWeight P n o.1 ^ 2
                ∂sourceObsLaw P n := by
            simpa [K, QS] using
              empiricalKish_mean (sourceObsLaw P n)
                (transportWeight P n) n hn hweightSqObsMem
          _ = kishDispersion P n := hkappaObs
      have hKmem : MemLp K 2 QS := by
        have heval (i : Fin n) :
            MeasurePreserving (fun sample : SourceSample 𝒳 n => sample i)
              QS (sourceObsLaw P n) := by
          refine ⟨measurable_pi_apply i, ?_⟩
          dsimp [QS]
          rw [Measure.pi_map_eval]
          simp
        have hcoord (i : Fin n) : MemLp
            (fun sample : SourceSample 𝒳 n =>
              transportWeight P n (sample i).1 ^ 2) 2 QS := by
          simpa [Function.comp_def] using
            hweightSqObsMem.comp_measurePreserving (heval i)
        unfold K empiricalKish Causalean.Stat.empiricalKishDispersion
        exact (memLp_finset_sum Finset.univ
          (fun i _hi => hcoord i)).const_mul _
      have hfourth : ∀ᵐ o ∂sourceObsLaw P n,
          transportWeight P n o.1 ^ 4 ≤
            4 * (k n : ℝ) ^ 2 * transportWeight P n o.1 ^ 2 := by
        filter_upwards [hweightObs] with o hw
        exact weight_fourth_le_envelope
          (transportWeight P n o.1) (k n : ℝ) hw.1 hw.2
      have hKvar : variance K QS ≤
          4 * (k n : ℝ) ^ 2 * kishDispersion P n / n := by
        simpa [K, QS] using empiricalKish_variance_le
          (sourceObsLaw P n) (transportWeight P n) n (k n)
          (kishDispersion P n) hn hweightSqObsMem hkappaObs hfourth
      have hKbadRaw :
          (QS {sample | K sample < kishDispersion P n / 2}).toReal ≤
            16 * (k n : ℝ) ^ 2 /
              ((n : ℝ) * kishDispersion P n) := by
        simpa [K] using empiricalKish_lower_tail_le n QS
          (transportWeight P n) (k n) (kishDispersion P n)
          hn hkappa hKmem hKmean hKvar
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hKbad :
          (QS {sample | K sample < kishDispersion P n / 2}).toReal ≤
            16 * (k n : ℝ) ^ 2 / n := by
        calc
          _ ≤ 16 * (k n : ℝ) ^ 2 /
              ((n : ℝ) * kishDispersion P n) := hKbadRaw
          _ ≤ 16 * (k n : ℝ) ^ 2 / n := by
            rw [div_le_div_iff₀ (mul_pos hnR hkappa) hnR]
            gcongr
            calc
              (n : ℝ) = (n : ℝ) * 1 := by ring
              _ ≤ (n : ℝ) * kishDispersion P n :=
                mul_le_mul_of_nonneg_left hkappaOne hnR.le
      have hbasePos : 0 < 8 / (alpha * epsilon ^ 2) := by
        exact div_pos (by norm_num)
          (mul_pos halpha.1 (sq_pos_of_pos hepsilon.1))
      have hLpos : 0 < L := by
        simpa [L] using Real.sqrt_pos.2 hbasePos
      have hLsq : L ^ 2 = 8 / (alpha * epsilon ^ 2) := by
        simpa [L] using Real.sq_sqrt hbasePos.le
      let a : ℝ :=
        L * Real.sqrt (kishDispersion P n / (2 * n))
      have ha : 0 < a := by
        unfold a
        exact mul_pos hLpos (Real.sqrt_pos.2 (by positivity))
      have hSbadRaw :
          (QS {sample | a < |S sample - 0|}).toReal ≤
            (4 * kishDispersion P n / (epsilon ^ 2 * n)) / a ^ 2 :=
        probability_abs_sub_mean_gt_le QS S 0
          (4 * kishDispersion P n / (epsilon ^ 2 * n)) a
          hSmem ha hSmean hSvar
      have hSratio :
          (4 * kishDispersion P n / (epsilon ^ 2 * n)) / a ^ 2 =
            alpha := by
        unfold a
        change (4 * kishDispersion P n / (epsilon ^ 2 * n)) /
          (Real.sqrt (8 / (alpha * epsilon ^ 2)) *
            Real.sqrt (kishDispersion P n / (2 * n))) ^ 2 = alpha
        rw [mul_pow, Real.sq_sqrt hbasePos.le,
          Real.sq_sqrt (by positivity)]
        field_simp [halpha.1.ne', hepsilon.1.ne', hnR.ne', hkappa.ne']
        ring
      have hSbad :
          (QS {sample | a < |S sample|}).toReal ≤ alpha := by
        simpa [hSratio] using hSbadRaw
      have hKMeas : Measurable K := by
        unfold K empiricalKish Causalean.Stat.empiricalKishDispersion
        fun_prop
      have hSMeas : Measurable S := by
        rw [hSeq]
        fun_prop
      let BK : Set (SourceSample 𝒳 n) :=
        {sample | K sample < kishDispersion P n / 2}
      let BS : Set (SourceSample 𝒳 n) :=
        {sample | a < |S sample|}
      have hBKMeas : MeasurableSet BK :=
        measurableSet_lt hKMeas measurable_const
      have hBSMeas : MeasurableSet BS :=
        measurableSet_lt measurable_const hSMeas.abs
      have hbadUnion :
          (QS (BK ∪ BS)).toReal ≤ delta n + alpha := by
        change QS.real (BK ∪ BS) ≤ delta n + alpha
        calc
          QS.real (BK ∪ BS) ≤ QS.real BK + QS.real BS :=
            measureReal_union_le (μ := QS) BK BS
          _ ≤ 16 * (k n : ℝ) ^ 2 / n + alpha := by
            exact add_le_add (by simpa [Measure.real, BK] using hKbad)
              (by simpa [Measure.real, BS] using hSbad)
          _ = delta n + alpha := by simp [delta, hn0]
      have hgoodSource :
          1 - alpha - delta n ≤ (QS ((BK ∪ BS)ᶜ)).toReal := by
        change 1 - alpha - delta n ≤ QS.real ((BK ∪ BS)ᶜ)
        rw [measureReal_compl (hBKMeas.union hBSMeas)]
        have hQSone : QS.real Set.univ = 1 := by
          simp [Measure.real]
        rw [hQSone]
        change QS.real (BK ∪ BS) ≤ _ at hbadUnion
        linarith
      let QT : Measure (TargetSample 𝒳 (N n)) :=
        Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
      have hgoodProd :
          (twoSampleLaw P N n (((BK ∪ BS)ᶜ) ×ˢ Set.univ)).toReal =
            (QS ((BK ∪ BS)ᶜ)).toReal := by
        rw [twoSampleLaw, Measure.prod_prod]
        simp [QS, QT]
      have hgoodSubset :
          ((BK ∪ BS)ᶜ) ×ˢ (Set.univ : Set (TargetSample 𝒳 (N n))) ⊆
            {s | targetCACE P n ∈ oracleSet C P n s} := by
        intro s hs
        have hgood := hs.1
        simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq,
          not_or] at hgood
        have hKhalf : kishDispersion P n / 2 ≤ K s.1 :=
          le_of_not_gt hgood.1
        have hroot : Real.sqrt (kishDispersion P n / (2 * n)) ≤
            Real.sqrt (K s.1 / n) := by
          apply Real.sqrt_le_sqrt
          calc
            kishDispersion P n / (2 * (n : ℝ)) =
                (kishDispersion P n / 2) / n := by ring
            _ ≤ K s.1 / n :=
              div_le_div_of_nonneg_right hKhalf hnR.le
        have hscore : |S s.1| ≤
            L * Real.sqrt (K s.1 / n) := by
          calc
            |S s.1| ≤ a := le_of_not_gt hgood.2
            _ = L * Real.sqrt (kishDispersion P n / (2 * n)) := rfl
            _ ≤ L * Real.sqrt (K s.1 / n) :=
              mul_le_mul_of_nonneg_left hroot hLpos.le
        change targetCACE P n ∈ oracleSet C P n s
        simp only [oracleSet, C]
        exact ⟨htheta, by simpa [S, theta, K] using hscore⟩
      calc
        1 - alpha - delta n ≤
            (QS ((BK ∪ BS)ᶜ)).toReal := hgoodSource
        _ = (twoSampleLaw P N n
            (((BK ∪ BS)ᶜ) ×ˢ
              (Set.univ : Set (TargetSample 𝒳 (N n))))).toReal :=
          hgoodProd.symm
        _ ≤ oracleCoverage C P n := by
          exact measureReal_mono hgoodSubset
    have hInhab : ∀ᶠ n in atTop, ∃ P,
        TransportedIVClass P N k c epsilon n :=
      hClass 1 zero_lt_one
    have hCoverageRange : ∀ n P,
        TransportedIVClass P N k c epsilon n →
          0 ≤ oracleCoverage C P n ∧
            oracleCoverage C P n ≤ 1 := by
      intro n P hP
      letI : IsProbabilityMeasure (sourceObsLaw P n) :=
        hP.twoSampleArray.2.1 n
      letI : IsProbabilityMeasure (targetXLaw P n) :=
        hP.twoSampleArray.2.2.1 n
      letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
        unfold twoSampleLaw
        infer_instance
      constructor
      · exact ENNReal.toReal_nonneg
      · simpa [oracleCoverage, Measure.real] using
          (measureReal_le_one (μ := twoSampleLaw P N n))
    have hHonest :
        OracleHonest N k c epsilon alpha C := by
      have hcanonical :
          1 - alpha ≤ Filter.liminf
            (fun n => ⨅ P : {P : TransportedArray 𝒳 //
                TransportedIVClass P N k c epsilon n},
              oracleCoverage C P n) atTop :=
        abstractClass_coverage_liminf
          (fun n P => TransportedIVClass P N k c epsilon n)
          (fun n P => oracleCoverage C P n) alpha delta
          hdelta hInhab hCoverageRange hCoveragePoint
      have hrows :
          ∀ᶠ n in atTop,
            oracleCoverageClassInf N k c epsilon C n =
              (⨅ P : {P : TransportedArray 𝒳 //
                  TransportedIVClass P N k c epsilon n},
                oracleCoverage C P n) := by
        filter_upwards [hInhab] with n hn
        exact scoreProcedure_oracleCoverageClassInf_eq
          N k c epsilon L C hCset n
          ⟨⟨hn.choose, hn.choose_spec⟩⟩
      exact ⟨halpha.1, halpha.2,
        hcanonical.trans_eq (Filter.liminf_congr hrows).symm⟩

    refine ⟨hHonest, ?_⟩
    intro t0 ht0
    let ell : ℕ → TransportedArray 𝒳 → ℝ := fun n P =>
      if n = 0 then 0 else oracleExpectedLength C P n
    have hellNonneg : ∀ n P,
        TransportedIVClass P N k c epsilon n → 0 ≤ ell n P := by
      intro n P hP
      unfold ell
      split_ifs
      · norm_num
      · exact integral_nonneg fun _ => ENNReal.toReal_nonneg
    have hellPoint : ∀ n P,
        TransportedIVClass P N k c epsilon n →
          ell n P ≤ max 2 (4 * L + 8 / epsilon ^ 2) *
            min 1 (effectiveStrength P n ^ (-1 / 2 : ℝ)) := by
      intro n P hP
      unfold ell
      split_ifs with hn0
      · have hstrength : 0 ≤ effectiveStrength P n := by
          unfold effectiveStrength kishDispersion
          positivity
        exact mul_nonneg
          (le_trans (by norm_num) (le_max_left _ _))
          (le_min (by norm_num) (Real.rpow_nonneg hstrength _))
      · exact hRiskPoint n P (Nat.pos_of_ne_zero hn0) hP
    have hriskEll :
        abstractClassFrontierRisk
            (fun n P => TransportedIVClass P N k c epsilon n)
            (fun n P => effectiveStrength P n) ell t0 ≤
          max 2 (4 * L + 8 / epsilon ^ 2) *
            min 1 (t0 ^ (-1 / 2 : ℝ)) :=
      abstractClassFrontierRisk_le
        (fun n P => TransportedIVClass P N k c epsilon n)
        (fun n P => effectiveStrength P n) ell
        (max 2 (4 * L + 8 / epsilon ^ 2)) t0
        (le_trans (by norm_num) (le_max_left _ _)) ht0
        hellNonneg hellPoint
    calc
      frontierRiskTotal N k c epsilon C t0 =
          abstractClassFrontierRisk
            (fun n P => TransportedIVClass P N k c epsilon n)
            (fun n P => effectiveStrength P n) ell t0 := by
        unfold frontierRiskTotal abstractClassFrontierRisk
        apply Filter.limsup_congr
        filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
        have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hn)
        simp only [ell, hn0, if_false]
        exact scoreProcedure_frontierRiskRow_eq
          N k c epsilon L t0 C hCset n
      _ ≤ max 2 (4 * L + 8 / epsilon ^ 2) *
          min 1 (t0 ^ (-1 / 2 : ℝ)) := hriskEll
  refine ⟨C, ?_, hUpper.1, ?_⟩
  · intro n x
    rfl
  intro t0 ht0
  have hfixed : ∀ (g' : Geometry 𝒳)
      (hg' : AdmissibleGeometry g' k epsilon),
      3 * (1 - alpha) ^ 2 / 16 *
          min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
        fixedGeometryValueTotal N k c epsilon alpha ⟨g', hg'⟩ t0 ∧
      fixedGeometryValueTotal N k c epsilon alpha ⟨g', hg'⟩ t0 ≤
        max 2 (4 * L + 8 / epsilon ^ 2) *
          min 1 (t0 ^ (-1 / 2 : ℝ)) := by
    intro g' hg'
    simpa [L] using
      fixed_geometry_frontier N k c epsilon alpha g' hc hN hkPos hkInf
        hkRoot hepsilon hg'
        (fun n P hP => hTwo n P hP.1)
        (fun n P hP => hOverlap n P hP.1)
        (fun n P hP => hEnvelope n P hP.1)
        (fun n P hP => hSecond n P hP.1)
        (fun n P hP => hDegrade n P hP.1)
        halpha t0 ht0
  have hlowerRisk : ∀ E : OracleProcedure 𝒳 N k c epsilon,
      OracleHonest N k c epsilon alpha E →
      3 * (1 - alpha) ^ 2 / 16 *
          min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
        frontierRiskTotal N k c epsilon E t0 := by
    intro E hE
    exact (hfixed g hg).1.trans
      (fixedGeometryValue_le_frontierRisk N k c epsilon alpha g E hE t0
        hc hepsilon ht0 hg hN hkPos hkInf hkRoot)
  have hlower :
      3 * (1 - alpha) ^ 2 / 16 *
          min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
        oracleValueTotal (𝒳 := 𝒳) N k c epsilon alpha t0 := by
    letI : Nonempty {E : OracleProcedure 𝒳 N k c epsilon //
        OracleHonest N k c epsilon alpha E} :=
      ⟨⟨C, hUpper.1⟩⟩
    unfold oracleValueTotal
    apply le_ciInf
    intro E
    exact hlowerRisk E E.2
  have hsetLengthTwo : ∀ A : Set ℝ, setLength A ≤ 2 := by
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
  have hRiskNonneg : ∀ E : OracleProcedure 𝒳 N k c epsilon,
      0 ≤ frontierRiskTotal N k c epsilon E t0 := by
    intro E
    let row : ℕ → ℝ := frontierRiskRow N k c epsilon E t0
    have hrowNonneg : ∀ n, 0 ≤ row n := by
      intro n
      cases isEmpty_or_nonempty
          {P : TransportedArray 𝒳 //
            TransportedIVClass P N k c epsilon n ∧
              t0 ≤ effectiveStrength P n} with
      | inl h =>
          letI := h
          unfold row frontierRiskRow
          calc
            0 ≤ (0 : ℝ) := le_rfl
            _ = (⨆ P :
                {P : TransportedArray 𝒳 //
                  TransportedIVClass P N k c epsilon n ∧
                    t0 ≤ effectiveStrength P n},
                oracleExpectedLength E P n) :=
              ((iSup_of_empty' _).trans Real.sSup_empty).symm
      | inr h =>
          letI := h
          let P := Classical.choice h
          refine le_trans ?_ (le_ciSup ?_ P)
          · exact integral_nonneg (fun _ => ENNReal.toReal_nonneg)
          · refine ⟨2, ?_⟩
            rintro y ⟨Q, rfl⟩
            letI : IsProbabilityMeasure (sourceObsLaw Q.1 n) :=
              Q.property.1.twoSampleArray.2.1 n
            letI : IsProbabilityMeasure (targetXLaw Q.1 n) :=
              Q.property.1.twoSampleArray.2.2.1 n
            letI : IsProbabilityMeasure
                (twoSampleLaw Q.1 N n) := by
              unfold twoSampleLaw
              infer_instance
            exact (integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
              (integrable_const 2)
              (Filter.Eventually.of_forall fun s =>
                hsetLengthTwo
                  (oracleSet E Q.1 n s))).trans_eq (by simp)
    have hrowTwo : ∀ n, row n ≤ 2 := by
      intro n
      cases isEmpty_or_nonempty
          {P : TransportedArray 𝒳 //
            TransportedIVClass P N k c epsilon n ∧
              t0 ≤ effectiveStrength P n} with
      | inl h =>
          letI := h
          unfold row frontierRiskRow
          calc
            (⨆ P :
                {P : TransportedArray 𝒳 //
                  TransportedIVClass P N k c epsilon n ∧
                    t0 ≤ effectiveStrength P n},
                oracleExpectedLength E P n) =
                0 := (iSup_of_empty' _).trans Real.sSup_empty
            _ ≤ 2 := by norm_num
      | inr h =>
          letI := h
          apply ciSup_le
          intro P
          letI : IsProbabilityMeasure (sourceObsLaw P.1 n) :=
            P.property.1.twoSampleArray.2.1 n
          letI : IsProbabilityMeasure (targetXLaw P.1 n) :=
            P.property.1.twoSampleArray.2.2.1 n
          letI : IsProbabilityMeasure
              (twoSampleLaw P.1 N n) := by
            unfold twoSampleLaw
            infer_instance
          exact (integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
            (integrable_const 2)
            (Filter.Eventually.of_forall fun s =>
              hsetLengthTwo
                (oracleSet E P.1 n s))).trans_eq (by simp)
    unfold frontierRiskTotal
    have hzeroCobounded :
        IsCoboundedUnder (· ≤ ·) atTop (fun _ : ℕ => (0 : ℝ)) := by
      change ∃ b, ∀ a, (∀ᶠ _n : ℕ in atTop, (0 : ℝ) ≤ a) → b ≤ a
      exact ⟨0, fun a ha => ha.exists.choose_spec⟩
    have hrowBounded : IsBoundedUnder (· ≤ ·) atTop row := by
      change ∃ b, ∀ᶠ n in atTop, row n ≤ b
      exact ⟨2, Filter.Eventually.of_forall hrowTwo⟩
    change 0 ≤ Filter.limsup row atTop
    rw [← Filter.limsup_const (f := (atTop : Filter ℕ)) (0 : ℝ)]
    exact Filter.limsup_le_limsup
      (Filter.Eventually.of_forall hrowNonneg)
      hzeroCobounded hrowBounded
  have hupperValue :
      oracleValueTotal (𝒳 := 𝒳) N k c epsilon alpha t0 ≤
        max 2 (4 * L + 8 / epsilon ^ 2) *
          min 1 (t0 ^ (-1 / 2 : ℝ)) := by
    unfold oracleValueTotal
    have hbdd : BddBelow
        (Set.range (fun E :
          {E : OracleProcedure 𝒳 N k c epsilon //
            OracleHonest N k c epsilon alpha E} =>
          frontierRiskTotal N k c epsilon E.1 t0)) := by
      exact ⟨0, by
        rintro y ⟨E, rfl⟩
        exact hRiskNonneg E⟩
    exact (ciInf_le hbdd ⟨C, hUpper.1⟩).trans (hUpper.2 t0 ht0)
  exact ⟨hUpper.2 t0 ht0, hlower, hupperValue, hfixed⟩

end CausalSmith.Stat.TransportedLateStrengthFrontier
