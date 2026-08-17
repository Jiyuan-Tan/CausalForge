/-
# Transported score inversion

The oracle score, empirical first stage, empirical Kish scale, and its inverted
acceptance set.  The target sample is absent from the definition.
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Frontier
import Causalean.Stat.Sample.EffectiveSampleSize

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- Instrument multiplier formed from the declared propensity input. -/
noncomputable def oracleInstrumentScore (e : 𝒳 → ℝ)
    (o : SourceObs 𝒳) : ℝ :=
  if o.2.1 then 1 / e o.1 else -1 / (1 - e o.1)

/-- Empirical transported outcome score. -/
noncomputable def scoreOutcomeMean (weight e : 𝒳 → ℝ) (n : ℕ)
    (sample : SourceSample 𝒳 n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, weight (sample i).1 *
    oracleInstrumentScore e (sample i) * (sample i).2.2.2

/-- Empirical transported receipt score. -/
noncomputable def scoreReceiptMean (weight e : 𝒳 → ℝ) (n : ℕ)
    (sample : SourceSample 𝒳 n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, weight (sample i).1 *
    oracleInstrumentScore e (sample i) * boolReal (sample i).2.2.1

/-- Empirical second moment of the oracle transport weight. -/
noncomputable abbrev empiricalKish (weight : 𝒳 → ℝ) (n : ℕ)
    (sample : SourceSample 𝒳 n) : ℝ :=
  Causalean.Stat.empiricalKishDispersion
    (fun o : SourceObs 𝒳 => weight o.1) n sample

-- @node: def:inversion-handle
/-- Inversion of the affine transported score over `Theta`. -/
noncomputable def inversionHandle (weight e : 𝒳 → ℝ) (n : ℕ) (L : ℝ)
    (sample : SourceSample 𝒳 n) : Set ℝ :=
  {theta | theta ∈ parameterSpace ∧
    |scoreOutcomeMean weight e n sample -
        theta * scoreReceiptMean weight e n sample| ≤
      L * Real.sqrt (empiricalKish weight n sample / n)}
  -- @realizes C_n(score-inversion confidence set)
  -- @realizes \Theta(inversion restricted to [-1,1])

/-- The inversion handle only inspects the weight at realized source-sample
covariates. -/
lemma inversionHandle_congr_of_sample
    {weight weight' e : 𝒳 → ℝ} {n : ℕ} {L : ℝ}
    {sample : SourceSample 𝒳 n}
    (h : ∀ i, weight (sample i).1 = weight' (sample i).1) :
    inversionHandle weight e n L sample =
      inversionHandle weight' e n L sample := by
  unfold inversionHandle scoreOutcomeMean scoreReceiptMean empiricalKish
    Causalean.Stat.empiricalKishDispersion
  simp_rw [h]

/-- Every density-ratio version agrees with the canonical version
simultaneously at the finitely many realized source covariates. -/
lemma sourceSample_weight_version_ae_eq
    (P : TransportedArray 𝒳) (n : ℕ) (w : TransportWeightVersion P n)
    [SigmaFinite (sourceObsLaw P n)] :
    (fun s : SourceSample 𝒳 n => fun i => w.1.1 (s i).1) =ᵐ[
        Measure.pi (fun _ : Fin n => sourceObsLaw P n)]
      (fun s : SourceSample 𝒳 n =>
        fun i => transportWeight P n (s i).1) := by
  have hwObs :
      (fun o : SourceObs 𝒳 => w.1.1 o.1) =ᵐ[sourceObsLaw P n]
        (fun o : SourceObs 𝒳 => transportWeight P n o.1) := by
    simpa only [sourceXLaw, Function.comp_def] using
      (MeasureTheory.ae_eq_comp measurable_fst.aemeasurable w.property.2)
  exact Measure.ae_eq_pi (fun _ => hwObs)

/-- Score inversion is unchanged almost surely throughout a density-ratio
version fiber. -/
lemma inversionHandle_weight_version_ae_eq
    (P : TransportedArray 𝒳) (n : ℕ) (w : TransportWeightVersion P n)
    (L : ℝ) [SigmaFinite (sourceObsLaw P n)] :
    (fun s : SourceSample 𝒳 n =>
      inversionHandle w.1.1 (P.propensity n) n L s) =ᵐ[
        Measure.pi (fun _ : Fin n => sourceObsLaw P n)]
      (fun s : SourceSample 𝒳 n =>
        inversionHandle (transportWeight P n) (P.propensity n) n L s) := by
  filter_upwards [sourceSample_weight_version_ae_eq P n w] with s hs
  exact inversionHandle_congr_of_sample (fun i => congrFun hs i)

/-- A score-inversion procedure gives the same random set almost surely
throughout a model's density-ratio version fiber. -/
lemma scoreProcedure_set_weight_version_ae_eq
    (N k : ℕ → ℕ) (c epsilon L : ℝ)
    (C : OracleProcedure 𝒳 N k c epsilon)
    (hC : ∀ n x, C.set n x =
      inversionHandle x.2.1.1 x.2.2 n L x.1.1)
    (P : TransportedArray 𝒳) (n : ℕ)
    (hP : TransportedIVClass P N k c epsilon n)
    (w : TransportWeightVersion P n) :
    (oracleSetAtWeight C P n w) =ᵐ[twoSampleLaw P N n]
      (oracleSet C P n) := by
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hP.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hP.twoSampleArray.2.2.1 n
  letI : IsProbabilityMeasure
      (Measure.pi (fun _ : Fin n => sourceObsLaw P n)) := by
    infer_instance
  letI : IsProbabilityMeasure
      (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) := by
    infer_instance
  have hs := inversionHandle_weight_version_ae_eq P n w L
  have hs' :
      (fun z : TwoSample 𝒳 n (N n) =>
        inversionHandle w.1.1 (P.propensity n) n L z.1) =ᵐ[
          twoSampleLaw P N n]
      (fun z : TwoSample 𝒳 n (N n) =>
        inversionHandle (transportWeight P n) (P.propensity n) n L z.1) := by
    let μS := Measure.pi (fun _ : Fin n => sourceObsLaw P n)
    let μT := Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
    have hmap : Measure.map Prod.fst (μS.prod μT) = μS := by
      simp [μS, μT]
    have hsmap :
        (fun s : SourceSample 𝒳 n =>
          inversionHandle w.1.1 (P.propensity n) n L s) =ᵐ[
            Measure.map Prod.fst (μS.prod μT)]
        (fun s : SourceSample 𝒳 n =>
          inversionHandle (transportWeight P n) (P.propensity n) n L s) := by
      rw [hmap]
      exact hs
    simpa only [twoSampleLaw, μS, μT, Function.comp_def] using
      (MeasureTheory.ae_eq_comp measurable_fst.aemeasurable hsmap)
  filter_upwards [hs'] with z hz
  simpa only [oracleSetAtWeight, oracleSet, hC, transportWeightInput] using hz

/-- For a score-inversion procedure, coverage is unchanged when the canonical transport weight is replaced by any admissible version. -/
lemma scoreProcedure_coverage_weight_version_eq
    (N k : ℕ → ℕ) (c epsilon L : ℝ)
    (C : OracleProcedure 𝒳 N k c epsilon)
    (hC : ∀ n x, C.set n x =
      inversionHandle x.2.1.1 x.2.2 n L x.1.1)
    (P : TransportedArray 𝒳) (n : ℕ)
    (hP : TransportedIVClass P N k c epsilon n)
    (w : TransportWeightVersion P n) :
    oracleCoverageAtWeight C P n w = oracleCoverage C P n := by
  unfold oracleCoverageAtWeight oracleCoverage
  congr 1
  apply measure_congr
  filter_upwards [
    scoreProcedure_set_weight_version_ae_eq N k c epsilon L C hC P n hP w
  ] with s hs
  exact congrArg (fun A : Set ℝ => targetCACE P n ∈ A) hs

/-- For a score-inversion procedure, expected confidence-set length is unchanged when the canonical transport weight is replaced by any admissible version. -/
lemma scoreProcedure_expectedLength_weight_version_eq
    (N k : ℕ → ℕ) (c epsilon L : ℝ)
    (C : OracleProcedure 𝒳 N k c epsilon)
    (hC : ∀ n x, C.set n x =
      inversionHandle x.2.1.1 x.2.2 n L x.1.1)
    (P : TransportedArray 𝒳) (n : ℕ)
    (hP : TransportedIVClass P N k c epsilon n)
    (w : TransportWeightVersion P n) :
    oracleExpectedLengthAtWeight C P n w =
      oracleExpectedLength C P n := by
  unfold oracleExpectedLengthAtWeight oracleExpectedLength
  apply integral_congr_ae
  filter_upwards [
    scoreProcedure_set_weight_version_ae_eq N k c epsilon L C hC P n hP w
  ] with s hs
  rw [hs]

set_option maxHeartbeats 3000000 in
/-- For score inversion, taking the infimum over the full version fiber is
exactly the canonical coverage infimum. -/
lemma scoreProcedure_oracleCoverageClassInf_eq
    (N k : ℕ → ℕ) (c epsilon L : ℝ)
    (C : OracleProcedure 𝒳 N k c epsilon)
    (hC : ∀ n x, C.set n x =
      inversionHandle x.2.1.1 x.2.2 n L x.1.1)
    (n : ℕ)
    (hrow : Nonempty {P : TransportedArray 𝒳 //
      TransportedIVClass P N k c epsilon n}) :
    oracleCoverageClassInf N k c epsilon C n =
      (⨅ P : {P : TransportedArray 𝒳 //
          TransportedIVClass P N k c epsilon n},
        oracleCoverage C P n) := by
  letI := hrow
  simp only [oracleCoverageClassInf, coverageInfOrOne]
  exact Causalean.Stat.coverageInfOrOne_of_nonempty _

set_option maxHeartbeats 3000000 in
/-- For score inversion, the full representative-fiber risk row equals the
canonical row used by the existing score calculation. -/
lemma scoreProcedure_frontierRiskRow_eq
    (N k : ℕ → ℕ) (c epsilon L t0 : ℝ)
    (C : OracleProcedure 𝒳 N k c epsilon)
    (hC : ∀ n x, C.set n x =
      inversionHandle x.2.1.1 x.2.2 n L x.1.1)
    (n : ℕ) :
    frontierRiskRow N k c epsilon C t0 n =
      (⨆ P : {P : TransportedArray 𝒳 //
          TransportedIVClass P N k c epsilon n ∧
            t0 ≤ effectiveStrength P n},
        oracleExpectedLength C P n) := by
  rfl

/-- Affine inversion has length at most the interval diameter and, away from a
zero empirical first stage, at most twice radius over slope. -/
lemma inversionHandle_length_le (weight e : 𝒳 → ℝ) (n : ℕ) (L : ℝ)
    (sample : SourceSample 𝒳 n) (hL : 0 ≤ L)
    (hB : scoreReceiptMean weight e n sample ≠ 0) :
    setLength (inversionHandle weight e n L sample) ≤
      min 2 (2 * (L * Real.sqrt (empiricalKish weight n sample / n)) /
        |scoreReceiptMean weight e n sample|) := by
  let A := scoreOutcomeMean weight e n sample
  let B := scoreReceiptMean weight e n sample
  let r := L * Real.sqrt (empiricalKish weight n sample / n)
  have hr : 0 ≤ r := mul_nonneg hL (Real.sqrt_nonneg _)
  have hAbsB : 0 < |B| := abs_pos.mpr hB
  apply le_min
  · unfold setLength parameterSpace
    calc
      (volume (inversionHandle weight e n L sample ∩ Set.Icc (-1) 1)).toReal
          ≤ (volume (Set.Icc (-1 : ℝ) 1)).toReal := ENNReal.toReal_mono
            (by simp [Real.volume_Icc]) (measure_mono (Set.inter_subset_right))
      _ = 2 := by simp [Real.volume_Icc] <;> norm_num
  · have hsub :
        inversionHandle weight e n L sample ∩ parameterSpace ⊆
          Set.Icc (A / B - r / |B|) (A / B + r / |B|) := by
      intro x hx
      have hscore := hx.1.2
      change |A - x * B| ≤ r at hscore
      change A / B - r / |B| ≤ x ∧ x ≤ A / B + r / |B|
      have hid : A - x * B = B * (A / B - x) := by
        field_simp [B, hB]
      rw [hid, abs_mul] at hscore
      have hx' : |A / B - x| ≤ r / |B| := by
        rw [le_div_iff₀ hAbsB]
        simpa [mul_comm] using hscore
      rw [abs_le] at hx'
      constructor <;> linarith
    unfold setLength
    calc
      (volume (inversionHandle weight e n L sample ∩ parameterSpace)).toReal
          ≤ (volume (Set.Icc (A / B - r / |B|)
              (A / B + r / |B|))).toReal := ENNReal.toReal_mono
            (by simp [Real.volume_Icc]) (measure_mono hsub)
      _ = 2 * r / |B| := by
        simp [Real.volume_Icc, ENNReal.toReal_ofReal,
          div_nonneg hr hAbsB.le]
        field_simp
        ring

end CausalSmith.Stat.TransportedLateStrengthFrontier
