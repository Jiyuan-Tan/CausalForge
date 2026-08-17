import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.FiniteMaxDecision
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.FiniteMaxDepoisson

/-!
# Causal finite-packing lower bound

This module converts the causal hard-family cell experiment into a
coordinatewise testing problem and transfers its loss back to a fixed-size
sample.
-/

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Equip the causal risk index set with the discrete measurable structure. -/
local instance causalRiskIndexMeasurableSpace (M : ℕ) :
    MeasurableSpace (Unit ⊕ Fin M) := ⊤

/-- Every singleton causal risk index is measurable. -/
local instance causalRiskIndexMeasurableSingletonClass (M : ℕ) :
    MeasurableSingletonClass (Unit ⊕ Fin M) := ⟨fun _ => trivial⟩

/-- A polynomial-size packing eventually has enough logarithmic cardinality
to absorb a sufficiently small fourth-power frontier budget. -/
-- @node: causalScaledFrontier_eventually_klBudget
lemma causalScaledFrontier_eventually_klBudget
    (q : ℕ) (hq : 1 ≤ q) (c gamma K : ℝ)
    (hc : 0 < c) (hgamma : 0 < gamma) (hK : 0 ≤ K)
    (hsmall : 128 * (q : ℝ) * K * gamma ^ 4 ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ,
      c * Real.rpow (gamma * frontierRate n) (-(1 : ℝ) / q) ≤ M →
      K * (n : ℝ) * (gamma * frontierRate n) ^ 4 ≤
        (1 / 4 : ℝ) * Real.log M := by
  have hlog_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog_pos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) :=
    hlog_atTop.eventually_gt_atTop 0
  have hloglog_bound : ∀ᶠ n : ℕ in atTop,
      Real.log (Real.log (n : ℝ)) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
    filter_upwards [hlog_atTop.eventually_ge_atTop 16, hlog_pos] with n hnlog hnlogpos
    have hnlog0 : 0 ≤ Real.log (n : ℝ) := le_trans (by norm_num) hnlog
    have hbase := Real.log_le_rpow_div hnlog0 (show (0 : ℝ) < 1 / 2 by norm_num)
    have hsqrt : Real.log (Real.log (n : ℝ)) ≤
        2 * Real.sqrt (Real.log (n : ℝ)) := by
      simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using hbase
    have hfour : 4 ≤ Real.sqrt (Real.log (n : ℝ)) := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
      apply Real.sqrt_le_sqrt
      norm_num
      exact hnlog
    nlinarith [Real.sq_sqrt hnlog0]
  let D : ℝ := -(Real.log c + (-(1 : ℝ) / q) * Real.log gamma)
  have hconst : ∀ᶠ n : ℕ in atTop,
      D ≤ (1 / (32 * (q : ℝ))) * Real.log (n : ℝ) := by
    have hcoef : 0 < (1 / (32 * (q : ℝ)) : ℝ) := by positivity
    exact (hlog_atTop.const_mul_atTop hcoef).eventually_ge_atTop D
  filter_upwards [eventually_ge_atTop (2 : ℕ), hloglog_bound, hconst]
      with n hn hloglog hconstn
  intro M hM
  have hnreal : (0 : ℝ) < n := by positivity
  have hrate : 0 < frontierRate n := frontierRate_pos hn
  have hqreal : (0 : ℝ) < q := by positivity
  have hdelta : 0 < gamma * frontierRate n := mul_pos hgamma hrate
  have hlowpos : 0 < c * Real.rpow (gamma * frontierRate n)
      (-(1 : ℝ) / q) := mul_pos hc (Real.rpow_pos_of_pos hdelta _)
  have hlogM := Real.log_le_log hlowpos hM
  rw [show Real.log (c * Real.rpow (gamma * frontierRate n)
      (-(1 : ℝ) / q)) = Real.log c +
        Real.log (Real.rpow (gamma * frontierRate n) (-(1 : ℝ) / q)) by
      exact Real.log_mul hc.ne' (ne_of_gt (Real.rpow_pos_of_pos hdelta _)),
    show Real.log (Real.rpow (gamma * frontierRate n) (-(1 : ℝ) / q)) =
        (-(1 : ℝ) / q) * Real.log (gamma * frontierRate n) by
          exact Real.log_rpow hdelta _,
    Real.log_mul hgamma.ne' hrate.ne'] at hlogM
  have hlograte : Real.log (frontierRate n) =
      (1 / 4 : ℝ) * (Real.log (Real.log n) - Real.log n) := by
    unfold frontierRate
    have hn1r : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn1r
    rw [show Real.log (Real.rpow (Real.log n / n) (1 / 4 : ℝ)) =
        (1 / 4 : ℝ) * Real.log (Real.log n / n) by
          exact Real.log_rpow (div_pos hlogn hnreal) _,
      Real.log_div hlogn.ne' hnreal.ne']
  rw [hlograte] at hlogM
  have hlogMlower : (1 / (32 * (q : ℝ))) * Real.log n ≤ Real.log M := by
    dsimp [D] at hconstn
    have hterm : (1 / (8 * (q : ℝ))) * Real.log n ≤
        (-(1 : ℝ) / q) *
          ((1 / 4 : ℝ) * (Real.log (Real.log n) - Real.log n)) := by
      rw [show (1 / (8 * (q : ℝ))) * Real.log n =
          ((1 / 8 : ℝ) * Real.log n) / q by ring,
        show (-(1 : ℝ) / q) * ((1 / 4 : ℝ) *
            (Real.log (Real.log n) - Real.log n)) =
          (-(1 / 4 : ℝ) * (Real.log (Real.log n) - Real.log n)) / q by ring]
      exact (div_le_div_iff_of_pos_right hqreal).2 (by linarith)
    have hconst' : -(1 / (32 * (q : ℝ))) * Real.log n ≤
        Real.log c + (-(1 : ℝ) / q) * Real.log gamma := by linarith
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have hcoeff : (1 / (32 * (q : ℝ))) * Real.log n ≤
        -(1 / (32 * (q : ℝ))) * Real.log n +
          (1 / (8 * (q : ℝ))) * Real.log n := by
      field_simp [ne_of_gt hqreal]
      linarith
    calc
      (1 / (32 * (q : ℝ))) * Real.log n ≤
          -(1 / (32 * (q : ℝ))) * Real.log n +
            (1 / (8 * (q : ℝ))) * Real.log n := hcoeff
      _ ≤ Real.log c + (-(1 : ℝ) / q) * Real.log gamma +
          (-(1 : ℝ) / q) * ((1 / 4 : ℝ) *
            (Real.log (Real.log n) - Real.log n)) := add_le_add hconst' hterm
      _ ≤ Real.log M := by simpa [mul_add, add_assoc] using hlogM
  have hcoef : K * gamma ^ 4 ≤ 1 / (128 * (q : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 128 * (q : ℝ))).2
    nlinarith
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  rw [mul_pow]
  calc
    K * (n : ℝ) * (gamma ^ 4 * frontierRate n ^ 4) =
        (K * gamma ^ 4) * Real.log n := by
          rw [← frontierRate_fourth_power n hn]
          ring
    _ ≤ (1 / (128 * (q : ℝ))) * Real.log n :=
      mul_le_mul_of_nonneg_right hcoef hlog0
    _ = (1 / 4 : ℝ) * ((1 / (32 * (q : ℝ))) * Real.log n) := by ring
    _ ≤ (1 / 4 : ℝ) * Real.log M :=
      mul_le_mul_of_nonneg_left hlogMlower (by norm_num)

/-- Value of a causal rule on the retained prefix of a global marked sample. -/
-- @node: globalCausalPackingPoissonValue
noncomputable def globalCausalPackingPoissonValue {n : ℕ}
    (T : A1A2PIRule n) (P0 : A1A2Law) (x : Score)
    (s : FiniteSample (CausalObservation × ℝ)) : ℝ :=
  if n ≤ s.count then T.map (knownGeometry P0) x
    (canonicalPrefixObservations (0, 0) n
      (finiteSampleMap (causalPackingMarkedStatistic P0 x) s)) else 0

-- @node: globalCausalPackingPoissonValue_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma globalCausalPackingPoissonValue_measurable {n : ℕ}
    (T : A1A2PIRule n) (P0 : A1A2Law) (x : Score) :
    Measurable (globalCausalPackingPoissonValue T P0 x) := by
  apply Measurable.ite
  · exact measurable_finiteSample_count measurableSet_Ici
  · exact (T.section_measurable (knownGeometry P0) x).comp
      ((measurable_canonicalPrefixObservations (0, 0) n).comp
        (measurable_finiteSampleMap _
          (causalPackingMarkedStatistic_measurable P0 x)))
  · exact measurable_const

/-- Maximum target error on a global causal marked configuration. -/
-- @node: globalCausalPackingPoissonLoss
noncomputable def globalCausalPackingPoissonLoss {M n : ℕ}
    (T : A1A2PIRule n) (P0 : A1A2Law) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool)
    (s : FiniteSample (CausalObservation × ℝ)) : ℝ≥0∞ :=
  ⨆ j, ENNReal.ofReal
    |globalCausalPackingPoissonValue T P0 (centers j) s - values j (omega j)|

-- @node: globalCausalPackingPoissonLoss_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma globalCausalPackingPoissonLoss_measurable {M n : ℕ}
    (T : A1A2PIRule n) (P0 : A1A2Law) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool) :
    Measurable (globalCausalPackingPoissonLoss T P0 centers values omega) := by
  unfold globalCausalPackingPoissonLoss
  apply Measurable.iSup
  intro j
  exact Measurable.ennreal_ofReal
    (((globalCausalPackingPoissonValue_measurable T P0 (centers j)).sub_const _).abs)

/-- The blockwise loss used by the direct-product experiment. -/
-- @node: blockCausalPackingPoissonLoss
noncomputable def blockCausalPackingPoissonLoss {M n : ℕ}
    (T : A1A2PIRule n) (P0 : A1A2Law) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool)
    (data : (Unit → FiniteSample (CausalObservation × ℝ)) ×
      (Fin M → FiniteSample (CausalObservation × ℝ))) : ℝ≥0∞ :=
  ⨆ j, ENNReal.ofReal
    |causalPackingPoissonValue T P0 centers j
        (compressCausalPackingCell P0 centers j (data.2 j)) data.2 data.1 -
      values j (omega j)|

-- @node: blockCausalPackingPoissonLoss_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma blockCausalPackingPoissonLoss_measurable {M n : ℕ}
    (T : A1A2PIRule n) (P0 : A1A2Law) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool) :
    Measurable (blockCausalPackingPoissonLoss T P0 centers values omega) := by
  unfold blockCausalPackingPoissonLoss
  apply Measurable.iSup
  intro j
  apply Measurable.ennreal_ofReal
  apply Measurable.abs
  apply Measurable.sub_const
  have hm := (causalPackingPoissonValue_measurable T P0 centers j).comp
    (((compressCausalPackingCell_measurable P0 centers j).comp
      ((measurable_pi_apply j).comp measurable_snd)).prodMk
        (measurable_snd.prodMk measurable_fst))
  exact hm

/-- Reassembling the local signed block and the other raw blocks equals
mapping the synthesized global configuration. -/
-- @node: assembleCausalPackingBlocks_eq_globalMap
lemma assembleCausalPackingBlocks_eq_globalMap {M : ℕ}
    (P0 : A1A2Law) (centers : Fin M → Score) (j : Fin M)
    (cells : Fin M → FiniteSample (CausalObservation × ℝ))
    (common : Unit → FiniteSample (CausalObservation × ℝ)) :
    assembleCausalPackingBlocks P0 centers j
        (compressCausalPackingCell P0 centers j (cells j)) cells common =
      finiteSampleMap (causalPackingMarkedStatistic P0 (centers j))
        (synthesizeCausalPackingConfiguration (common, cells)) := by
  unfold assembleCausalPackingBlocks compressCausalPackingCell
    synthesizeCausalPackingConfiguration superposeByMarks
  rw [show finiteSampleMap (causalPackingMarkedStatistic P0 (centers j))
      (orderByMarks (superpose ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Unit ⊕ Fin M => FiniteSample (CausalObservation × ℝ))).symm
          (common, cells)))) =
      orderByMarks (finiteSampleMap (causalPackingMarkedStatistic P0 (centers j))
        (superpose ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Unit ⊕ Fin M => FiniteSample (CausalObservation × ℝ))).symm
            (common, cells)))) by rfl]
  congr 1
  change superpose _ = finiteSampleMap _ (superpose _)
  rw [show finiteSampleMap (causalPackingMarkedStatistic P0 (centers j))
      (superpose ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Unit ⊕ Fin M => FiniteSample (CausalObservation × ℝ))).symm
          (common, cells))) = superpose (fun k => finiteSampleMap
      (causalPackingMarkedStatistic P0 (centers j))
      (((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Unit ⊕ Fin M => FiniteSample (CausalObservation × ℝ))).symm
          (common, cells)) k)) by rfl]
  congr 1
  funext k
  cases k with
  | inl u => rfl
  | inr k =>
      change (if k = j then finiteSampleMap _ (cells j)
        else finiteSampleMap _ (cells k)) = finiteSampleMap _ (cells k)
      by_cases h : k = j <;> simp [h]

-- @node: blockCausalPackingPoissonLoss_eq_global
/-- The two stated constructions agree under the theorem's assumptions. -/
lemma blockCausalPackingPoissonLoss_eq_global {M n : ℕ}
    (T : A1A2PIRule n) (P0 : A1A2Law) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool)
    (data : (Unit → FiniteSample (CausalObservation × ℝ)) ×
      (Fin M → FiniteSample (CausalObservation × ℝ))) :
    blockCausalPackingPoissonLoss T P0 centers values omega data =
      globalCausalPackingPoissonLoss T P0 centers values omega
        (synthesizeCausalPackingConfiguration data) := by
  rcases data with ⟨common, cells⟩
  unfold blockCausalPackingPoissonLoss globalCausalPackingPoissonLoss
  congr 1
  funext j
  congr 2
  unfold causalPackingPoissonValue globalCausalPackingPoissonValue
  rw [assembleCausalPackingBlocks_eq_globalMap]
  rfl

/-- The causal cell experiment inherits the finite direct-product testing
lower bound from its compressed one-cell KL budgets. -/
-- @node: causalPackingCoordinatewiseError_lower_bound
lemma causalPackingCoordinatewiseError_lower_bound {M n : ℕ}
    (hM : 1 ≤ M) (T : A1A2PIRule n) (P0 : A1A2Law)
    (centers : Fin M → Score) (values : Fin M → Bool → ℝ)
    (w rho kappa : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (causalHardCell (centers i) w) (causalHardCell (centers j) w))
    (laws : (Fin M → Bool) → A1A2Law)
    (Q0 : Fin M → Bool → Measure (ℝ × ℝ))
    (hprob : ∀ j b, IsProbabilityMeasure (Q0 j b))
    (hrho : 0 < rho)
    (hmass : ∀ omega j,
      (laws omega).law {z | causalScore z ∈ causalHardCell (centers j) w} =
        ENNReal.ofReal rho)
    (hmap : ∀ omega j, Measure.map (signedObservationAt (laws omega) (centers j))
      ((laws omega).law.restrict
        {z | causalScore z ∈ causalHardCell (centers j) w}) =
      ENNReal.ofReal rho • Q0 j (omega j))
    (hgeom : ∀ omega, (laws omega).support = P0.support ∧
      (laws omega).A1 = P0.A1 ∧ (laws omega).A0 = P0.A0 ∧
      (laws omega).boundary = P0.boundary)
    (hkappa : kappa < 1)
    (hkl : ∀ j, InformationTheory.klDiv (Q0 j false) (Q0 j true) *
        ENNReal.ofReal (2 * n * rho) ≤ ENNReal.ofReal (kappa * Real.log M)) :
    ENNReal.ofReal ((1 / 2 : ℝ) *
        (1 - Real.exp (-((M : ℝ) ^ (1 - kappa)) / 2))) ≤
      coordinatewiseErrorProbability
        (fun j b => causalPackingCellExperiment
          (causalPackingFinitePartition centers w hdis) laws (2 * n) j b)
        (causalPackingCommonExperiment
          (causalPackingFinitePartition centers w hdis) laws (2 * n))
        (fun j => compressCausalPackingCell P0 centers j)
        (causalPackingPoissonDecoder T P0 centers values) := by
  letI : StandardBorelSpace (FiniteSample (CausalObservation × ℝ)) :=
    finiteSample_standardBorelSpace
  letI : StandardBorelSpace (FiniteSample ((ℝ × ℝ) × ℝ)) :=
    finiteSample_standardBorelSpace
  let p := causalPackingFinitePartition centers w hdis
  let Q : ∀ j : Fin M, Bool → Measure (FiniteSample (CausalObservation × ℝ)) :=
    fun j b => causalPackingCellExperiment p laws (2 * n) j b
  let R : Measure (Unit → FiniteSample (CausalObservation × ℝ)) :=
    causalPackingCommonExperiment p laws (2 * n)
  let compress : ∀ j : Fin M,
      FiniteSample (CausalObservation × ℝ) → FiniteSample ((ℝ × ℝ) × ℝ) :=
    fun j => compressCausalPackingCell P0 centers j
  let decoder := causalPackingPoissonDecoder T P0 centers values
  have hcompress : ∀ j, Measurable (compress j) :=
    fun j => compressCausalPackingCell_measurable P0 centers j
  have hdecoder : ∀ j, Measurable
      (fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
          (Fin M → FiniteSample (CausalObservation × ℝ)) ×
          (Unit → FiniteSample (CausalObservation × ℝ)) =>
        decoder j z.1 z.2.1 z.2.2) :=
    fun j => causalPackingPoissonDecoder_measurable T P0 centers values j
  have hlocal : ∀ j s z z' a,
      (∀ k, k ≠ j → z k = z' k) →
      decoder j s z a = decoder j s z' a := by
    intro j s z z' a hz
    exact causalPackingPoissonDecoder_local T P0 centers values j s z z' a hz
  have hdp := (coordinatewise_overlap_direct_product hM Q R compress
    hcompress decoder hdecoder hlocal).2 kappa hkappa
  have hcoord : ∀ j, InformationTheory.klDiv
      (compressedCoordinateLaw (compress j) (Q j false))
      (compressedCoordinateLaw (compress j) (Q j true)) ≤
        ENNReal.ofReal (kappa * Real.log M) := by
    intro j
    let t : ℝ≥0 := (2 * n) * ENNReal.toNNReal (ENNReal.ofReal rho)
    letI : IsProbabilityMeasure (Q0 j false) := hprob j false
    letI : IsProbabilityMeasure (Q0 j true) := hprob j true
    have hcomp (b : Bool) : compress j = compressCausalPackingCell
        (laws (causalPackingSingleBit j b)) centers j := by
      unfold compress compressCausalPackingCell causalPackingMarkedStatistic
      funext s
      cases s with
      | mk count points =>
          change (⟨count, fun i =>
              (signedObservationAt P0 (centers j) (points i).1, (points i).2)⟩ :
              Σ k, Fin k → (ℝ × ℝ) × ℝ) =
            ⟨count, fun i =>
              (signedObservationAt (laws (causalPackingSingleBit j b))
                (centers j) (points i).1, (points i).2)⟩
          congr
          funext i
          exact congrArg (fun y => (y, (points i).2))
            (congrFun (signedObservationAt_eq_of_hard_geometry_eq P0
              (laws (causalPackingSingleBit j b))
              ⟨(hgeom _).1.symm, (hgeom _).2.1.symm,
                (hgeom _).2.2.1.symm, (hgeom _).2.2.2.symm⟩ (centers j))
              (points i).1)
    rw [show compressedCoordinateLaw (compress j) (Q j false) =
        canonicalMarkedPoissonSampleLaw (Q0 j false) packingMarkLaw t by
          rw [hcomp false]
          exact compressedCausalPackingCellExperiment_eq centers w rho hdis laws
            Q0 hprob hrho hmass hmap (2 * n) j false,
      show compressedCoordinateLaw (compress j) (Q j true) =
        canonicalMarkedPoissonSampleLaw (Q0 j true) packingMarkLaw t by
          rw [hcomp true]
          exact compressedCausalPackingCellExperiment_eq centers w rho hdis laws
            Q0 hprob hrho hmass hmap (2 * n) j true]
    unfold canonicalMarkedPoissonSampleLaw
    calc
      InformationTheory.klDiv
          (Measure.map orderByMarks
            (finiteMarkedPoissonSampleLaw (Q0 j false) packingMarkLaw t))
          (Measure.map orderByMarks
            (finiteMarkedPoissonSampleLaw (Q0 j true) packingMarkLaw t)) ≤
          InformationTheory.klDiv
            (finiteMarkedPoissonSampleLaw (Q0 j false) packingMarkLaw t)
            (finiteMarkedPoissonSampleLaw (Q0 j true) packingMarkLaw t) :=
        compressedCoordinateLaw_klDiv_le orderByMarks measurable_orderByMarks _ _
      _ = (t : ℝ≥0∞) * InformationTheory.klDiv (Q0 j false) (Q0 j true) := by
        rw [← finiteMeasureMarkedPoissonLaw_probability_eq (Q0 j false)
            (Q0 j false) packingMarkLaw t,
          ← finiteMeasureMarkedPoissonLaw_probability_eq (Q0 j true)
            (Q0 j false) packingMarkLaw t,
          klDiv_finiteMeasureMarkedPoissonLaw (Q0 j false) (Q0 j true)
            (Q0 j false) packingMarkLaw t (by simp)]
      _ = InformationTheory.klDiv (Q0 j false) (Q0 j true) *
            ENNReal.ofReal (2 * n * rho) := by
        rw [mul_comm]
        congr 1
        simp [t]
      _ ≤ _ := hkl j
  rw [coordinatewiseErrorProbability_eq_one_sub_success Q R compress hcompress
    decoder hdecoder]
  simpa [Q, R, compress, decoder, p] using hdp hcoord

/-- Averaging the direct-product error selects a causal vertex whose global
Poissonized maximum loss is large. -/
-- @node: exists_vertex_causalPoissonLoss_ge_coordinatewiseError
lemma exists_vertex_causalPoissonLoss_ge_coordinatewiseError {M n : ℕ}
    (T : A1A2PIRule n) (P0 : A1A2Law) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (w rho delta : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (causalHardCell (centers i) w) (causalHardCell (centers j) w))
    (laws : (Fin M → Bool) → A1A2Law) (hrho : 0 < rho)
    (hmass : ∀ omega j,
      (laws omega).law {z | causalScore z ∈ causalHardCell (centers j) w} =
        ENNReal.ofReal rho)
    (hlocal : ∀ omega omega' j, omega j = omega' j →
      (laws omega).law.restrict
          {z | causalScore z ∈ causalHardCell (centers j) w} =
        (laws omega').law.restrict
          {z | causalScore z ∈ causalHardCell (centers j) w})
    (hoff : ∀ omega omega', (laws omega).law.restrict
        {z | causalScore z ∉ ⋃ j, causalHardCell (centers j) w} =
      (laws omega').law.restrict
        {z | causalScore z ∉ ⋃ j, causalHardCell (centers j) w})
    (hvalues : ∀ omega j, (laws omega).tau (centers j) = values j (omega j))
    (hsep : ∀ j, delta ≤ |values j true - values j false|) :
    ∃ omega : Fin M → Bool,
      letI : IsProbabilityMeasure (laws omega).law := (laws omega).law_isProbability
      ENNReal.ofReal (delta / 2) *
          coordinatewiseErrorProbability
            (fun j b => causalPackingCellExperiment
              (causalPackingFinitePartition centers w hdis) laws (2 * n) j b)
            (causalPackingCommonExperiment
              (causalPackingFinitePartition centers w hdis) laws (2 * n))
            (fun j => compressCausalPackingCell P0 centers j)
            (causalPackingPoissonDecoder T P0 centers values) ≤
        ∫⁻ s, globalCausalPackingPoissonLoss T P0 centers values omega s
          ∂canonicalMarkedPoissonSampleLaw (laws omega).law packingMarkLaw (2 * n) := by
  classical
  letI lawProb (omega : Fin M → Bool) : IsProbabilityMeasure (laws omega).law :=
    (laws omega).law_isProbability
  let p := causalPackingFinitePartition centers w hdis
  let Q : ∀ j : Fin M, Bool → Measure (FiniteSample (CausalObservation × ℝ)) :=
    fun j b => causalPackingCellExperiment p laws (2 * n) j b
  let R : Measure (Unit → FiniteSample (CausalObservation × ℝ)) :=
    causalPackingCommonExperiment p laws (2 * n)
  let μ (omega : Fin M → Bool) := R.prod (Measure.pi fun j => Q j (omega j))
  let bad (omega : Fin M → Bool) :=
    {data : (Unit → FiniteSample (CausalObservation × ℝ)) ×
        (Fin M → FiniteSample (CausalObservation × ℝ)) |
      ∃ j, causalPackingPoissonDecoder T P0 centers values j
        (compressCausalPackingCell P0 centers j (data.2 j)) data.2 data.1 ≠ omega j}
  let risk (omega : Fin M → Bool) :=
    ∫⁻ data, blockCausalPackingPoissonLoss T P0 centers values omega data ∂μ omega
  have hrisk (omega : Fin M → Bool) :
      ENNReal.ofReal (delta / 2) * μ omega (bad omega) ≤ risk omega := by
    rw [← setLIntegral_const]
    calc
      (∫⁻ _ in bad omega, ENNReal.ofReal (delta / 2) ∂μ omega) ≤
          ∫⁻ data in bad omega,
            blockCausalPackingPoissonLoss T P0 centers values omega data ∂μ omega := by
        apply setLIntegral_mono
          (blockCausalPackingPoissonLoss_measurable T P0 centers values omega)
        intro data hdata
        obtain ⟨j, hj⟩ := hdata
        unfold blockCausalPackingPoissonLoss
        refine le_trans (ENNReal.ofReal_le_ofReal
          (midpointDecoder_wrong_bit_error (values j)
            (causalPackingPoissonValue T P0 centers j
              (compressCausalPackingCell P0 centers j (data.2 j)) data.2 data.1)
            delta (hsep j) (omega j) hj)) ?_
        exact le_iSup (fun k : Fin M => ENNReal.ofReal
          |causalPackingPoissonValue T P0 centers k
              (compressCausalPackingCell P0 centers k (data.2 k)) data.2 data.1 -
            values k (omega k)|) j
      _ ≤ risk omega := setLIntegral_le_lintegral _ _
  obtain ⟨omegaMax, -, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin M → Bool)) risk Finset.univ_nonempty
  refine ⟨omegaMax, ?_⟩
  have hsum : ENNReal.ofReal (delta / 2) *
        (∑ omega : Fin M → Bool, μ omega (bad omega)) ≤
      ((2 : ℝ≥0∞) ^ M) * risk omegaMax := by
    calc
      ENNReal.ofReal (delta / 2) *
          (∑ omega : Fin M → Bool, μ omega (bad omega)) =
          ∑ omega : Fin M → Bool,
            ENNReal.ofReal (delta / 2) * μ omega (bad omega) := by
              rw [Finset.mul_sum]
      _ ≤ ∑ omega : Fin M → Bool, risk omega :=
        Finset.sum_le_sum fun omega _ => hrisk omega
      _ ≤ ∑ _omega : Fin M → Bool, risk omegaMax :=
        Finset.sum_le_sum fun omega homega => hmax omega homega
      _ = ((2 : ℝ≥0∞) ^ M) * risk omegaMax := by simp [Fintype.card_fun]
  have hpow : (2 : ℝ≥0∞) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpowtop : (2 : ℝ≥0∞) ^ M ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have havg : ENNReal.ofReal (delta / 2) *
      ((∑ omega : Fin M → Bool, μ omega (bad omega)) /
        ((2 : ℝ≥0∞) ^ M)) ≤ risk omegaMax := by
    rw [← mul_div_assoc]
    apply (ENNReal.div_le_iff_le_mul (Or.inl hpow) (Or.inl hpowtop)).2
    simpa [mul_comm] using hsum
  have hsynth := causalPackingExperiment_synthesis_law centers w rho hdis laws
    hrho hmass hlocal hoff (2 * n) omegaMax
  have hriskEq : risk omegaMax =
      ∫⁻ s, globalCausalPackingPoissonLoss T P0 centers values omegaMax s
        ∂canonicalMarkedPoissonSampleLaw (laws omegaMax).law packingMarkLaw
          (2 * n) := by
    unfold risk μ R Q p
    rw [← hsynth]
    rw [lintegral_map'
      (globalCausalPackingPoissonLoss_measurable T P0 centers values omegaMax).aemeasurable
      synthesizeCausalPackingConfiguration_measurable.aemeasurable]
    apply lintegral_congr
    intro data
    exact blockCausalPackingPoissonLoss_eq_global T P0 centers values omegaMax data
  rw [← hriskEq]
  simpa [coordinatewiseErrorProbability, Q, R, μ, bad, p] using havg

/-- On the successful count event the causal global Poisson loss is the
finite packing loss of the retained sample. -/
-- @node: globalCausalPackingPoissonLoss_eq_finitePackingLoss
lemma globalCausalPackingPoissonLoss_eq_finitePackingLoss {M n : ℕ}
    (T : A1A2PIRule n) (rhoRule : A1A2RuleFun n) (P0 P : A1A2Law)
    (centers : Fin M → Score) (values : Fin M → Bool → ℝ)
    (omega : Fin M → Bool)
    (hgeometry : knownGeometry P0 = knownGeometry P)
    (hsection : ∀ w j, rhoRule w (knownGeometry P) (centers j) =
      T.map (knownGeometry P) (centers j) (signedDistanceData n P w (centers j)))
    (hvalues : ∀ j, P.tau (centers j) = values j (omega j))
    (s : FiniteSample (CausalObservation × ℝ)) (hs : n ≤ s.count) :
    globalCausalPackingPoissonLoss T P0 centers values omega s =
      causalFinitePackingLoss rhoRule P centers
        (canonicalPrefixObservations (0, 0) n s) := by
  unfold globalCausalPackingPoissonLoss causalFinitePackingLoss
  congr 1
  funext j
  congr 2
  rw [hvalues j, hsection]
  unfold globalCausalPackingPoissonValue
  rw [if_pos hs]
  have hstat : causalPackingMarkedStatistic P0 (centers j) =
      causalPackingMarkedStatistic P (centers j) := by
    funext z
    unfold causalPackingMarkedStatistic signedObservationAt observedOutcome treatment
    have hA1 := congrArg GeometryData.A1 hgeometry
    change P0.A1 = P.A1 at hA1
    rw [hA1, hgeometry]
  rw [hstat]
  rw [hgeometry]
  unfold signedDistanceData
  unfold canonicalPrefixObservations
  have hmap : n ≤ (finiteSampleMap
      (causalPackingMarkedStatistic P (centers j)) s).count := by simpa
  rw [dif_pos hmap, dif_pos hs]
  rfl

/-- Failed-count zero defaults are bounded by the target envelope. -/
-- @node: globalCausalPackingPoissonLoss_le_on_count_lt
lemma globalCausalPackingPoissonLoss_le_on_count_lt {M n : ℕ}
    (T : A1A2PIRule n) (P0 : A1A2Law) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool)
    (B : ℝ) (hB : ∀ j, |values j (omega j)| ≤ B)
    (s : FiniteSample (CausalObservation × ℝ)) (hs : s.count < n) :
    globalCausalPackingPoissonLoss T P0 centers values omega s ≤
      ENNReal.ofReal B := by
  unfold globalCausalPackingPoissonLoss
  apply iSup_le
  intro j
  apply ENNReal.ofReal_le_ofReal
  unfold globalCausalPackingPoissonValue
  rw [if_neg (Nat.not_le_of_lt hs)]
  simpa only [zero_sub, abs_neg] using hB j

/-- De-Poissonization for the causal finite packing maximum. -/
-- @node: globalCausalPackingPoissonRisk_le_fixedRisk_add_tail
lemma globalCausalPackingPoissonRisk_le_fixedRisk_add_tail {M n : ℕ}
    (T : A1A2PIRule n) (rhoRule : A1A2RuleFun n) (P0 P : A1A2Law)
    (centers : Fin M → Score) (values : Fin M → Bool → ℝ)
    (omega : Fin M → Bool)
    (hgeometry : knownGeometry P0 = knownGeometry P)
    (hsection : ∀ w j, rhoRule w (knownGeometry P) (centers j) =
      T.map (knownGeometry P) (centers j) (signedDistanceData n P w (centers j)))
    (hvalues : ∀ j, P.tau (centers j) = values j (omega j))
    (hfiniteMeas : Measurable (causalFinitePackingLoss rhoRule P centers))
    (B : ℝ) (hB : ∀ j, |values j (omega j)| ≤ B) :
    (letI : IsProbabilityMeasure P.law := P.law_isProbability
     ∫⁻ s, globalCausalPackingPoissonLoss T P0 centers values omega s
          ∂canonicalMarkedPoissonSampleLaw P.law packingMarkLaw (2 * n)) ≤
      (∫⁻ w, causalFinitePackingLoss rhoRule P centers w ∂causalSampleLaw P n) +
        ENNReal.ofReal B *
          ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  let μ := canonicalMarkedPoissonSampleLaw P.law packingMarkLaw (2 * n)
  let success : Set (FiniteSample (CausalObservation × ℝ)) :=
    FiniteSample.count ⁻¹' Ici n
  have hsuccess : MeasurableSet success :=
    measurable_finiteSample_count measurableSet_Ici
  have hsplit := lintegral_add_compl
    (globalCausalPackingPoissonLoss T P0 centers values omega) (μ := μ) hsuccess
  rw [← hsplit]
  apply add_le_add
  · have hmap := map_canonicalPrefixObservations_restrict_count_ge
      P.law packingMarkLaw (2 * n) (0, 0) n
    have heq : ∫⁻ s in success,
          globalCausalPackingPoissonLoss T P0 centers values omega s ∂μ =
        ∫⁻ s in success, causalFinitePackingLoss rhoRule P centers
          (canonicalPrefixObservations (0, 0) n s) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hsuccess] with s hs
      exact globalCausalPackingPoissonLoss_eq_finitePackingLoss T rhoRule P0 P
        centers values omega hgeometry hsection hvalues s hs
    rw [heq]
    change (∫⁻ s, causalFinitePackingLoss rhoRule P centers
        (canonicalPrefixObservations (0, 0) n s) ∂μ.restrict success) ≤ _
    rw [← lintegral_map' hfiniteMeas.aemeasurable
      (measurable_canonicalPrefixObservations (0, 0) n).aemeasurable]
    rw [hmap, lintegral_smul_measure]
    change (poissonMeasure (2 * n)) (Ici n) *
      (∫⁻ w, causalFinitePackingLoss rhoRule P centers w ∂causalSampleLaw P n) ≤ _
    exact mul_le_of_le_one_left (by positivity) prob_le_one
  · calc
      (∫⁻ s in successᶜ,
          globalCausalPackingPoissonLoss T P0 centers values omega s ∂μ) ≤
          ∫⁻ _s in successᶜ, ENNReal.ofReal B ∂μ := by
        apply setLIntegral_mono measurable_const
        intro s hs
        apply globalCausalPackingPoissonLoss_le_on_count_lt
          T P0 centers values omega B hB s
        simpa [success] using hs
      _ = ENNReal.ofReal B * μ successᶜ := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal B *
          ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) := by
        gcongr
        have hcount := canonicalMarkedPoissonSampleLaw_map_count
          P.law packingMarkLaw (2 * n)
        have hfail : μ successᶜ = (poissonMeasure (2 * n)) {k | k < n} := by
          rw [← hcount]
          rw [Measure.map_apply measurable_finiteSample_count (by measurability)]
          congr 1
          ext s
          simp [success]
        rw [hfail]
        exact poisson_two_n_lower_tail n

end CausalSmith.Stat.BddUniformLogPenalty
