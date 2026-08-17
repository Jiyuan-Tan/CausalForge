import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.FiniteMaxAssembly
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.DirectProduct

/-!
# Causal finite-maximum decoders

This module reconstructs each fixed-geometry signed-distance section from the
local compressed Poisson block and the remaining raw partition blocks.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Equip the causal decision index set with the discrete measurable structure. -/
local instance causalDecisionIndexMeasurableSpace (M : ℕ) :
    MeasurableSpace (Unit ⊕ Fin M) := ⊤

/-- Every singleton causal decision index is measurable. -/
local instance causalDecisionIndexMeasurableSingletonClass (M : ℕ) :
    MeasurableSingletonClass (Unit ⊕ Fin M) := ⟨fun _ => trivial⟩

/-- Equal assignment geometry makes the observed signed statistic identical. -/
-- @node: signedObservationAt_eq_of_hard_geometry_eq
lemma signedObservationAt_eq_of_hard_geometry_eq (P P' : A1A2Law)
    (h : P.support = P'.support ∧ P.A1 = P'.A1 ∧ P.A0 = P'.A0 ∧
      P.boundary = P'.boundary) (x : Score) :
    signedObservationAt P x = signedObservationAt P' x := by
  funext z
  simp only [signedObservationAt, observedOutcome, treatment, signedDistance,
    knownGeometry]
  simp [h.2.1, h.2.2.1]

-- @node: knownGeometry_eq_of_components_eq
/-- The two stated constructions agree under the theorem's assumptions. -/
lemma knownGeometry_eq_of_components_eq (P P' : A1A2Law)
    (h : P.support = P'.support ∧ P.A1 = P'.A1 ∧ P.A0 = P'.A0 ∧
      P.boundary = P'.boundary) : knownGeometry P = knownGeometry P' := by
  unfold knownGeometry
  rw [GeometryData.mk.injEq]
  exact ⟨h.1, h.2.2.1, h.2.1, h.2.2.2, rfl, rfl⟩

/-- The fixed-law signed-distance sample map is measurable. -/
-- @node: signedDistanceData_measurable
lemma signedDistanceData_measurable (n : ℕ) (P : A1A2Law) (x : Score) :
    Measurable (fun w : CausalSample n => signedDistanceData n P w x) := by
  apply measurable_pi_lambda
  intro i
  exact (signedObservationAt_measurable P x).comp
    (measurable_pi_apply i : Measurable (fun w : CausalSample n => w i))

/-- Mark a causal observation after replacing it by its observed outcome and
signed distance at one fixed-geometry center. -/
-- @node: causalPackingMarkedStatistic
noncomputable def causalPackingMarkedStatistic (P : A1A2Law) (x : Score) :
    CausalObservation × ℝ → (ℝ × ℝ) × ℝ :=
  fun z => (signedObservationAt P x z.1, z.2)

-- @node: causalPackingMarkedStatistic_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma causalPackingMarkedStatistic_measurable (P : A1A2Law) (x : Score) :
    Measurable (causalPackingMarkedStatistic P x) := by
  exact (signedObservationAt_measurable P x).comp measurable_fst |>.prodMk
    measurable_snd

/-- Compress one raw causal partition block to its signed observation. -/
-- @node: compressCausalPackingCell
noncomputable def compressCausalPackingCell {M : ℕ} (P0 : A1A2Law)
    (centers : Fin M → Score) (j : Fin M)
    (s : FiniteSample (CausalObservation × ℝ)) :
    FiniteSample ((ℝ × ℝ) × ℝ) :=
  finiteSampleMap (causalPackingMarkedStatistic P0 (centers j)) s

-- @node: compressCausalPackingCell_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma compressCausalPackingCell_measurable {M : ℕ} (P0 : A1A2Law)
    (centers : Fin M → Score) (j : Fin M) :
    Measurable (compressCausalPackingCell P0 centers j) :=
  measurable_finiteSampleMap _
    (causalPackingMarkedStatistic_measurable P0 (centers j))

/-- Reassemble the signed marked sample for decoder `j`. -/
-- @node: assembleCausalPackingBlocks
noncomputable def assembleCausalPackingBlocks {M : ℕ} (P0 : A1A2Law)
    (centers : Fin M → Score) (j : Fin M)
    (own : FiniteSample ((ℝ × ℝ) × ℝ))
    (cells : Fin M → FiniteSample (CausalObservation × ℝ))
    (common : Unit → FiniteSample (CausalObservation × ℝ)) :
    FiniteSample ((ℝ × ℝ) × ℝ) :=
  superposeByMarks (fun k : Unit ⊕ Fin M => match k with
    | .inl u => finiteSampleMap
        (causalPackingMarkedStatistic P0 (centers j)) (common u)
    | .inr k => if k = j then own else finiteSampleMap
        (causalPackingMarkedStatistic P0 (centers j)) (cells k))

-- @node: assembleCausalPackingBlocks_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma assembleCausalPackingBlocks_measurable {M : ℕ} (P0 : A1A2Law)
    (centers : Fin M → Score) (j : Fin M) : Measurable
    (fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
        (Fin M → FiniteSample (CausalObservation × ℝ)) ×
        (Unit → FiniteSample (CausalObservation × ℝ)) =>
      assembleCausalPackingBlocks P0 centers j z.1 z.2.1 z.2.2) := by
  apply measurable_superposeByMarks.comp
  apply measurable_pi_lambda
  intro k
  cases k with
  | inl u =>
      exact (measurable_finiteSampleMap _
        (causalPackingMarkedStatistic_measurable P0 _)).comp
          ((measurable_pi_apply u).comp measurable_snd.snd)
  | inr k =>
      by_cases h : k = j
      · simp only [assembleCausalPackingBlocks, h, if_pos]
        exact measurable_fst
      · simp only [assembleCausalPackingBlocks, h, if_neg]
        exact (measurable_finiteSampleMap _
          (causalPackingMarkedStatistic_measurable P0 _)).comp
            ((measurable_pi_apply k).comp measurable_snd.fst)

/-- The point estimate reconstructed from the independent causal blocks. -/
-- @node: causalPackingPoissonValue
noncomputable def causalPackingPoissonValue {n M : ℕ} (T : A1A2PIRule n)
    (P0 : A1A2Law) (centers : Fin M → Score) (j : Fin M)
    (own : FiniteSample ((ℝ × ℝ) × ℝ))
    (cells : Fin M → FiniteSample (CausalObservation × ℝ))
    (common : Unit → FiniteSample (CausalObservation × ℝ)) : ℝ :=
  let s := assembleCausalPackingBlocks P0 centers j own cells common
  if n ≤ s.count then T.map (knownGeometry P0) (centers j)
    (canonicalPrefixObservations (0, 0) n s) else 0

-- @node: causalPackingPoissonValue_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma causalPackingPoissonValue_measurable {n M : ℕ} (T : A1A2PIRule n)
    (P0 : A1A2Law) (centers : Fin M → Score) (j : Fin M) : Measurable
    (fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
        (Fin M → FiniteSample (CausalObservation × ℝ)) ×
        (Unit → FiniteSample (CausalObservation × ℝ)) =>
      causalPackingPoissonValue T P0 centers j z.1 z.2.1 z.2.2) := by
  let f := fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
      (Fin M → FiniteSample (CausalObservation × ℝ)) ×
      (Unit → FiniteSample (CausalObservation × ℝ)) =>
    assembleCausalPackingBlocks P0 centers j z.1 z.2.1 z.2.2
  have hf : Measurable f := assembleCausalPackingBlocks_measurable P0 centers j
  apply Measurable.ite
  · exact (measurable_finiteSample_count measurableSet_Ici).preimage hf
  · exact (T.section_measurable (knownGeometry P0) (centers j)).comp
      ((measurable_canonicalPrefixObservations (0, 0) n).comp hf)
  · exact measurable_const

/-- The midpoint decoder attached to the fixed measurable section. -/
-- @node: causalPackingPoissonDecoder
noncomputable def causalPackingPoissonDecoder {n M : ℕ} (T : A1A2PIRule n)
    (P0 : A1A2Law) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (j : Fin M)
    (own : FiniteSample ((ℝ × ℝ) × ℝ))
    (cells : Fin M → FiniteSample (CausalObservation × ℝ))
    (common : Unit → FiniteSample (CausalObservation × ℝ)) : Bool :=
  let t := causalPackingPoissonValue T P0 centers j own cells common
  decide (|t - values j true| ≤ |t - values j false|)

-- @node: causalPackingPoissonDecoder_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma causalPackingPoissonDecoder_measurable {n M : ℕ} (T : A1A2PIRule n)
    (P0 : A1A2Law) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (j : Fin M) : Measurable
    (fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
        (Fin M → FiniteSample (CausalObservation × ℝ)) ×
        (Unit → FiniteSample (CausalObservation × ℝ)) =>
      causalPackingPoissonDecoder T P0 centers values j z.1 z.2.1 z.2.2) := by
  let t := fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
      (Fin M → FiniteSample (CausalObservation × ℝ)) ×
      (Unit → FiniteSample (CausalObservation × ℝ)) =>
    causalPackingPoissonValue T P0 centers j z.1 z.2.1 z.2.2
  have ht : Measurable t := causalPackingPoissonValue_measurable T P0 centers j
  apply measurable_to_bool
  change MeasurableSet {z | decide
    (|t z - values j true| ≤ |t z - values j false|) = true}
  have hm := measurableSet_le
    (ht.sub (measurable_const : Measurable (fun _ => values j true))).abs
    (ht.sub (measurable_const : Measurable (fun _ => values j false))).abs
  convert hm using 1 <;> ext z <;> simp

-- @node: causalPackingPoissonDecoder_local
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma causalPackingPoissonDecoder_local {n M : ℕ} (T : A1A2PIRule n)
    (P0 : A1A2Law) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (j : Fin M)
    (own : FiniteSample ((ℝ × ℝ) × ℝ))
    (cells cells' : Fin M → FiniteSample (CausalObservation × ℝ))
    (common : Unit → FiniteSample (CausalObservation × ℝ))
    (h : ∀ k, k ≠ j → cells k = cells' k) :
    causalPackingPoissonDecoder T P0 centers values j own cells common =
      causalPackingPoissonDecoder T P0 centers values j own cells' common := by
  have hblocks : (fun k : Unit ⊕ Fin M => match k with
      | .inl u => finiteSampleMap
          (causalPackingMarkedStatistic P0 (centers j)) (common u)
      | .inr k => if k = j then own else finiteSampleMap
          (causalPackingMarkedStatistic P0 (centers j)) (cells k)) =
    (fun k : Unit ⊕ Fin M => match k with
      | .inl u => finiteSampleMap
          (causalPackingMarkedStatistic P0 (centers j)) (common u)
      | .inr k => if k = j then own else finiteSampleMap
          (causalPackingMarkedStatistic P0 (centers j)) (cells' k)) := by
    funext k
    cases k with
    | inl u => rfl
    | inr k => by_cases hkj : k = j <;> simp [hkj, h k]
  unfold causalPackingPoissonDecoder causalPackingPoissonValue
    assembleCausalPackingBlocks
  rw [hblocks]

/-- The measurable finite maximum at the selected causal packing centers. -/
-- @node: causalFinitePackingLoss
noncomputable def causalFinitePackingLoss {n M : ℕ} (rho : A1A2RuleFun n)
    (P : A1A2Law) (centers : Fin M → Score) (w : CausalSample n) : ℝ≥0∞ :=
  ⨆ j, ENNReal.ofReal
    |rho w (knownGeometry P) (centers j) - P.tau (centers j)|

-- @node: causalFinitePackingLoss_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma causalFinitePackingLoss_measurable {n M p : ℕ} {ν L : ℝ}
    (rho : A1A2RuleFun n) (hrho : rho ∈ A1A2PointIndexedDecisionClass n p ν L)
    (P : A1A2Law) (hP : A1A2Class p ν L P)
    (centers : Fin M → Score) (hcenters : ∀ j, centers j ∈ P.boundary) :
    Measurable (causalFinitePackingLoss rho P centers) := by
  obtain ⟨T, hT⟩ := hrho
  unfold causalFinitePackingLoss
  apply Measurable.iSup
  intro j
  apply Measurable.ennreal_ofReal
  apply Measurable.abs
  apply Measurable.sub_const
  rw [show (fun w : CausalSample n =>
      rho w (knownGeometry P) (centers j)) = fun w =>
      T.map (knownGeometry P) (centers j) (signedDistanceData n P w (centers j)) by
    funext w
    exact hT P hP w (centers j) (hcenters j)]
  exact (T.section_measurable (knownGeometry P) (centers j)).comp
    (signedDistanceData_measurable n P (centers j))

/-- Compressing a canonical causal cell block gives the marked-Poisson
experiment generated by the normalized signed-observation cell law. -/
-- @node: compressedCausalPackingCellExperiment_eq
lemma compressedCausalPackingCellExperiment_eq {M : ℕ}
    (centers : Fin M → Score) (w rho : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (causalHardCell (centers i) w) (causalHardCell (centers j) w))
    (laws : (Fin M → Bool) → A1A2Law)
    (Q : Fin M → Bool → Measure (ℝ × ℝ))
    (hprob : ∀ j b, IsProbabilityMeasure (Q j b))
    (hrho : 0 < rho)
    (hmass : ∀ omega j,
      (laws omega).law {z | causalScore z ∈ causalHardCell (centers j) w} =
        ENNReal.ofReal rho)
    (hmap : ∀ omega j, Measure.map (signedObservationAt (laws omega) (centers j))
      ((laws omega).law.restrict
        {z | causalScore z ∈ causalHardCell (centers j) w}) =
      ENNReal.ofReal rho • Q j (omega j))
    (lam : ℝ≥0) (j : Fin M) (b : Bool) :
    compressedCoordinateLaw (compressCausalPackingCell
        (laws (causalPackingSingleBit j b)) centers j)
      (causalPackingCellExperiment
        (causalPackingFinitePartition centers w hdis) laws lam j b) =
      canonicalMarkedPoissonSampleLaw (Q j b) packingMarkLaw
        (lam * ENNReal.toNNReal (ENNReal.ofReal rho)) := by
  let omega := causalPackingSingleBit j b
  let P := laws omega
  let p := causalPackingFinitePartition centers w hdis
  let f := signedObservationAt P (centers j)
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  letI : IsProbabilityMeasure (Q j b) := hprob j b
  have hcell : P.law (p.cellSet (.inr j)) = ENNReal.ofReal rho := by
    rw [show p = causalPackingFinitePartition centers w hdis by rfl,
      causalPackingFinitePartition_cell_measure_eq]
    exact hmass omega j
  have hpos : P.law (p.cellSet (.inr j)) ≠ 0 := by
    rw [hcell]
    exact (ENNReal.ofReal_pos.mpr hrho).ne'
  have hm := hmap omega j
  have hm' : Measure.map f (P.law.restrict (p.cellSet (.inr j))) =
      ENNReal.ofReal rho • Q j b := by
    simpa [f, P, omega, p, causalPackingFinitePartition_cellSet,
      causalPackingPartitionSet, causalPackingSingleBit] using hm
  have hnorm : Measure.map f (p.cellObservationLaw P.law (.inr j)) = Q j b := by
    unfold FiniteMeasurablePartition.cellObservationLaw
    rw [dif_neg hpos, Measure.map_smul, hm', hcell]
    rw [← smul_assoc]
    change ((ENNReal.ofReal rho)⁻¹ * ENNReal.ofReal rho) • Q j b = Q j b
    rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hrho).ne'
      ENNReal.ofReal_ne_top, one_smul]
  unfold compressedCoordinateLaw compressCausalPackingCell
    causalPackingCellExperiment canonicalMarkedPoissonSampleLaw
  rw [Measure.map_map
      (measurable_finiteSampleMap _
        (causalPackingMarkedStatistic_measurable P (centers j)))
      measurable_orderByMarks]
  have hcomm : finiteSampleMap (causalPackingMarkedStatistic P (centers j)) ∘
      orderByMarks = orderByMarks ∘ finiteSampleMap
        (fun z : CausalObservation × ℝ => (f z.1, z.2)) := by
    funext s
    exact finiteSampleMap_orderByMarks f s
  have hg : Measurable (fun z : CausalObservation × ℝ => (f z.1, z.2)) :=
    ((signedObservationAt_measurable P (centers j)).comp measurable_fst).prodMk
      measurable_snd
  rw [hcomm]
  conv_lhs =>
    rw [← Measure.map_map measurable_orderByMarks
      (measurable_finiteSampleMap _ hg)]
  rw [map_finiteMarkedPoissonSampleLaw_finiteSampleMap
    (p.cellObservationLaw P.law (.inr j)) packingMarkLaw f
      (signedObservationAt_measurable P (centers j))
    (lam * p.cellMass P.law (.inr j))]
  unfold FiniteMeasurablePartition.cellMass
  rw [hcell]
  congr 3

end CausalSmith.Stat.BddUniformLogPenalty
