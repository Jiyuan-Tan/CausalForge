import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularPackingTheorem
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.DirectProduct
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.Poissonization

/-!
# Finite-packing Poisson experiment core

The angular packing, marked Poisson experiment, coordinatewise direct-product
bound, midpoint decoding, and de-Poissonization are assembled once here for an
arbitrary point-indexed rule.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Equip the packing index set with the discrete measurable structure. -/
local instance packingIndexMeasurableSpace (M : ℕ) :
    MeasurableSpace (Unit ⊕ Fin M) := ⊤

/-- The continuous uniform mark law on `(0,1]` used to put every finite
Poisson configuration into a canonical order. -/
-- @node: packingMarkLaw
noncomputable def packingMarkLaw : Measure ℝ := volume.restrict (Ioc 0 1)

/-- The stated experiment law has total mass one and therefore defines a probability distribution. -/
instance packingMarkLaw_isProbabilityMeasure :
    IsProbabilityMeasure packingMarkLaw := by
  rw [isProbabilityMeasure_iff]
  simp [packingMarkLaw]

/-- The packing-mark distribution assigns zero probability to every individual mark. -/
instance packingMarkLaw_noAtoms : NullSingletonClass packingMarkLaw := by
  unfold packingMarkLaw
  infer_instance

/-- The packing cells together with their common complement form the finite
partition used to split the marked Poisson experiment. -/
-- @node: packingPartitionSet
def packingPartitionSet {M : ℕ} (centers : Fin M → Score) (w : ℝ) :
    Unit ⊕ Fin M → Set Observation
  | .inr j => {o | o.2 ∈ packingCell centers w j}
  | .inl _ => {o | o.2 ∉ ⋃ j, packingCell centers w j}

/-- Every packing-partition cell is measurable. -/
-- @node: packingPartitionSet_measurable
lemma packingPartitionSet_measurable {M : ℕ} (centers : Fin M → Score) (w : ℝ)
    (j : Unit ⊕ Fin M) : MeasurableSet (packingPartitionSet centers w j) := by
  have hcell (k : Fin M) :
      MeasurableSet {o : Observation | o.2 ∈ packingCell centers w k} := by
    unfold packingCell
    exact (Metric.isClosed_closedBall.measurableSet.inter
      packingSquare_isCompact.isClosed.measurableSet).preimage measurable_snd
  cases j with
  | inl u =>
      rw [show packingPartitionSet centers w (.inl u) =
          (⋃ k : Fin M, {o : Observation | o.2 ∈ packingCell centers w k})ᶜ by
        ext o
        simp [packingPartitionSet]]
      exact (MeasurableSet.iUnion hcell).compl
  | inr j =>
      simpa [packingPartitionSet] using hcell j

/-- Distinct packing-partition cells are disjoint. -/
-- @node: packingPartitionSet_pairwiseDisjoint
lemma packingPartitionSet_pairwiseDisjoint {M : ℕ} (centers : Fin M → Score)
    (w : ℝ) (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j)) :
    Pairwise (fun i j : Unit ⊕ Fin M =>
      Disjoint (packingPartitionSet centers w i) (packingPartitionSet centers w j)) := by
  intro i j hij
  cases i with
  | inl u =>
      cases j with
      | inl v => exact (hij (by cases u; cases v; rfl)).elim
      | inr j =>
          apply Set.disjoint_left.2
          intro o ho hj
          exact ho (Set.mem_iUnion.2 ⟨j, hj⟩)
  | inr i =>
      cases j with
      | inl u =>
          apply Set.disjoint_left.2
          intro o hi ho
          exact ho (Set.mem_iUnion.2 ⟨i, hi⟩)
      | inr j =>
          apply Set.disjoint_left.2
          intro o hi hj
          exact Set.disjoint_left.1
            (hdis i j (fun h => hij (congrArg Sum.inr h))) hi hj

/-- The packing-partition cells cover the observation space. -/
-- @node: packingPartitionSet_iUnion
lemma packingPartitionSet_iUnion {M : ℕ} (centers : Fin M → Score) (w : ℝ) :
    ⋃ j : Unit ⊕ Fin M, packingPartitionSet centers w j = Set.univ := by
  ext o
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases h : o.2 ∈ ⋃ j, packingCell centers w j
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
    exact ⟨.inr j, hj⟩
  · exact ⟨.inl (), h⟩

/-- The classifier partition associated with the packing cells. -/
-- @node: packingFinitePartition
noncomputable def packingFinitePartition {M : ℕ} (centers : Fin M → Score) (w : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j)) :
    FiniteMeasurablePartition Observation (Unit ⊕ Fin M) :=
  FiniteMeasurablePartition.ofSets (packingPartitionSet centers w)
    (packingPartitionSet_measurable centers w)
    (packingPartitionSet_pairwiseDisjoint centers w hdis)
    (packingPartitionSet_iUnion centers w)

/-- The abstract classifier has exactly the intended packing cells. -/
-- @node: packingFinitePartition_cellSet
lemma packingFinitePartition_cellSet {M : ℕ} (centers : Fin M → Score) (w : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (j : Unit ⊕ Fin M) :
    (packingFinitePartition centers w hdis).cellSet j =
      packingPartitionSet centers w j := by
  exact FiniteMeasurablePartition.ofSets_cellSet _ _ _ _ j

/-- The mass of a packing cell can be read from the score marginal. -/
-- @node: packingFinitePartition_cell_measure_eq_map_snd
lemma packingFinitePartition_cell_measure_eq_map_snd {M : ℕ}
    (centers : Fin M → Score) (w : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (P : CtyLaw) (j : Fin M) :
    P.law ((packingFinitePartition centers w hdis).cellSet (.inr j)) =
      Measure.map Prod.snd P.law (packingCell centers w j) := by
  rw [packingFinitePartition_cellSet, packingPartitionSet]
  have hs : MeasurableSet (packingCell centers w j) := by
    unfold packingCell
    exact Metric.isClosed_closedBall.measurableSet.inter
      packingSquare_isCompact.isClosed.measurableSet
  change P.law (Prod.snd ⁻¹' packingCell centers w j) =
    Measure.map Prod.snd P.law (packingCell centers w j)
  exact (Measure.map_apply measurable_snd hs).symm

/-- Equal positive packing-cell mass and the angular locality certificate
identify the normalized within-cell observation laws. -/
-- @node: packingCellObservationLaw_eq_of_bit_eq
lemma packingCellObservationLaw_eq_of_bit_eq {M : ℕ}
    (centers : Fin M → Score) (w m : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (laws : (Fin M → Bool) → CtyLaw)
    (hm : 0 < m)
    (hmass : ∀ omega j,
      Measure.map Prod.snd (laws omega).law (packingCell centers w j) =
        ENNReal.ofReal m)
    (hlocal : ∀ omega omega' j, omega j = omega' j →
      (laws omega).law.restrict {o | o.2 ∈ packingCell centers w j} =
        (laws omega').law.restrict {o | o.2 ∈ packingCell centers w j})
    (omega omega' : Fin M → Bool) (j : Fin M) (hbit : omega j = omega' j) :
    (letI : IsProbabilityMeasure (laws omega).law := (laws omega).law_isProbability
     letI : IsProbabilityMeasure (laws omega').law := (laws omega').law_isProbability
     (packingFinitePartition centers w hdis).cellObservationLaw
      (laws omega).law (.inr j) =
      (packingFinitePartition centers w hdis).cellObservationLaw
        (laws omega').law (.inr j)) := by
  letI : IsProbabilityMeasure (laws omega).law := (laws omega).law_isProbability
  letI : IsProbabilityMeasure (laws omega').law := (laws omega').law_isProbability
  let p := packingFinitePartition centers w hdis
  have hω : (laws omega).law (p.cellSet (.inr j)) = ENNReal.ofReal m := by
    rw [show p = packingFinitePartition centers w hdis by rfl,
      packingFinitePartition_cell_measure_eq_map_snd]
    exact hmass omega j
  have hω' : (laws omega').law (p.cellSet (.inr j)) = ENNReal.ofReal m := by
    rw [show p = packingFinitePartition centers w hdis by rfl,
      packingFinitePartition_cell_measure_eq_map_snd]
    exact hmass omega' j
  apply cellObservationLaw_eq_of_restrict_eq p (laws omega).law
    (laws omega').law (.inr j)
  · rw [hω]
    exact (ENNReal.ofReal_pos.mpr hm).ne'
  · rw [hω, hω']
  · simpa [p, packingFinitePartition_cellSet, packingPartitionSet] using
      hlocal omega omega' j hbit

/-- The complete canonical marked-Poisson experiment in a packing cell is a
function only of that cell's Boolean coordinate. -/
-- @node: packingCanonicalCellLaw_eq_of_bit_eq
lemma packingCanonicalCellLaw_eq_of_bit_eq {M : ℕ}
    (centers : Fin M → Score) (w m : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (laws : (Fin M → Bool) → CtyLaw)
    (hm : 0 < m)
    (hmass : ∀ omega j,
      Measure.map Prod.snd (laws omega).law (packingCell centers w j) =
        ENNReal.ofReal m)
    (hlocal : ∀ omega omega' j, omega j = omega' j →
      (laws omega).law.restrict {o | o.2 ∈ packingCell centers w j} =
        (laws omega').law.restrict {o | o.2 ∈ packingCell centers w j})
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0)
    (omega omega' : Fin M → Bool) (j : Fin M) (hbit : omega j = omega' j) :
    (letI : IsProbabilityMeasure (laws omega).law := (laws omega).law_isProbability
     letI : IsProbabilityMeasure (laws omega').law := (laws omega').law_isProbability
     let p := packingFinitePartition centers w hdis
     canonicalMarkedPoissonSampleLaw
        (p.cellObservationLaw (laws omega).law (.inr j)) R
        (lam * p.cellMass (laws omega).law (.inr j)) =
      canonicalMarkedPoissonSampleLaw
        (p.cellObservationLaw (laws omega').law (.inr j)) R
        (lam * p.cellMass (laws omega').law (.inr j))) := by
  letI : IsProbabilityMeasure (laws omega).law := (laws omega).law_isProbability
  letI : IsProbabilityMeasure (laws omega').law := (laws omega').law_isProbability
  let p := packingFinitePartition centers w hdis
  have hobs := packingCellObservationLaw_eq_of_bit_eq centers w m hdis laws hm
    hmass hlocal omega omega' j hbit
  have hmeasure :
      (laws omega).law (p.cellSet (.inr j)) =
        (laws omega').law (p.cellSet (.inr j)) := by
    rw [show p = packingFinitePartition centers w hdis by rfl,
      packingFinitePartition_cell_measure_eq_map_snd,
      packingFinitePartition_cell_measure_eq_map_snd,
      hmass omega j, hmass omega' j]
  have hcellMass : p.cellMass (laws omega).law (.inr j) =
      p.cellMass (laws omega').law (.inr j) := by
    unfold FiniteMeasurablePartition.cellMass
    rw [hmeasure]
  change canonicalMarkedPoissonSampleLaw
      (p.cellObservationLaw (laws omega).law (.inr j)) R
      (lam * p.cellMass (laws omega).law (.inr j)) =
    canonicalMarkedPoissonSampleLaw
      (p.cellObservationLaw (laws omega').law (.inr j)) R
      (lam * p.cellMass (laws omega').law (.inr j))
  change p.cellObservationLaw (laws omega).law (.inr j) =
      p.cellObservationLaw (laws omega').law (.inr j) at hobs
  unfold canonicalMarkedPoissonSampleLaw
  simp only [hobs, hcellMass]

/-- On laws supported by the common packing square, the abstract complement
cell restriction is exactly the construction's common off-cell restriction. -/
-- @node: packingComplement_restrict_eq
lemma packingComplement_restrict_eq {M : ℕ}
    (centers : Fin M → Score) (w : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (laws : (Fin M → Bool) → CtyLaw)
    (hsupport : ∀ omega, (laws omega).support = packingSquare)
    (hoff : ∀ omega omega',
      (laws omega).law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j} =
        (laws omega').law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j})
    (omega omega' : Fin M → Bool) :
    (laws omega).law.restrict
        ((packingFinitePartition centers w hdis).cellSet (.inl ())) =
      (laws omega').law.restrict
        ((packingFinitePartition centers w hdis).cellSet (.inl ())) := by
  let C : Set Observation := {o | o.2 ∉ ⋃ j, packingCell centers w j}
  let C' : Set Observation :=
    {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j}
  have hsupp (eta : Fin M → Bool) :
      ∀ᵐ o ∂(laws eta).law, o.2 ∈ packingSquare := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    simpa [← hsupport eta, (laws eta).support_eq_marginal_support] using
      (Measure.map Prod.snd (laws eta).law).support_mem_ae
  have hC (eta : Fin M → Bool) : C =ᵐ[(laws eta).law] C' := by
    filter_upwards [hsupp eta] with o ho
    change (o.2 ∉ ⋃ j, packingCell centers w j) =
      (o.2 ∈ packingSquare ∧ o.2 ∉ ⋃ j, packingCell centers w j)
    simp [ho]
  rw [packingFinitePartition_cellSet, packingPartitionSet]
  exact ((laws omega).law.restrict_congr_set (hC omega)).trans
    ((hoff omega omega').trans
      ((laws omega').law.restrict_congr_set (hC omega')).symm)

/-- A zero-intensity canonical marked-Poisson law is independent of its
observation law. -/
-- @node: canonicalMarkedPoissonSampleLaw_zero
lemma canonicalMarkedPoissonSampleLaw_zero
    {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R] :
    canonicalMarkedPoissonSampleLaw P R 0 =
      canonicalMarkedPoissonSampleLaw Q R 0 := by
  have hpois : poissonMeasure 0 = Measure.dirac 0 := by
    ext s hs
    rw [poissonMeasure, Measure.sum_apply _ hs,
      tsum_eq_single 0 (fun n hn => by
        simp [Measure.smul_apply, zero_pow hn])]
    simp [Measure.smul_apply]
  have hfinite : finiteMarkedPoissonSampleLaw P R 0 =
      finiteMarkedPoissonSampleLaw Q R 0 := by
    let K (S : Measure (X × ℝ)) [IsProbabilityMeasure S] :
        Kernel ℕ (FiniteSample (X × ℝ)) :=
      { toFun := fun n => Measure.map (fixedSizeEmbed n)
          (Measure.pi fun _ : Fin n => S)
        measurable' := Measurable.of_discrete }
    letI Kmarkov (S : Measure (X × ℝ)) [IsProbabilityMeasure S] :
        IsMarkovKernel (K S) :=
      { isProbabilityMeasure := fun n => by
          dsimp [K]
          exact Measure.isProbabilityMeasure_map
            (measurable_fixedSizeEmbed n).aemeasurable }
    have hbind (S : Measure (X × ℝ)) [IsProbabilityMeasure S] :
        finitePoissonSampleLaw S 0 =
          (poissonMeasure 0).bind (K S) := by
      ext s hs
      rw [Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_countable']
      symm
      calc
        ∑' n : ℕ, (K S n) s * poissonMeasure 0 {n} =
            ∑' n : ℕ, ((finitePoissonSampleLaw S 0).restrict
              (FiniteSample.count ⁻¹' ({n} : Set ℕ))) s := by
          congr 1
          funext n
          rw [finitePoissonSampleLaw_restrict_count_eq, Measure.smul_apply]
          rw [smul_eq_mul]
          exact mul_comm ((K S n) s) (poissonMeasure 0 {n})
        _ = finitePoissonSampleLaw S 0 s := by
          rw [← Measure.sum_apply _ hs, ← Measure.restrict_iUnion]
          · rw [show (⋃ n : ℕ, FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
                Set.univ by
                ext x
                simp only [Set.mem_iUnion, Set.mem_preimage,
                  Set.mem_singleton_iff, Set.mem_univ, iff_true]
                exact ⟨x.count, rfl⟩,
              Measure.restrict_univ]
          · intro i j hij
            exact (Set.disjoint_singleton.mpr hij).preimage FiniteSample.count
          · intro n
            exact measurable_finiteSample_count (MeasurableSet.singleton n)
    unfold finiteMarkedPoissonSampleLaw
    rw [hbind, hbind, hpois]
    ext s hs
    rw [Measure.bind_apply hs (Kernel.aemeasurable _),
      Measure.bind_apply hs (Kernel.aemeasurable _)]
    simp only [lintegral_dirac' _ (Kernel.measurable_coe _ hs)]
    have heq : (Measure.pi fun _ : Fin 0 => P.prod R) =
        (Measure.pi fun _ : Fin 0 => Q.prod R) := by
      apply Measure.pi_eq
      intro u hu
      simp
    change (Measure.map (fixedSizeEmbed 0)
        (Measure.pi fun _ : Fin 0 => P.prod R)) s =
      (Measure.map (fixedSizeEmbed 0)
        (Measure.pi fun _ : Fin 0 => Q.prod R)) s
    rw [heq]
  unfold canonicalMarkedPoissonSampleLaw
  rw [hfinite]

/-- The canonical marked-Poisson complement experiment is common to all
vertices, including when the common complement has zero mass. -/
-- @node: packingCanonicalComplementLaw_eq
lemma packingCanonicalComplementLaw_eq {M : ℕ}
    (centers : Fin M → Score) (w : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (laws : (Fin M → Bool) → CtyLaw)
    (hsupport : ∀ omega, (laws omega).support = packingSquare)
    (hoff : ∀ omega omega',
      (laws omega).law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j} =
        (laws omega').law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j})
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0)
    (omega omega' : Fin M → Bool) :
    (letI : IsProbabilityMeasure (laws omega).law := (laws omega).law_isProbability
     letI : IsProbabilityMeasure (laws omega').law := (laws omega').law_isProbability
     let p := packingFinitePartition centers w hdis
     canonicalMarkedPoissonSampleLaw
        (p.cellObservationLaw (laws omega).law (.inl ())) R
        (lam * p.cellMass (laws omega).law (.inl ())) =
      canonicalMarkedPoissonSampleLaw
        (p.cellObservationLaw (laws omega').law (.inl ())) R
        (lam * p.cellMass (laws omega').law (.inl ()))) := by
  letI : IsProbabilityMeasure (laws omega).law := (laws omega).law_isProbability
  letI : IsProbabilityMeasure (laws omega').law := (laws omega').law_isProbability
  let p := packingFinitePartition centers w hdis
  have hrest := packingComplement_restrict_eq centers w hdis laws hsupport hoff
    omega omega'
  have hmass : (laws omega).law (p.cellSet (.inl ())) =
      (laws omega').law (p.cellSet (.inl ())) := by
    have := congrArg (fun μ : Measure Observation => μ Set.univ) hrest
    simpa [Measure.restrict_apply_univ] using this
  have hcellMass : p.cellMass (laws omega).law (.inl ()) =
      p.cellMass (laws omega').law (.inl ()) := by
    unfold FiniteMeasurablePartition.cellMass
    rw [hmass]
  change canonicalMarkedPoissonSampleLaw
      (p.cellObservationLaw (laws omega).law (.inl ())) R
      (lam * p.cellMass (laws omega).law (.inl ())) =
    canonicalMarkedPoissonSampleLaw
      (p.cellObservationLaw (laws omega').law (.inl ())) R
      (lam * p.cellMass (laws omega').law (.inl ()))
  by_cases hpos : (laws omega).law (p.cellSet (.inl ())) = 0
  · have hpos' : (laws omega').law (p.cellSet (.inl ())) = 0 := by
      rw [← hmass, hpos]
    have hzero : p.cellMass (laws omega).law (.inl ()) = 0 := by
      unfold FiniteMeasurablePartition.cellMass
      rw [hpos]
      simp
    have hzero' : p.cellMass (laws omega').law (.inl ()) = 0 := by
      unfold FiniteMeasurablePartition.cellMass
      rw [hpos']
      simp
    rw [hzero, hzero']
    simp only [mul_zero]
    exact canonicalMarkedPoissonSampleLaw_zero
      (p.cellObservationLaw (laws omega).law (.inl ()))
      (p.cellObservationLaw (laws omega').law (.inl ())) R
  · have hobs := cellObservationLaw_eq_of_restrict_eq p (laws omega).law
      (laws omega').law (.inl ()) hpos hmass hrest
    unfold canonicalMarkedPoissonSampleLaw
    simp only [hobs, hcellMass]

/-- Replace the score of a marked observation by its distance from one
packing center, retaining the outcome and the ordering mark. -/
-- @node: packingMarkedDistance
noncomputable def packingMarkedDistance (x : Score) : Observation × ℝ → (ℝ × ℝ) × ℝ :=
  fun z => ((z.1.1, dist z.1.2 x), z.2)

-- @node: packingMarkedDistance_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma packingMarkedDistance_measurable (x : Score) :
    Measurable (packingMarkedDistance x) := by
  unfold packingMarkedDistance
  fun_prop

/-- The distance-compressed marked configuration in one packing cell. -/
-- @node: compressPackingCell
noncomputable def compressPackingCell {M : ℕ}
    (centers : Fin M → Score) (j : Fin M)
    (s : FiniteSample (Observation × ℝ)) : FiniteSample ((ℝ × ℝ) × ℝ) :=
  finiteSampleMap (packingMarkedDistance (centers j)) s

-- @node: compressPackingCell_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma compressPackingCell_measurable {M : ℕ}
    (centers : Fin M → Score) (j : Fin M) :
    Measurable (compressPackingCell centers j) := by
  exact measurable_finiteSampleMap _ (packingMarkedDistance_measurable _)

/-- Reassemble, for decoder `j`, the marked distance configuration from its
compressed own cell, the raw off-cell blocks, and the common complement. -/
-- @node: assemblePackingDistanceBlocks
noncomputable def assemblePackingDistanceBlocks {M : ℕ}
    (centers : Fin M → Score) (j : Fin M)
    (own : FiniteSample ((ℝ × ℝ) × ℝ))
    (cells : Fin M → FiniteSample (Observation × ℝ))
    (common : Unit → FiniteSample (Observation × ℝ)) :
    FiniteSample ((ℝ × ℝ) × ℝ) :=
  superposeByMarks (fun k : Unit ⊕ Fin M => match k with
    | .inl u => finiteSampleMap (packingMarkedDistance (centers j)) (common u)
    | .inr k => if k = j then own
        else finiteSampleMap (packingMarkedDistance (centers j)) (cells k))

-- @node: assemblePackingDistanceBlocks_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma assemblePackingDistanceBlocks_measurable {M : ℕ}
    (centers : Fin M → Score) (j : Fin M) :
    Measurable (fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
        (Fin M → FiniteSample (Observation × ℝ)) ×
        (Unit → FiniteSample (Observation × ℝ)) =>
      assemblePackingDistanceBlocks centers j z.1 z.2.1 z.2.2) := by
  apply measurable_superposeByMarks.comp
  apply measurable_pi_lambda
  intro k
  cases k with
  | inl u =>
      exact (measurable_finiteSampleMap _ (packingMarkedDistance_measurable _)).comp
        ((measurable_pi_apply u).comp measurable_snd.snd)
  | inr k =>
      by_cases h : k = j
      · simp only [assemblePackingDistanceBlocks, h, if_pos]
        exact measurable_fst
      · simp only [assemblePackingDistanceBlocks, h, if_neg]
        exact (measurable_finiteSampleMap _ (packingMarkedDistance_measurable _)).comp
          ((measurable_pi_apply k).comp measurable_snd.fst)

/-- The Poissonized point estimate computed from the compressed own cell and
raw off-cell blocks, with zero fallback when fewer than `n` atoms arrive. -/
-- @node: packingPoissonValue
noncomputable def packingPoissonValue {n M : ℕ}
    (T : PIRule n) (centers : Fin M → Score) (j : Fin M)
    (own : FiniteSample ((ℝ × ℝ) × ℝ))
    (cells : Fin M → FiniteSample (Observation × ℝ))
    (common : Unit → FiniteSample (Observation × ℝ)) : ℝ :=
  let s := assemblePackingDistanceBlocks centers j own cells common
  if n ≤ s.count then
    T.map (centers j) (canonicalPrefixObservations (0, 0) n s)
  else 0

-- @node: packingPoissonValue_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma packingPoissonValue_measurable {n M : ℕ}
    (T : PIRule n) (centers : Fin M → Score) (j : Fin M) :
    Measurable (fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
        (Fin M → FiniteSample (Observation × ℝ)) ×
        (Unit → FiniteSample (Observation × ℝ)) =>
      packingPoissonValue T centers j z.1 z.2.1 z.2.2) := by
  let f := fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
        (Fin M → FiniteSample (Observation × ℝ)) ×
        (Unit → FiniteSample (Observation × ℝ)) =>
      assemblePackingDistanceBlocks centers j z.1 z.2.1 z.2.2
  have hf : Measurable f := assemblePackingDistanceBlocks_measurable centers j
  apply Measurable.ite
  · exact (measurable_finiteSample_count measurableSet_Ici).preimage hf
  · exact (T.section_measurable (centers j)).comp
      ((measurable_canonicalPrefixObservations (0, 0) n).comp hf)
  · exact measurable_const

/-- The midpoint decoder induced by a point-indexed Borel section, with zero
output on the failed Poisson-count event. -/
-- @node: packingPoissonDecoder
noncomputable def packingPoissonDecoder {n M : ℕ}
    (T : PIRule n) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (j : Fin M)
    (own : FiniteSample ((ℝ × ℝ) × ℝ))
    (cells : Fin M → FiniteSample (Observation × ℝ))
    (common : Unit → FiniteSample (Observation × ℝ)) : Bool :=
  let t := packingPoissonValue T centers j own cells common
  decide (|t - values j true| ≤ |t - values j false|)

-- @node: packingPoissonDecoder_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma packingPoissonDecoder_measurable {n M : ℕ}
    (T : PIRule n) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (j : Fin M) :
    Measurable (fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
        (Fin M → FiniteSample (Observation × ℝ)) ×
        (Unit → FiniteSample (Observation × ℝ)) =>
      packingPoissonDecoder T centers values j z.1 z.2.1 z.2.2) := by
  let t := fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
        (Fin M → FiniteSample (Observation × ℝ)) ×
        (Unit → FiniteSample (Observation × ℝ)) =>
      packingPoissonValue T centers j z.1 z.2.1 z.2.2
  have ht : Measurable t := packingPoissonValue_measurable T centers j
  apply measurable_to_bool
  change MeasurableSet {z | decide
    (|t z - values j true| ≤ |t z - values j false|) = true}
  have hm := measurableSet_le
    (ht.sub (measurable_const : Measurable (fun _ => values j true))).abs
    (ht.sub (measurable_const : Measurable (fun _ => values j false))).abs
  convert hm using 1 <;> ext z <;> simp

-- @node: packingPoissonDecoder_local
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma packingPoissonDecoder_local {n M : ℕ}
    (T : PIRule n) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (j : Fin M)
    (own : FiniteSample ((ℝ × ℝ) × ℝ))
    (cells cells' : Fin M → FiniteSample (Observation × ℝ))
    (common : Unit → FiniteSample (Observation × ℝ))
    (h : ∀ k, k ≠ j → cells k = cells' k) :
    packingPoissonDecoder T centers values j own cells common =
      packingPoissonDecoder T centers values j own cells' common := by
  have hblocks :
      (fun k : Unit ⊕ Fin M => match k with
        | .inl u => finiteSampleMap (packingMarkedDistance (centers j)) (common u)
        | .inr k => if k = j then own
            else finiteSampleMap (packingMarkedDistance (centers j)) (cells k)) =
      (fun k : Unit ⊕ Fin M => match k with
        | .inl u => finiteSampleMap (packingMarkedDistance (centers j)) (common u)
        | .inr k => if k = j then own
            else finiteSampleMap (packingMarkedDistance (centers j)) (cells' k)) := by
    funext k
    cases k with
    | inl u => rfl
    | inr k =>
        by_cases hkj : k = j
        · simp [hkj]
        · simp [hkj, h k hkj]
  unfold packingPoissonDecoder packingPoissonValue assemblePackingDistanceBlocks
  rw [hblocks]

/-- The measurable maximum of the losses at finitely many packing points. -/
noncomputable def finitePackingLoss {n M : ℕ}
    (rho : RuleFun n) (P : CtyLaw) (centers : Fin M → Score)
    (w : Sample n) : ℝ≥0∞ :=
  ⨆ j : Fin M, ENNReal.ofReal |rho w (centers j) - P.mu (centers j)|

/-- A point-indexed rule has a measurable finite packing loss whenever its
fixed sections are represented by the measurable maps in its certificate. -/
-- @node: finitePackingLoss_measurable_of_pointIndexed
lemma finitePackingLoss_measurable_of_pointIndexed {n M q : ℕ} {L : ℝ}
    (rho : RuleFun n) (hrho : rho ∈ PointIndexedDecisionClass n q L)
    (P : CtyLaw) (hP : CtyNonparametricClass q L P)
    (centers : Fin M → Score)
    (hcenters : ∀ j, centers j ∈ frontier P.support) :
    Measurable (finitePackingLoss rho P centers) := by
  obtain ⟨T, hT⟩ := hrho
  unfold finitePackingLoss
  apply Measurable.iSup
  intro j
  apply Measurable.ennreal_ofReal
  apply Measurable.abs
  apply Measurable.sub_const
  rw [show (fun w : Sample n => rho w (centers j)) =
      fun w => T.map (centers j) (distanceData n w (centers j)) by
    funext w
    exact hT P hP w (centers j) (hcenters j)]
  exact (T.section_measurable (centers j)).comp
    (measurable_distanceData n (centers j))

/-- If the midpoint decoder for two separated values chooses the wrong bit,
the corresponding estimation error is at least half their separation. -/
-- @node: midpointDecoder_error_ge_half_separation
lemma midpointDecoder_error_ge_half_separation
    (a b t delta : ℝ) (hsep : delta ≤ |b - a|) :
    (decide (|t - b| ≤ |t - a|) : Bool) ≠ true → delta / 2 ≤ |t - b| := by
  intro hwrong
  have hdecfalse : decide (|t - b| ≤ |t - a|) = false :=
    Bool.eq_false_of_not_eq_true hwrong
  have hnle : ¬ |t - b| ≤ |t - a| := of_decide_eq_false hdecfalse
  have hlt : |t - a| < |t - b| := by
    exact lt_of_not_ge hnle
  have htri : |b - a| ≤ |t - b| + |t - a| := by
    calc
      |b - a| = |(b - t) + (t - a)| := by ring_nf
      _ ≤ |b - t| + |t - a| := abs_add_le _ _
      _ = |t - b| + |t - a| := by rw [abs_sub_comm b t]
  linarith

/-- The nearest-midpoint decoder can be wrong only when the estimate is at
least half the endpoint separation away from the true endpoint. -/
-- @node: midpointDecoder_wrong_bit_error
lemma midpointDecoder_wrong_bit_error
    (a : Bool → ℝ) (t delta : ℝ) (hsep : delta ≤ |a true - a false|)
    (b : Bool)
    (hwrong : (decide (|t - a true| ≤ |t - a false|) : Bool) ≠ b) :
    delta / 2 ≤ |t - a b| := by
  cases b with
  | false =>
      have hdec : decide (|t - a true| ≤ |t - a false|) = true := by
        cases h : decide (|t - a true| ≤ |t - a false|)
        · exact (hwrong h).elim
        · rfl
      have hle : |t - a true| ≤ |t - a false| := of_decide_eq_true hdec
      have htri : |a true - a false| ≤
          |t - a true| + |t - a false| := by
        calc
          |a true - a false| = |(a true - t) + (t - a false)| := by ring_nf
          _ ≤ |a true - t| + |t - a false| := abs_add_le _ _
          _ = |t - a true| + |t - a false| := by
            rw [abs_sub_comm (a true) t]
      linarith
  | true =>
      exact midpointDecoder_error_ge_half_separation (a false) (a true) t delta
        hsep hwrong

/-- A wrong midpoint decision at one packing center forces the finite maximum
loss to exceed half the certified center-value separation. -/
-- @node: finitePackingLoss_ge_of_midpointDecoder_wrong
lemma finitePackingLoss_ge_of_midpointDecoder_wrong {n M : ℕ}
    (rho : RuleFun n) (P : CtyLaw) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool) (w : Sample n)
    (hvalues : ∀ j, P.mu (centers j) = values j (omega j))
    (delta : ℝ) (hsep : ∀ j, delta ≤ |values j true - values j false|)
    (j : Fin M)
    (hwrong : (decide
      (|rho w (centers j) - values j true| ≤
        |rho w (centers j) - values j false|) : Bool) ≠ omega j) :
    ENNReal.ofReal (delta / 2) ≤ finitePackingLoss rho P centers w := by
  have hj : delta / 2 ≤
      |rho w (centers j) - P.mu (centers j)| := by
    rw [hvalues j]
    exact midpointDecoder_wrong_bit_error (values j) (rho w (centers j)) delta
      (hsep j) (omega j) hwrong
  exact le_trans (ENNReal.ofReal_le_ofReal hj) (le_iSup (fun k : Fin M =>
    ENNReal.ofReal |rho w (centers k) - P.mu (centers k)|) j)

end CausalSmith.Stat.BddUniformLogPenalty
