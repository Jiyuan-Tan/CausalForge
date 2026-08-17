import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.Divergence
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.FiniteMaxExperiment

/-!
# Causal finite-maximum assembly

This module builds the finite measurable partition used to split the causal
hard-family marked-Poisson experiment into its local cells and common
complement.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Equip the causal packing index set with the discrete measurable structure. -/
local instance causalPackingIndexMeasurableSpace (M : ℕ) :
    MeasurableSpace (Unit ⊕ Fin M) := ⊤

/-- The disjoint hard cells and their common complement as a classifier. -/
-- @node: causalPackingPartitionSet
def causalPackingPartitionSet {M : ℕ} (centers : Fin M → Score) (w : ℝ) :
    Unit ⊕ Fin M → Set CausalObservation
  | .inr j => {z | causalScore z ∈ causalHardCell (centers j) w}
  | .inl _ => {z | causalScore z ∉ ⋃ j, causalHardCell (centers j) w}

/-- Every causal packing cell, including the complement, is measurable. -/
-- @node: causalPackingPartitionSet_measurable
lemma causalPackingPartitionSet_measurable {M : ℕ}
    (centers : Fin M → Score) (w : ℝ) (j : Unit ⊕ Fin M) :
    MeasurableSet (causalPackingPartitionSet centers w j) := by
  have hscore : Measurable (causalScore : CausalObservation → Score) := by
    unfold causalScore
    fun_prop
  have hcell (k : Fin M) :
      MeasurableSet {z : CausalObservation |
        causalScore z ∈ causalHardCell (centers k) w} := by
    exact Metric.isClosed_closedBall.measurableSet.preimage hscore
  cases j with
  | inl u =>
      rw [show causalPackingPartitionSet centers w (.inl u) =
          (⋃ k : Fin M, {z : CausalObservation |
            causalScore z ∈ causalHardCell (centers k) w})ᶜ by
        ext z
        simp [causalPackingPartitionSet]]
      exact (MeasurableSet.iUnion hcell).compl
  | inr j => simpa [causalPackingPartitionSet] using hcell j

/-- Distinct indices select disjoint causal partition cells. -/
-- @node: causalPackingPartitionSet_pairwiseDisjoint
lemma causalPackingPartitionSet_pairwiseDisjoint {M : ℕ}
    (centers : Fin M → Score) (w : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (causalHardCell (centers i) w) (causalHardCell (centers j) w)) :
    Pairwise (fun i j : Unit ⊕ Fin M =>
      Disjoint (causalPackingPartitionSet centers w i)
        (causalPackingPartitionSet centers w j)) := by
  intro i j hij
  cases i with
  | inl u =>
      cases j with
      | inl v => exact (hij (by cases u; cases v; rfl)).elim
      | inr j =>
          apply Set.disjoint_left.2
          intro z hz hj
          exact hz (Set.mem_iUnion.2 ⟨j, hj⟩)
  | inr i =>
      cases j with
      | inl u =>
          apply Set.disjoint_left.2
          intro z hi hz
          exact hz (Set.mem_iUnion.2 ⟨i, hi⟩)
      | inr j =>
          apply Set.disjoint_left.2
          intro z hi hj
          exact Set.disjoint_left.1
            (hdis i j (fun h => hij (congrArg Sum.inr h))) hi hj

/-- The causal packing partition covers the observation space. -/
-- @node: causalPackingPartitionSet_iUnion
lemma causalPackingPartitionSet_iUnion {M : ℕ}
    (centers : Fin M → Score) (w : ℝ) :
    ⋃ j : Unit ⊕ Fin M, causalPackingPartitionSet centers w j = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases h : causalScore z ∈ ⋃ j, causalHardCell (centers j) w
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
    exact ⟨.inr j, hj⟩
  · exact ⟨.inl (), h⟩

/-- The finite measurable partition formed by the causal hard cells. -/
-- @node: causalPackingFinitePartition
noncomputable def causalPackingFinitePartition {M : ℕ}
    (centers : Fin M → Score) (w : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (causalHardCell (centers i) w) (causalHardCell (centers j) w)) :
    FiniteMeasurablePartition CausalObservation (Unit ⊕ Fin M) :=
  FiniteMeasurablePartition.ofSets (causalPackingPartitionSet centers w)
    (causalPackingPartitionSet_measurable centers w)
    (causalPackingPartitionSet_pairwiseDisjoint centers w hdis)
    (causalPackingPartitionSet_iUnion centers w)

/-- The abstract partition has the intended causal hard cells. -/
-- @node: causalPackingFinitePartition_cellSet
lemma causalPackingFinitePartition_cellSet {M : ℕ}
    (centers : Fin M → Score) (w : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (causalHardCell (centers i) w) (causalHardCell (centers j) w))
    (j : Unit ⊕ Fin M) :
    (causalPackingFinitePartition centers w hdis).cellSet j =
      causalPackingPartitionSet centers w j := by
  exact FiniteMeasurablePartition.ofSets_cellSet _ _ _ _ j

/-- A local partition-cell mass is exactly the score-cell probability. -/
-- @node: causalPackingFinitePartition_cell_measure_eq
lemma causalPackingFinitePartition_cell_measure_eq {M : ℕ}
    (centers : Fin M → Score) (w : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (causalHardCell (centers i) w) (causalHardCell (centers j) w))
    (P : A1A2Law) (j : Fin M) :
    P.law ((causalPackingFinitePartition centers w hdis).cellSet (.inr j)) =
      P.law {z | causalScore z ∈ causalHardCell (centers j) w} := by
  rw [causalPackingFinitePartition_cellSet, causalPackingPartitionSet]

/-- Equal positive cell mass and raw restriction locality identify the
normalized observation laws in a causal packing cell. -/
-- @node: causalPackingCellObservationLaw_eq_of_bit_eq
lemma causalPackingCellObservationLaw_eq_of_bit_eq {M : ℕ}
    (centers : Fin M → Score) (w rho : ℝ)
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
    (omega omega' : Fin M → Bool) (j : Fin M)
    (hbit : omega j = omega' j) :
    (letI : IsProbabilityMeasure (laws omega).law :=
      (laws omega).law_isProbability
     letI : IsProbabilityMeasure (laws omega').law :=
      (laws omega').law_isProbability
     (causalPackingFinitePartition centers w hdis).cellObservationLaw
        (laws omega).law (.inr j) =
      (causalPackingFinitePartition centers w hdis).cellObservationLaw
        (laws omega').law (.inr j)) := by
  letI : IsProbabilityMeasure (laws omega).law :=
    (laws omega).law_isProbability
  letI : IsProbabilityMeasure (laws omega').law :=
    (laws omega').law_isProbability
  let p := causalPackingFinitePartition centers w hdis
  apply cellObservationLaw_eq_of_restrict_eq p (laws omega).law
    (laws omega').law (.inr j)
  · rw [show (laws omega).law (p.cellSet (.inr j)) = ENNReal.ofReal rho by
      rw [show p = causalPackingFinitePartition centers w hdis by rfl,
        causalPackingFinitePartition_cell_measure_eq, hmass omega j]]
    exact (ENNReal.ofReal_pos.mpr hrho).ne'
  · rw [show (laws omega).law (p.cellSet (.inr j)) = ENNReal.ofReal rho by
        rw [show p = causalPackingFinitePartition centers w hdis by rfl,
          causalPackingFinitePartition_cell_measure_eq, hmass omega j],
      show (laws omega').law (p.cellSet (.inr j)) = ENNReal.ofReal rho by
        rw [show p = causalPackingFinitePartition centers w hdis by rfl,
          causalPackingFinitePartition_cell_measure_eq, hmass omega' j]]
  · simpa [p, causalPackingFinitePartition_cellSet,
      causalPackingPartitionSet] using hlocal omega omega' j hbit

/-- A canonical vertex carrying the selected causal cell bit. -/
-- @node: causalPackingSingleBit
def causalPackingSingleBit {M : ℕ} (j : Fin M) (b : Bool) : Fin M → Bool :=
  fun k => if k = j then b else false

/-- The canonical marked-Poisson law in causal coordinate `j`. -/
-- @node: causalPackingCellExperiment
noncomputable def causalPackingCellExperiment {M : ℕ}
    (p : FiniteMeasurablePartition CausalObservation (Unit ⊕ Fin M))
    (laws : (Fin M → Bool) → A1A2Law) (lam : ℝ≥0)
    (j : Fin M) (b : Bool) :
    Measure (FiniteSample (CausalObservation × ℝ)) := by
  letI : IsProbabilityMeasure (laws (causalPackingSingleBit j b)).law :=
    (laws (causalPackingSingleBit j b)).law_isProbability
  exact canonicalMarkedPoissonSampleLaw
    (p.cellObservationLaw (laws (causalPackingSingleBit j b)).law (.inr j))
    packingMarkLaw
    (lam * p.cellMass (laws (causalPackingSingleBit j b)).law (.inr j))

/-- The stated experiment law has total mass one and therefore defines a probability distribution. -/
instance causalPackingCellExperiment_isProbabilityMeasure {M : ℕ}
    (p : FiniteMeasurablePartition CausalObservation (Unit ⊕ Fin M))
    (laws : (Fin M → Bool) → A1A2Law) (lam : ℝ≥0)
    (j : Fin M) (b : Bool) :
    IsProbabilityMeasure (causalPackingCellExperiment p laws lam j b) := by
  unfold causalPackingCellExperiment
  infer_instance

/-- The causal complement experiment, represented at the all-false vertex. -/
-- @node: causalPackingCommonExperiment
noncomputable def causalPackingCommonExperiment {M : ℕ}
    (p : FiniteMeasurablePartition CausalObservation (Unit ⊕ Fin M))
    (laws : (Fin M → Bool) → A1A2Law) (lam : ℝ≥0) :
    Measure (Unit → FiniteSample (CausalObservation × ℝ)) := by
  let omega0 : Fin M → Bool := fun _ => false
  letI : IsProbabilityMeasure (laws omega0).law :=
    (laws omega0).law_isProbability
  exact Measure.pi (fun _ : Unit => canonicalMarkedPoissonSampleLaw
    (p.cellObservationLaw (laws omega0).law (.inl ())) packingMarkLaw
    (lam * p.cellMass (laws omega0).law (.inl ())))

/-- The stated experiment law has total mass one and therefore defines a probability distribution. -/
instance causalPackingCommonExperiment_isProbabilityMeasure {M : ℕ}
    (p : FiniteMeasurablePartition CausalObservation (Unit ⊕ Fin M))
    (laws : (Fin M → Bool) → A1A2Law) (lam : ℝ≥0) :
    IsProbabilityMeasure (causalPackingCommonExperiment p laws lam) := by
  unfold causalPackingCommonExperiment
  infer_instance

/-- A canonical causal cell experiment depends only on its own Boolean bit. -/
-- @node: causalPackingCanonicalCellLaw_eq_of_bit_eq
lemma causalPackingCanonicalCellLaw_eq_of_bit_eq {M : ℕ}
    (centers : Fin M → Score) (w rho : ℝ)
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
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0)
    (omega omega' : Fin M → Bool) (j : Fin M)
    (hbit : omega j = omega' j) :
    (letI : IsProbabilityMeasure (laws omega).law :=
      (laws omega).law_isProbability
     letI : IsProbabilityMeasure (laws omega').law :=
      (laws omega').law_isProbability
     let p := causalPackingFinitePartition centers w hdis
     canonicalMarkedPoissonSampleLaw
        (p.cellObservationLaw (laws omega).law (.inr j)) R
        (lam * p.cellMass (laws omega).law (.inr j)) =
      canonicalMarkedPoissonSampleLaw
        (p.cellObservationLaw (laws omega').law (.inr j)) R
        (lam * p.cellMass (laws omega').law (.inr j))) := by
  letI : IsProbabilityMeasure (laws omega).law :=
    (laws omega).law_isProbability
  letI : IsProbabilityMeasure (laws omega').law :=
    (laws omega').law_isProbability
  let p := causalPackingFinitePartition centers w hdis
  have hobs := causalPackingCellObservationLaw_eq_of_bit_eq centers w rho hdis
    laws hrho hmass hlocal omega omega' j hbit
  have hobs' : p.cellObservationLaw (laws omega).law (.inr j) =
      p.cellObservationLaw (laws omega').law (.inr j) := by
    simpa [p] using hobs
  have hmassEq : p.cellMass (laws omega).law (.inr j) =
      p.cellMass (laws omega').law (.inr j) := by
    unfold FiniteMeasurablePartition.cellMass
    rw [show (laws omega).law (p.cellSet (.inr j)) = ENNReal.ofReal rho by
        rw [show p = causalPackingFinitePartition centers w hdis by rfl,
          causalPackingFinitePartition_cell_measure_eq, hmass omega j],
      show (laws omega').law (p.cellSet (.inr j)) = ENNReal.ofReal rho by
        rw [show p = causalPackingFinitePartition centers w hdis by rfl,
          causalPackingFinitePartition_cell_measure_eq, hmass omega' j]]
  change canonicalMarkedPoissonSampleLaw
      (p.cellObservationLaw (laws omega).law (.inr j)) R
      (lam * p.cellMass (laws omega).law (.inr j)) =
    canonicalMarkedPoissonSampleLaw
      (p.cellObservationLaw (laws omega').law (.inr j)) R
      (lam * p.cellMass (laws omega').law (.inr j))
  unfold canonicalMarkedPoissonSampleLaw
  simp only [hobs', hmassEq]

/-- The canonical complement experiment is common to every causal vertex. -/
-- @node: causalPackingCanonicalComplementLaw_eq
lemma causalPackingCanonicalComplementLaw_eq {M : ℕ}
    (centers : Fin M → Score) (w : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (causalHardCell (centers i) w) (causalHardCell (centers j) w))
    (laws : (Fin M → Bool) → A1A2Law)
    (hoff : ∀ omega omega', (laws omega).law.restrict
        {z | causalScore z ∉ ⋃ j, causalHardCell (centers j) w} =
      (laws omega').law.restrict
        {z | causalScore z ∉ ⋃ j, causalHardCell (centers j) w})
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0)
    (omega omega' : Fin M → Bool) :
    (letI : IsProbabilityMeasure (laws omega).law :=
      (laws omega).law_isProbability
     letI : IsProbabilityMeasure (laws omega').law :=
      (laws omega').law_isProbability
     let p := causalPackingFinitePartition centers w hdis
     canonicalMarkedPoissonSampleLaw
        (p.cellObservationLaw (laws omega).law (.inl ())) R
        (lam * p.cellMass (laws omega).law (.inl ())) =
      canonicalMarkedPoissonSampleLaw
        (p.cellObservationLaw (laws omega').law (.inl ())) R
        (lam * p.cellMass (laws omega').law (.inl ()))) := by
  letI : IsProbabilityMeasure (laws omega).law :=
    (laws omega).law_isProbability
  letI : IsProbabilityMeasure (laws omega').law :=
    (laws omega').law_isProbability
  let p := causalPackingFinitePartition centers w hdis
  have hrest : (laws omega).law.restrict (p.cellSet (.inl ())) =
      (laws omega').law.restrict (p.cellSet (.inl ())) := by
    simpa [p, causalPackingFinitePartition_cellSet,
      causalPackingPartitionSet] using hoff omega omega'
  have hmass : (laws omega).law (p.cellSet (.inl ())) =
      (laws omega').law (p.cellSet (.inl ())) := by
    have h := congrArg (fun μ : Measure CausalObservation => μ Set.univ) hrest
    simpa [Measure.restrict_apply_univ] using h
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

/-- Put the causal complement and cell blocks back into one marked sample. -/
-- @node: synthesizeCausalPackingConfiguration
noncomputable def synthesizeCausalPackingConfiguration {M : ℕ}
    (z : (Unit → FiniteSample (CausalObservation × ℝ)) ×
      (Fin M → FiniteSample (CausalObservation × ℝ))) :
    FiniteSample (CausalObservation × ℝ) :=
  superposeByMarks
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Unit ⊕ Fin M => FiniteSample (CausalObservation × ℝ))).symm z)

-- @node: synthesizeCausalPackingConfiguration_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma synthesizeCausalPackingConfiguration_measurable {M : ℕ} :
    Measurable (synthesizeCausalPackingConfiguration (M := M)) := by
  exact measurable_superposeByMarks.comp
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Unit ⊕ Fin M =>
        FiniteSample (CausalObservation × ℝ))).symm.measurable

/-- Partition splitting identifies the independent causal blocks with the
canonical marked-Poisson law at the selected vertex. -/
-- @node: causalPackingExperiment_synthesis_law
lemma causalPackingExperiment_synthesis_law {M : ℕ}
    (centers : Fin M → Score) (w rho : ℝ)
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
    (lam : ℝ≥0) (omega : Fin M → Bool) :
    (letI : IsProbabilityMeasure (laws omega).law :=
      (laws omega).law_isProbability
     Measure.map synthesizeCausalPackingConfiguration
        ((causalPackingCommonExperiment
          (causalPackingFinitePartition centers w hdis) laws lam).prod
          (Measure.pi fun j => causalPackingCellExperiment
            (causalPackingFinitePartition centers w hdis)
              laws lam j (omega j))) =
      canonicalMarkedPoissonSampleLaw (laws omega).law packingMarkLaw lam) := by
  let p := causalPackingFinitePartition centers w hdis
  let omega0 : Fin M → Bool := fun _ => false
  letI : IsProbabilityMeasure (laws omega).law :=
    (laws omega).law_isProbability
  letI : IsProbabilityMeasure (laws omega0).law :=
    (laws omega0).law_isProbability
  let cellLaw (k : Unit ⊕ Fin M) := canonicalMarkedPoissonSampleLaw
    (p.cellObservationLaw (laws omega).law k) packingMarkLaw
    (lam * p.cellMass (laws omega).law k)
  have hcoord (j : Fin M) :
      causalPackingCellExperiment p laws lam j (omega j) = cellLaw (.inr j) := by
    symm
    exact causalPackingCanonicalCellLaw_eq_of_bit_eq centers w rho hdis laws
      hrho hmass hlocal packingMarkLaw lam omega
      (causalPackingSingleBit j (omega j)) j (by simp [causalPackingSingleBit])
  have hcommon : (fun _ : Unit => canonicalMarkedPoissonSampleLaw
      (p.cellObservationLaw (laws omega0).law (.inl ())) packingMarkLaw
      (lam * p.cellMass (laws omega0).law (.inl ()))) =
      (fun _ : Unit => cellLaw (.inl ())) := by
    funext u
    cases u
    exact causalPackingCanonicalComplementLaw_eq centers w hdis laws hoff
      packingMarkLaw lam omega0 omega
  have hprod : (causalPackingCommonExperiment p laws lam).prod
      (Measure.pi fun j => causalPackingCellExperiment p laws lam j (omega j)) =
      (Measure.pi fun u : Unit => cellLaw (.inl u)).prod
        (Measure.pi fun j : Fin M => cellLaw (.inr j)) := by
    change (Measure.pi (fun _ : Unit => canonicalMarkedPoissonSampleLaw
      (p.cellObservationLaw (laws omega0).law (.inl ())) packingMarkLaw
      (lam * p.cellMass (laws omega0).law (.inl ())))).prod
      (Measure.pi fun j => causalPackingCellExperiment p laws lam j (omega j)) = _
    rw [hcommon]
    rw [show (fun j => causalPackingCellExperiment p laws lam j (omega j)) =
      (fun j : Fin M => cellLaw (.inr j)) by funext j; exact hcoord j]
  rw [show causalPackingFinitePartition centers w hdis = p by rfl, hprod]
  calc
    Measure.map synthesizeCausalPackingConfiguration
        ((Measure.pi fun u : Unit => cellLaw (.inl u)).prod
          (Measure.pi fun j : Fin M => cellLaw (.inr j))) =
        Measure.map superposeByMarks (Measure.pi cellLaw) := by
      rw [show synthesizeCausalPackingConfiguration = superposeByMarks ∘
          (MeasurableEquiv.sumPiEquivProdPi
            (fun _ : Unit ⊕ Fin M =>
              FiniteSample (CausalObservation × ℝ))).symm by rfl,
        ← Measure.map_map measurable_superposeByMarks
          (MeasurableEquiv.sumPiEquivProdPi
            (fun _ : Unit ⊕ Fin M =>
              FiniteSample (CausalObservation × ℝ))).symm.measurable]
      rw [(measurePreserving_sumPiEquivProdPi_symm cellLaw).map_eq]
    _ = canonicalMarkedPoissonSampleLaw (laws omega).law packingMarkLaw lam := by
      simpa [cellLaw] using
        (map_superposeByMarks_canonicalCellLaws p (laws omega).law
          packingMarkLaw lam)

end CausalSmith.Stat.BddUniformLogPenalty
