import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Finite measurable partitions and restriction maps

This file represents a finite measurable partition by its measurable cell
classifier. It defines the cell sets, their normalized observation laws, and
the measurable restriction maps that stably filter a finite marked sequence.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- A finite measurable partition is represented by a measurable classifier;
its cells are the fibres of that classifier. -/
structure FiniteMeasurablePartition (X : Type*) (ι : Type*)
    [MeasurableSpace X] [MeasurableSpace ι] where
  /-- The cell containing an observation. -/
  cell : X → ι
  /-- Cell membership is measurable. -/
  measurable_cell : Measurable cell

namespace FiniteMeasurablePartition

/-- A finite family of measurable, pairwise disjoint sets covering the whole
space determines its unique measurable classifier partition. -/
noncomputable def ofSets (A : ι → Set X)
    (hA : ∀ j, MeasurableSet (A j))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : ⋃ j, A j = Set.univ) : FiniteMeasurablePartition X ι := by
  classical
  have hex : ∀ x : X, ∃ j : ι, x ∈ A j := by
    intro x
    have hx : x ∈ ⋃ j, A j := by rw [hcover]; exact Set.mem_univ x
    simpa only [Set.mem_iUnion] using hx
  let c : X → ι := fun x => Classical.choose (hex x)
  have hc_mem (x : X) : x ∈ A (c x) := Classical.choose_spec (hex x)
  have hc_fiber (j : ι) : c ⁻¹' {j} = A j := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      rw [← hx]
      exact hc_mem x
    · intro hx
      by_contra hne
      exact Set.disjoint_left.1 (hdis hne) (hc_mem x) hx
  exact ⟨c, measurable_to_countable' fun j => hc_fiber j ▸ hA j⟩

/-- The classifier constructed from a disjoint measurable cover has exactly
the supplied sets as its fibres. -/
lemma ofSets_cellSet (A : ι → Set X)
    (hA : ∀ j, MeasurableSet (A j))
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcover : ⋃ j, A j = Set.univ) (j : ι) :
    (ofSets A hA hdis hcover).cell ⁻¹' {j} = A j := by
  classical
  unfold ofSets
  dsimp only
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    rw [← hx]
    exact Classical.choose_spec (show ∃ k, x ∈ A k by
      have hx' : x ∈ ⋃ k, A k := by rw [hcover]; exact Set.mem_univ x
      simpa only [Set.mem_iUnion] using hx')
  · intro hx
    let hex : ∃ k, x ∈ A k := by
      have hx' : x ∈ ⋃ k, A k := by rw [hcover]; exact Set.mem_univ x
      simpa only [Set.mem_iUnion] using hx'
    by_contra hne
    exact Set.disjoint_left.1 (hdis hne)
      (Classical.choose_spec hex) hx

/-- The measurable set forming cell `j` of a classifier partition. -/
def cellSet (p : FiniteMeasurablePartition X ι) (j : ι) : Set X :=
  p.cell ⁻¹' {j}

/-- Every classifier cell is measurable. -/
lemma measurableSet_cellSet (p : FiniteMeasurablePartition X ι) (j : ι) :
    MeasurableSet (p.cellSet j) := by
  exact (measurableSet_singleton j).preimage p.measurable_cell

/-- Distinct classifier cells are disjoint. -/
lemma disjoint_cellSet (p : FiniteMeasurablePartition X ι) {i j : ι} (hij : i ≠ j) :
    Disjoint (p.cellSet i) (p.cellSet j) := by
  apply Set.disjoint_left.2
  intro x hxi hxj
  exact hij (hxi.symm.trans hxj)

/-- The union of all classifier cells is the whole observation space. -/
lemma iUnion_cellSet (p : FiniteMeasurablePartition X ι) :
    ⋃ j : ι, p.cellSet j = Set.univ := by
  ext x
  simp [cellSet]

/-- The probability mass of a cell, represented as a nonnegative real. -/
noncomputable def cellMass (p : FiniteMeasurablePartition X ι) (P : Measure X) (j : ι) :
    ℝ≥0 :=
  (P (p.cellSet j)).toNNReal

/-- Cell masses sum to one under a probability law. -/
lemma sum_cellMass (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P] :
    ∑ j, p.cellMass P j = 1 := by
  apply ENNReal.coe_injective
  rw [ENNReal.coe_finset_sum]
  simp only [ENNReal.coe_one, cellMass]
  simp_rw [ENNReal.coe_toNNReal (measure_ne_top P _)]
  calc
    ∑ j, P (p.cellSet j) = P (⋃ j ∈ (Finset.univ : Finset ι), p.cellSet j) := by
      symm
      apply measure_biUnion_finset
      · intro i _ j _ hij
        exact p.disjoint_cellSet hij
      · intro j _
        exact p.measurableSet_cellSet j
    _ = P (⋃ j, p.cellSet j) := by simp
    _ = 1 := by rw [p.iUnion_cellSet, measure_univ]

/-- The within-cell observation law is the normalised restriction when the
cell has positive mass and the ambient probability law when its mass is zero. -/
noncomputable def cellObservationLaw (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P] (j : ι) : Measure X :=
  if h : P (p.cellSet j) = 0 then P
  else (P (p.cellSet j))⁻¹ • P.restrict (p.cellSet j)

/-- The within-cell observation law is a probability measure, including the
zero-mass fallback branch. -/
instance cellObservationLaw_isProbabilityMeasure
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P] (j : ι) :
    IsProbabilityMeasure (p.cellObservationLaw P j) := by
  unfold cellObservationLaw
  split_ifs with h
  · infer_instance
  · constructor
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
    simpa using ENNReal.inv_mul_cancel h (measure_ne_top P _)

/-- A positive-mass within-cell law assigns probability one to its own cell. -/
lemma cellObservationLaw_apply_cellSet
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P] (j : ι)
    (hj : P (p.cellSet j) ≠ 0) :
    p.cellObservationLaw P j (p.cellSet j) = 1 := by
  rw [cellObservationLaw, dif_neg hj, Measure.smul_apply,
    Measure.restrict_apply (p.measurableSet_cellSet j)]
  simpa using ENNReal.inv_mul_cancel hj (measure_ne_top P _)

/-- Indices of the marked observations belonging to cell `j`. -/
noncomputable def cellIndices (p : FiniteMeasurablePartition X ι) (j : ι)
    (s : FiniteSample (X × ℝ)) : Finset (Fin s.count) := by
  classical
  exact Finset.univ.filter (fun k => p.cell (s.points k).1 = j)

/-- Restrict a finite marked sequence to one cell, preserving the original
relative order of all points that lie in that cell. -/
noncomputable def restrictCell (p : FiniteMeasurablePartition X ι) (j : ι)
    (s : FiniteSample (X × ℝ)) : FiniteSample (X × ℝ) := by
  classical
  let t := p.cellIndices j s
  exact ⟨t.card, fun k => s.points (t.orderIsoOfFin rfl k)⟩

/-- Restrict a finite marked sequence simultaneously to every partition cell. -/
noncomputable def restrictPartition (p : FiniteMeasurablePartition X ι)
    (s : FiniteSample (X × ℝ)) : ι → FiniteSample (X × ℝ) :=
  fun j => p.restrictCell j s

/-- Restriction to one measurable cell is a measurable map on finite marked
sequences. -/
lemma measurable_restrictCell (p : FiniteMeasurablePartition X ι) (j : ι) :
    Measurable (p.restrictCell j) := by
  classical
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf] at hs ⊢
  intro n
  change MeasurableSet
    (fixedSizeEmbed n ⁻¹' (p.restrictCell j ⁻¹' s))
  rw [show fixedSizeEmbed n ⁻¹' (p.restrictCell j ⁻¹' s) =
      ⋃ t : Finset (Fin n),
        {x : Fin n → X × ℝ | p.cellIndices j (fixedSizeEmbed n x) = t} ∩
          (fun x : Fin n → X × ℝ =>
            fun k => x (t.orderIsoOfFin rfl k)) ⁻¹'
              (fixedSizeEmbed t.card ⁻¹' s) by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro hx
      let t := p.cellIndices j (fixedSizeEmbed n x)
      refine ⟨t, rfl, ?_⟩
      simpa [restrictCell] using hx
    · rintro ⟨t, ht, hx⟩
      subst t
      simpa [restrictCell] using hx]
  apply MeasurableSet.iUnion
  intro t
  apply MeasurableSet.inter
  · rw [show {x : Fin n → X × ℝ |
          p.cellIndices j (fixedSizeEmbed n x) = t} =
        ⋂ k : Fin n, if k ∈ t then
          {x : Fin n → X × ℝ | p.cell (x k).1 = j}
        else {x : Fin n → X × ℝ | p.cell (x k).1 = j}ᶜ by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [Finset.ext_iff]
      simp only [cellIndices, FiniteSample.count, FiniteSample.points, fixedSizeEmbed,
        Finset.mem_filter, Finset.mem_univ, true_and]
      apply forall_congr'
      intro k
      by_cases hkt : k ∈ t
      · simp only [hkt, if_true, Set.mem_setOf_eq]
        constructor
        · intro h
          exact (Finset.mem_filter.1 (h.2 hkt)).2
        · intro hk
          constructor
          · intro _
            exact hkt
          · intro _
            exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
      · simp only [hkt, if_false, Set.mem_compl_iff, Set.mem_setOf_eq]
        constructor
        · intro h hk
          have hkf : k ∈ ({k | p.cell (x k).1 = j} : Finset (Fin n)) :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
          exact hkt (h.1 hkf)
        · intro hk
          constructor
          · intro hkf
            exact (hk (Finset.mem_filter.1 hkf).2).elim
          · intro hkt'
            exact (hkt hkt').elim]
    apply MeasurableSet.iInter
    intro k
    split_ifs
    · exact (p.measurable_cell.comp ((measurable_pi_apply k).fst))
        (measurableSet_singleton j)
    · exact ((p.measurable_cell.comp ((measurable_pi_apply k).fst))
        (measurableSet_singleton j)).compl
  · have hst : MeasurableSet (fixedSizeEmbed t.card ⁻¹' s) := hs t.card
    exact hst.preimage (by fun_prop)

/-- Simultaneous restriction to all cells is measurable. -/
lemma measurable_restrictPartition (p : FiniteMeasurablePartition X ι) :
    Measurable p.restrictPartition := by
  unfold restrictPartition
  exact measurable_pi_lambda _ fun j => p.measurable_restrictCell j


end FiniteMeasurablePartition

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
