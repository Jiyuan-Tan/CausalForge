/- Exact reindexing bridges from the polynomial estimation fold to a finite product law. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.SplitBridge
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.FixedBranchAssembly
import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat

-- @node: polynomialFoldBEquiv
/-- The balanced estimation fold has the canonical finite index type of its
declared cardinality. -/
noncomputable def polynomialFoldBEquiv {n d : ℕ} (P : RealLaw d) :
    Fin (n - n / 2) ≃o (polynomialBalancedSplit P).foldB n :=
  ((polynomialBalancedSplit P).foldB n).orderIsoOfFin (by
    rw [(polynomialBalancedSplit P).foldB_card]
    rfl)

-- @node: polynomialFoldBReindex
/-- Reindex an estimation-fold tuple by the canonical finite type with the
same cardinality. -/
noncomputable def polynomialFoldBReindex {n d : ℕ} (P : RealLaw d)
    (x : (polynomialBalancedSplit P).foldB n → Obs d) :
    Fin (n - n / 2) → Obs d :=
  fun j => x (polynomialFoldBEquiv P j)

-- @node: polynomialFoldBAsFin
/-- Regard an estimation-fold index as an index of the original finite
sample. -/
def polynomialFoldBAsFin {n d : ℕ} (P : RealLaw d)
    (i : (polynomialBalancedSplit P).foldB n) : Fin n :=
  ⟨i.val, by
    have hmem := i.property
    change i.val ∈ (Finset.range n).filter (fun q => n / 2 ≤ q) at hmem
    exact Finset.mem_range.mp (Finset.mem_filter.mp hmem).1⟩

-- @node: rebuildPolynomialEstimationSample_foldBAsFin
/-- [Rebuilding a full tuple and then restricting to an estimation-fold index returns the original
  fold observation](goal). -/
lemma rebuildPolynomialEstimationSample_foldBAsFin {n d : ℕ}
    (P : RealLaw d) (base : Obs d)
    (x : (polynomialBalancedSplit P).foldB n → Obs d)
    (i : (polynomialBalancedSplit P).foldB n) :
    rebuildPolynomialEstimationSample P base x (polynomialFoldBAsFin P i) = x i := by
  have hmem := i.property
  change i.val ∈ (Finset.range n).filter (fun q => n / 2 ≤ q) at hmem
  have hge := (Finset.mem_filter.mp hmem).2
  unfold rebuildPolynomialEstimationSample
  change (if h : n / 2 ≤ i.val then
      x ⟨i.val, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (polynomialFoldBAsFin P i).isLt, h⟩⟩
    else base) = x i
  rw [dif_pos hge]

-- @node: map_polynomialFoldBReindex_iid_eq_productLaw
/-- [Under the infinite iid realization, the reindexed balanced estimation fold has exactly the
  finite product law of size `n - n / 2`](goal). -/
lemma map_polynomialFoldBReindex_iid_eq_productLaw {n d : ℕ}
    (P : RealLaw d) :
    Measure.map
        (fun ω : ℕ → Obs d => polynomialFoldBReindex P
          (fun i : (polynomialBalancedSplit P).foldB n => ω i))
        (Measure.infinitePi fun _ : ℕ => P.observedLaw) =
      productLaw (n - n / 2) P := by
  let S := iidSample_infinitePi P.observedLaw
  let e := polynomialFoldBEquiv (n := n) P
  let YB : (ℕ → Obs d) → (polynomialBalancedSplit P).foldB n → Obs d :=
    fun ω i => S.Z i ω
  let T : ((polynomialBalancedSplit P).foldB n → Obs d) ≃ᵐ
      (Fin (n - n / 2) → Obs d) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin (n - n / 2) => Obs d)
      e.symm.toEquiv
  have hYB : Measurable YB := by
    apply measurable_pi_lambda
    intro i
    exact S.meas i
  have heq :
      (fun ω : ℕ → Obs d => polynomialFoldBReindex P
        (fun i : (polynomialBalancedSplit P).foldB n => ω i)) = T ∘ YB := by
    funext ω j
    change S.Z (e j) ω = T (YB ω) j
    simpa [T, YB] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := e.symm.toEquiv)
        (β := fun _ : Fin (n - n / 2) => Obs d)
        (x := fun i : (polynomialBalancedSplit P).foldB n => S.Z i ω)
        (i := e j)).symm
  rw [heq, ← Measure.map_map T.measurable hYB]
  rw [oneShot_iid S (polynomialBalancedSplit P) n]
  unfold productLaw
  simpa [T] using Measure.pi_map_piCongrLeft
    (e := e.symm.toEquiv) (β := fun _ : Fin (n - n / 2) => Obs d)
    (μ := fun _ : Fin (n - n / 2) => P.observedLaw)

-- @node: estimationArmCount_rebuild_eq_reindex
/-- [Every estimation-block arm/cell count is the corresponding count on the canonically reindexed
  fold tuple](goal). -/
lemma estimationArmCount_rebuild_eq_reindex {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (x : (polynomialBalancedSplit P).foldB n → Obs d)
    (a : Bool) (k : Fin d) :
    estimationArmCount (rebuildPolynomialEstimationSample P base x) a k =
      Causalean.Stat.groupArmCount (fun o : Obs d => o.x) (fun o => o.a)
        (polynomialFoldBReindex P x) a k := by
  classical
  unfold estimationArmCount Causalean.Stat.groupArmCount
  symm
  apply Finset.card_bij
    (fun j _ => ⟨(polynomialFoldBEquiv P j).val,
      by
        have hmem := (polynomialFoldBEquiv P j).property
        change (polynomialFoldBEquiv P j).val ∈
          (Finset.range n).filter (fun i => n / 2 ≤ i) at hmem
        exact Finset.mem_range.mp (Finset.mem_filter.mp hmem).1⟩)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have hmem := (polynomialFoldBEquiv P j).property
    change (polynomialFoldBEquiv P j).val ∈
      (Finset.range n).filter (fun i => n / 2 ≤ i) at hmem
    have hge := (Finset.mem_filter.mp hmem).2
    simp only [inPilot, rebuildPolynomialEstimationSample, hge, dite_true]
    have hxeq :
        x ⟨(polynomialFoldBEquiv P j).val, by
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hmem).1, hge⟩⟩ =
          x (polynomialFoldBEquiv P j) := by
      congr 1
    refine ⟨?_, ?_⟩
    · simp [Nat.not_lt.mpr hge]
    rw [hxeq]
    simpa [polynomialFoldBReindex] using hj
  · intro j₁ _ j₂ _ h
    apply (polynomialFoldBEquiv P).injective
    apply Subtype.ext
    exact Fin.ext_iff.mp h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hge : n / 2 ≤ i.val := by
      simpa [inPilot, Bool.not_eq_true] using hi.1
    let ib : (polynomialBalancedSplit P).foldB n :=
      ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hge⟩⟩
    let j := (polynomialFoldBEquiv P).symm ib
    refine ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [polynomialFoldBReindex, j, ib,
        rebuildPolynomialEstimationSample, hge] using hi.2
    · apply Fin.ext
      change (polynomialFoldBEquiv P j).val = i.val
      simp [j, ib]

-- @node: estimationArmSum_rebuild_eq_reindex
/-- [Every estimation-block marked outcome sum is the corresponding supported mark sum on the
  canonically reindexed fold tuple](goal). -/
lemma estimationArmSum_rebuild_eq_reindex {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (x : (polynomialBalancedSplit P).foldB n → Obs d)
    (a : Bool) (k : Fin d) :
    estimationArmSum (rebuildPolynomialEstimationSample P base x) a k =
      Causalean.Stat.FiniteStratumMarkedRatioMse.armMarkSum
        (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y)
        (polynomialFoldBReindex P x) a k := by
  classical
  unfold estimationArmSum
  unfold Causalean.Stat.FiniteStratumMarkedRatioMse.armMarkSum
    Causalean.Stat.FiniteStratumMarkedRatioMse.supportedArmMark
    Causalean.Stat.FiniteStratumMarkedRatioMse.armCategoryEvent
    Causalean.Stat.armGroupEvent Set.indicator
  simp only [Set.mem_ofPred_eq]
  rw [← Finset.sum_filter]
  simp_rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij
    (fun j _ => polynomialFoldBAsFin P (polynomialFoldBEquiv P j))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have hmem := (polynomialFoldBEquiv P j).property
    change (polynomialFoldBEquiv P j).val ∈
      (Finset.range n).filter (fun i => n / 2 ≤ i) at hmem
    have hge := (Finset.mem_filter.mp hmem).2
    refine ⟨?_, ?_⟩
    · change (!decide ((polynomialFoldBEquiv P j).val < n / 2)) = true
      simp [Nat.not_lt.mpr hge]
    · rw [rebuildPolynomialEstimationSample_foldBAsFin]
      simpa [polynomialFoldBReindex] using hj
  · intro j₁ _ j₂ _ h
    apply (polynomialFoldBEquiv P).injective
    apply Subtype.ext
    exact Fin.ext_iff.mp h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hge : n / 2 ≤ i.val := by
      simpa [inPilot, Bool.not_eq_true] using hi.1
    let ib : (polynomialBalancedSplit P).foldB n :=
      ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hge⟩⟩
    let j := (polynomialFoldBEquiv P).symm ib
    refine ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [polynomialFoldBReindex, j, ib,
        rebuildPolynomialEstimationSample, hge] using hi.2
    · apply Fin.ext
      change (polynomialFoldBEquiv P j).val = i.val
      simp [j, ib]
  · intro j _
    rw [rebuildPolynomialEstimationSample_foldBAsFin]
    rfl

-- @node: estimationCellCount_rebuild_eq_reindex
/-- [The estimation-block cell count is the generic cell count on the reindexed fold](goal). -/
lemma estimationCellCount_rebuild_eq_reindex {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (x : (polynomialBalancedSplit P).foldB n → Obs d)
    (k : Fin d) :
    estimationCellCount (rebuildPolynomialEstimationSample P base x) k =
      Causalean.Stat.groupCount (fun o : Obs d => o.x) (fun o => o.a)
        (polynomialFoldBReindex P x) k := by
  unfold estimationCellCount Causalean.Stat.groupCount
  rw [estimationArmCount_rebuild_eq_reindex,
    estimationArmCount_rebuild_eq_reindex]

-- @node: estimationArmMean_rebuild_eq_reindex
/-- [The zero-safe estimation-block arm mean is the generic totalized arm mean on the reindexed
  fold](goal). -/
lemma estimationArmMean_rebuild_eq_reindex {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (x : (polynomialBalancedSplit P).foldB n → Obs d)
    (a : Bool) (k : Fin d) :
    estimationArmMean (rebuildPolynomialEstimationSample P base x) a k =
      Causalean.Stat.FiniteStratumMarkedRatioMse.totalizedArmMean
        (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y)
        (polynomialFoldBReindex P x) a k := by
  unfold estimationArmMean
    Causalean.Stat.FiniteStratumMarkedRatioMse.totalizedArmMean
    Causalean.Stat.FiniteStratumMarkedRatioMse.categoryArmCount
  rw [estimationArmCount_rebuild_eq_reindex,
    estimationArmSum_rebuild_eq_reindex]
  split_ifs with h
  · rw [div_eq_mul_inv, mul_comm]
  · rfl

-- @node: heavyEmpiricalTerm_rebuild_eq_reindex
/-- [The concrete heavy-cell term is exactly the normalized fixed-stratum term on the reindexed
  estimation fold](goal). -/
lemma heavyEmpiricalTerm_rebuild_eq_reindex {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (x : (polynomialBalancedSplit P).foldB n → Obs d)
    (M : ℝ) (k : Fin d) :
    heavyEmpiricalTerm M (rebuildPolynomialEstimationSample P base x) k =
      (Causalean.Stat.FiniteStratumMarkedRatioMse.categoryCount
          (fun o : Obs d => o.x) (fun o => o.a)
          (polynomialFoldBReindex P x) k : ℝ) / (n - n / 2 : ℕ) *
        ((Causalean.Stat.FiniteStratumMarkedRatioMse.totalizedArmMean
            (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y)
            (polynomialFoldBReindex P x) true k -
          Causalean.Stat.FiniteStratumMarkedRatioMse.totalizedArmMean
            (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y)
            (polynomialFoldBReindex P x) false k) / M) := by
  unfold heavyEmpiricalTerm estimationBlockSize
  rw [estimationCellCount_rebuild_eq_reindex,
    estimationArmMean_rebuild_eq_reindex,
    estimationArmMean_rebuild_eq_reindex]
  rfl

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
