/- Exact sample-split bridges for the heavy/light polynomial program. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.SelectionDecomposition
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Pilot
import Causalean.Stat.SampleSplit.OneShot

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

-- @node: polynomialBalancedSplit
/-- The deterministic half-split used by the concrete polynomial estimator,
packaged as a generic one-shot split of the infinite iid realization. -/
noncomputable def polynomialBalancedSplit {d : ℕ} (P : RealLaw d) :
    Causalean.Stat.OneShotSplit
      (Causalean.Stat.iidSample_infinitePi P.observedLaw) where
  n₁ n := n / 2
  bound n := Nat.div_le_self n 2
  grow := Nat.tendsto_div_const_atTop (by norm_num)
  cogrow := by
    show Filter.Tendsto (fun n : ℕ => n - n / 2) Filter.atTop Filter.atTop
    apply Filter.tendsto_atTop_mono
      (f := fun n : ℕ => n / 2) (g := fun n => n - n / 2)
    · intro n
      omega
    · exact Nat.tendsto_div_const_atTop (by norm_num)

-- @node: rebuildPolynomialPilotSample
/-- Rebuild a full sample from its pilot fold, filling the unused estimation
positions by an arbitrary fixed observation. -/
def rebuildPolynomialPilotSample {n d : ℕ} (P : RealLaw d) (base : Obs d)
    (x : (polynomialBalancedSplit P).foldA n → Obs d) : Fin n → Obs d :=
  fun i => if h : i.val < n / 2 then
    x ⟨i.val, by
      simpa [Causalean.Stat.OneShotSplit.foldA, polynomialBalancedSplit] using h⟩
  else base

-- @node: rebuildPolynomialEstimationSample
/-- Rebuild a full sample from its estimation fold, filling the unused pilot
positions by an arbitrary fixed observation. -/
def rebuildPolynomialEstimationSample {n d : ℕ} (P : RealLaw d) (base : Obs d)
    (x : (polynomialBalancedSplit P).foldB n → Obs d) : Fin n → Obs d :=
  fun i => if h : n / 2 ≤ i.val then
    x ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, h⟩⟩
  else base

-- @node: rebuildPolynomialEstimationSample_measurable
/-- [Rebuilding the full tuple from the estimation fold is measurable](goal). -/
lemma rebuildPolynomialEstimationSample_measurable {n d : ℕ} (P : RealLaw d)
    (base : Obs d) :
    Measurable (rebuildPolynomialEstimationSample (n := n) P base) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : n / 2 ≤ i.val
  · simp only [rebuildPolynomialEstimationSample, dif_pos hi]
    exact measurable_pi_apply _
  · simp only [rebuildPolynomialEstimationSample, dif_neg hi]
    exact measurable_const

-- @node: pilotCount_rebuildPolynomialPilot
/-- [Rebuilding from the pilot fold preserves every concrete pilot count](goal). -/
lemma pilotCount_rebuildPolynomialPilot {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (omega : ℕ → Obs d) (k : Fin d) :
    pilotCount (rebuildPolynomialPilotSample P base
      (fun i : (polynomialBalancedSplit P).foldA n => omega i)) k =
      pilotCount (fun i : Fin n => omega i) k := by
  classical
  unfold pilotCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i.val < n / 2
  · simp [inPilot, rebuildPolynomialPilotSample, hi]
  · simp [inPilot, rebuildPolynomialPilotSample, hi]

-- @node: estimationArmCount_rebuildPolynomialEstimation
/-- [Rebuilding from the estimation fold preserves every arm-cell count](goal). -/
lemma estimationArmCount_rebuildPolynomialEstimation {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (omega : ℕ → Obs d) (a : Bool) (k : Fin d) :
    estimationArmCount (rebuildPolynomialEstimationSample P base
      (fun i : (polynomialBalancedSplit P).foldB n => omega i)) a k =
      estimationArmCount (fun i : Fin n => omega i) a k := by
  classical
  unfold estimationArmCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : n / 2 ≤ i.val
  · simp [inPilot, rebuildPolynomialEstimationSample, hi,
      Nat.not_lt.mpr hi]
  · have hlt : i.val < n / 2 := Nat.lt_of_not_ge hi
    simp [inPilot, rebuildPolynomialEstimationSample, hi, hlt]

-- @node: estimationArmSum_rebuildPolynomialEstimation
/-- [Rebuilding from the estimation fold preserves every marked outcome sum](goal). -/
lemma estimationArmSum_rebuildPolynomialEstimation {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (omega : ℕ → Obs d) (a : Bool) (k : Fin d) :
    estimationArmSum (rebuildPolynomialEstimationSample P base
      (fun i : (polynomialBalancedSplit P).foldB n => omega i)) a k =
      estimationArmSum (fun i : Fin n => omega i) a k := by
  classical
  unfold estimationArmSum
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : n / 2 ≤ i.val
  · simp [inPilot, rebuildPolynomialEstimationSample, hi,
      Nat.not_lt.mpr hi]
  · have hlt : i.val < n / 2 := Nat.lt_of_not_ge hi
    simp [inPilot, rebuildPolynomialEstimationSample, hi, hlt]

-- @node: orderedMarkedFactorial_rebuildPolynomialEstimation
/-- [The aggregate one-mark factorial is a function of the estimation fold alone](goal). -/
lemma orderedMarkedFactorial_rebuildPolynomialEstimation {n d : ℕ}
    (P : RealLaw d) (base : Obs d) (omega : ℕ → Obs d)
    (M : ℝ) (k : Fin d) (a : Bool) (j : ℕ) :
    orderedMarkedFactorial M (rebuildPolynomialEstimationSample P base
      (fun i : (polynomialBalancedSplit P).foldB n => omega i)) k a j =
      orderedMarkedFactorial M (fun i : Fin n => omega i) k a j := by
  unfold orderedMarkedFactorial estimationCellCount
  rw [estimationArmSum_rebuildPolynomialEstimation P base omega,
    estimationArmCount_rebuildPolynomialEstimation P base omega,
    estimationArmCount_rebuildPolynomialEstimation P base omega,
    estimationArmCount_rebuildPolynomialEstimation P base omega]

-- @node: lightPolynomialTerm_rebuildPolynomialEstimation
/-- [Every fixed light-cell polynomial contribution depends only on the estimation fold](goal). -/
lemma lightPolynomialTerm_rebuildPolynomialEstimation {n d : ℕ}
    (P : RealLaw d) (base : Obs d) (omega : ℕ → Obs d)
    (M B : ℝ) (K : ℕ) (k : Fin d) :
    lightPolynomialTerm M B K (rebuildPolynomialEstimationSample P base
      (fun i : (polynomialBalancedSplit P).foldB n => omega i)) k =
      lightPolynomialTerm M B K (fun i : Fin n => omega i) k := by
  unfold lightPolynomialTerm
  simp_rw [orderedMarkedFactorial_rebuildPolynomialEstimation P base omega]

-- @node: heavyEmpiricalTerm_rebuildPolynomialEstimation
/-- [Every fixed heavy-cell marked-ratio contribution depends only on the estimation fold](goal). -/
lemma heavyEmpiricalTerm_rebuildPolynomialEstimation {n d : ℕ}
    (P : RealLaw d) (base : Obs d) (omega : ℕ → Obs d)
    (M : ℝ) (k : Fin d) :
    heavyEmpiricalTerm M (rebuildPolynomialEstimationSample P base
      (fun i : (polynomialBalancedSplit P).foldB n => omega i)) k =
      heavyEmpiricalTerm M (fun i : Fin n => omega i) k := by
  unfold heavyEmpiricalTerm estimationCellCount estimationArmMean
  rw [estimationArmCount_rebuildPolynomialEstimation P base omega false k,
    estimationArmCount_rebuildPolynomialEstimation P base omega true k,
    estimationArmSum_rebuildPolynomialEstimation P base omega false k,
    estimationArmSum_rebuildPolynomialEstimation P base omega true k]

-- @node: polynomialPilotHeavySet
/-- The finite heavy-set branch selected by a rebuilt pilot fold. -/
noncomputable def polynomialPilotHeavySet {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (x : (polynomialBalancedSplit P).foldA n → Obs d) :
    Finset (Fin d) :=
  Finset.univ.filter fun k =>
    256 * logEN n < pilotCount (rebuildPolynomialPilotSample P base x) k

-- @node: polynomialPilotHeavySet_measurable
/-- [The finite heavy-set selector is measurable as a function of the pilot fold. Its value
  depends only on the finite cell labels, not on outcomes](goal). -/
lemma polynomialPilotHeavySet_measurable {n d : ℕ} (P : RealLaw d)
    (base : Obs d) :
    Measurable (polynomialPilotHeavySet (n := n) P base) := by
  let design : ((polynomialBalancedSplit P).foldA n → Obs d) →
      ((polynomialBalancedSplit P).foldA n → Fin d × Bool) :=
    fun x i => ((x i).x, (x i).a)
  let select : ((polynomialBalancedSplit P).foldA n → Fin d × Bool) →
      Finset (Fin d) := fun z =>
    Finset.univ.filter fun k =>
      256 * logEN n < (Finset.univ.filter fun i : Fin n =>
        inPilot i ∧
          (if h : i.val < n / 2 then
            (z ⟨i.val, by
              simpa [Causalean.Stat.OneShotSplit.foldA,
                polynomialBalancedSplit] using h⟩).1
          else base.x) = k).card
  have hdesign : Measurable design := by
    apply measurable_pi_lambda
    intro i
    have hobs : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
      measurable_iff_comap_le.mpr le_rfl
    have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp hobs
    have ha : Measurable (fun o : Obs d => o.a) :=
      measurable_fst.comp (measurable_snd.comp hobs)
    exact (hx.prodMk ha).comp (measurable_pi_apply i)
  have hselect : Measurable select := measurable_of_finite _
  have heq : polynomialPilotHeavySet (n := n) P base = select ∘ design := by
    funext x
    ext k
    simp only [polynomialPilotHeavySet, select, design, Function.comp_apply,
      Finset.mem_filter, Finset.mem_univ, true_and]
    change (256 * logEN n <
        ((Finset.univ.filter fun i : Fin n => inPilot i ∧
          (rebuildPolynomialPilotSample P base x i).x = k).card : ℝ)) ↔
      256 * logEN n <
        ((Finset.univ.filter fun i : Fin n => inPilot i ∧
          (if h : i.val < n / 2 then (x ⟨i.val, by
            simpa [Causalean.Stat.OneShotSplit.foldA,
              polynomialBalancedSplit] using h⟩).x else base.x) = k).card : ℝ)
    have hfilter :
        (Finset.univ.filter fun i : Fin n => inPilot i ∧
          (rebuildPolynomialPilotSample P base x i).x = k) =
        Finset.univ.filter fun i : Fin n => inPilot i ∧
          (if h : i.val < n / 2 then (x ⟨i.val, by
            simpa [Causalean.Stat.OneShotSplit.foldA,
              polynomialBalancedSplit] using h⟩).x else base.x) = k := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi : i.val < n / 2 <;>
        simp [rebuildPolynomialPilotSample, hi]
    rw [hfilter]
  rw [heq]
  exact hselect.comp hdesign

-- @node: polynomialSelectorEligible
/-- A deterministic selector value is eligible when every selected-heavy cell
lies above the lower pilot band and every complementary light cell lies below
the upper pilot band. -/
def polynomialSelectorEligible {d : ℕ} (P : RealLaw d)
    (lowerBand upperBand : ℝ) (H : Finset (Fin d)) : Prop :=
  (∀ k ∈ H, lowerBand ≤ P.cellMass k) ∧
    (∀ k ∉ H, P.cellMass k ≤ upperBand)

-- @node: polynomialPilotFoldGood
/-- The fold-level good event is the measurable preimage of the eligible
finite selector values. -/
def polynomialPilotFoldGood {n d : ℕ} (P : RealLaw d) (base : Obs d)
    (lowerBand upperBand : ℝ) :
    Set ((polynomialBalancedSplit P).foldA n → Obs d) :=
  {x | polynomialSelectorEligible P lowerBand upperBand
    (polynomialPilotHeavySet P base x)}

-- @node: polynomialPilotFoldGood_measurable
/-- [Eligibility of the pilot-selected heavy set is a measurable event on the finite pilot
  fold](goal). -/
lemma polynomialPilotFoldGood_measurable {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (lowerBand upperBand : ℝ) :
    MeasurableSet (polynomialPilotFoldGood (n := n) P base lowerBand upperBand) := by
  classical
  let eligible : Finset (Fin d) → Bool := fun H =>
    decide (polynomialSelectorEligible P lowerBand upperBand H)
  have heligible : Measurable eligible := measurable_of_finite _
  have heq : polynomialPilotFoldGood (n := n) P base lowerBand upperBand =
      (eligible ∘ polynomialPilotHeavySet P base) ⁻¹' {true} := by
    ext x
    simp [polynomialPilotFoldGood, eligible]
  rw [heq]
  exact (heligible.comp (polynomialPilotHeavySet_measurable P base))
    (measurableSet_singleton true)

-- @node: polynomialFixedHeavyError
/-- Normalized heavy error for a deterministic pilot-selected set, evaluated
only on the independent estimation fold. -/
noncomputable def polynomialFixedHeavyError {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (M : ℝ) (H : Finset (Fin d))
    (x : (polynomialBalancedSplit P).foldB n → Obs d) : ℝ :=
  ∑ k ∈ H, (
    heavyEmpiricalTerm M (rebuildPolynomialEstimationSample P base x) k -
      P.cellMass k * cellEffect P k / M)

-- @node: polynomialFixedLightError
/-- Normalized light error for the complementary deterministic set, evaluated
only on the independent estimation fold. -/
noncomputable def polynomialFixedLightError {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (M : ℝ) (H : Finset (Fin d))
    (x : (polynomialBalancedSplit P).foldB n → Obs d) : ℝ :=
  let K := polynomialDegree n
  let B := 4096 * logEN n / (n - n / 2 : ℕ)
  ∑ k : Fin d, if k ∈ H then 0 else
    lightPolynomialTerm M B K (rebuildPolynomialEstimationSample P base x) k -
      P.cellMass k * cellEffect P k / M

-- @node: polynomialFixedHeavyError_measurable
/-- [Every deterministic heavy-branch error is measurable on the independent estimation
  fold](goal). -/
lemma polynomialFixedHeavyError_measurable {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (M : ℝ) (H : Finset (Fin d)) :
    Measurable (polynomialFixedHeavyError (n := n) P base M H) := by
  unfold polynomialFixedHeavyError
  apply Finset.measurable_sum
  intro k _
  exact ((measurable_heavyEmpiricalTerm M k).comp
    (rebuildPolynomialEstimationSample_measurable P base)).sub measurable_const

-- @node: polynomialFixedLightError_measurable
/-- [Every deterministic complementary light-branch error is measurable on the independent
  estimation fold](goal). -/
lemma polynomialFixedLightError_measurable {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (M : ℝ) (H : Finset (Fin d)) :
    Measurable (polynomialFixedLightError (n := n) P base M H) := by
  unfold polynomialFixedLightError
  apply Finset.measurable_sum
  intro k _
  by_cases hk : k ∈ H
  · simp only [if_pos hk]
    exact measurable_const
  · simp only [if_neg hk]
    exact ((measurable_lightPolynomialTerm M
      (4096 * logEN n / (n - n / 2 : ℕ)) (polynomialDegree n) k).comp
        (rebuildPolynomialEstimationSample_measurable P base)).sub measurable_const

-- @node: polynomialFixedTotalError
/-- The fixed-selector branch error combines the heavy score on the selected
set with the polynomial score on its complement. -/
noncomputable def polynomialFixedTotalError {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (M : ℝ) (H : Finset (Fin d))
    (x : (polynomialBalancedSplit P).foldB n → Obs d) : ℝ :=
  polynomialFixedHeavyError P base M H x +
    polynomialFixedLightError P base M H x

-- @node: polynomialFixedTotalError_measurable
/-- [Every fixed-selector total error is measurable on the estimation fold](goal). -/
lemma polynomialFixedTotalError_measurable {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (M : ℝ) (H : Finset (Fin d)) :
    Measurable (polynomialFixedTotalError (n := n) P base M H) := by
  exact (polynomialFixedHeavyError_measurable P base M H).add
    (polynomialFixedLightError_measurable P base M H)

-- @node: polynomialPilotHeavySet_iidPrefix
/-- [On the iid realization, the fold-valued selector is exactly the heavy set appearing in the
  concrete full-sample estimator](goal). -/
lemma polynomialPilotHeavySet_iidPrefix {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (omega : ℕ → Obs d) :
    polynomialPilotHeavySet P base
      (fun i : (polynomialBalancedSplit P).foldA n => omega i) =
      Finset.univ.filter (fun k =>
        256 * logEN n < pilotCount (fun i : Fin n => omega i) k) := by
  ext k
  simp only [polynomialPilotHeavySet, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [pilotCount_rebuildPolynomialPilot P base omega k]

-- @node: polynomialPilotGood_implies_foldGood
/-- If [the pilot event is good](hyp:hgood), [the simultaneous pilot sandwich event from the
  probability bound implies eligibility of the concrete finite selector on the pilot fold](goal). -/
lemma polynomialPilotGood_implies_foldGood {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (lowerBand upperBand : ℝ) (omega : ℕ → Obs d)
    (hgood : omega ∈ polynomialPilotGood (n := n) P lowerBand upperBand) :
    (fun i : (polynomialBalancedSplit P).foldA n => omega i) ∈
      polynomialPilotFoldGood P base lowerBand upperBand := by
  change polynomialSelectorEligible P lowerBand upperBand
    (polynomialPilotHeavySet P base
      (fun i : (polynomialBalancedSplit P).foldA n => omega i))
  unfold polynomialSelectorEligible
  rw [polynomialPilotHeavySet_iidPrefix P base omega]
  constructor
  · intro k hk
    exact polynomialPilotGood_selectedHeavy_lower P hgood k
      (by simpa using (Finset.mem_filter.mp hk).2)
  · intro k hk
    apply polynomialPilotGood_selectedLight_upper P hgood k
    intro hselected
    exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hselected⟩)

-- @node: polynomialFixedHeavyError_iidPrefix
/-- [Selecting the fixed-heavy branch with the pilot fold recovers the concrete selected-heavy
  error on the iid prefix](goal). -/
lemma polynomialFixedHeavyError_iidPrefix {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (omega : ℕ → Obs d) (M : ℝ) :
    polynomialFixedHeavyError P base M
      (polynomialPilotHeavySet P base
        (fun i : (polynomialBalancedSplit P).foldA n => omega i))
      (fun i : (polynomialBalancedSplit P).foldB n => omega i) =
      polynomialHeavySelectedError P M (fun i : Fin n => omega i) := by
  classical
  unfold polynomialFixedHeavyError polynomialHeavySelectedError
  rw [polynomialPilotHeavySet_iidPrefix P base omega]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  rw [heavyEmpiricalTerm_rebuildPolynomialEstimation P base omega M k]

-- @node: polynomialFixedLightError_iidPrefix
/-- [Selecting the complementary fixed-light branch with the pilot fold recovers the concrete
  selected-light error on the iid prefix](goal). -/
lemma polynomialFixedLightError_iidPrefix {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (omega : ℕ → Obs d) (M : ℝ) :
    polynomialFixedLightError P base M
      (polynomialPilotHeavySet P base
        (fun i : (polynomialBalancedSplit P).foldA n => omega i))
      (fun i : (polynomialBalancedSplit P).foldB n => omega i) =
      polynomialLightSelectedError P M (fun i : Fin n => omega i) := by
  classical
  unfold polynomialFixedLightError polynomialLightSelectedError
  rw [polynomialPilotHeavySet_iidPrefix P base omega]
  apply Finset.sum_congr rfl
  intro k _
  rw [lightPolynomialTerm_rebuildPolynomialEstimation P base omega]
  by_cases hk : 256 * logEN n < pilotCount (fun i : Fin n => omega i) k <;>
    simp [hk]

-- @node: polynomialFixedTotalError_iidPrefix
/-- [Selecting a fixed total branch with the pilot fold recovers the complete normalized
  pre-clipping error on the iid prefix](goal). -/
lemma polynomialFixedTotalError_iidPrefix {n d : ℕ} (P : RealLaw d)
    (base : Obs d) (omega : ℕ → Obs d) (M : ℝ) :
    polynomialFixedTotalError P base M
      (polynomialPilotHeavySet P base
        (fun i : (polynomialBalancedSplit P).foldA n => omega i))
      (fun i : (polynomialBalancedSplit P).foldB n => omega i) =
      polynomialNormalizedSum M (fun i : Fin n => omega i) -
        rawAteFormula P / M := by
  rw [polynomialNormalizedSum_sub_target_eq_selectedErrors,
    polynomialFixedTotalError, polynomialFixedHeavyError_iidPrefix,
    polynomialFixedLightError_iidPrefix]

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
