/- Canonical affine real-law construction for binary source experiments. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.AffineEmbedding
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Endpoint
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HeavyCellMoments

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
noncomputable section

private abbrev BinLaw := CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw
private abbrev BinObs := CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs
-- @node: binaryOutcomePMF
/-- This is the two-point outcome distribution with the specified success probability and affine
  outcome scale. -/
noncomputable def binaryOutcomePMF {d : ℕ} (P : BinLaw d) (a : Bool) (k : Fin d) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal
    (if b then CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k
      else 1 - CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k)) (by
    rw [Fintype.sum_bool]
    simp only [if_true, if_false]
    rw [← ENNReal.ofReal_add]
    · norm_num
    · exact (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean_mem_unitInterval
        P a k).1
    · simpa only [Bool.false_eq_true, if_false] using
        sub_nonneg.mpr
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean_mem_unitInterval
            P a k).2)

-- @node: binaryOutcomePMF_true_toReal
/-- [the binary outcome distribution assigns real probability p to the upper affine
  endpoint](goal). -/
lemma binaryOutcomePMF_true_toReal {d : ℕ} (P : BinLaw d) (a : Bool) (k : Fin d) :
    ((binaryOutcomePMF P a k) true).toReal =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k := by
  rw [binaryOutcomePMF, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean_mem_unitInterval P a k).1

-- @node: binaryOutcomePMF_false_toReal
/-- [the binary outcome distribution assigns real probability one minus p to the lower affine
  endpoint](goal). -/
lemma binaryOutcomePMF_false_toReal {d : ℕ} (P : BinLaw d) (a : Bool) (k : Fin d) :
    ((binaryOutcomePMF P a k) false).toReal =
      1 - CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k := by
  rw [binaryOutcomePMF, PMF.ofFintype_apply]
  rw [show (if false then
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k
    else 1 - CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k) =
      1 - CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k from rfl]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr
    (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean_mem_unitInterval P a k).2)

-- @node: binaryIndependentLift
/-- This augments an observed binary record with an independently drawn missing potential outcome. -/
def binaryIndependentLift {d : ℕ} (z : BinObs d) (other : Bool) : BinaryFullObs d :=
  if z.2.1 then ⟨z.1, true, other, z.2.2⟩ else ⟨z.1, false, z.2.2, other⟩

-- @node: binaryIndependentFullPMF
/-- This is the full-data probability mass function obtained by independently imputing the missing
  binary potential outcome. -/
noncomputable def binaryIndependentFullPMF {d : ℕ} (P : BinLaw d) : PMF (BinaryFullObs d) :=
  P.pmf.bind fun z =>
    (binaryOutcomePMF P (!z.2.1) z.1).map (binaryIndependentLift z)

-- @node: binaryIndependentLift_observed
/-- [projecting the independent full-data lift recovers the original observed binary
  record](goal). -/
lemma binaryIndependentLift_observed {d : ℕ} (z : BinObs d) (other : Bool) :
    (binaryIndependentLift z other).observed = z := by
  rcases z with ⟨k, a, y⟩
  cases a <;> rfl

-- @node: map_binaryIndependentFullPMF_observed
/-- [projecting the independent full-data distribution gives the original observed-data
  law](goal). -/
lemma map_binaryIndependentFullPMF_observed {d : ℕ} (P : BinLaw d) :
    (binaryIndependentFullPMF P).map BinaryFullObs.observed = P.pmf := by
  rw [binaryIndependentFullPMF, PMF.map_bind]
  simp_rw [PMF.map_comp]
  have hmap (z : BinObs d) :
      PMF.map (BinaryFullObs.observed ∘ binaryIndependentLift z)
          (binaryOutcomePMF P (!z.2.1) z.1) = PMF.pure z := by
    rw [← PMF.map_const]
    congr 1
    funext other
    exact binaryIndependentLift_observed z other
  simp_rw [hmap]
  exact PMF.bind_pure _

-- @node: realMass_map_binaryOutcomePMF
/-- If [the specified event is measurable](hyp:hs), [the affine image of the binary outcome
  distribution assigns each endpoint its binary probability](goal). -/
lemma realMass_map_binaryOutcomePMF {d : ℕ} (M : ℝ) (P : BinLaw d)
    (a : Bool) (k : Fin d) (s : Set ℝ) (hs : MeasurableSet s) :
    realMass (((binaryOutcomePMF P a k).map
      (fun b => M * ((if b then 1 else 0) - 1 / 2))).toMeasure) s =
      ∑ b : Bool, s.indicator (fun _ => ((binaryOutcomePMF P a k) b).toReal)
        (M * ((if b then 1 else 0) - 1 / 2)) := by
  classical
  have hscale : Measurable
      (fun b : Bool => M * ((if b then 1 else 0) - 1 / 2)) := by fun_prop
  unfold realMass
  rw [← PMF.toMeasure_map _ _ hscale]
  rw [Measure.map_apply_of_aemeasurable hscale.aemeasurable hs]
  rw [PMF.toMeasure_apply _ MeasurableSet.of_discrete]
  simp only [Set.indicator, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · simp_rw [apply_ite]
    simp [Set.indicator]
  · intro b
    split_ifs <;> simp [PMF.apply_ne_top]

-- @node: realMass_affineObserved_event
/-- If [the specified event is measurable](hyp:hs), [the affine observed-data pushforward assigns
  each arm-cell-outcome event the corresponding binary joint probability](goal). -/
lemma realMass_affineObserved_event {d : ℕ} (M : ℝ) (P : BinLaw d)
    (k : Fin d) (a : Bool) (s : Set ℝ) (hs : MeasurableSet s) :
    realMass ((P.pmf.map (affineObserved M)).toMeasure)
        {o | o.x = k ∧ o.a = a ∧ o.y ∈ s} =
      ∑ y : Bool, s.indicator (fun _ =>
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a y)
        (M * ((if y then 1 else 0) - 1 / 2)) := by
  classical
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
  have ha : Measurable (fun o : Obs d => o.a) := measurable_fst.comp htuple.snd
  have hy : Measurable (fun o : Obs d => o.y) := htuple.snd.snd
  have hevent : MeasurableSet {o : Obs d | o.x = k ∧ o.a = a ∧ o.y ∈ s} :=
    ((measurableSet_singleton k).preimage hx).inter
      (((measurableSet_singleton a).preimage ha).inter (hs.preimage hy))
  unfold realMass
  rw [← PMF.toMeasure_map _ _ (measurable_affineObserved M)]
  rw [Measure.map_apply_of_aemeasurable
    (measurable_affineObserved M).aemeasurable hevent]
  rw [PMF.toMeasure_apply _ MeasurableSet.of_discrete]
  simp only [Set.indicator, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · simp_rw [apply_ite]
    simp only [CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single k]
    · rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single a]
      · simp [affineObserved, Set.indicator]
      · intro b _ hba
        simp [affineObserved, hba]
      · simp
    · intro l _ hlk
      simp [affineObserved, hlk]
    · simp
  · intro z
    split_ifs <;> simp [PMF.apply_ne_top]

-- @node: affineBinaryRealLaw
/-- This construction embeds a binary-outcome observational law into a real-outcome law by affine
  outcome scaling and an independent full-data coupling. -/
noncomputable def affineBinaryRealLaw {d : ℕ} (M : ℝ) (P : BinLaw d) : RealLaw d where
  observedLaw := (P.pmf.map (affineObserved M)).toMeasure
  observed_isProbability := by infer_instance
  fullLaw := ((binaryIndependentFullPMF P).map
    (BinaryFullObs.affine M (fun k => k))).toMeasure
  full_isProbability := by infer_instance
  cellMass := CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P
  propensity := CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P
  outcomeLaw := fun a k =>
    ((binaryOutcomePMF P a k).map
      (fun b => M * ((if b then 1 else 0) - 1 / 2))).toMeasure
  outcome_isProbability := by intro; infer_instance
  outcomeMean := fun a k => M *
    (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k - 1 / 2)
  observed_margin := by
    rw [PMF.toMeasure_map]
    congr 1
    rw [← map_binaryIndependentFullPMF_observed P, PMF.map_comp, PMF.map_comp]
    congr 1
    funext z
    exact observed_affine_binaryFullObs M z
    fun_prop
  cellMass_eq := by
    intro k
    have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) := by
      rw [measurable_iff_comap_le]
      rfl
    have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
    have hs : MeasurableSet {o : Obs d | o.x = k} :=
      (measurableSet_singleton k).preimage hx
    unfold realMass
    rw [← PMF.toMeasure_map (affineObserved M) P.pmf (measurable_affineObserved M)]
    rw [Measure.map_apply_of_aemeasurable (measurable_affineObserved M).aemeasurable hs]
    rw [PMF.toMeasure_apply P.pmf MeasurableSet.of_discrete]
    simp [CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass,
      affineObserved, Set.indicator]
    rw [ENNReal.toReal_sum]
    · simp_rw [apply_ite]
      simp only [Fintype.sum_prod_type]
      symm
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hbk
        simp [hbk]
      · simp
    · intro a
      split_ifs <;> simp [PMF.apply_ne_top]
  cellMass_range := CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass_mem_unitInterval P
  propensity_range := CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity_mem_unitInterval P
  arm_outcome_factorization := by
    intro a k s hs
    rw [realMass_map_binaryOutcomePMF M P a k s hs,
      realMass_affineObserved_event M P k a s hs]
    by_cases hp : 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k
    · have hfactor :
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k *
              (if a then CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P k
                else 1 - CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P k) =
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a := by
        have hpne : CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k ≠ 0 :=
          ne_of_gt hp
        cases a with
        | false =>
            have hadd :=
              CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass_add_eq_cellMass P k
            simp only [Bool.false_eq_true, if_false]
            rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity]
            field_simp [hpne]
            nlinarith
        | true =>
            simp only [if_true]
            rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity]
            field_simp [hpne]
      rw [hfactor, Fintype.sum_bool, Fintype.sum_bool,
        binaryOutcomePMF_true_toReal, binaryOutcomePMF_false_toReal]
      have htrue :=
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass_true_eq_outcomeMean_mul_armMass
          P k a
      have hsum : CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a =
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a false +
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a true := by
        simp [CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass, add_comm]
      simp only [if_pos True.intro, if_neg Bool.false_ne_true]
      by_cases ht : M * (1 - (1 : ℝ) / 2) ∈ s
      · simp only [Set.indicator_of_mem ht]
        by_cases hf : M * (0 - (1 : ℝ) / 2) ∈ s
        · simp only [Set.indicator_of_mem hf]
          nlinarith
        · simp only [Set.indicator_of_notMem hf]
          nlinarith
      · simp only [Set.indicator_of_notMem ht]
        by_cases hf : M * (0 - (1 : ℝ) / 2) ∈ s
        · simp only [Set.indicator_of_mem hf]
          nlinarith
        · simp only [Set.indicator_of_notMem hf]
          nlinarith
    · have hp0 : CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k = 0 :=
        le_antisymm (le_of_not_gt hp)
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass_mem_unitInterval P k).1
      have hj (y : Bool) :
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a y = 0 :=
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass_eq_zero_of_cellMass_eq_zero
          P k hp0 a y
      simp [hp0, hj, Set.indicator]
  outcomeMean_eq := by
    intro a k
    have hscale : Measurable
        (fun b : Bool => M * ((if b then 1 else 0) - 1 / 2)) := by fun_prop
    rw [← PMF.toMeasure_map _ _ hscale]
    rw [integral_map hscale.aemeasurable (by fun_prop)]
    rw [PMF.integral_eq_sum]
    rw [Fintype.sum_bool, binaryOutcomePMF_true_toReal,
      binaryOutcomePMF_false_toReal]
    simp
    ring

-- @node: binaryOutcomePMF_toMeasure_eq_conditional
/-- If [the stated pos condition holds](hyp:hpos), [the measure induced by the binary outcome
  distribution equals the corresponding conditional outcome law](goal). -/
lemma binaryOutcomePMF_toMeasure_eq_conditional {d : ℕ} (P : BinLaw d)
    (a : Bool) (k : Fin d)
    (hpos : 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a) :
    (binaryOutcomePMF P a k).toMeasure = binaryConditionalOutcomeLaw P a k := by
  classical
  have hsum : CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a false +
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a true := by
    simp [CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass, add_comm]
  have hfalse : 1 -
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a true /
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a false /
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a := by
    field_simp [ne_of_gt hpos]
    linarith
  ext s hs
  rw [PMF.toMeasure_apply _ hs]
  unfold binaryConditionalOutcomeLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply' _ hs, tsum_fintype, Fintype.sum_bool]
  by_cases ht : true ∈ s <;> by_cases hf : false ∈ s <;>
    simp [Set.indicator, ht, hf, binaryOutcomePMF, PMF.ofFintype_apply,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean, hfalse, add_comm]

-- @node: affineBinaryRealLaw_embedding
/-- [the affine real-outcome construction satisfies the binary embedding identities for cell
  probabilities, propensities, and conditional means](goal). -/
lemma affineBinaryRealLaw_embedding {d : ℕ} (M : ℝ) (P : BinLaw d) :
    AffineBinaryEmbedding M P (affineBinaryRealLaw M P) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (PMF.toMeasure_map (affineObserved M) P.pmf
      (measurable_affineObserved M)).symm
  · intro k
    rfl
  · intro k
    rfl
  · intro a k hpos
    rw [← binaryOutcomePMF_toMeasure_eq_conditional P a k hpos]
    exact (PMF.toMeasure_map _ _ (by fun_prop)).symm
  · intro a k
    rfl
  · refine ⟨(binaryIndependentFullPMF P).toMeasure, ?_, ?_⟩
    · constructor
      · infer_instance
      · rw [PMF.toMeasure_map BinaryFullObs.observed _ (measurable_of_finite _)]
        exact congrArg PMF.toMeasure (map_binaryIndependentFullPMF_observed P)
    · exact (PMF.toMeasure_map _ _ (by fun_prop)).symm

-- @node: binaryIndependentFullPMF_apply_toReal
/-- [the real probability assigned to a full-data atom factors into its observed-atom probability
  and the independent missing-potential probability](goal). -/
lemma binaryIndependentFullPMF_apply_toReal {d : ℕ} (P : BinLaw d)
    (z : BinaryFullObs d) :
    ((binaryIndependentFullPMF P) z).toReal =
      if z.a then
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P z.x true z.b1 *
          ((binaryOutcomePMF P false z.x) z.b0).toReal
      else
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P z.x false z.b0 *
          ((binaryOutcomePMF P true z.x) z.b1).toReal := by
  rcases z with ⟨x, a, b0, b1⟩
  cases a <;> cases b0 <;> cases b1 <;>
    simp only [binaryIndependentFullPMF, PMF.bind_apply, PMF.map_apply,
      binaryIndependentLift, CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass,
      tsum_fintype, Fintype.sum_prod_type, Bool.false_eq_true, if_false,
      if_true]
  all_goals
    rw [Finset.sum_eq_single x]
    · simp [ENNReal.toReal_mul]
    · intro y _ hy
      simp [binaryIndependentLift, Ne.symm hy]
    · simp

-- @node: affineBinaryRealLaw_consistency
/-- [the affine binary real law satisfies consistency](goal). -/
lemma affineBinaryRealLaw_consistency {d : ℕ} (M : ℝ) (P : BinLaw d) :
    Consistency (affineBinaryRealLaw M P) := by
  unfold Consistency
  change ((PMF.map (BinaryFullObs.affine M (fun k => k))
    (binaryIndependentFullPMF P)).toMeasure) _ = 0
  rw [← PMF.toMeasure_map _ _ (by fun_prop)]
  have htuple : Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  have ha : Measurable (fun z : FullObs d => z.a) := htuple.snd.fst
  have hy0 : Measurable (fun z : FullObs d => z.y0) := htuple.snd.snd.fst
  have hy1 : Measurable (fun z : FullObs d => z.y1) := htuple.snd.snd.snd.fst
  have hy : Measurable (fun z : FullObs d => z.y) := htuple.snd.snd.snd.snd
  have hevent : MeasurableSet
      {z : FullObs d | z.y ≠ if z.a then z.y1 else z.y0} := by
    have hf : Measurable (fun z : FullObs d =>
        z.y - if z.a then z.y1 else z.y0) := by
      apply hy.sub
      exact Measurable.ite ((measurableSet_singleton true).preimage ha) hy1 hy0
    have hz := (measurableSet_singleton (0 : ℝ)).compl.preimage hf
    have heq : {z : FullObs d | z.y ≠ if z.a then z.y1 else z.y0} =
        ((fun z : FullObs d => z.y - if z.a then z.y1 else z.y0) ⁻¹' {0})ᶜ := by
      ext z
      simp [sub_eq_zero]
    rw [heq]
    exact hz
  rw [Measure.map_apply_of_aemeasurable (by fun_prop) hevent]
  have hempty : (BinaryFullObs.affine M (fun k => k)) ⁻¹'
      {z : FullObs d | z.y ≠ if z.a then z.y1 else z.y0} = ∅ := by
    ext z
    rcases z with ⟨x, a, b0, b1⟩
    cases a <;> simp [BinaryFullObs.affine]
  rw [hempty]
  simp

set_option maxHeartbeats 800000 in
-- The finite four-bit expansion creates many polynomial branches.
-- @node: affineBinaryRealLaw_exchangeability
/-- [The independent missing-potential-outcome augmentation makes the affine full-data law
  conditionally exchangeable](goal). -/
lemma affineBinaryRealLaw_exchangeability {d : ℕ} (M : ℝ) (P : BinLaw d) :
    ConditionalExchangeability (affineBinaryRealLaw M P) := by
  unfold ConditionalExchangeability
  intro k a s0 s1 hs0 hs1
  change ((PMF.map (BinaryFullObs.affine M (fun k => k))
      (binaryIndependentFullPMF P)).toMeasure) _ *
    ((PMF.map (BinaryFullObs.affine M (fun k => k))
      (binaryIndependentFullPMF P)).toMeasure) _ =
    ((PMF.map (BinaryFullObs.affine M (fun k => k))
      (binaryIndependentFullPMF P)).toMeasure) _ *
    ((PMF.map (BinaryFullObs.affine M (fun k => k))
      (binaryIndependentFullPMF P)).toMeasure) _
  have hx : MeasurableSet {z : FullObs d | z.x = k} :=
    (measurableSet_singleton k).preimage measurable_full_x
  have harm : MeasurableSet {z : FullObs d | z.x = k ∧ z.a = a} :=
    hx.inter ((measurableSet_singleton a).preimage measurable_full_a)
  have hpot : MeasurableSet
      {z : FullObs d | z.x = k ∧ z.y0 ∈ s0 ∧ z.y1 ∈ s1} :=
    hx.inter ((hs0.preimage measurable_full_y0).inter
      (hs1.preimage measurable_full_y1))
  have hjoint : MeasurableSet
      {z : FullObs d | z.x = k ∧ z.a = a ∧ z.y0 ∈ s0 ∧ z.y1 ∈ s1} :=
    hx.inter (((measurableSet_singleton a).preimage measurable_full_a).inter
      ((hs0.preimage measurable_full_y0).inter (hs1.preimage measurable_full_y1)))
  have hmap (E : Set (FullObs d)) (hE : MeasurableSet E) :
      ((PMF.map (BinaryFullObs.affine M (fun k => k))
        (binaryIndependentFullPMF P)).toMeasure) E =
      (binaryIndependentFullPMF P).toMeasure
        ((BinaryFullObs.affine M (fun k => k)) ⁻¹' E) := by
    rw [← PMF.toMeasure_map _ _ (by fun_prop)]
    exact Measure.map_apply (by fun_prop) hE
  rw [hmap _ hjoint, hmap _ hx, hmap _ harm, hmap _ hpot]
  rw [PMF.toMeasure_apply _ MeasurableSet.of_discrete,
    PMF.toMeasure_apply _ MeasurableSet.of_discrete,
    PMF.toMeasure_apply _ MeasurableSet.of_discrete,
    PMF.toMeasure_apply _ MeasurableSet.of_discrete]
  simp only [tsum_fintype]
  classical
  have hsum (E : Set (BinaryFullObs d)) :
      (∑ x, E.indicator (⇑(binaryIndependentFullPMF P)) x) ≠ ∞ := by
    apply (ENNReal.sum_ne_top).2
    intro x hx
    simp only [Set.indicator]
    split
    · exact (binaryIndependentFullPMF P).apply_ne_top x
    · simp
  rw [← ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top (hsum _) (hsum _))
    (ENNReal.mul_ne_top (hsum _) (hsum _))]
  simp_rw [ENNReal.toReal_mul]
  have htoReal (E : Set (BinaryFullObs d)) :
      (∑ x, E.indicator (⇑(binaryIndependentFullPMF P)) x).toReal =
        ∑ x, (E.indicator (⇑(binaryIndependentFullPMF P)) x).toReal := by
    apply ENNReal.toReal_sum
    intro x hx
    simp only [Set.indicator]
    split
    · exact (binaryIndependentFullPMF P).apply_ne_top x
    · simp
  simp_rw [htoReal]
  simp only [Set.indicator]
  simp_rw [apply_ite, ENNReal.toReal_zero,
    binaryIndependentFullPMF_apply_toReal]
  let e : (Fin d × Bool × Bool × Bool) ≃ BinaryFullObs d := {
    toFun := fun z => ⟨z.1, z.2.1, z.2.2.1, z.2.2.2⟩
    invFun := fun z => (z.x, z.a, z.b0, z.b1)
    left_inv := by intro z; rcases z with ⟨x, a, b0, b1⟩; rfl
    right_inv := by intro z; rcases z with ⟨x, a, b0, b1⟩; rfl }
  simp_rw [← e.sum_comp]
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have sum_cell (f : Fin d → ℝ) (hf : ∀ x, x ≠ k → f x = 0) :
      (∑ x, f x) = f k := by
    apply Finset.sum_eq_single k
    · intro x hx hne
      exact hf x hne
    · simp
  repeat' rw [sum_cell _ (by
    intro x hx
    simp [e, BinaryFullObs.affine, hx])]
  have hrel (b : Bool) :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k b true =
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P b k *
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k b false +
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k b true) := by
    calc
      _ = CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P b k *
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k b :=
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass_true_eq_outcomeMean_mul_armMass
          P k b
      _ = _ := by
        rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass, Fintype.sum_bool]
        ring
  have hrel_mul (b c y : Bool) :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k b true *
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k c y =
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P b k *
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k b false +
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k b true)) *
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k c y := by
    exact congrArg (fun r => r *
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k c y) (hrel b)
  cases a <;>
    simp [e, BinaryFullObs.affine, binaryOutcomePMF_true_toReal,
      binaryOutcomePMF_false_toReal] <;>
    split_ifs <;> nlinarith [hrel false, hrel true,
      hrel_mul false true false, hrel_mul false true true,
      hrel_mul true false false, hrel_mul true false true]

end

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
