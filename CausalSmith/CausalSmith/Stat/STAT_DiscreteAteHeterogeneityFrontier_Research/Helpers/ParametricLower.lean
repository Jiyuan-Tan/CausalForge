/- One-cell real-outcome construction and Le Cam transfer for the parametric lower bound. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Basic
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmParametric
import Causalean.Mathlib.Probability.SignedTwoPoint

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

-- @node: testFullAtom
/-- This is the full-data atom used in the parametric two-point lower-bound experiment. -/
noncomputable def testFullAtom {d : ℕ} (k : Fin d) (a : Bool) (y : ℝ) : FullObs d :=
  ⟨k, a, 0, y, if a then y else 0⟩

-- @node: measurable_testFullAtom
/-- [the parametric full-data atom is measurable as a function of its outcome](goal). -/
lemma measurable_testFullAtom {d : ℕ} (k : Fin d) (a : Bool) :
    Measurable (testFullAtom k a) := by
  cases a
  · rw [measurable_comap_iff]
    change Measurable (fun y : ℝ => (k, false, 0, y, 0))
    fun_prop
  · rw [measurable_comap_iff]
    change Measurable (fun y : ℝ => (k, true, 0, y, y))
    fun_prop

-- @node: measurable_fullObserved
/-- [the projection from full data to observed data is measurable](goal). -/
lemma measurable_fullObserved {d : ℕ} : Measurable (FullObs.observed : FullObs d → Obs d) := by
  have htuple : Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  rw [measurable_comap_iff]
  change Measurable (fun z : FullObs d => (z.x, z.a, z.y))
  have hx : Measurable (fun z : FullObs d => z.x) := measurable_fst.comp htuple
  have ha : Measurable (fun z : FullObs d => z.a) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hy : Measurable (fun z : FullObs d => z.y) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp htuple)))
  exact Measurable.prod hx (Measurable.prod ha hy)

attribute [fun_prop] measurable_testFullAtom measurable_fullObserved

-- @node: measurable_full_x
/-- [the full-data covariate coordinate is measurable](goal). -/
lemma measurable_full_x {d : ℕ} : Measurable (fun z : FullObs d => z.x) := by
  have h : Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) := by
    rw [measurable_iff_comap_le]; rfl
  exact measurable_fst.comp h

-- @node: measurable_full_a
/-- [the full-data treatment coordinate is measurable](goal). -/
lemma measurable_full_a {d : ℕ} : Measurable (fun z : FullObs d => z.a) := by
  have h : Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) := by
    rw [measurable_iff_comap_le]; rfl
  exact measurable_fst.comp (measurable_snd.comp h)

-- @node: measurable_full_y0
/-- [the control potential-outcome coordinate is measurable](goal). -/
lemma measurable_full_y0 {d : ℕ} : Measurable (fun z : FullObs d => z.y0) := by
  have h : Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) := by
    rw [measurable_iff_comap_le]; rfl
  exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp h))

-- @node: measurable_full_y1
/-- [the treated potential-outcome coordinate is measurable](goal). -/
lemma measurable_full_y1 {d : ℕ} : Measurable (fun z : FullObs d => z.y1) := by
  have h : Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) := by
    rw [measurable_iff_comap_le]; rfl
  exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp h)))

-- @node: measurable_full_y
/-- [the observed-outcome coordinate on full data is measurable](goal). -/
lemma measurable_full_y {d : ℕ} : Measurable (fun z : FullObs d => z.y) := by
  have h : Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) := by
    rw [measurable_iff_comap_le]; rfl
  exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp h)))

-- @node: testFullLaw
/-- This is the full-data law of the parametric two-point experiment. -/
noncomputable def testFullLaw {d : ℕ} (k : Fin d) (B u : ℝ) : Measure (FullObs d) :=
  (2 : ENNReal)⁻¹ • Measure.map (testFullAtom k false)
      (Causalean.Mathlib.Probability.twoPointMean B u) +
  (2 : ENNReal)⁻¹ • Measure.map (testFullAtom k true)
      (Causalean.Mathlib.Probability.twoPointMean B u)

-- @node: testFullLaw_prob
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the test full law is a probability measure](goal). -/
lemma testFullLaw_prob {d : ℕ} (k : Fin d) {B u : ℝ}
    (hB : 0 < B) (hu : |u| ≤ B) : IsProbabilityMeasure (testFullLaw k B u) := by
  letI : IsProbabilityMeasure (Causalean.Mathlib.Probability.twoPointMean B u) :=
    Causalean.Mathlib.Probability.twoPointMean_isProbabilityMeasure hB hu
  rw [isProbabilityMeasure_iff, testFullLaw, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply]
  rw [Measure.map_apply (measurable_testFullAtom k false) MeasurableSet.univ,
    Measure.map_apply (measurable_testFullAtom k true) MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, smul_eq_mul, mul_one]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

-- @node: testObsAtom
/-- This is the observed-data atom associated with the parametric full-data atom. -/
noncomputable def testObsAtom {d : ℕ} (k : Fin d) (a : Bool) (y : ℝ) : Obs d :=
  ⟨k, a, y⟩

-- @node: measurable_testObsAtom
/-- [the parametric observed-data atom is measurable as a function of its outcome](goal). -/
lemma measurable_testObsAtom {d : ℕ} (k : Fin d) (a : Bool) :
    Measurable (testObsAtom k a) := by
  rw [measurable_comap_iff]
  change Measurable (fun y : ℝ => (k, a, y))
  fun_prop

-- @node: measurable_obs_x
/-- [the observed covariate coordinate is measurable](goal). -/
lemma measurable_obs_x {d : ℕ} : Measurable (fun o : Obs d => o.x) := by
  exact measurable_fst.comp (measurable_iff_comap_le.mpr le_rfl)

-- @node: measurable_obs_a
/-- [the observed treatment coordinate is measurable](goal). -/
lemma measurable_obs_a {d : ℕ} : Measurable (fun o : Obs d => o.a) := by
  exact measurable_fst.comp (measurable_snd.comp (measurable_iff_comap_le.mpr le_rfl))

/-- [the observed outcome coordinate is measurable](goal). -/
lemma measurable_obs_y {d : ℕ} : Measurable (fun o : Obs d => o.y) := by
  exact measurable_snd.comp (measurable_snd.comp (measurable_iff_comap_le.mpr le_rfl))

-- @node: testObservedLaw
/-- This is the observed-data margin of the parametric two-point experiment. -/
noncomputable def testObservedLaw {d : ℕ} (k : Fin d) (B u : ℝ) : Measure (Obs d) :=
  (2 : ENNReal)⁻¹ • Measure.dirac (testObsAtom k false 0) +
  (2 : ENNReal)⁻¹ • Measure.map (testObsAtom k true)
      (Causalean.Mathlib.Probability.twoPointMean B u)

-- @node: testObservedLaw_prob
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the test observed law is a probability measure](goal). -/
lemma testObservedLaw_prob {d : ℕ} (k : Fin d) {B u : ℝ}
    (hB : 0 < B) (hu : |u| ≤ B) : IsProbabilityMeasure (testObservedLaw k B u) := by
  letI : IsProbabilityMeasure (Causalean.Mathlib.Probability.twoPointMean B u) :=
    Causalean.Mathlib.Probability.twoPointMean_isProbabilityMeasure hB hu
  rw [isProbabilityMeasure_iff, testObservedLaw, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_testObsAtom k true) MeasurableSet.univ]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ, Pi.one_apply,
    Set.preimage_univ, measure_univ, smul_eq_mul, mul_one]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

-- @node: test_observed_margin
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the observed margin of the parametric full-data law equals the constructed
  observed-data law](goal). -/
lemma test_observed_margin {d : ℕ} (k : Fin d) {B u : ℝ}
    (hB : 0 < B) (hu : |u| ≤ B) :
    Measure.map FullObs.observed (testFullLaw k B u) = testObservedLaw k B u := by
  letI : IsProbabilityMeasure (Causalean.Mathlib.Probability.twoPointMean B u) :=
    Causalean.Mathlib.Probability.twoPointMean_isProbabilityMeasure hB hu
  rw [testFullLaw, testObservedLaw, Measure.map_add]
  · rw [Measure.map_smul, Measure.map_smul, Measure.map_map,
      Measure.map_map]
    · congr 2
      · rw [show FullObs.observed ∘ testFullAtom k false =
            fun _ : ℝ => testObsAtom k false 0 by funext y; rfl,
          Measure.map_const, measure_univ, one_smul]
    all_goals first | exact measurable_fullObserved | fun_prop
  · exact measurable_fullObserved

-- @node: testOutcomeLaw
/-- This is the conditional outcome distribution in the parametric test model. -/
noncomputable def testOutcomeLaw (B u : ℝ) (a : Bool) : Measure ℝ :=
  if a then Causalean.Mathlib.Probability.twoPointMean B u else Measure.dirac 0

-- @node: testOutcomeLaw_prob
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the test outcome law is a probability measure](goal). -/
lemma testOutcomeLaw_prob {B u : ℝ} (hB : 0 < B) (hu : |u| ≤ B) (a : Bool) :
    IsProbabilityMeasure (testOutcomeLaw B u a) := by
  cases a
  · change IsProbabilityMeasure (Measure.dirac 0)
    infer_instance
  · simpa [testOutcomeLaw] using
      Causalean.Mathlib.Probability.twoPointMean_isProbabilityMeasure hB hu

-- @node: test_cellMass_eq
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the test law assigns unit cell probability to the designated cell and zero to
  every other cell](goal). -/
lemma test_cellMass_eq {d : ℕ} (k l : Fin d) {B u : ℝ}
    (hB : 0 < B) (hu : |u| ≤ B) :
    realMass (testObservedLaw k B u) {o | o.x = l} = if l = k then 1 else 0 := by
  letI : IsProbabilityMeasure (Causalean.Mathlib.Probability.twoPointMean B u) :=
    Causalean.Mathlib.Probability.twoPointMean_isProbabilityMeasure hB hu
  have hs : MeasurableSet {o : Obs d | o.x = l} := by
    have ht : Measurable (fun o : Obs d => (o.x, o.a, o.y)) := by
      rw [measurable_iff_comap_le]
      rfl
    exact (measurableSet_singleton l).preimage (measurable_fst.comp ht)
  rw [realMass, testObservedLaw, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_testObsAtom k true) hs]
  by_cases hl : l = k
  · subst l
    simp only [Measure.dirac_apply' _ hs, Set.mem_setOf_eq, testObsAtom,
      Set.preimage_setOf_eq, true_iff, if_true]
    simp [ENNReal.toReal_add, ENNReal.toReal_mul]
    rw [← two_mul]
    norm_num
  · have hkl : k ≠ l := Ne.symm hl
    simp [Measure.dirac_apply' _ hs, testObsAtom, hl, hkl]

-- @node: test_outcomeMean
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the test outcome mean is the local mean in the treated arm and zero in the
  control arm](goal). -/
lemma test_outcomeMean {B u : ℝ} (hB : 0 < B) (hu : |u| ≤ B) (a : Bool) :
    ∫ y, y ∂testOutcomeLaw B u a = if a then u else 0 := by
  cases a
  · simp [testOutcomeLaw]
  · simpa [testOutcomeLaw] using
      Causalean.Mathlib.Probability.twoPointMean_mean hB hu

-- @node: testOutcome_second
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the conditional outcome law has an integrable squared centered outcome with
  second moment at most the squared outcome bound](goal). -/
lemma testOutcome_second {B u : ℝ} (hB : 0 < B) (hu : |u| ≤ B) (a : Bool) :
    Integrable (fun y => (y - if a then u else 0) ^ 2) (testOutcomeLaw B u a) ∧
      ∫ y, (y - if a then u else 0) ^ 2 ∂testOutcomeLaw B u a ≤ B ^ 2 := by
  cases a
  · constructor
    · simpa [testOutcomeLaw] using
        (integrable_dirac (f := fun y : ℝ => (y - 0) ^ 2) (a := 0) (by simp [enorm]))
    · simp [testOutcomeLaw]
      positivity
  · have hint : Integrable (fun y : ℝ => (y - u) ^ 2)
        (Causalean.Mathlib.Probability.twoPointMean B u) := by
      unfold Causalean.Mathlib.Probability.twoPointMean
      apply Integrable.add_measure
      · exact Integrable.smul_measure
          (integrable_dirac (f := fun y : ℝ => (y - u) ^ 2) (a := B)
            (by simp [enorm])) (by simp)
      · exact Integrable.smul_measure
          (integrable_dirac (f := fun y : ℝ => (y - u) ^ 2) (a := -B)
            (by simp [enorm])) (by simp)
    refine ⟨by simpa [testOutcomeLaw] using hint, ?_⟩
    rw [show testOutcomeLaw B u true =
      Causalean.Mathlib.Probability.twoPointMean B u by rfl,
      Causalean.Mathlib.Probability.twoPointMean_integral hB hu]
    have hcalc : ((1 + u / B) / 2) * (B - u) ^ 2 +
        ((1 - u / B) / 2) * (-B - u) ^ 2 = B ^ 2 - u ^ 2 := by
      field_simp [hB.ne']
      ring
    simp only [Bool.true_eq, if_true]
    rw [hcalc]
    nlinarith [sq_nonneg u]

-- @node: testRealLaw
/-- This assembles the real-outcome law for the parametric two-point experiment. -/
noncomputable def testRealLaw {d : ℕ} (k : Fin d) (B u : ℝ)
    (hB : 0 < B) (hu : |u| ≤ B) : RealLaw d where
  observedLaw := testObservedLaw k B u
  observed_isProbability := testObservedLaw_prob k hB hu
  fullLaw := testFullLaw k B u
  full_isProbability := testFullLaw_prob k hB hu
  cellMass := fun l => if l = k then 1 else 0
  propensity := fun _ => 1 / 2
  outcomeLaw := fun a _ => testOutcomeLaw B u a
  outcome_isProbability := fun a _ => testOutcomeLaw_prob hB hu a
  outcomeMean := fun a _ => if a then u else 0
  observed_margin := test_observed_margin k hB hu
  cellMass_eq := fun l => (test_cellMass_eq k l hB hu).symm
  cellMass_range := by
    intro l
    split <;> simp_all
  propensity_range := by norm_num
  arm_outcome_factorization := by
    intro a l s hs
    have hset : MeasurableSet {o : Obs d | o.x = l ∧ o.a = a ∧ o.y ∈ s} :=
      ((measurableSet_singleton l).preimage measurable_obs_x).inter
        (((measurableSet_singleton a).preimage measurable_obs_a).inter
          (hs.preimage measurable_obs_y))
    unfold realMass
    rw [testObservedLaw, Measure.add_apply,
      Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply (measurable_testObsAtom k true) hset]
    by_cases hl : l = k
    · subst l
      cases a
      · by_cases h0 : (0 : ℝ) ∈ s <;>
          simp [testOutcomeLaw, testObsAtom, Measure.dirac_apply' _ hset,
            ENNReal.toReal_add, ENNReal.toReal_mul, h0] <;> norm_num
      · simp [testOutcomeLaw, testObsAtom, Measure.dirac_apply' _ hset,
          ENNReal.toReal_add, ENNReal.toReal_mul]
    · have hkl : k ≠ l := Ne.symm hl
      cases a <;>
        simp [testOutcomeLaw, testObsAtom, Measure.dirac_apply' _ hset, hl, hkl]
  outcomeMean_eq := by
    intro a l
    exact (test_outcomeMean hB hu a).symm

-- @node: testRealLaw_rawAte
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the raw average-treatment-effect formula of the parametric test law equals its
  local mean parameter](goal). -/
lemma testRealLaw_rawAte {d : ℕ} (k : Fin d) {B u : ℝ}
    (hB : 0 < B) (hu : |u| ≤ B) : rawAteFormula (testRealLaw k B u hB hu) = u := by
  classical
  simp [rawAteFormula, cellEffect, testRealLaw]

-- @node: testRealLaw_consistency
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the test real law satisfies consistency](goal). -/
lemma testRealLaw_consistency {d : ℕ} (k : Fin d) {B u : ℝ}
    (hB : 0 < B) (hu : |u| ≤ B) : Consistency (testRealLaw k B u hB hu) := by
  unfold Consistency
  change testFullLaw k B u {z | z.y ≠ if z.a then z.y1 else z.y0} = 0
  have hsel : Measurable (fun z : FullObs d => if z.a then z.y1 else z.y0) := by
    apply Measurable.ite
    · exact (measurableSet_singleton true).preimage measurable_full_a
    · exact measurable_full_y1
    · exact measurable_full_y0
  have hbad : MeasurableSet {z : FullObs d | z.y ≠ if z.a then z.y1 else z.y0} :=
    (measurableSet_eq_fun measurable_full_y hsel).compl
  rw [testFullLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_testFullAtom k false) hbad,
    Measure.map_apply (measurable_testFullAtom k true) hbad]
  simp [testFullAtom]

-- @node: testFullLaw_joint
/-- If [the control-potential event is measurable](hyp:hs0) and [the treated-potential event is
  measurable](hyp:hs1), [the joint covariate-treatment-potential-outcome probability under the
  test law has the stated two-point formula](goal). -/
lemma testFullLaw_joint {d : ℕ} (k l : Fin d) {B u : ℝ} (a : Bool)
    {s0 s1 : Set ℝ} (hs0 : MeasurableSet s0) (hs1 : MeasurableSet s1) :
    testFullLaw k B u {z | z.x = l ∧ z.a = a ∧ z.y0 ∈ s0 ∧ z.y1 ∈ s1} =
      if l = k ∧ 0 ∈ s0 then
        (2 : ENNReal)⁻¹ * Causalean.Mathlib.Probability.twoPointMean B u s1
      else 0 := by
  have hset : MeasurableSet
      {z : FullObs d | z.x = l ∧ z.a = a ∧ z.y0 ∈ s0 ∧ z.y1 ∈ s1} :=
    ((measurableSet_singleton l).preimage measurable_full_x).inter
      (((measurableSet_singleton a).preimage measurable_full_a).inter
        ((hs0.preimage measurable_full_y0).inter (hs1.preimage measurable_full_y1)))
  rw [testFullLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_testFullAtom k false) hset,
    Measure.map_apply (measurable_testFullAtom k true) hset]
  by_cases hl : l = k
  · subst l
    by_cases h0 : (0 : ℝ) ∈ s0 <;> cases a <;>
      simp [testFullAtom, h0]
  · have hkl : k ≠ l := Ne.symm hl
    cases a <;> simp [testFullAtom, hl, hkl]

-- @node: testFullLaw_x
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the covariate marginal of the parametric full-data law is concentrated on the
  designated cell](goal). -/
lemma testFullLaw_x {d : ℕ} (k l : Fin d) {B u : ℝ}
    (hB : 0 < B) (hu : |u| ≤ B) :
    testFullLaw k B u {z | z.x = l} = if l = k then 1 else 0 := by
  letI : IsProbabilityMeasure (Causalean.Mathlib.Probability.twoPointMean B u) :=
    Causalean.Mathlib.Probability.twoPointMean_isProbabilityMeasure hB hu
  have hset : MeasurableSet {z : FullObs d | z.x = l} :=
    (measurableSet_singleton l).preimage measurable_full_x
  rw [testFullLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_testFullAtom k false) hset,
    Measure.map_apply (measurable_testFullAtom k true) hset]
  by_cases hl : l = k
  · subst l
    simp only [testFullAtom, Set.preimage_setOf_eq, true_iff, measure_univ, if_true,
      smul_eq_mul, mul_one]
    rw [show {a : ℝ | True} = Set.univ by ext; simp, measure_univ]
    simp only [mul_one]
    rw [← two_mul]
    exact ENNReal.mul_inv_cancel (a := (2 : ENNReal)) (by norm_num) (by norm_num)
  · have hkl : k ≠ l := Ne.symm hl
    simp [testFullAtom, hl, hkl]

-- @node: testFullLaw_arm
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the treatment-arm marginal of the parametric full-data law is one half](goal). -/
lemma testFullLaw_arm {d : ℕ} (k l : Fin d) {B u : ℝ} (a : Bool)
    (hB : 0 < B) (hu : |u| ≤ B) :
    testFullLaw k B u {z | z.x = l ∧ z.a = a} =
      if l = k then (2 : ENNReal)⁻¹ else 0 := by
  letI : IsProbabilityMeasure (Causalean.Mathlib.Probability.twoPointMean B u) :=
    Causalean.Mathlib.Probability.twoPointMean_isProbabilityMeasure hB hu
  have hset : MeasurableSet {z : FullObs d | z.x = l ∧ z.a = a} :=
    ((measurableSet_singleton l).preimage measurable_full_x).inter
      ((measurableSet_singleton a).preimage measurable_full_a)
  rw [testFullLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_testFullAtom k false) hset,
    Measure.map_apply (measurable_testFullAtom k true) hset]
  by_cases hl : l = k
  · subst l
    cases a <;> simp [testFullAtom]
  · have hkl : k ≠ l := Ne.symm hl
    cases a <;> simp [testFullAtom, hl, hkl]

-- @node: testFullLaw_potential
/-- If [the control-potential event is measurable](hyp:hs0) and [the treated-potential event is
  measurable](hyp:hs1), [the potential-outcome marginal of the parametric full-data law has the
  stated formula](goal). -/
lemma testFullLaw_potential {d : ℕ} (k l : Fin d) {B u : ℝ}
    {s0 s1 : Set ℝ} (hs0 : MeasurableSet s0) (hs1 : MeasurableSet s1) :
    testFullLaw k B u {z | z.x = l ∧ z.y0 ∈ s0 ∧ z.y1 ∈ s1} =
      if l = k ∧ 0 ∈ s0 then
        Causalean.Mathlib.Probability.twoPointMean B u s1 else 0 := by
  have hset : MeasurableSet {z : FullObs d | z.x = l ∧ z.y0 ∈ s0 ∧ z.y1 ∈ s1} :=
    ((measurableSet_singleton l).preimage measurable_full_x).inter
      ((hs0.preimage measurable_full_y0).inter (hs1.preimage measurable_full_y1))
  rw [testFullLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_testFullAtom k false) hset,
    Measure.map_apply (measurable_testFullAtom k true) hset]
  by_cases hl : l = k
  · subst l
    by_cases h0 : (0 : ℝ) ∈ s0
    · simp only [testFullAtom, Set.preimage_setOf_eq, true_and, h0, if_true,
        smul_eq_mul]
      rw [← add_mul, ← two_mul]
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      rfl
    · simp [testFullAtom, h0]
  · have hkl : k ≠ l := Ne.symm hl
    simp [testFullAtom, hl, hkl]

-- @node: testRealLaw_exchangeability
/-- If [the outcome bound is positive](hyp:hB) and [the local mean lies within the outcome
  bound](hyp:hu), [the parametric test law satisfies conditional exchangeability](goal). -/
lemma testRealLaw_exchangeability {d : ℕ} (k : Fin d) {B u : ℝ}
    (hB : 0 < B) (hu : |u| ≤ B) :
    ConditionalExchangeability (testRealLaw k B u hB hu) := by
  unfold ConditionalExchangeability
  intro l a s0 s1 hs0 hs1
  change testFullLaw k B u
        {z | z.x = l ∧ z.a = a ∧ z.y0 ∈ s0 ∧ z.y1 ∈ s1} *
      testFullLaw k B u {z | z.x = l} =
    testFullLaw k B u {z | z.x = l ∧ z.a = a} *
      testFullLaw k B u {z | z.x = l ∧ z.y0 ∈ s0 ∧ z.y1 ∈ s1}
  rw [testFullLaw_joint k l a hs0 hs1, testFullLaw_x k l hB hu,
    testFullLaw_arm k l a hB hu, testFullLaw_potential k l hs0 hs1]
  by_cases hl : l = k <;> by_cases h0 : (0 : ℝ) ∈ s0 <;>
    simp [hl, h0] <;> ring

-- @node: testModelClass
/-- This packages the parametric test law as a member of the heterogeneous model class. -/
noncomputable def testModelClass {d : ℕ} (k : Fin d)
    (epsilon M sigma u : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hM : 1 ≤ M) (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) (hu : |u| ≤ M / 2) :
    ModelClass d epsilon M sigma := by
  have hB : 0 < M / 2 := by positivity
  let P := testRealLaw k (M / 2) u hB hu
  refine {
    law := P
    epsilon_pos := he0
    epsilon_lt_half := he1
    M_ge_one := hM
    sigma_nonneg := hs0
    sigma_le_two := hs2
    consistency := testRealLaw_consistency k hB hu
    exchangeability := testRealLaw_exchangeability k hB hu
    overlap := ?_
    mean_normalization := ?_
    second_moment := ?_
    homogeneity := ?_ }
  · intro l hl
    have hlk : l = k := by
      by_contra hne
      simp [P, testRealLaw, hne] at hl
    subst l
    simp [P, testRealLaw]
    constructor <;> linarith
  · intro a l hl
    have hlk : l = k := by
      by_contra hne
      simp [P, testRealLaw, hne] at hl
    subst l
    cases a
    · simp [P, testRealLaw]
      positivity
    · simpa [P, testRealLaw] using hu
  · intro a l hl
    have hlk : l = k := by
      by_contra hne
      simp [P, testRealLaw, hne] at hl
    subst l
    have hsec := testOutcome_second hB hu a
    refine ⟨by simpa [P, testRealLaw] using hsec.1, ?_⟩
    calc
      ∫ y, (y - P.outcomeMean a k) ^ 2 ∂P.outcomeLaw a k ≤ (M / 2) ^ 2 := by
        simpa [P, testRealLaw] using hsec.2
      _ ≤ M ^ 2 := by nlinarith
  · intro l hl
    have hlk : l = k := by
      by_contra hne
      simp [P, testRealLaw, hne] at hl
    subst l
    have hate := testRealLaw_rawAte k hB hu
    rw [show P = testRealLaw k (M / 2) u hB hu by rfl]
    unfold cellDeviation cellEffect
    rw [hate]
    simp only [testRealLaw, Bool.true_eq, if_true, Bool.false_eq_true, if_false,
      sub_zero, sub_self, abs_zero]
    exact mul_nonneg hs0 (le_trans zero_le_one hM)

-- @node: testScaleBinaryObs
/-- This rescales a binary test observation into the real-outcome observation space. -/
noncomputable def testScaleBinaryObs {d : ℕ} (k : Fin d) (M : ℝ)
    (z : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs 1) : Obs d :=
  ⟨k, z.2.1, if z.2.1 then M * ((if z.2.2 then 1 else 0) - 1 / 2) else 0⟩

-- @node: measurable_testScaleBinaryObs
/-- [the affine map from binary test observations to real observations is measurable](goal). -/
lemma measurable_testScaleBinaryObs {d : ℕ} (k : Fin d) (M : ℝ) :
    Measurable (testScaleBinaryObs k M) := measurable_of_finite _

-- @node: test_map_endpoint_null
/-- If [the outcome scale satisfies its stated bound](hyp:hM) and [the second order satisfies its
  stated bound](hyp:hv), [at the null endpoint, affine rescaling maps the test observed law to the
  binary null law](goal). -/
lemma test_map_endpoint_null {d : ℕ} (k : Fin d) {M g : ℝ}
    (hM : 0 < M)
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin 1) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin 1) g g)) :
    Measure.map (testScaleBinaryObs k M)
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw hv)) =
      testObservedLaw k (M / 2) (M * (g - 1 / 2)) := by
  ext s hs
  rw [Measure.map_apply (measurable_testScaleBinaryObs k M) hs]
  change (Causalean.Estimation.MinimaxATE.obsPMF hv).toMeasure
      ((testScaleBinaryObs k M) ⁻¹' s) = _
  rw [PMF.toMeasure_apply _ (hs.preimage (measurable_testScaleBinaryObs k M)), tsum_fintype]
  rw [testObservedLaw, Causalean.Mathlib.Probability.twoPointMean,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [Measure.map_apply (measurable_testObsAtom k true) hs]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp [Fintype.sum_prod_type, Causalean.Estimation.MinimaxATE.obsPMF,
    Causalean.Estimation.MinimaxATE.obsReal,
    Causalean.Estimation.MinimaxATE.Parametric.mC,
    Causalean.Estimation.MinimaxATE.Parametric.gNull,
    testScaleBinaryObs, testObsAtom, PMF.ofFintype_apply,
    Measure.dirac_apply' _ hs, Set.indicator]
  have hg := hv.g_mem true (0 : Fin 1)
  have hgg : g ∈ Icc (0 : ℝ) 1 := by
    simpa [Causalean.Estimation.MinimaxATE.Parametric.gNull] using hg
  have hplus : ENNReal.ofReal ((1 + M * (g - 1 / 2) / (M / 2)) / 2) =
      ENNReal.ofReal g := by
    congr 1
    field_simp [hM.ne']
    ring
  have hminus : ENNReal.ofReal ((1 - M * (g - 1 / 2) / (M / 2)) / 2) =
      ENNReal.ofReal (1 - g) := by
    congr 1
    field_simp [hM.ne']
    ring
  norm_num at hplus hminus ⊢
  rw [hplus, hminus]
  have hcontrol : ENNReal.ofReal ((1 - (1 / 2 : ℝ)) * g) +
      ENNReal.ofReal ((1 - (1 / 2 : ℝ)) * (1 - g)) = (2 : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 - (1 / 2 : ℝ))),
      ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 - (1 / 2 : ℝ))), ← mul_add]
    have hsum : ENNReal.ofReal g + ENNReal.ofReal (1 - g) = 1 := by
      rw [← ENNReal.ofReal_add hgg.1 (sub_nonneg.mpr hgg.2)]
      norm_num
    rw [hsum]
    rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by ring]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hcontrol' : ENNReal.ofReal (g * (1 / 2)) +
      ENNReal.ofReal (1 / 2 + g * (-1 / 2)) = (2 : ENNReal)⁻¹ := by
    convert hcontrol using 1 <;> ring
  have hsum' : ENNReal.ofReal g + ENNReal.ofReal (1 - g) = 1 := by
    rw [← ENNReal.ofReal_add hgg.1 (sub_nonneg.mpr hgg.2)]
    norm_num
  have hhalf : (2 : ENNReal)⁻¹ * ENNReal.ofReal g +
      (2 : ENNReal)⁻¹ * ENNReal.ofReal (1 - g) = (2 : ENNReal)⁻¹ := by
    rw [← mul_add, hsum']
    simp
  have heqPlus : M * (2 : ℝ)⁻¹ = M * (1 / 2 : ℝ) := by norm_num
  have heqMinus : -(M * (2 : ℝ)⁻¹) = M * (-1 / 2 : ℝ) := by ring
  split <;> split <;> split <;>
    simp_all [Set.indicator, hcontrol', hhalf, heqPlus, heqMinus,
      div_eq_mul_inv, smul_eq_mul] <;>
    abel

-- @node: test_map_endpoint_pert
/-- If [the outcome scale satisfies its stated bound](hyp:hM) and [the second order satisfies its
  stated bound](hyp:hv), [at the perturbed endpoint, affine rescaling maps the test observed law
  to the binary alternative law](goal). -/
lemma test_map_endpoint_pert {d : ℕ} (k : Fin d) {M g delta : ℝ}
    (hM : 0 < M)
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin 1) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin 1) g g delta)) :
    Measure.map (testScaleBinaryObs k M)
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw hv)) =
      testObservedLaw k (M / 2) (M * (g + delta - 1 / 2)) := by
  ext s hs
  rw [Measure.map_apply (measurable_testScaleBinaryObs k M) hs]
  change (Causalean.Estimation.MinimaxATE.obsPMF hv).toMeasure
      ((testScaleBinaryObs k M) ⁻¹' s) = _
  rw [PMF.toMeasure_apply _ (hs.preimage (measurable_testScaleBinaryObs k M)), tsum_fintype]
  rw [testObservedLaw, Causalean.Mathlib.Probability.twoPointMean,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [Measure.map_apply (measurable_testObsAtom k true) hs]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp [Fintype.sum_prod_type, Causalean.Estimation.MinimaxATE.obsPMF,
    Causalean.Estimation.MinimaxATE.obsReal,
    Causalean.Estimation.MinimaxATE.Parametric.mC,
    Causalean.Estimation.MinimaxATE.Parametric.gPert,
    testScaleBinaryObs, testObsAtom, PMF.ofFintype_apply,
    Measure.dirac_apply' _ hs, Set.indicator]
  have hgc : g ∈ Icc (0 : ℝ) 1 := by
    simpa [Causalean.Estimation.MinimaxATE.Parametric.gPert] using
      hv.g_mem false (0 : Fin 1)
  have hgt : g + delta ∈ Icc (0 : ℝ) 1 := by
    simpa [Causalean.Estimation.MinimaxATE.Parametric.gPert] using
      hv.g_mem true (0 : Fin 1)
  have hplus : ENNReal.ofReal
      ((1 + M * (g + delta - 1 / 2) / (M / 2)) / 2) =
      ENNReal.ofReal (g + delta) := by
    congr 1
    field_simp [hM.ne']
    ring
  have hminus : ENNReal.ofReal
      ((1 - M * (g + delta - 1 / 2) / (M / 2)) / 2) =
      ENNReal.ofReal (1 - (g + delta)) := by
    congr 1
    field_simp [hM.ne']
    ring
  norm_num at hplus hminus ⊢
  rw [hplus, hminus]
  have hsumC : ENNReal.ofReal g + ENNReal.ofReal (1 - g) = 1 := by
    rw [← ENNReal.ofReal_add hgc.1 (sub_nonneg.mpr hgc.2)]
    norm_num
  have hsumT : ENNReal.ofReal (g + delta) +
      ENNReal.ofReal (1 - (g + delta)) = 1 := by
    rw [← ENNReal.ofReal_add hgt.1 (sub_nonneg.mpr hgt.2)]
    norm_num
  have hcontrol : ENNReal.ofReal ((1 - (1 / 2 : ℝ)) * g) +
      ENNReal.ofReal ((1 - (1 / 2 : ℝ)) * (1 - g)) = (2 : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 - (1 / 2 : ℝ))),
      ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 - (1 / 2 : ℝ))), ← mul_add,
      hsumC, mul_one, show (1 - (1 / 2 : ℝ)) = 1 / 2 by ring,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hhalfT : (2 : ENNReal)⁻¹ * ENNReal.ofReal (g + delta) +
      (2 : ENNReal)⁻¹ * ENNReal.ofReal (1 - (g + delta)) =
        (2 : ENNReal)⁻¹ := by
    rw [← mul_add, hsumT]
    simp
  have hhalfC : (2 : ENNReal)⁻¹ * ENNReal.ofReal g +
      (2 : ENNReal)⁻¹ * ENNReal.ofReal (1 - g) = (2 : ENNReal)⁻¹ := by
    rw [← mul_add, hsumC]
    simp
  have heqPlus : M * (2 : ℝ)⁻¹ = M * (1 / 2 : ℝ) := by norm_num
  have heqMinus : -(M * (2 : ℝ)⁻¹) = M * (-1 / 2 : ℝ) := by ring
  split <;> split <;> split <;>
    simp_all [Set.indicator, hcontrol, hhalfT, hhalfC, heqPlus, heqMinus,
      div_eq_mul_inv, smul_eq_mul] <;>
    abel

-- @node: test_product_map_null
/-- If [the outcome scale satisfies its stated bound](hyp:hM) and [the second order satisfies its
  stated bound](hyp:hv) and [the first order satisfies its stated bound](hyp:hu), [coordinatewise
  affine rescaling maps the null test-sample law to the binary null product law](goal). -/
lemma test_product_map_null {n d : ℕ} (k : Fin d) {M g : ℝ}
    (hM : 0 < M)
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin 1) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gNull (C := Fin 1) g g))
    (hu : |M * (g - 1 / 2)| ≤ M / 2) :
    productLaw n (testRealLaw k (M / 2) (M * (g - 1 / 2)) (by positivity) hu) =
      Measure.map (fun sample i => testScaleBinaryObs k M (sample i))
        (Causalean.Estimation.MinimaxATE.productLaw hv n) := by
  unfold productLaw Causalean.Estimation.MinimaxATE.productLaw
  change Measure.pi (fun _ : Fin n => testObservedLaw k (M / 2) (M * (g - 1 / 2))) = _
  rw [← test_map_endpoint_null k hM hv]
  exact (Measure.pi_map_pi
    (μ := fun _ : Fin n =>
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricLaw hv))
    (f := fun _ : Fin n => testScaleBinaryObs k M)
    (fun _ => (measurable_testScaleBinaryObs k M).aemeasurable)).symm

-- @node: test_product_map_pert
/-- If [the outcome scale satisfies its stated bound](hyp:hM) and [the second order satisfies its
  stated bound](hyp:hv) and [the first order satisfies its stated bound](hyp:hu), [coordinatewise
  affine rescaling maps the perturbed test-sample law to the binary alternative product
  law](goal). -/
lemma test_product_map_pert {n d : ℕ} (k : Fin d) {M g delta : ℝ}
    (hM : 0 < M)
    (hv : Causalean.Estimation.MinimaxATE.ValidDGP
      (Causalean.Estimation.MinimaxATE.Parametric.mC (C := Fin 1) (1 / 2))
      (Causalean.Estimation.MinimaxATE.Parametric.gPert (C := Fin 1) g g delta))
    (hu : |M * (g + delta - 1 / 2)| ≤ M / 2) :
    productLaw n
        (testRealLaw k (M / 2) (M * (g + delta - 1 / 2)) (by positivity) hu) =
      Measure.map (fun sample i => testScaleBinaryObs k M (sample i))
        (Causalean.Estimation.MinimaxATE.productLaw hv n) := by
  unfold productLaw Causalean.Estimation.MinimaxATE.productLaw
  change Measure.pi (fun _ : Fin n =>
    testObservedLaw k (M / 2) (M * (g + delta - 1 / 2))) = _
  rw [← test_map_endpoint_pert k hM hv]
  exact (Measure.pi_map_pi
    (μ := fun _ : Fin n =>
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.endpointParametricPertLaw hv))
    (f := fun _ : Fin n => testScaleBinaryObs k M)
    (fun _ => (measurable_testScaleBinaryObs k M).aemeasurable)).symm

-- @node: test_model_mse_le
/-- [risk on the parametric test model is bounded by the ambient minimax risk](goal). -/
lemma test_model_mse_le {n d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (est : Estimator n d M) :
    mse P.law est.1 ≤ (2 * M) ^ 2 := by
  let U : UnrestrictedClass d epsilon M :=
    { law := P.law
      epsilon_pos := P.epsilon_pos
      epsilon_lt_half := P.epsilon_lt_half
      M_ge_one := P.M_ge_one
      consistency := P.consistency
      exchangeability := P.exchangeability
      overlap := P.overlap
      mean_normalization := P.mean_normalization
      second_moment := P.second_moment }
  have htau : |rawAteFormula P.law| ≤ M := by
    simpa [U] using ((scale_sanity (d := d) (epsilon := epsilon) (M := M)).1 U).2.1
  have hM0 : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have hpoint (x : Fin n → Obs d) :
      (est.1 x - rawAteFormula P.law) ^ 2 ≤ (2 * M) ^ 2 := by
    have hest : |est.1 x| ≤ M := (abs_le).2 (est.2.2 x)
    have habs : |est.1 x - rawAteFormula P.law| ≤ 2 * M := by
      calc
        |est.1 x - rawAteFormula P.law| ≤ |est.1 x| + |rawAteFormula P.law| :=
          abs_sub _ _
        _ ≤ M + M := add_le_add hest htau
        _ = 2 * M := by ring
    exact (sq_le_sq).2 (by simpa [abs_mul, abs_of_nonneg hM0] using habs)
  have hint : Integrable (fun x => (est.1 x - rawAteFormula P.law) ^ 2)
      (productLaw n P.law) := by
    apply Integrable.of_bound (C := (2 * M) ^ 2)
      ((est.2.1.sub measurable_const).pow_const 2).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  unfold mse
  calc
    ∫ x, (est.1 x - rawAteFormula P.law) ^ 2 ∂productLaw n P.law ≤
        ∫ _x, (2 * M) ^ 2 ∂productLaw n P.law := by
      exact integral_mono hint (integrable_const _) hpoint
    _ = (2 * M) ^ 2 := by simp

-- @node: test_model_sq_integrable
/-- [finite ambient risk makes the squared error on the parametric test model integrable](goal). -/
lemma test_model_sq_integrable {n d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (est : Estimator n d M) :
    Integrable (fun x => (est.1 x - rawAteFormula P.law) ^ 2) (productLaw n P.law) := by
  let U : UnrestrictedClass d epsilon M :=
    { law := P.law
      epsilon_pos := P.epsilon_pos
      epsilon_lt_half := P.epsilon_lt_half
      M_ge_one := P.M_ge_one
      consistency := P.consistency
      exchangeability := P.exchangeability
      overlap := P.overlap
      mean_normalization := P.mean_normalization
      second_moment := P.second_moment }
  have htau : |rawAteFormula P.law| ≤ M := by
    simpa [U] using ((scale_sanity (d := d) (epsilon := epsilon) (M := M)).1 U).2.1
  have hM0 : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  apply Integrable.of_bound (C := (2 * M) ^ 2)
    ((est.2.1.sub measurable_const).pow_const 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hest : |est.1 x| ≤ M := (abs_le).2 (est.2.2 x)
  have habs : |est.1 x - rawAteFormula P.law| ≤ 2 * M := by
    calc
      |est.1 x - rawAteFormula P.law| ≤ |est.1 x| + |rawAteFormula P.law| :=
        abs_sub _ _
      _ ≤ M + M := add_le_add hest htau
      _ = 2 * M := by ring
  exact (sq_le_sq).2 (by simpa [abs_mul, abs_of_nonneg hM0] using habs)

-- @node: test_minimax_two_point
/-- If [the outcome scale satisfies its stated bound](hyp:hM) and [the bad-event probability is
  bounded as stated](hyp:hdelta) and [the stated tau0 condition holds](hyp:htau0) and [the stated
  tau1 condition holds](hyp:htau1) and [the stated tv condition holds](hyp:htv), [the two
  parametric test laws give the stated two-point minimax lower bound](goal). -/
lemma test_minimax_two_point {n d : ℕ} {epsilon M sigma delta : ℝ}
    (P0 P1 : ModelClass d epsilon M sigma) (hM : 1 ≤ M)
    (hdelta : 0 ≤ delta)
    (htau0 : rawAteFormula P0.law = 0)
    (htau1 : rawAteFormula P1.law = delta)
    (htv : Causalean.Stat.tvDist (productLaw n P0.law) (productLaw n P1.law) ≤ 1 / 2) :
    delta ^ 2 / 16 ≤ minimaxRisk n d epsilon M sigma := by
  let est0 : Estimator n d M := ⟨fun _ ↦ 0, measurable_const, fun _ ↦ by simp; linarith⟩
  letI : Nonempty (Estimator n d M) := ⟨est0⟩
  unfold minimaxRisk
  apply le_ciInf
  intro est
  have hprob := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := productLaw n P0.law) (P₁ := productLaw n P1.law) est.2.1
    (θ₀ := rawAteFormula P0.law) (θ₁ := rawAteFormula P1.law)
    (s := delta / 2) (c := (1 / 2 : ℝ))
    (by rw [htau0, htau1, zero_sub, abs_neg, abs_of_nonneg hdelta]; linarith) htv
  have hmse (P : ModelClass d epsilon M sigma) :
      (delta / 2) ^ 2 * (productLaw n P.law).real
          {x | delta / 2 ≤ |est.1 x - rawAteFormula P.law|} ≤ mse P.law est.1 := by
    unfold mse
    have hset : {x | delta / 2 ≤ |est.1 x - rawAteFormula P.law|} =
        {x | (delta / 2) ^ 2 ≤ (est.1 x - rawAteFormula P.law) ^ 2} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;>
        nlinarith [hdelta, abs_nonneg (est.1 x - rawAteFormula P.law),
          sq_abs (est.1 x - rawAteFormula P.law)]
    rw [hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg (est.1 x - rawAteFormula P.law))
      (test_model_sq_integrable P est) ((delta / 2) ^ 2)
  have htwo : delta ^ 2 / 16 ≤ max (mse P0.law est.1) (mse P1.law est.1) := by
    have hscale : 0 ≤ (delta / 2) ^ 2 := sq_nonneg _
    have hp := mul_le_mul_of_nonneg_left hprob hscale
    norm_num at hp
    rw [mul_max_of_nonneg _ _ hscale] at hp
    calc
      delta ^ 2 / 16 = (delta / 2) ^ 2 * (1 / 4) := by ring
      _ ≤ max
          ((delta / 2) ^ 2 * (productLaw n P0.law).real
            {x | delta / 2 ≤ |est.1 x - rawAteFormula P0.law|})
          ((delta / 2) ^ 2 * (productLaw n P1.law).real
            {x | delta / 2 ≤ |est.1 x - rawAteFormula P1.law|}) := hp
      _ ≤ _ := max_le_max (hmse P0) (hmse P1)
  have hb : BddAbove (Set.range (fun P : ModelClass d epsilon M sigma ↦
      mse P.law est.1)) := by
    refine ⟨(2 * M) ^ 2, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact test_model_mse_le P est
  exact htwo.trans (max_le (le_ciSup hb P0) (le_ciSup hb P1))

-- @node: parametric_lower_core
/-- [the parametric two-point experiment yields the stated inverse-sample-size minimax lower
  bound](goal). -/
lemma parametric_lower_core :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ c_epsilon : ℝ, 0 < c_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        c_epsilon * M ^ 2 / n ≤ minimaxRisk n d epsilon M sigma := by
  intro epsilon he0 hehalf
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro n d M sigma hn hd hM hs0 hs2
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let k : Fin d := Classical.arbitrary (Fin d)
  let delta : ℝ := (2 / 5) / Real.sqrt n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hdelta0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hdeltasq : delta ^ 2 = 4 / (25 * (n : ℝ)) := by
    dsimp [delta]
    rw [div_pow, Real.sq_sqrt hnR.le]
    ring
  have hsqrt_one : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hdeltaU : delta ≤ 2 / 5 := by
    dsimp [delta]
    exact div_le_self (by norm_num) hsqrt_one
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let u0 : ℝ := M * ((1 / 2 : ℝ) - 1 / 2)
  let u1 : ℝ := M * ((1 / 2 : ℝ) + delta - 1 / 2)
  have hu0 : |u0| ≤ M / 2 := by dsimp [u0]; simp; positivity
  have hu1 : |u1| ≤ M / 2 := by
    have hdhalf : delta ≤ 1 / 2 := hdeltaU.trans (by norm_num)
    rw [show u1 = M * delta by dsimp [u1]; ring, abs_mul,
      abs_of_nonneg hdelta0, abs_of_nonneg hM0.le]
    nlinarith
  let P0 : ModelClass d epsilon M sigma :=
    testModelClass k epsilon M sigma u0 he0 hehalf hM hs0 hs2 hu0
  let P1 : ModelClass d epsilon M sigma :=
    testModelClass k epsilon M sigma u1 he0 hehalf hM hs0 hs2 hu1
  let hv0 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_null
    (C := Fin 1) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let hv1 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_pert
    (C := Fin 1) (m₀ := (1 / 2 : ℝ)) (g₀ := (1 / 2 : ℝ)) (g₁ := (1 / 2 : ℝ))
    (δ := delta) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hdelta0 (by linarith)
  have hreg : (n : ℝ) *
      ((1 / 2 : ℝ) * delta ^ 2 / ((1 / 2 : ℝ) * (1 - 1 / 2))) ≤ Real.log 2 := by
    rw [hdeltasq]
    have hlog : (8 / 25 : ℝ) ≤ Real.log 2 :=
      le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
    convert hlog using 1 <;> field_simp <;> ring
  have htvSource : Causalean.Stat.tvDist
      (Causalean.Estimation.MinimaxATE.productLaw hv0 n)
      (Causalean.Estimation.MinimaxATE.productLaw hv1 n) ≤ 1 / 2 :=
    Causalean.Estimation.MinimaxATE.Parametric.tvDist_productLaw_le_half
      hv0 hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hreg
  have hmap0 : productLaw n P0.law =
      Measure.map (fun sample i => testScaleBinaryObs k M (sample i))
        (Causalean.Estimation.MinimaxATE.productLaw hv0 n) := by
    simpa [P0, u0, testModelClass] using
      (test_product_map_null (n := n) k hM0 hv0 hu0)
  have hmap1 : productLaw n P1.law =
      Measure.map (fun sample i => testScaleBinaryObs k M (sample i))
        (Causalean.Estimation.MinimaxATE.productLaw hv1 n) := by
    simpa [P1, u1, testModelClass] using
      (test_product_map_pert (n := n) k hM0 hv1 hu1)
  have htv : Causalean.Stat.tvDist (productLaw n P0.law) (productLaw n P1.law) ≤ 1 / 2 := by
    rw [hmap0, hmap1]
    exact (CausalSmith.Stat.DiscreteAteMinimaxLoggap.tvDist_map_le
      (Causalean.Estimation.MinimaxATE.productLaw hv0 n)
      (Causalean.Estimation.MinimaxATE.productLaw hv1 n)
      (fun sample i => testScaleBinaryObs k M (sample i)) (by fun_prop)).trans htvSource
  have htau0 : rawAteFormula P0.law = 0 := by
    simpa [P0, u0, testModelClass] using
      (testRealLaw_rawAte k (show 0 < M / 2 by positivity) hu0)
  have htau1 : rawAteFormula P1.law = M * delta := by
    have hraw := testRealLaw_rawAte k (show 0 < M / 2 by positivity) hu1
    simpa [P1, u1, testModelClass] using hraw
  have hlow := test_minimax_two_point P0 P1 hM
    (mul_nonneg hM0.le hdelta0) htau0 htau1 htv
  rw [show (M * delta) ^ 2 = M ^ 2 * delta ^ 2 by ring, hdeltasq] at hlow
  convert hlow using 1 <;> field_simp <;> ring

end
end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
