/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Concentration.TailBounds.BinomialCount
import Causalean.Stat.Sample.PiTransport

/-!
# Finite-category counts on arbitrary IID pilot blocks

This module controls threshold selection from finite-category counts on an
arbitrary finite block of iid pilot observations. Its simultaneous good event
ensures that selected categories have enough population mass while rejected
categories have no more than a supplied upper mass band.

The file provides measurable counts, cellwise tilted Chernoff bounds, and a
cardinality-explicit union bound. Empty coordinate blocks and empty category
types remain totalized.
-/

noncomputable section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Omega X Iota : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [MeasurableSpace Iota]
  {mu : Measure Omega} {P : Measure X}

/-- A category's population mass is the probability that the observation's
label equals that category, represented as a real number. -/
def categoryMass (P : Measure X) (label : X -> Iota) (k : Iota) : Real :=
  P.real (label ⁻¹' {k})

/-- A category indicator is one when an observation has the designated label
and zero otherwise. -/
def categoryIndicator [DecidableEq Iota] (label : X -> Iota) (k : Iota) (x : X) : Real :=
  if label x = k then 1 else 0

/-- Given [a measurable category label](hyp:hlabel) and [a fixed
category](hyp:k), [the corresponding zero-one category indicator is
measurable](goal). -/
lemma measurable_categoryIndicator [DecidableEq Iota] [MeasurableSingletonClass Iota]
    {label : X -> Iota} (hlabel : Measurable label) (k : Iota) :
    Measurable (categoryIndicator label k) := by
  unfold categoryIndicator
  exact measurable_const.ite (hlabel (measurableSet_singleton k)) measurable_const

/-- Given [a measurable category label](hyp:hlabel) and [a fixed
category](hyp:k), [the mean of its zero-one indicator under a probability law
equals the category's population mass](goal). -/
lemma integral_categoryIndicator [DecidableEq Iota] [MeasurableSingletonClass Iota]
    [IsProbabilityMeasure P] {label : X -> Iota} (hlabel : Measurable label) (k : Iota) :
    ∫ x, categoryIndicator label k x ∂P = categoryMass P label k := by
  rw [show categoryIndicator label k =
      (label ⁻¹' {k}).indicator (fun _ => (1 : Real)) by
    funext x
    by_cases hx : label x = k <;> simp [categoryIndicator, hx]]
  rw [integral_indicator (hlabel (measurableSet_singleton k)), integral_const]
  simp [categoryMass]

/-- A pilot category count is the number of coordinates in a chosen finite
block whose observed label equals the designated category. -/
def pilotCategoryCount (S : Causalean.Stat.IIDSample Omega X mu P)
    [DecidableEq Iota] (label : X -> Iota) (block : Finset Nat)
    (k : Iota) (omega : Omega) : Nat :=
  (block.filter (fun j => label (S.Z j omega) = k)).card

/-- Given [an iid sample](hyp:S), [a measurable category label](hyp:hlabel), [a
finite coordinate block](hyp:block), and [a fixed category](hyp:k), [the pilot
count of that category is measurable](goal). -/
lemma measurable_pilotCategoryCount [DecidableEq Iota] [MeasurableSingletonClass Iota]
    (S : Causalean.Stat.IIDSample Omega X mu P)
    {label : X -> Iota} (hlabel : Measurable label)
    (block : Finset Nat) (k : Iota) :
    Measurable (pilotCategoryCount S label block k) := by
  induction block using Finset.induction_on with
  | empty =>
      unfold pilotCategoryCount
      exact measurable_const
  | @insert j block hj ih =>
      have hset : MeasurableSet {omega | label (S.Z j omega) = k} :=
        (hlabel.comp (S.meas j)) (measurableSet_singleton k)
      unfold pilotCategoryCount at ih
      have hsucc : Measurable (fun omega =>
          (block.filter (fun i => label (S.Z i omega) = k)).card + 1) :=
        ih.add measurable_const
      unfold pilotCategoryCount
      have heq : (fun omega =>
          ((insert j block).filter (fun i => label (S.Z i omega) = k)).card) =
          fun omega => if label (S.Z j omega) = k then
            (block.filter (fun i => label (S.Z i omega) = k)).card + 1
          else (block.filter (fun i => label (S.Z i omega) = k)).card := by
        funext omega
        by_cases h : label (S.Z j omega) = k
        · rw [Finset.filter_insert]
          simp [h, Finset.card_insert_of_notMem, hj]
        · rw [Finset.filter_insert]
          simp [h]
      rw [heq]
      exact hsucc.ite hset ih

/-- Given [an iid sample](hyp:S), [a category label](hyp:label), [a finite
coordinate block](hyp:block), [a category](hyp:k), and [a sample
outcome](hyp:omega), [the real-valued pilot count equals the sum of category
indicators over the block](goal). -/
lemma pilotCategoryCount_cast_eq_sum [DecidableEq Iota]
    (S : Causalean.Stat.IIDSample Omega X mu P)
    (label : X -> Iota) (block : Finset Nat) (k : Iota) (omega : Omega) :
    (pilotCategoryCount S label block k omega : Real) =
      ∑ j ∈ block, categoryIndicator label k (S.Z j omega) := by
  simp only [pilotCategoryCount, categoryIndicator, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- Given [an iid sample](hyp:S), [a measurable category label](hyp:hlabel), [a
finite pilot block](hyp:block), [a fixed category](hyp:k), [an upper bound on
that category's population mass](hyp:hmass), [an exponential tilt](hyp:s), and
[nonnegativity of the tilt](hyp:hs), [the probability that the category count
exceeds the specified level is bounded by the corresponding Chernoff
exponent](goal). -/
theorem pilotCategoryCount_upper_tail_of_tilt
    [DecidableEq Iota] [MeasurableSingletonClass Iota]
    (S : Causalean.Stat.IIDSample Omega X mu P)
    {label : X -> Iota} (hlabel : Measurable label)
    (block : Finset Nat) (k : Iota) {p a : Real}
    (hmass : categoryMass P label k ≤ p) (s : Real) (hs : 0 ≤ s) :
    mu.real {omega | a < (pilotCategoryCount S label block k omega : Real)} ≤
      Real.exp (-s * a + (block.card : Real) * (p * (Real.exp s - 1))) := by
  /- Repeat the bounded-count MGF proof from `BinomialCount` over `block`
  instead of `range m`: the composed indicators are independent by
  `S.indep.comp`, each has mean `categoryMass`, and `iIndepFun.mgf_sum`
  tensorizes the MGF.  Finish with `measure_ge_le_exp_mul_mgf`. -/
  haveI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let Xk : Nat -> Omega -> Real :=
    fun j => categoryIndicator label k ∘ S.Z j
  have hindicator : Measurable (categoryIndicator label k) :=
    measurable_categoryIndicator hlabel k
  have hXk_meas : ∀ j, Measurable (Xk j) :=
    fun j => hindicator.comp (S.meas j)
  have hXk_indep : iIndepFun Xk mu :=
    S.indep.comp (fun _ => categoryIndicator label k) (fun _ => hindicator)
  have h01 : ∀ x, categoryIndicator label k x ∈ Set.Icc (0 : Real) 1 := by
    intro x
    by_cases hx : label x = k <;> simp [categoryIndicator, hx]
  have hmgf_one : ∀ j, mgf (Xk j) mu s ≤
      Real.exp (categoryMass P label k * (Real.exp s - 1)) := by
    intro j
    rw [← mgf_map (S.meas j).aemeasurable (by fun_prop), S.map_eq]
    rw [← integral_categoryIndicator hlabel k]
    exact Causalean.Stat.Concentration.mgf_le_of_mem_Icc_zero_one
      hindicator.aemeasurable (ae_of_all _ h01) s
  have hsum : (fun omega =>
      (pilotCategoryCount S label block k omega : Real)) =
      ∑ j ∈ block, Xk j := by
    funext omega
    simpa [Xk, Function.comp_apply] using
      pilotCategoryCount_cast_eq_sum S label block k omega
  have hmgf_base : mgf (fun omega =>
      (pilotCategoryCount S label block k omega : Real)) mu s ≤
      Real.exp ((block.card : Real) *
        (categoryMass P label k * (Real.exp s - 1))) := by
    rw [hsum, hXk_indep.mgf_sum hXk_meas]
    calc
      (∏ j ∈ block, mgf (Xk j) mu s) ≤
          ∏ _j ∈ block,
            Real.exp (categoryMass P label k * (Real.exp s - 1)) :=
        Finset.prod_le_prod (fun j _ => mgf_nonneg) (fun j _ => hmgf_one j)
      _ = Real.exp ((block.card : Real) *
          (categoryMass P label k * (Real.exp s - 1))) := by
        rw [Finset.prod_const, ← Real.exp_nat_mul]
  have hcoef : 0 ≤ Real.exp s - 1 := by
    linarith [Real.one_le_exp hs]
  have hmgf : mgf (fun omega =>
      (pilotCategoryCount S label block k omega : Real)) mu s ≤
      Real.exp ((block.card : Real) * (p * (Real.exp s - 1))) :=
    hmgf_base.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hmass hcoef) (Nat.cast_nonneg block.card)))
  have hcount_meas : Measurable (fun omega =>
      (pilotCategoryCount S label block k omega : Real)) := by
    rw [hsum]
    convert (Finset.measurable_fun_sum block fun j _ => hXk_meas j) using 1
    ext omega
    simp
  have hcount_le : ∀ omega, (pilotCategoryCount S label block k omega : Real) ≤
      (block.card : Real) := by
    intro omega
    exact_mod_cast Finset.card_filter_le block
      (fun j => label (S.Z j omega) = k)
  have hint : Integrable (fun omega =>
      Real.exp (s * (pilotCategoryCount S label block k omega : Real))) mu := by
    refine Integrable.of_bound
      (hcount_meas.const_mul _ |>.exp.aestronglyMeasurable)
      (Real.exp (s * block.card)) (ae_of_all _ fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hcount_le omega) hs)
  calc
    mu.real {omega | a < (pilotCategoryCount S label block k omega : Real)} ≤
        mu.real {omega | a ≤ (pilotCategoryCount S label block k omega : Real)} :=
      measureReal_mono (by
        intro omega homega
        change a < (pilotCategoryCount S label block k omega : Real) at homega
        exact homega.le)
    _ ≤ Real.exp (-s * a) * mgf (fun omega =>
        (pilotCategoryCount S label block k omega : Real)) mu s :=
      measure_ge_le_exp_mul_mgf a hs hint
    _ ≤ Real.exp (-s * a) *
        Real.exp ((block.card : Real) * (p * (Real.exp s - 1))) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-s * a +
        (block.card : Real) * (p * (Real.exp s - 1))) :=
      (Real.exp_add _ _).symm

/-- Given [an iid sample](hyp:S), [a measurable category label](hyp:hlabel), [a
finite pilot block](hyp:block), [a fixed category](hyp:k), [a lower bound on
that category's population mass](hyp:hmass), [an exponential tilt](hyp:s), and
[nonpositivity of the tilt](hyp:hs), [the probability that the category count
is at most the specified level is bounded by the corresponding Chernoff
exponent](goal). -/
theorem pilotCategoryCount_lower_tail_of_tilt
    [DecidableEq Iota] [MeasurableSingletonClass Iota]
    (S : Causalean.Stat.IIDSample Omega X mu P)
    {label : X -> Iota} (hlabel : Measurable label)
    (block : Finset Nat) (k : Iota) {p a : Real}
    (hmass : p ≤ categoryMass P label k) (s : Real) (hs : s ≤ 0) :
    mu.real {omega | (pilotCategoryCount S label block k omega : Real) ≤ a} ≤
      Real.exp (-s * a + (block.card : Real) * (p * (Real.exp s - 1))) := by
  /- Use the same finite-block MGF tensorization at a nonpositive tilt.  Since
  `exp s - 1 ≤ 0`, replace the true category mass by its lower bound `p`,
  then apply `measure_le_le_exp_mul_mgf`. -/
  haveI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let Xk : Nat -> Omega -> Real :=
    fun j => categoryIndicator label k ∘ S.Z j
  have hindicator : Measurable (categoryIndicator label k) :=
    measurable_categoryIndicator hlabel k
  have hXk_meas : ∀ j, Measurable (Xk j) :=
    fun j => hindicator.comp (S.meas j)
  have hXk_indep : iIndepFun Xk mu :=
    S.indep.comp (fun _ => categoryIndicator label k) (fun _ => hindicator)
  have h01 : ∀ x, categoryIndicator label k x ∈ Set.Icc (0 : Real) 1 := by
    intro x
    by_cases hx : label x = k <;> simp [categoryIndicator, hx]
  have hmgf_one : ∀ j, mgf (Xk j) mu s ≤
      Real.exp (categoryMass P label k * (Real.exp s - 1)) := by
    intro j
    rw [← mgf_map (S.meas j).aemeasurable (by fun_prop), S.map_eq]
    rw [← integral_categoryIndicator hlabel k]
    exact Causalean.Stat.Concentration.mgf_le_of_mem_Icc_zero_one
      hindicator.aemeasurable (ae_of_all _ h01) s
  have hsum : (fun omega =>
      (pilotCategoryCount S label block k omega : Real)) =
      ∑ j ∈ block, Xk j := by
    funext omega
    simpa [Xk, Function.comp_apply] using
      pilotCategoryCount_cast_eq_sum S label block k omega
  have hmgf_base : mgf (fun omega =>
      (pilotCategoryCount S label block k omega : Real)) mu s ≤
      Real.exp ((block.card : Real) *
        (categoryMass P label k * (Real.exp s - 1))) := by
    rw [hsum, hXk_indep.mgf_sum hXk_meas]
    calc
      (∏ j ∈ block, mgf (Xk j) mu s) ≤
          ∏ _j ∈ block,
            Real.exp (categoryMass P label k * (Real.exp s - 1)) :=
        Finset.prod_le_prod (fun j _ => mgf_nonneg) (fun j _ => hmgf_one j)
      _ = Real.exp ((block.card : Real) *
          (categoryMass P label k * (Real.exp s - 1))) := by
        rw [Finset.prod_const, ← Real.exp_nat_mul]
  have hcoef : Real.exp s - 1 ≤ 0 := by
    linarith [Real.exp_le_one_iff.mpr hs]
  have hmgf : mgf (fun omega =>
      (pilotCategoryCount S label block k omega : Real)) mu s ≤
      Real.exp ((block.card : Real) * (p * (Real.exp s - 1))) :=
    hmgf_base.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonpos_right hmass hcoef) (Nat.cast_nonneg block.card)))
  have hcount_meas : Measurable (fun omega =>
      (pilotCategoryCount S label block k omega : Real)) := by
    rw [hsum]
    convert (Finset.measurable_fun_sum block fun j _ => hXk_meas j) using 1
    ext omega
    simp
  have hcount_nonneg : ∀ omega,
      0 ≤ (pilotCategoryCount S label block k omega : Real) :=
    fun _ => Nat.cast_nonneg _
  have hint : Integrable (fun omega =>
      Real.exp (s * (pilotCategoryCount S label block k omega : Real))) mu := by
    refine Integrable.of_bound
      (hcount_meas.const_mul _ |>.exp.aestronglyMeasurable)
      1 (ae_of_all _ fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (s * (pilotCategoryCount S label block k omega : Real)) ≤
          Real.exp 0 := Real.exp_le_exp.mpr
            (mul_nonpos_of_nonpos_of_nonneg hs (hcount_nonneg omega))
      _ = 1 := Real.exp_zero
  calc
    mu.real {omega | (pilotCategoryCount S label block k omega : Real) ≤ a} ≤
        Real.exp (-s * a) * mgf (fun omega =>
          (pilotCategoryCount S label block k omega : Real)) mu s :=
      measure_le_le_exp_mul_mgf a hs hint
    _ ≤ Real.exp (-s * a) *
        Real.exp ((block.card : Real) * (p * (Real.exp s - 1))) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-s * a +
        (block.card : Real) * (p * (Real.exp s - 1))) :=
      (Real.exp_add _ _).symm

/-- Pilot thresholding selects exactly the categories whose finite-block count
is strictly larger than the threshold. -/
def pilotSelected [Fintype Iota] [DecidableEq Iota]
    (S : Causalean.Stat.IIDSample Omega X mu P) (label : X -> Iota)
    (block : Finset Nat) (t : Real) (omega : Omega) : Finset Iota :=
  Finset.univ.filter (fun k => t < (pilotCategoryCount S label block k omega : Real))

/-- The finite-category pilot good event requires every selected category to
have at least the lower population-mass band and every rejected category to
have at most the upper band. -/
def finiteCategoryPilotGood [Fintype Iota] [DecidableEq Iota]
    (S : Causalean.Stat.IIDSample Omega X mu P) (label : X -> Iota)
    (block : Finset Nat) (t lowerBand upperBand : Real) : Set Omega :=
  {omega |
    (∀ k ∈ pilotSelected S label block t omega,
      lowerBand ≤ categoryMass P label k) ∧
    (∀ k ∉ pilotSelected S label block t omega,
      categoryMass P label k ≤ upperBand)}

/-- Given [an iid sample](hyp:S), [a measurable category label](hyp:hlabel), [a
finite pilot block](hyp:block), [a selection threshold](hyp:t), [a lower mass
band](hyp:lowerBand), and [an upper mass band](hyp:upperBand), [the simultaneous
finite-category pilot good event is measurable](goal). -/
lemma measurableSet_finiteCategoryPilotGood
    [Fintype Iota] [DecidableEq Iota] [MeasurableSingletonClass Iota]
    (S : Causalean.Stat.IIDSample Omega X mu P)
    {label : X -> Iota} (hlabel : Measurable label)
    (block : Finset Nat) (t lowerBand upperBand : Real) :
    MeasurableSet (finiteCategoryPilotGood S label block t lowerBand upperBand) := by
  classical
  have hcount : ∀ k, Measurable (fun omega =>
      (pilotCategoryCount S label block k omega : Real)) := fun k =>
    MeasurableEmbedding.natCast.measurable.comp
      (measurable_pilotCategoryCount S hlabel block k)
  rw [show finiteCategoryPilotGood S label block t lowerBand upperBand =
      (⋂ k, {omega | t < (pilotCategoryCount S label block k omega : Real) ->
        lowerBand ≤ categoryMass P label k}) ∩
      (⋂ k, {omega | (pilotCategoryCount S label block k omega : Real) ≤ t ->
        categoryMass P label k ≤ upperBand}) by
    ext omega
    simp [finiteCategoryPilotGood, pilotSelected]]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro k
    by_cases hk : lowerBand ≤ categoryMass P label k
    · simpa [hk] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set Omega))
    · simpa [hk, not_lt] using measurableSet_le (hcount k) measurable_const
  · apply MeasurableSet.iInter
    intro k
    by_cases hk : categoryMass P label k ≤ upperBand
    · simpa [hk] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set Omega))
    · simpa [hk, not_le] using measurableSet_lt measurable_const (hcount k)

/-- Given [an iid sample](hyp:S), [a measurable category label](hyp:hlabel), [a
finite pilot block](hyp:block), [a positive selection threshold](hyp:ht), [a
lower population-mass band](hyp:lowerBand), [an upper population-mass
band](hyp:upperBand), [an upper-tail exponential tilt](hyp:sUpper), [a
lower-tail exponential tilt](hyp:sLower), [nonnegativity of the upper-tail
tilt](hyp:hsUpper), and [nonpositivity of the lower-tail tilt](hyp:hsLower),
[failure of the simultaneous category-mass sandwich has probability at most
the number of categories times the sum of the two explicit Chernoff
tails](goal). The bound also covers empty blocks and empty category types. -/
theorem finiteCategoryPilot_bad_probability
    [Fintype Iota] [DecidableEq Iota] [MeasurableSingletonClass Iota]
    (S : Causalean.Stat.IIDSample Omega X mu P)
    {label : X -> Iota} (hlabel : Measurable label)
    (block : Finset Nat) {t : Real} (ht : 0 < t)
    (lowerBand upperBand sUpper sLower : Real)
    (hsUpper : 0 ≤ sUpper) (hsLower : sLower ≤ 0) :
    mu.real (finiteCategoryPilotGood S label block t lowerBand upperBand)ᶜ ≤
      (Fintype.card Iota : Real) *
        (Real.exp (-sUpper * t +
          (block.card : Real) * (lowerBand * (Real.exp sUpper - 1))) +
         Real.exp (-sLower * t +
          (block.card : Real) * (upperBand * (Real.exp sLower - 1)))) := by
  /- Negate the two universal clauses defining the good event.  The bad set is
  contained in a union over categories of (selected and mass below the lower
  band) and (rejected and mass above the upper band).  For each fixed category,
  split on the deterministic mass comparison and use the corresponding
  cellwise tail; then apply the two finite union bounds. -/
  classical
  haveI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  let A : Iota -> Set Omega := fun k =>
    {omega | t < (pilotCategoryCount S label block k omega : Real) ∧
      ¬ lowerBand ≤ categoryMass P label k}
  let B : Iota -> Set Omega := fun k =>
    {omega | (pilotCategoryCount S label block k omega : Real) ≤ t ∧
      ¬ categoryMass P label k ≤ upperBand}
  have hbad : (finiteCategoryPilotGood S label block t lowerBand upperBand)ᶜ =
      (⋃ k, A k) ∪ ⋃ k, B k := by
    ext omega
    simp [finiteCategoryPilotGood, pilotSelected, A, B]
    constructor
    · intro h
      by_cases hall : ∀ k, t < (pilotCategoryCount S label block k omega : Real) ->
          lowerBand ≤ categoryMass P label k
      · exact Or.inr (h hall)
      · left
        push_neg at hall
        exact hall
    · rintro (hA | hB) hall
      · obtain ⟨k, hkCount, hkMass⟩ := hA
        exact False.elim ((not_lt_of_ge (hall k hkCount)) hkMass)
      · exact hB
  let upperTail := Real.exp (-sUpper * t +
    (block.card : Real) * (lowerBand * (Real.exp sUpper - 1)))
  let lowerTail := Real.exp (-sLower * t +
    (block.card : Real) * (upperBand * (Real.exp sLower - 1)))
  have hA : ∀ k, mu.real (A k) ≤ upperTail := by
    intro k
    by_cases hk : lowerBand ≤ categoryMass P label k
    · have hempty : A k = ∅ := by
        ext omega
        simp [A, hk]
      rw [hempty]
      simp [upperTail, (Real.exp_pos _).le]
    · refine (measureReal_mono (fun omega homega => homega.1)).trans ?_
      exact pilotCategoryCount_upper_tail_of_tilt S hlabel block k
        (le_of_lt (lt_of_not_ge hk)) sUpper hsUpper
  have hB : ∀ k, mu.real (B k) ≤ lowerTail := by
    intro k
    by_cases hk : categoryMass P label k ≤ upperBand
    · have hempty : B k = ∅ := by
        ext omega
        simp [B, hk]
      rw [hempty]
      simp [lowerTail, (Real.exp_pos _).le]
    · refine (measureReal_mono (fun omega homega => homega.1)).trans ?_
      exact pilotCategoryCount_lower_tail_of_tilt S hlabel block k
        (le_of_lt (lt_of_not_ge hk)) sLower hsLower
  rw [hbad]
  calc
    mu.real ((⋃ k, A k) ∪ ⋃ k, B k) ≤
        mu.real (⋃ k, A k) + mu.real (⋃ k, B k) :=
      measureReal_union_le _ _
    _ ≤ (∑ k, mu.real (A k)) + ∑ k, mu.real (B k) :=
      add_le_add (measureReal_iUnion_fintype_le A)
        (measureReal_iUnion_fintype_le B)
    _ ≤ (∑ _k : Iota, upperTail) + ∑ _k : Iota, lowerTail := by
      gcongr with k
      · exact hA k
      · exact hB k
    _ = (Fintype.card Iota : Real) * (upperTail + lowerTail) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = (Fintype.card Iota : Real) *
        (Real.exp (-sUpper * t +
          (block.card : Real) * (lowerBand * (Real.exp sUpper - 1))) +
         Real.exp (-sLower * t +
          (block.card : Real) * (upperBand * (Real.exp sLower - 1)))) := by
      rfl

/-- Given [an iid sample](hyp:S), [a measurable category label](hyp:hlabel), [a
finite pilot block](hyp:block), [a positive selection threshold](hyp:ht), [a
lower population-mass band](hyp:lowerBand), and [an upper population-mass
band](hyp:upperBand), [the simultaneous category-mass sandwich failure
probability obeys the explicit bound obtained from opposite logarithmic tilts
of magnitude log two](goal). -/
theorem finiteCategoryPilot_bad_probability_log_two
    [Fintype Iota] [DecidableEq Iota] [MeasurableSingletonClass Iota]
    (S : Causalean.Stat.IIDSample Omega X mu P)
    {label : X -> Iota} (hlabel : Measurable label)
    (block : Finset Nat) {t : Real} (ht : 0 < t)
    (lowerBand upperBand : Real) :
    mu.real (finiteCategoryPilotGood S label block t lowerBand upperBand)ᶜ ≤
      (Fintype.card Iota : Real) *
        (Real.exp (-Real.log 2 * t + (block.card : Real) * lowerBand) +
         Real.exp (Real.log 2 * t - (block.card : Real) * upperBand / 2)) := by
  have hlog : 0 ≤ Real.log (2 : Real) :=
    (Real.log_pos (by norm_num)).le
  have h := finiteCategoryPilot_bad_probability S hlabel block ht
    lowerBand upperBand (Real.log 2) (-Real.log 2) hlog (neg_nonpos.mpr hlog)
  have hexp_pos : Real.exp (Real.log 2) = (2 : Real) :=
    Real.exp_log (by norm_num)
  have hexp_neg : Real.exp (-Real.log 2) = (1 / 2 : Real) := by
    rw [Real.exp_neg, hexp_pos]
    norm_num
  convert h using 1 <;> rw [hexp_pos, hexp_neg] <;> ring

end Causalean.Stat
