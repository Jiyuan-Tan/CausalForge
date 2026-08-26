/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.IndepIntegral
import Causalean.Stat.SampleSplit.OneShot

/-!
# Finite pilot-selected L2 transfer

This module transfers uniform squared-risk bounds through a finite branch
chosen from an independent pilot sample. It also bounds the full risk after a
controlled bad pilot event and supplies the corresponding one-shot iid split
bridge.

The construction expands the selected risk over measurable selector cells and
uses independence to factor each cell probability from its fixed-branch tail
risk. The statements are neutral about the meaning of the branches and sample
coordinates.
-/

noncomputable section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Omega Alpha Beta Iota X : Type*}
  [MeasurableSpace Omega] [MeasurableSpace Alpha] [MeasurableSpace Beta]
  [MeasurableSpace Iota] [MeasurableSpace X]

/-- The selector cell for a branch is the part of a designated pilot event on
which a finite-valued selection rule chooses that branch. -/
def selectorCell (select : Alpha -> Iota) (good : Set Alpha) (i : Iota) : Set Alpha :=
  good ∩ select ⁻¹' {i}

/-- When [the selection rule is measurable](hyp:hselect), [the designated pilot
event is measurable](hyp:hgood), and [a branch is fixed](hyp:i), [its selector
cell is measurable](goal). -/
lemma measurableSet_selectorCell [MeasurableSingletonClass Iota]
    {select : Alpha -> Iota} (hselect : Measurable select)
    {good : Set Alpha} (hgood : MeasurableSet good) (i : Iota) :
    MeasurableSet (selectorCell select good i) := by
  exact hgood.inter (hselect (measurableSet_singleton i))

/-- When [finite branch selection is measurable](hyp:hselect) and [each
branch-specific error is measurable](hyp:herr), [evaluating the selected error
on a pilot-tail pair is measurable](goal). -/
lemma measurable_finiteSelector_apply [Fintype Iota] [MeasurableSingletonClass Iota]
    {select : Alpha -> Iota} (hselect : Measurable select)
    {err : Iota -> Beta -> Real} (herr : ∀ i, Measurable (err i)) :
    Measurable (fun z : Alpha × Beta => err (select z.1) z.2) := by
  classical
  let cell : Iota → Set (Alpha × Beta) :=
    fun i => (fun z : Alpha × Beta => select z.1) ⁻¹' {i}
  have hcell : ∀ i, MeasurableSet (cell i) := fun i =>
    (hselect.comp measurable_fst) (measurableSet_singleton i)
  have hsum : Measurable (fun z : Alpha × Beta =>
      ∑ i : Iota, (cell i).indicator (fun z => err i z.2) z) := by
    exact Finset.measurable_sum Finset.univ fun i _ =>
      ((herr i).comp measurable_snd).indicator (hcell i)
  convert hsum using 1
  funext z
  simp only [cell, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
  simp

/-- If [the pilot coordinate is measurable](hyp:hpilot), [the tail coordinate is
measurable](hyp:htail), [the finite selection rule is measurable](hyp:hselect),
and [every branch error is measurable](hyp:herr), [the selected squared error is
measurable](goal). -/
lemma measurable_finiteSelector_sq [Fintype Iota] [MeasurableSingletonClass Iota]
    {pilot : Omega -> Alpha} {tail : Omega -> Beta}
    {select : Alpha -> Iota} {err : Iota -> Beta -> Real}
    (hpilot : Measurable pilot) (htail : Measurable tail)
    (hselect : Measurable select) (herr : ∀ i, Measurable (err i)) :
    Measurable (fun omega => (err (select (pilot omega)) (tail omega)) ^ 2) := by
  exact ((measurable_finiteSelector_apply hselect herr).comp
    (hpilot.prodMk htail)).pow_const 2

/-- If [pilot and tail coordinates are independent](hyp:hind), [the pilot
coordinate is measurable](hyp:hpilot), [the tail coordinate is
measurable](hyp:htail), [the finite selection rule is measurable](hyp:hselect),
and [every fixed branch has integrable squared error under the tail
law](hyp:herr), [the pilot-selected squared error is integrable under the
ambient probability law](goal). -/
theorem IndepFun.integrable_finiteSelector_sq
    [Fintype Iota] [MeasurableSingletonClass Iota]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {pilot : Omega -> Alpha} {tail : Omega -> Beta}
    {select : Alpha -> Iota} {err : Iota -> Beta -> Real}
    (hind : IndepFun pilot tail mu)
    (hpilot : Measurable pilot) (htail : Measurable tail)
    (hselect : Measurable select)
    (herr : ∀ i, Integrable (fun b => (err i b) ^ 2) (mu.map tail)) :
    Integrable (fun omega => (err (select (pilot omega)) (tail omega)) ^ 2) mu := by
  /- Expand over the measurable selector fibers.  On each fiber, independence
  transports the branch integrability from `mu.map tail`; combine the finitely
  many restricted integrable functions. -/
  classical
  let cell : Iota → Set Omega := fun i => pilot ⁻¹' (select ⁻¹' {i})
  have hcell : ∀ i, MeasurableSet (cell i) := fun i =>
    hpilot ((hselect (measurableSet_singleton i)))
  have hcover : (⋃ i, cell i) = Set.univ := by
    ext omega
    simp [cell]
  rw [← integrableOn_univ, ← hcover, integrableOn_finite_iUnion]
  intro i
  have hi : Integrable (fun omega => (err i (tail omega)) ^ 2) mu :=
    (herr i).comp_aemeasurable htail.aemeasurable
  refine hi.integrableOn.congr_fun ?_ (hcell i)
  intro omega homega
  have hsel : select (pilot omega) = i := homega
  simp [hsel]

/-- If [pilot and tail coordinates are independent](hyp:hind), [the pilot
coordinate is measurable](hyp:hpilot), [the tail coordinate is
measurable](hyp:htail), [the finite selection rule is measurable](hyp:hselect),
[the designated pilot event is measurable](hyp:hgood), and [every fixed branch
has integrable squared error under the tail law](hyp:herr), [the selected risk
on that event equals the sum of each selector-cell probability times its
fixed-branch tail risk](goal). -/
theorem IndepFun.integral_finiteSelector_sq_eq_sum
    [Fintype Iota] [MeasurableSingletonClass Iota]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {pilot : Omega -> Alpha} {tail : Omega -> Beta}
    {select : Alpha -> Iota} {err : Iota -> Beta -> Real}
    (hind : IndepFun pilot tail mu)
    (hpilot : Measurable pilot) (htail : Measurable tail)
    (hselect : Measurable select)
    {good : Set Alpha} (hgood : MeasurableSet good)
    (herr : ∀ i, Integrable (fun b => (err i b) ^ 2) (mu.map tail)) :
    ∫ omega in pilot ⁻¹' good,
        (err (select (pilot omega)) (tail omega)) ^ 2 ∂mu =
      ∑ i : Iota, (mu (pilot ⁻¹' selectorCell select good i)).toReal *
        ∫ b, (err i b) ^ 2 ∂(mu.map tail) := by
  /- Integrability is essential here: without it, Lean's Bochner integral is
  zero for a non-integrable function, so finite additivity across selector
  cells can fail when one cell is non-integrable and another contributes a
  positive finite integral.  Partition `pilot ⁻¹' good` by the disjoint
  selector fibers.  On the
  `i`th fiber replace the selected branch pointwise by `err i`, apply
  `IndepFun.integral_restrict_preimage_eq_mul`, then rewrite the tail-composed
  integral with `integral_map`. -/
  classical
  let F : Omega → Real :=
    fun omega => (err (select (pilot omega)) (tail omega)) ^ 2
  let cell : Iota → Set Omega :=
    fun i => pilot ⁻¹' selectorCell select good i
  have hcell : ∀ i, MeasurableSet (cell i) := fun i =>
    hpilot (measurableSet_selectorCell hselect hgood i)
  have hpair : Pairwise (Function.onFun Disjoint cell) := by
    intro i j hij
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro omega hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hcover : (⋃ i, cell i) = pilot ⁻¹' good := by
    ext omega
    simp [cell, selectorCell]
  have hInt : IntegrableOn F (pilot ⁻¹' good) mu :=
    (IndepFun.integrable_finiteSelector_sq hind hpilot htail hselect herr).integrableOn
  have hsplit :
      ∫ omega in pilot ⁻¹' good, F omega ∂mu =
        ∑ i : Iota, ∫ omega in cell i, F omega ∂mu := by
    rw [← hcover]
    exact integral_iUnion_fintype hcell hpair fun i =>
      hInt.mono_set (by rw [← hcover]; exact Set.subset_iUnion cell i)
  have hfactor : ∀ i : Iota,
      ∫ omega in cell i, F omega ∂mu =
        (mu (cell i)).toReal * ∫ b, (err i b) ^ 2 ∂(mu.map tail) := by
    intro i
    have hcongr : ∫ omega in cell i, F omega ∂mu =
        ∫ omega in cell i, (err i (tail omega)) ^ 2 ∂mu := by
      refine setIntegral_congr_fun (hcell i) ?_
      intro omega homega
      simp only [F]
      rw [homega.2]
    rw [hcongr]
    have hdrop := hind.integral_restrict_preimage_eq_mul
      hpilot.aemeasurable htail.aemeasurable
      (measurableSet_selectorCell hselect hgood i) (hcell i)
      (herr i).aestronglyMeasurable
    rw [hdrop, integral_map htail.aemeasurable (herr i).aestronglyMeasurable]
  rw [show (∫ omega in pilot ⁻¹' good,
      (err (select (pilot omega)) (tail omega)) ^ 2 ∂mu) =
      ∫ omega in pilot ⁻¹' good, F omega ∂mu from rfl,
    hsplit]
  apply Finset.sum_congr rfl
  intro i _
  exact hfactor i

/-- If [the pilot coordinate is measurable](hyp:hpilot), [the tail coordinate is
measurable](hyp:htail), [the finite selection rule is measurable](hyp:hselect),
[the designated pilot event is measurable](hyp:hgood), [every branch selected
there is eligible](hyp:hEligible), and [eligible branches have integrable
squared error under the tail law](hyp:hbranchInt), [the selected squared error
is integrable on that pilot event](goal). -/
theorem integrableOn_finiteSelector_sq_of_eligible
    [Fintype Iota] [MeasurableSingletonClass Iota]
    {mu : Measure Omega}
    {pilot : Omega -> Alpha} {tail : Omega -> Beta}
    {select : Alpha -> Iota} {err : Iota -> Beta -> Real}
    {Eligible : Iota -> Prop}
    (hpilot : Measurable pilot) (htail : Measurable tail)
    (hselect : Measurable select)
    {good : Set Alpha} (hgood : MeasurableSet good)
    (hEligible : ∀ a ∈ good, Eligible (select a))
    (hbranchInt : ∀ i, Eligible i ->
      Integrable (fun b => (err i b) ^ 2) (mu.map tail)) :
    IntegrableOn (fun omega =>
      (err (select (pilot omega)) (tail omega)) ^ 2) (pilot ⁻¹' good) mu := by
  /- Partition the good pullback into selector cells.  An empty cell is
  integrable trivially.  From a point in a nonempty ambient cell, its pilot
  value lies in the corresponding `selectorCell`; `hEligible` makes the
  branch eligible, and
  `hbranchInt` transported along `tail` gives ambient integrability.  Replace
  the selected branch by that fixed branch on the cell and combine the finite
  union with `integrableOn_finite_iUnion`. -/
  classical
  let cell : Iota → Set Omega :=
    fun i => pilot ⁻¹' selectorCell select good i
  have hcell : ∀ i, MeasurableSet (cell i) := fun i =>
    hpilot (measurableSet_selectorCell hselect hgood i)
  have hcover : (⋃ i, cell i) = pilot ⁻¹' good := by
    ext omega
    simp [cell, selectorCell]
  rw [← hcover, integrableOn_finite_iUnion]
  intro i
  by_cases hi_empty : cell i = ∅
  · simp [hi_empty]
  · obtain ⟨omega, homega⟩ := Set.nonempty_iff_ne_empty.mpr hi_empty
    have hi_eligible : Eligible i := by
      have hsel : select (pilot omega) = i := homega.2
      exact hsel ▸ hEligible (pilot omega) homega.1
    have hi : Integrable (fun omega => (err i (tail omega)) ^ 2) mu :=
      (hbranchInt i hi_eligible).comp_aemeasurable htail.aemeasurable
    refine hi.integrableOn.congr_fun ?_ (hcell i)
    intro omega homega
    change (err i (tail omega)) ^ 2 =
      (err (select (pilot omega)) (tail omega)) ^ 2
    rw [homega.2]

/-- If [pilot and tail coordinates are independent](hyp:hind), [the pilot
coordinate is measurable](hyp:hpilot), [the tail coordinate is
measurable](hyp:htail), [the finite selection rule is measurable](hyp:hselect),
[the designated pilot event is measurable](hyp:hgood), [the common risk bound
is nonnegative](hyp:hV), [every branch selected on that event is
eligible](hyp:hEligible), [eligible branches have integrable squared tail
error](hyp:hbranchInt), and [their fixed-branch risks obey the common
bound](hyp:hbranch), [the pilot-selected risk on the event obeys that same
bound](goal). -/
theorem IndepFun.integral_finiteSelector_sq_le
    [Fintype Iota] [MeasurableSingletonClass Iota]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {pilot : Omega -> Alpha} {tail : Omega -> Beta}
    {select : Alpha -> Iota} {err : Iota -> Beta -> Real}
    {Eligible : Iota -> Prop} {V : Real}
    (hind : IndepFun pilot tail mu)
    (hpilot : Measurable pilot) (htail : Measurable tail)
    (hselect : Measurable select)
    {good : Set Alpha} (hgood : MeasurableSet good)
    (hV : 0 ≤ V)
    (hEligible : ∀ a ∈ good, Eligible (select a))
    (hbranchInt : ∀ i, Eligible i ->
      Integrable (fun b => (err i b) ^ 2) (mu.map tail))
    (hbranch : ∀ i, Eligible i -> ∫ b, (err i b) ^ 2 ∂(mu.map tail) ≤ V) :
    ∫ omega in pilot ⁻¹' good,
        (err (select (pilot omega)) (tail omega)) ^ 2 ∂mu ≤ V := by
  /- First obtain genuine integrability on the good event from
  `integrableOn_finiteSelector_sq_of_eligible`; there is no `integral_undef`
  case.  Split into selector cells.  Empty cells contribute zero.  For every
  nonempty cell, eligibility supplies both fixed-branch integrability and the
  bound, so independence factors its integral.  Sum the cell probabilities
  and use that the good-event probability is at most one. -/
  classical
  let F : Omega → Real :=
    fun omega => (err (select (pilot omega)) (tail omega)) ^ 2
  let cell : Iota → Set Omega :=
    fun i => pilot ⁻¹' selectorCell select good i
  have hcell : ∀ i, MeasurableSet (cell i) := fun i =>
    hpilot (measurableSet_selectorCell hselect hgood i)
  have hpair : Pairwise (Function.onFun Disjoint cell) := by
    intro i j hij
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro omega hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hcover : (⋃ i, cell i) = pilot ⁻¹' good := by
    ext omega
    simp [cell, selectorCell]
  have hInt : IntegrableOn F (pilot ⁻¹' good) mu :=
    integrableOn_finiteSelector_sq_of_eligible hpilot htail hselect hgood
      hEligible hbranchInt
  have hsplit :
      ∫ omega in pilot ⁻¹' good, F omega ∂mu =
        ∑ i : Iota, ∫ omega in cell i, F omega ∂mu := by
    rw [← hcover]
    exact integral_iUnion_fintype hcell hpair fun i =>
      hInt.mono_set (by rw [← hcover]; exact Set.subset_iUnion cell i)
  have hfactor_bound : ∀ i : Iota,
      ∫ omega in cell i, F omega ∂mu ≤ (mu (cell i)).toReal * V := by
    intro i
    by_cases hi_empty : cell i = ∅
    · simp [hi_empty]
    · obtain ⟨omega, homega⟩ := Set.nonempty_iff_ne_empty.mpr hi_empty
      have hi_eligible : Eligible i := by
        have hsel : select (pilot omega) = i := homega.2
        exact hsel ▸ hEligible (pilot omega) homega.1
      have hcongr : ∫ omega in cell i, F omega ∂mu =
          ∫ omega in cell i, (err i (tail omega)) ^ 2 ∂mu := by
        refine setIntegral_congr_fun (hcell i) ?_
        intro omega homega
        simp only [F]
        rw [homega.2]
      rw [hcongr]
      have hdrop := hind.integral_restrict_preimage_eq_mul
        hpilot.aemeasurable htail.aemeasurable
        (measurableSet_selectorCell hselect hgood i) (hcell i)
        (hbranchInt i hi_eligible).aestronglyMeasurable
      rw [hdrop, ← integral_map htail.aemeasurable
        (hbranchInt i hi_eligible).aestronglyMeasurable]
      change (mu (cell i)).toReal *
        (∫ b, (err i b) ^ 2 ∂(mu.map tail)) ≤ (mu (cell i)).toReal * V
      exact mul_le_mul_of_nonneg_left (hbranch i hi_eligible) ENNReal.toReal_nonneg
  have hmass : ∑ i : Iota, (mu (cell i)).toReal =
      mu.real (pilot ⁻¹' good) := by
    rw [measureReal_def, ← hcover, measure_iUnion hpair hcell, tsum_fintype,
      ENNReal.toReal_sum]
    intro i _
    exact measure_ne_top mu (cell i)
  rw [show (∫ omega in pilot ⁻¹' good,
      (err (select (pilot omega)) (tail omega)) ^ 2 ∂mu) =
      ∫ omega in pilot ⁻¹' good, F omega ∂mu from rfl,
    hsplit]
  calc
    ∑ i : Iota, ∫ omega in cell i, F omega ∂mu ≤
        ∑ i : Iota, (mu (cell i)).toReal * V :=
      Finset.sum_le_sum fun i _ => hfactor_bound i
    _ = (∑ i : Iota, (mu (cell i)).toReal) * V := by
      rw [Finset.sum_mul]
    _ = mu.real (pilot ⁻¹' good) * V := by rw [hmass]
    _ ≤ 1 * V := mul_le_mul_of_nonneg_right measureReal_le_one hV
    _ = V := one_mul V

/-- If [pilot and tail coordinates are independent](hyp:hind), [the pilot
coordinate is measurable](hyp:hpilot), [the tail coordinate is
measurable](hyp:htail), [the finite selection rule is measurable](hyp:hselect),
[all branch errors are measurable](hyp:herr), [the designated pilot event is
measurable](hyp:hgood), [the good-event risk bound is nonnegative](hyp:hV), [the
global squared-error envelope is nonnegative](hyp:hH), [every branch selected
on the good event is eligible](hyp:hEligible), [eligible branches have
integrable squared tail error](hyp:hbranchInt), [their fixed-branch risks obey
the good-event bound](hyp:hbranch), [the selected squared error obeys the global
envelope](hyp:hbounded), and [the bad pilot event has probability at most the
given tolerance](hyp:hbad), [the full risk is at most the good-event bound plus
the envelope times that tolerance](goal). -/
theorem IndepFun.integral_finiteSelector_sq_le_add_bad
    [Fintype Iota] [MeasurableSingletonClass Iota]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {pilot : Omega -> Alpha} {tail : Omega -> Beta}
    {select : Alpha -> Iota} {err : Iota -> Beta -> Real}
    {Eligible : Iota -> Prop} {V H delta : Real}
    (hind : IndepFun pilot tail mu)
    (hpilot : Measurable pilot) (htail : Measurable tail)
    (hselect : Measurable select) (herr : ∀ i, Measurable (err i))
    {good : Set Alpha} (hgood : MeasurableSet good)
    (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hEligible : ∀ a ∈ good, Eligible (select a))
    (hbranchInt : ∀ i, Eligible i ->
      Integrable (fun b => (err i b) ^ 2) (mu.map tail))
    (hbranch : ∀ i, Eligible i -> ∫ b, (err i b) ^ 2 ∂(mu.map tail) ≤ V)
    (hbounded : ∀ omega, (err (select (pilot omega)) (tail omega)) ^ 2 ≤ H)
    (hbad : mu.real (pilot ⁻¹' goodᶜ) ≤ delta) :
    ∫ omega, (err (select (pilot omega)) (tail omega)) ^ 2 ∂mu ≤
      V + H * delta := by
  /- The pointwise bound plus measurability makes the full square integrable.
  Split its integral over the good event and its complement.  Apply the
  selector theorem on the good part and the constant bound `H` on the bad
  part, whose real probability is at most `delta`. -/
  let F : Omega → Real :=
    fun omega => (err (select (pilot omega)) (tail omega)) ^ 2
  have hFmeas : Measurable F := by
    exact measurable_finiteSelector_sq hpilot htail hselect herr
  have hFint : Integrable F mu := by
    rw [← integrableOn_univ]
    apply mu.integrableOn_of_bounded (M := H) (by finiteness) hFmeas.aestronglyMeasurable
    filter_upwards with omega
    have hs : 0 ≤ F omega := by exact sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hs]
    exact hbounded omega
  have hgood_pre : MeasurableSet (pilot ⁻¹' good) := hpilot hgood
  have hbad_pre : (pilot ⁻¹' good)ᶜ = pilot ⁻¹' goodᶜ := by
    ext omega
    simp
  have hgood_bound : ∫ omega in pilot ⁻¹' good, F omega ∂mu ≤ V := by
    exact IndepFun.integral_finiteSelector_sq_le hind hpilot htail hselect hgood
      hV hEligible hbranchInt hbranch
  have hbad_bound : ∫ omega in pilot ⁻¹' goodᶜ, F omega ∂mu ≤ H * delta := by
    calc
      ∫ omega in pilot ⁻¹' goodᶜ, F omega ∂mu ≤
          ∫ _omega in pilot ⁻¹' goodᶜ, H ∂mu := by
        apply setIntegral_mono_on hFint.integrableOn integrableOn_const
          (hpilot hgood.compl)
        intro omega _
        exact hbounded omega
      _ = H * mu.real (pilot ⁻¹' goodᶜ) := by
        simp [integral_const, mul_comm]
      _ ≤ H * delta := mul_le_mul_of_nonneg_left hbad hH
  have hsplit := integral_add_compl hgood_pre hFint
  rw [hbad_pre] at hsplit
  change ∫ omega, F omega ∂mu ≤ V + H * delta
  linarith

/-- Given [an iid one-shot sample split](hyp:split), [a sample
horizon](hyp:n), [a measurable finite branch selector on the pilot
fold](hyp:hselect), [a measurable good pilot event](hyp:hgood), [a nonnegative
common risk bound](hyp:hV), [eligibility of every branch selected on the good
event](hyp:hEligible), [integrability of every eligible branch's squared error
under the tail-fold law](hyp:hbranchInt), and [the common fixed-branch risk
bound](hyp:hbranch), [the selected squared risk on the good event is at most
that common bound](goal). -/
theorem OneShotSplit.integral_finiteSelector_sq_le
    {mu : Measure Omega} {P : Measure X}
    [Fintype Iota] [MeasurableSingletonClass Iota]
    {S : IIDSample Omega X mu P}
    (split : OneShotSplit S) (n : Nat)
    {select : (split.foldA n -> X) -> Iota}
    {err : Iota -> (split.foldB n -> X) -> Real}
    {Eligible : Iota -> Prop} {V : Real}
    (hselect : Measurable select)
    {good : Set (split.foldA n -> X)} (hgood : MeasurableSet good)
    (hV : 0 ≤ V)
    (hEligible : ∀ a ∈ good, Eligible (select a))
    (hbranchInt : ∀ i, Eligible i ->
      Integrable (fun b => (err i b) ^ 2)
        (mu.map (fun omega => fun j : split.foldB n => S.Z j omega)))
    (hbranch : ∀ i, Eligible i ->
      ∫ b, (err i b) ^ 2
        ∂(mu.map (fun omega => fun j : split.foldB n => S.Z j omega)) ≤ V) :
    ∫ omega in (fun omega => fun j : split.foldA n => S.Z j omega) ⁻¹' good,
      (err (select (fun j : split.foldA n => S.Z j omega))
        (fun j : split.foldB n => S.Z j omega)) ^ 2 ∂mu ≤ V := by
  letI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  have hfoldA : Measurable (fun omega => fun j : split.foldA n => S.Z j omega) :=
    measurable_pi_lambda _ fun j => S.meas j
  have hfoldB : Measurable (fun omega => fun j : split.foldB n => S.Z j omega) :=
    measurable_pi_lambda _ fun j => S.meas j
  exact IndepFun.integral_finiteSelector_sq_le (split.folds_indep n)
    hfoldA hfoldB hselect hgood hV hEligible hbranchInt hbranch

end Causalean.Stat
