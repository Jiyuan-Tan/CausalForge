/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# IID sample → product measure transport (`Fin n` version)

The Phase E2 discharge of `localized_uniform_deviation` to `Ω`-events
needs the joint pushforward identity

    μ.map (fun ω : Ω => fun k : Fin n => S.Z k ω)
        = Measure.pi (fun _ : Fin n => P_W).

This file provides that identity (`iidSample_finN_pushforward`) plus the
event-transport corollary (`event_pullback_along_iidSample`) which
converts a high-probability event in `Set (Fin n → X)` (the natural
output of `localized_uniform_deviation`) into an Ω-event of equal mass
under the IID sample.

Pattern mirrors `FoldBEmpiricalProcess.oneShot_iid` (lines 301–314).
-/

import Causalean.Stat.Sample
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-! # Transport to Product Samples

This file proves that the joint observable of a finite independent identically
distributed sample pushes the underlying probability measure forward to the
corresponding finite product measure. It also transports high-probability events
on product samples back to events on the original sample space.

Two further transports live here.  First, forgetting part of an i.i.d. sample:
restricting a product sample to a sub-index (a cross-fitting fold, a sample
split, a `Finset` of coordinates) is measure preserving onto the product measure
over the sub-index, so integrals and pushforwards transport verbatim.  Second,
the *existence* of an i.i.d. sample with a prescribed marginal, which is shown
to be equivalent to that marginal being a probability measure — i.e. to carry no
information at all. -/

universe u

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- The coordinate projections on an infinite product probability space form
an i.i.d. sample with the common marginal law. -/
noncomputable def iidSample_infinitePi (P : Measure X) [IsProbabilityMeasure P] :
    IIDSample (ℕ → X) X (Measure.infinitePi (fun _ : ℕ => P)) P where
  Z i ω := ω i
  meas _ := measurable_pi_apply _
  indep := ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ => P) (X := fun _ : ℕ => id) (fun _ => measurable_id)
  identDist i := by
    refine ⟨(measurable_pi_apply 0).aemeasurable,
      (measurable_pi_apply i).aemeasurable, ?_⟩
    rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]
  law := Measure.infinitePi_map_eval _ _

/-- For [an i.i.d. sample `S`](hyp:S) [and a fixed horizon `n`](hyp:n), [the joint map of the first
`n` sample points pushes `μ` forward to the product measure on `Fin n → X`](goal). -/
lemma iidSample_finN_pushforward
    (S : IIDSample Ω X μ P) (n : ℕ) :
    μ.map (fun ω : Ω => fun k : Fin n => S.Z k ω) =
      Measure.pi (fun _ : Fin n => P) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hindep_s : iIndepFun (fun k : Fin n => S.Z (k : ℕ)) μ :=
    S.indep.precomp Fin.val_injective
  have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun k : Fin n => (S.meas k).aemeasurable)).mp hindep_s
  calc
    μ.map (fun ω : Ω => fun k : Fin n => S.Z k ω)
        = Measure.pi (fun k : Fin n => μ.map (S.Z k)) := hmap
    _ = Measure.pi (fun _ : Fin n => P) := by
        congr with k
        rw [← (S.identDist k).map_eq, S.law]

/-- The joint observable `Ψ ω k = S.Z k ω` is measurable
`Ω → (Fin n → X)`. -/
lemma iidSample_finN_measurable (S : IIDSample Ω X μ P) (n : ℕ) :
    Measurable (fun ω : Ω => fun k : Fin n => S.Z k ω) :=
  measurable_pi_lambda _ (fun k => S.meas k)

/-- **Event transport along an IID sample (`Fin n` version).** Given [a measurable event `E` in
the space of length-`n` outcome tuples](hyp:hE_meas) whose [product-measure probability under `n`
independent copies of the population law is at least $1-\delta$](hyp:hE_prob), the pullback of `E`
along the joint observable built from the first `n` coordinates of the i.i.d. sample [is a
measurable event on the underlying sample space, with probability at least
$1-\delta$](goal). -/
lemma event_pullback_along_iidSample
    (S : IIDSample Ω X μ P) (n : ℕ)
    {E : Set (Fin n → X)} (hE_meas : MeasurableSet E)
    {δ : ℝ}
    (hE_prob : Measure.pi (fun _ : Fin n => P) E ≥ 1 - ENNReal.ofReal δ) :
    let Ψ : Ω → (Fin n → X) := fun ω k => S.Z k ω
    let E' : Set Ω := Ψ ⁻¹' E
    MeasurableSet E' ∧ μ E' ≥ 1 - ENNReal.ofReal δ := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hΨ_meas := iidSample_finN_measurable S n
  refine ⟨hΨ_meas hE_meas, ?_⟩
  have hpush : μ.map (fun ω : Ω => fun k : Fin n => S.Z k ω) =
      Measure.pi (fun _ : Fin n => P) :=
    iidSample_finN_pushforward S n
  have hmap : μ ((fun ω : Ω => fun k : Fin n => S.Z k ω) ⁻¹' E)
      = Measure.pi (fun _ : Fin n => P) E := by
    rw [← hpush, Measure.map_apply hΨ_meas hE_meas]
  change μ ((fun ω : Ω => fun k : Fin n => S.Z k ω) ⁻¹' E)
      ≥ 1 - ENNReal.ofReal δ
  rw [hmap]
  exact hE_prob

/-! ## Restricting a product sample to a sub-index

A sample split, a cross-fitting fold, and "the observations whose index lies in
`S`" are all the same operation: keep the coordinates satisfying a decidable
predicate and forget the rest.  Because the coordinates are independent, the
kept ones again have the product law over the sub-index. -/

section Restrict

variable {ι : Type*} [Fintype ι]

/-- Dropping the coordinates outside a decidable sub-index of a product of probability measures
leaves the product measure over that sub-index: the retained coordinates carry exactly their own
product law, with no trace of the discarded ones.

The factors are allowed to differ from coordinate to coordinate. -/
theorem measurePreserving_pi_restrict_dep {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (fun (s : ∀ i, X i) (i : Subtype p) => s i.1)
      (Measure.pi μ) (Measure.pi fun i : Subtype p => μ i.1) := by
  have hsplit := MeasureTheory.measurePreserving_piEquivPiSubtypeProd (μ := μ) p
  have hfst : MeasurePreserving Prod.fst
      ((Measure.pi fun i : Subtype p => μ i.1).prod
        (Measure.pi fun i : Subtype (fun i => ¬ p i) => μ i.1))
      (Measure.pi fun i : Subtype p => μ i.1) := measurePreserving_fst
  simpa [MeasurableEquiv.piEquivPiSubtypeProd, Function.comp_def] using hfst.comp hsplit

/-- Dropping the coordinates outside a decidable sub-index of an i.i.d. product sample leaves the
i.i.d. product sample over that sub-index. -/
theorem measurePreserving_pi_restrict {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (fun (s : ι → X) (i : Subtype p) => s i.1)
      (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : Subtype p => μ) :=
  measurePreserving_pi_restrict_dep (fun _ : ι => μ) p

/-- The law of the sub-index coordinates of an i.i.d. product sample is the product law over that
sub-index; this is the pushforward packaging of the measure-preserving statement. -/
theorem map_pi_restrict {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : ι → Prop) [DecidablePred p] :
    (Measure.pi fun _ : ι => μ).map (fun (s : ι → X) (i : Subtype p) => s i.1) =
      Measure.pi fun _ : Subtype p => μ :=
  (measurePreserving_pi_restrict μ p).map_eq

/-- Averaging a function of the sub-index coordinates over the whole i.i.d. product sample is the
same as averaging it over an i.i.d. product sample indexed by the sub-index alone.

No measurability hypothesis is needed: when the integrand is not almost everywhere strongly
measurable both sides vanish. -/
theorem integral_comp_pi_restrict {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : ι → Prop) [DecidablePred p]
    (g : (Subtype p → X) → E) :
    ∫ s : ι → X, g (fun i : Subtype p => s i.1) ∂(Measure.pi fun _ : ι => μ) =
      ∫ z, g z ∂(Measure.pi fun _ : Subtype p => μ) := by
  classical
  have hmeasf : Measurable (fun (s : ι → X) (i : Subtype p) => s i.1) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.1
  by_cases hg : AEStronglyMeasurable g (Measure.pi fun _ : Subtype p => μ)
  · have hmap := integral_map (f := g) hmeasf.aemeasurable (by rwa [map_pi_restrict μ p])
    rw [map_pi_restrict μ p] at hmap
    exact hmap.symm
  · rw [integral_undef (fun h => hg h.aestronglyMeasurable),
      integral_undef fun h => hg ?_]
    -- Transport `L⁰`-measurability back across the product splitting.
    have hsplit := MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      (μ := fun _ : ι => μ) p
    have hcomp := h.aestronglyMeasurable.comp_measurePreserving
      (hsplit.symm (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) p))
    rw [show (fun s : ι → X => g fun i : Subtype p => s i.1) ∘
        ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) p).symm =
          fun w => g w.1 by
      funext w
      simp only [Function.comp_apply]
      refine congrArg g ?_
      funext i
      simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, i.2]] at hcomp
    exact AEStronglyMeasurable.of_comp_fst hcomp (IsProbabilityMeasure.ne_zero _)

/-- Dropping the coordinates outside a finite set of indices of an i.i.d. product sample leaves the
i.i.d. product sample indexed by that finite set. -/
theorem measurePreserving_pi_restrict_finset {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (S : Finset ι) :
    MeasurePreserving (fun (s : ι → X) (i : {i : ι // i ∈ S}) => s i.1)
      (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : {i : ι // i ∈ S} => μ) := by
  classical
  convert measurePreserving_pi_restrict μ (· ∈ S) using 2

/-- The law of the coordinates in a finite index set of an i.i.d. product sample is the product law
over that finite set; this is the pushforward packaging of the measure-preserving statement. -/
theorem map_pi_restrict_finset {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (S : Finset ι) :
    (Measure.pi fun _ : ι => μ).map (fun (s : ι → X) (i : {i : ι // i ∈ S}) => s i.1) =
      Measure.pi fun _ : {i : ι // i ∈ S} => μ :=
  (measurePreserving_pi_restrict_finset μ S).map_eq

/-- Averaging a function of the coordinates in a finite index set over the whole i.i.d. product
sample is the same as averaging it over an i.i.d. product sample indexed by that finite set. -/
theorem integral_comp_pi_restrict_finset {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsProbabilityMeasure μ] (S : Finset ι)
    (g : ({i : ι // i ∈ S} → X) → E) :
    ∫ s : ι → X, g (fun i : {i : ι // i ∈ S} => s i.1) ∂(Measure.pi fun _ : ι => μ) =
      ∫ z, g z ∂(Measure.pi fun _ : {i : ι // i ∈ S} => μ) := by
  classical
  convert integral_comp_pi_restrict μ (· ∈ S) g using 2
  congr 1
  exact Subsingleton.elim _ _

end Restrict

/-! ## Existence of an i.i.d. sample

Papers routinely list "there exists an i.i.d. sample from `P`" among their
assumptions.  The two theorems below record that this assumption is vacuous. -/

/-- Existence of an i.i.d. sample with a given law: the assertion that some probability space
carries an independent, identically distributed sample whose common marginal law is a given
measure. -/
def HasIIDSample {X : Type u} [MeasurableSpace X] (P : Measure X) : Prop :=
  ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
    Nonempty (@IIDSample Ω X mΩ _ μ P)

/-- An i.i.d. sample with a given law always exists: every probability measure is the common
marginal of some independent, identically distributed sample, realised on the infinite product
space by the coordinate projections. -/
theorem hasIIDSample_of_isProbabilityMeasure {X : Type u} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] : HasIIDSample P :=
  ⟨ℕ → X, inferInstance, Measure.infinitePi fun _ : ℕ => P, ⟨iidSample_infinitePi P⟩⟩

/-- The existence of an i.i.d. sample with a prescribed common marginal is equivalent to that
marginal being a probability measure.

In other words, assuming "the data are an i.i.d. draw from `P`" as an *existential* over ambient
probability spaces adds nothing to the assumption that `P` is a probability law: the infinite
product space always supplies such a sample. Any substantive sampling content has to come from
fixing the sample, not from asserting that one exists. -/
theorem hasIIDSample_iff_isProbabilityMeasure {X : Type u} [MeasurableSpace X] (P : Measure X) :
    HasIIDSample P ↔ IsProbabilityMeasure P := by
  refine ⟨?_, fun _ => hasIIDSample_of_isProbabilityMeasure P⟩
  rintro ⟨Ω, mΩ, μ, ⟨S⟩⟩
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  rw [← S.map_eq 0]
  exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable

end Causalean.Stat
