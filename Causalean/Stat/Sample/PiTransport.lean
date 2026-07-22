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

/-! # Transport to Product Samples

This file proves that the joint observable of a finite independent identically
distributed sample pushes the underlying probability measure forward to the
corresponding finite product measure. It also transports high-probability events
on product samples back to events on the original sample space. -/

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

/-- The joint observable of the first `n` IID sample points pushes
`μ` forward to the product measure on `Fin n → X`. -/
lemma iidSample_finN_pushforward [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (n : ℕ) :
    μ.map (fun ω : Ω => fun k : Fin n => S.Z k ω) =
      Measure.pi (fun _ : Fin n => P) := by
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

/-- **Event transport along an IID sample (`Fin n` version).**

Given a measurable event `E ⊆ (Fin n → X)` of `Measure.pi P`-mass
`≥ 1 - ENNReal.ofReal δ`, the pullback along the joint observable
`Ψ ω k = S.Z k ω` is a measurable Ω-event of `μ`-mass
`≥ 1 - ENNReal.ofReal δ`. -/
lemma event_pullback_along_iidSample
    [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) (n : ℕ)
    {E : Set (Fin n → X)} (hE_meas : MeasurableSet E)
    {δ : ℝ}
    (hE_prob : Measure.pi (fun _ : Fin n => P) E ≥ 1 - ENNReal.ofReal δ) :
    let Ψ : Ω → (Fin n → X) := fun ω k => S.Z k ω
    let E' : Set Ω := Ψ ⁻¹' E
    MeasurableSet E' ∧ μ E' ≥ 1 - ENNReal.ofReal δ := by
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

end Causalean.Stat
