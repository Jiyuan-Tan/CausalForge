/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax lower bound: witness measure identities
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Core

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory
open scoped ENNReal Topology

set_option linter.unusedVariables false

-- @node: dose-data-probability
/-- If the component laws are probability measures and the two-point means are bounded
inside the outcome range, then the witness data law is a probability measure. -/
lemma doseDataMeasure_isProbabilityMeasure {d : ℕ}
    {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ}
    (hB : 0 < B)
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    IsProbabilityMeasure (doseDataMeasure p0 q0 B alpha t0 lambda h zeta) := by
  classical
  let mX : Measure (Fin d → ℝ) := doseXMeasure p0
  let mA : Measure ℝ := doseAMeasure q0
  let mu : ℝ → (Fin d → ℝ) → ℝ := doseWitnessMu alpha t0 lambda h zeta
  have hmapprob :
      ∀ x a, IsProbabilityMeasure ((twoPointMean B (mu a x)).map
        (fun y => DoseObs.mk y a x)) := by
    intro x a
    letI : IsProbabilityMeasure (twoPointMean B (mu a x)) :=
      twoPointMean_isProbabilityMeasure hB (hmu a x)
    exact Measure.isProbabilityMeasure_map (measurable_doseObs_mk a x).aemeasurable
  have hmap :
      ∀ x, Measurable fun a : ℝ =>
        (twoPointMean B (mu a x)).map (fun y => DoseObs.mk y a x) := by
    intro x
    simpa [mu] using
      measurable_twoPointMean_map_doseObs (d := d) B alpha t0 lambda h zeta x
  have hinner :
      ∀ x, IsProbabilityMeasure (mA.bind fun a =>
        (twoPointMean B (mu a x)).map (fun y => DoseObs.mk y a x)) := by
    intro x
    letI : IsProbabilityMeasure mA := hpA
    exact isProbabilityMeasure_bind (hmap x).aemeasurable
      (Filter.Eventually.of_forall fun a => hmapprob x a)
  have hker :
      Measurable fun x => mA.bind fun a =>
        (twoPointMean B (mu a x)).map (fun y => DoseObs.mk y a x) := by
    simpa [mu] using
      measurable_doseOutcomeKernel (d := d) q0 B alpha t0 lambda h zeta
  change IsProbabilityMeasure (mX.bind fun x => mA.bind fun a =>
    (twoPointMean B (mu a x)).map (fun y => DoseObs.mk y a x))
  letI : IsProbabilityMeasure mX := hpX
  exact isProbabilityMeasure_bind hker.aemeasurable
    (Filter.Eventually.of_forall fun x => hinner x)

-- @node: dose-data-x-marginal
/-- Under the valid two-point outcome construction, marginalizing the witness data law
to covariates recovers the witness covariate measure. -/
lemma doseDataMeasure_map_X {d : ℕ}
    {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ}
    (hB : 0 < B)
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    (doseDataMeasure p0 q0 B alpha t0 lambda h zeta).map (fun O : DoseObs d => O.X) =
      doseXMeasure p0 := by
  classical
  let mX : Measure (Fin d → ℝ) := doseXMeasure p0
  let mA : Measure ℝ := doseAMeasure q0
  let mu : ℝ → (Fin d → ℝ) → ℝ := doseWitnessMu alpha t0 lambda h zeta
  have hκ1 : Measurable fun _x : Fin d → ℝ => mA := measurable_const
  have hp1 : ∀ _x : Fin d → ℝ, IsProbabilityMeasure mA := fun _ => hpA
  have hκ2 : Measurable fun p : (Fin d → ℝ) × ℝ => twoPointMean B (mu p.2 p.1) := by
    unfold mu doseWitnessMu
    fun_prop
  have hp2 : ∀ x a, IsProbabilityMeasure (twoPointMean B (mu a x)) := by
    intro x a
    exact twoPointMean_isProbabilityMeasure hB (hmu a x)
  have hg : ∀ (x : Fin d → ℝ) (a : ℝ), Measurable (fun y : ℝ => DoseObs.mk y a x) := by
    intro x a
    exact measurable_doseObs_mk a x
  have hmap :
      ∀ x, Measurable fun a : ℝ =>
        (twoPointMean B (mu a x)).map (fun y => DoseObs.mk y a x) := by
    intro x
    simpa [mu] using
      measurable_twoPointMean_map_doseObs (d := d) B alpha t0 lambda h zeta x
  have hker :
      Measurable fun x => mA.bind fun a =>
        (twoPointMean B (mu a x)).map (fun y => DoseObs.mk y a x) := by
    simpa [mu] using
      measurable_doseOutcomeKernel (d := d) q0 B alpha t0 lambda h zeta
  have h := Causalean.Mathlib.MeasureTheory.map_bind_bind_map_proj
    (m := mX) (κ₁ := fun _x : Fin d → ℝ => mA)
    (κ₂ := fun x a => twoPointMean B (mu a x))
    (g := fun x a y => DoseObs.mk y a x) (π := fun O : DoseObs d => O.X)
    hκ1 hp1 hκ2 hp2 hg hmap hker measurable_doseObs_X (by intro x a y; rfl)
  simpa [doseDataMeasure, mX, mA, mu] using h

-- @node: dose-witness-px-density
/-- Under the stated outcome and treatment-law assumptions, the witness covariate
density is tied to the covariate marginal of the witness data law. -/
lemma doseWitness_pxDens {d : ℕ}
    {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ}
    (hB : 0 < B)
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    PxIsXDensity (doseWitness p0 q0 B alpha t0 lambda h zeta) := by
  unfold PxIsXDensity doseWitness doseXMeasure
  exact doseDataMeasure_map_X (d := d) (p0 := p0) (q0 := q0)
    (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
    (h := h) (zeta := zeta) hB hpA hmu

-- @node: dose-witness-consistency
/-- The witness potential-outcome process is consistent with the observed outcome at
the realized treatment for every observation. -/
lemma doseWitness_consistency {d : ℕ}
    (p0 : (Fin d → ℝ) → ℝ) (q0 : ℝ → ℝ)
    (B alpha t0 lambda h zeta : ℝ) :
    Consistency (doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta) := by
  exact Filter.Eventually.of_forall fun O => by
    simp [doseWitness, dosePotential]

-- @node: dose-data-y-support
/-- If the two-point outcome support is contained in the target bound, then the witness
data law almost surely has outcomes inside that bounded interval. -/
lemma doseDataMeasure_ae_Y_mem_Icc {d : ℕ}
    {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B M alpha t0 lambda h zeta : ℝ}
    (hBM : |B| ≤ M) :
    ∀ᵐ O ∂doseDataMeasure p0 q0 B alpha t0 lambda h zeta, O.Y ∈ Set.Icc (-M) M := by
  classical
  let Sbad : Set (DoseObs d) := {O | O.Y ∉ Set.Icc (-M) M}
  have hSbad : MeasurableSet Sbad := by
    unfold Sbad
    exact measurable_doseObs_Y measurableSet_Icc.compl
  rw [ae_iff]
  change (doseDataMeasure p0 q0 B alpha t0 lambda h zeta) Sbad = 0
  let mX : Measure (Fin d → ℝ) := doseXMeasure p0
  let mA : Measure ℝ := doseAMeasure q0
  let mu : ℝ → (Fin d → ℝ) → ℝ := doseWitnessMu alpha t0 lambda h zeta
  have hmap :
      ∀ x, Measurable fun a : ℝ =>
        (twoPointMean B (mu a x)).map (fun y => DoseObs.mk y a x) := by
    intro x
    simpa [mu] using
      measurable_twoPointMean_map_doseObs (d := d) B alpha t0 lambda h zeta x
  have hker :
      Measurable fun x => mA.bind fun a =>
        (twoPointMean B (mu a x)).map (fun y => DoseObs.mk y a x) := by
    simpa [mu] using
      measurable_doseOutcomeKernel (d := d) q0 B alpha t0 lambda h zeta
  have hinner_zero :
      ∀ x a, ((twoPointMean B (mu a x)).map (fun y => DoseObs.mk y a x)) Sbad = 0 := by
    intro x a
    rw [Measure.map_apply (measurable_doseObs_mk a x) hSbad]
    simpa [Sbad] using
      twoPointMean_bad_support_zero (B := B) (M := M) (u := mu a x) hBM
  have hmid_zero :
      ∀ x, (mA.bind fun a =>
        (twoPointMean B (mu a x)).map (fun y => DoseObs.mk y a x)) Sbad = 0 := by
    intro x
    rw [Measure.bind_apply hSbad (hmap x).aemeasurable]
    simp [hinner_zero x]
  unfold doseDataMeasure
  change (mX.bind fun x => mA.bind fun a =>
    (twoPointMean B (mu a x)).map (fun y => DoseObs.mk y a x)) Sbad = 0
  rw [Measure.bind_apply hSbad hker.aemeasurable]
  simp [hmid_zero]

-- @node: dose-witness-bounded-outcome
/-- If the two-point outcome support is contained in the target bound, then the witness
law satisfies the bounded-outcome condition at that bound. -/
lemma doseWitness_bdd {d : ℕ}
    {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B M alpha t0 lambda h zeta : ℝ}
    (hBM : |B| ≤ M) :
    BoundedOutcome (doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta) M := by
  simpa [BoundedOutcome, doseWitness] using
    (doseDataMeasure_ae_Y_mem_Icc (d := d) (p0 := p0) (q0 := q0)
      (B := B) (M := M) (alpha := alpha) (t0 := t0)
      (lambda := lambda) (h := h) (zeta := zeta) hBM).mono
      (fun O hO => abs_le.mpr hO)

end CausalSmith.Stat.DoseResponseMinimax
