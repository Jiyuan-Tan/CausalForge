/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax lower bound: single-bind (channel) restructuring

The genuine joint data law `doseDataMeasure` was built as a nested
`X → A → Y` bind. For the conditional-mean (regression), ignorability, and KL
chain-rule arguments it is far cleaner to view it as a SINGLE bind of the shared
`(A,X)`-marginal `doseAXMeasure` against the outcome Markov kernel
`doseChannelAX`. This file records that restructuring and the marginal facts that
the downstream leaves consume.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Core

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {d : ℕ}

-- @node: dose-channel-ax
/-- The outcome Markov kernel `(a,x) ↦ twoPointMean B (μ_ζ(a,x))` pushed onto the
observed-unit space by `y ↦ (y, a, x)`. This is the single conditional kernel that,
composed with the shared `(A,X)`-marginal `doseAXMeasure`, reproduces the genuine
joint law `doseDataMeasure`. -/
noncomputable def doseChannelAX (p0 : (Fin d → ℝ) → ℝ) (q0 : ℝ → ℝ)
    (B alpha t0 lambda h zeta : ℝ) :
    Kernel (ℝ × (Fin d → ℝ)) (DoseObs d) where
  toFun := fun p =>
    (twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta p.1 p.2)).map
      (fun y => DoseObs.mk y p.1 p.2)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ ?_
    intro S hS
    exact (measurable_twoPointMean_map_doseObs_pair (d := d) B alpha t0 lambda h zeta S hS).comp
      (measurable_snd.prodMk measurable_fst)

/-- Applying the outcome channel at a treatment-covariate pair gives the two-point
outcome law pushed forward to the observed-data space at that same pair. -/
@[simp] lemma doseChannelAX_apply (p0 : (Fin d → ℝ) → ℝ) (q0 : ℝ → ℝ)
    (B alpha t0 lambda h zeta : ℝ) (p : ℝ × (Fin d → ℝ)) :
    doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta p =
      (twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta p.1 p.2)).map
        (fun y => DoseObs.mk y p.1 p.2) := rfl

/-- If the two-point outcome laws are valid probability laws, then the witness outcome
channel is a Markov kernel. -/
instance instIsMarkovDoseChannelAX
    {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ} (hB : 0 < B)
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    IsMarkovKernel (doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta) := by
  refine ⟨fun p => ?_⟩
  rw [doseChannelAX_apply]
  letI : IsProbabilityMeasure
      (twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta p.1 p.2)) :=
    twoPointMean_isProbabilityMeasure hB (hmu p.1 p.2)
  exact Measure.isProbabilityMeasure_map (measurable_doseObs_mk p.1 p.2).aemeasurable

-- @node: dose-ax-probability
/-- If the witness covariate and treatment measures are probability measures, then
their joint treatment-covariate measure is also a probability measure. -/
lemma doseAXMeasure_isProbabilityMeasure {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hpA : IsProbabilityMeasure (doseAMeasure q0)) :
    IsProbabilityMeasure (doseAXMeasure (d := d) p0 q0) := by
  classical
  let mX : Measure (Fin d → ℝ) := doseXMeasure p0
  let mA : Measure ℝ := doseAMeasure q0
  have hmap : Measurable fun x : Fin d → ℝ => mA.map fun a : ℝ => (a, x) := by
    letI : IsProbabilityMeasure mA := hpA
    exact Measurable.map_prodMk_right (μ := mA)
  have hprob : ∀ x : Fin d → ℝ, IsProbabilityMeasure (mA.map fun a : ℝ => (a, x)) := by
    intro x
    letI : IsProbabilityMeasure mA := hpA
    exact Measure.isProbabilityMeasure_map measurable_prodMk_right.aemeasurable
  change IsProbabilityMeasure (mX.bind fun x => mA.map fun a : ℝ => (a, x))
  letI : IsProbabilityMeasure mX := hpX
  exact isProbabilityMeasure_bind hmap.aemeasurable
    (Filter.Eventually.of_forall hprob)

-- @node: dose-data-eq-axbind
/-- The genuine nested `X → A → Y` joint law equals the single bind of the shared
`(A,X)`-marginal against the outcome channel. This is the bridge that lets the
regression, ignorability, and KL leaves work over one `Measure.bind`. -/
lemma doseDataMeasure_eq_AXbind {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ} :
    doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta =
      (doseAXMeasure (d := d) p0 q0).bind
        (doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta) := by
  classical
  let mX : Measure (Fin d → ℝ) := doseXMeasure p0
  let mA : Measure ℝ := doseAMeasure q0
  let κ : ℝ × (Fin d → ℝ) → Measure (DoseObs d) :=
    ⇑(doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta)
  haveI : SFinite mA := by
    dsimp [mA]
    unfold doseAMeasure
    infer_instance
  have hAXMeas : Measurable fun x : Fin d → ℝ => mA.map fun a : ℝ => (a, x) := by
    exact Measurable.map_prodMk_right (μ := mA)
  have hκMeas : Measurable κ := by
    exact (doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta).measurable
  have hinner (x : Fin d → ℝ) :
      (mA.map (fun a : ℝ => (a, x))).bind κ = mA.bind (fun a => κ (a, x)) := by
    ext s hs
    have hcomp : AEMeasurable (fun a : ℝ => κ (a, x)) mA := by
      simpa [Function.comp_def] using
        hκMeas.aemeasurable.comp_measurable (measurable_prodMk_right (y := x))
    have hκs : AEMeasurable (fun p => κ p s) (mA.map fun a : ℝ => (a, x)) :=
      (Measure.measurable_coe hs).comp_aemeasurable hκMeas.aemeasurable
    rw [Measure.bind_apply hs hκMeas.aemeasurable]
    rw [Measure.bind_apply hs hcomp]
    rw [lintegral_map' hκs measurable_prodMk_right.aemeasurable]
  unfold doseDataMeasure doseAXMeasure
  change mX.bind (fun x => mA.bind fun a => κ (a, x)) =
    (mX.bind fun x => mA.map fun a : ℝ => (a, x)).bind κ
  rw [Measure.bind_bind hAXMeas.aemeasurable hκMeas.aemeasurable]
  apply congrArg (Measure.bind mX)
  funext x
  exact (hinner x).symm

end CausalSmith.Stat.DoseResponseMinimax
