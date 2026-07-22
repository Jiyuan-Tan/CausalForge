/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax lower bound: witness base lemmas

Measure-theoretic and two-point-channel primitives for the genuine dose-response
two-point witnesses.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Divergence
import Causalean.Mathlib.MeasureTheory.IntegralBind

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory
open scoped ENNReal

-- The `twoPointMean` measurability/probability/integral/mean/support lemmas were promoted to
-- `Causalean.Mathlib.Probability.SignedTwoPoint`; re-export them so call sites resolve unchanged.
export Causalean.Mathlib.Probability
  (measurable_twoPointMean twoPointMean_isProbabilityMeasure twoPointMean_integral
    twoPointMean_mean twoPointMean_bad_support_zero)

-- @node: measurable-set-cube
/-- The unit covariate cube is a measurable set. -/
lemma measurableSet_cube (d : ℕ) : MeasurableSet (cube d) := by
  unfold cube
  measurability

-- @node: restrict-withDensity-ofReal-isProbability
/-- A nonnegative density on a measurable restriction that integrates to one defines
a probability measure after weighting the restricted measure. -/
lemma restrict_withDensity_ofReal_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → ℝ}
    (hs : MeasurableSet s) (h_nonneg : ∀ x ∈ s, 0 ≤ f x)
    (h_int : (∫ x, f x ∂(μ.restrict s)) = 1) :
    IsProbabilityMeasure ((μ.restrict s).withDensity fun x => ENNReal.ofReal (f x)) := by
  rw [isProbabilityMeasure_iff]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hf_int : Integrable f (μ.restrict s) := by
    refine Integrable.of_integral_ne_zero ?_
    simp [h_int]
  have hf_nn : 0 ≤ᵐ[μ.restrict s] f := by
    rw [Filter.EventuallyLE]
    exact (ae_restrict_iff' hs).2 (Filter.Eventually.of_forall fun x hx => h_nonneg x hx)
  rw [← ofReal_integral_eq_lintegral_ofReal hf_int hf_nn]
  simp [h_int]

-- @node: integrable-of-ae-bounded
/-- On a finite measure space, a measurable real function that is almost surely
bounded in absolute value is integrable. -/
lemma integrable_of_measurable_ae_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hfmeas : Measurable f) (C : ℝ) (hC : ∀ᵐ x ∂μ, |f x| ≤ C) :
    Integrable f μ := by
  refine Integrable.of_bound hfmeas.aestronglyMeasurable (max C 0) ?_
  filter_upwards [hC] with x hx
  exact (by simpa [Real.norm_eq_abs] using hx.trans (le_max_left C 0))

-- @node: doseObs-measurability
/-- The map sending an observation to its outcome, treatment, and covariate tuple is
measurable. -/
lemma measurable_doseObs_tuple {d : ℕ} :
    Measurable (fun O : DoseObs d => (O.Y, O.A, O.X)) :=
  Measurable.of_comap_le le_rfl

/-- The observed outcome coordinate is a measurable function of the observation. -/
lemma measurable_doseObs_Y {d : ℕ} : Measurable (fun O : DoseObs d => O.Y) := by
  change Measurable ((fun p : ℝ × (ℝ × (Fin d → ℝ)) => p.1) ∘
    (fun O : DoseObs d => (O.Y, O.A, O.X)))
  exact measurable_fst.comp measurable_doseObs_tuple

/-- The observed treatment coordinate is a measurable function of the observation. -/
lemma measurable_doseObs_A {d : ℕ} : Measurable (fun O : DoseObs d => O.A) := by
  change Measurable ((fun p : ℝ × (ℝ × (Fin d → ℝ)) => p.2.1) ∘
    (fun O : DoseObs d => (O.Y, O.A, O.X)))
  exact (measurable_fst.comp measurable_snd).comp measurable_doseObs_tuple

/-- The observed covariate coordinate is a measurable function of the observation. -/
lemma measurable_doseObs_X {d : ℕ} : Measurable (fun O : DoseObs d => O.X) := by
  change Measurable ((fun p : ℝ × (ℝ × (Fin d → ℝ)) => p.2.2) ∘
    (fun O : DoseObs d => (O.Y, O.A, O.X)))
  exact (measurable_snd.comp measurable_snd).comp measurable_doseObs_tuple

/-- The observed-data space has measurable singleton sets. -/
instance instMeasurableSingletonClassDoseObs {d : ℕ} :
    MeasurableSingletonClass (DoseObs d) := by
  refine ⟨?_⟩
  intro O
  have hset : MeasurableSet ((fun O' : DoseObs d => (O'.Y, O'.A, O'.X)) ⁻¹'
      ({(O.Y, O.A, O.X)} : Set (ℝ × ℝ × (Fin d → ℝ)))) :=
    measurable_doseObs_tuple (measurableSet_singleton _)
  convert hset using 1
  ext O'
  cases O
  cases O'
  simp

/-- For fixed treatment and covariates, forming an observation from an outcome is
measurable. -/
@[fun_prop] lemma measurable_doseObs_mk {d : ℕ} (a : ℝ) (x : Fin d → ℝ) :
    Measurable (fun y : ℝ => DoseObs.mk y a x) := by
  rw [measurable_comap_iff]
  fun_prop

/-- Forming an observation from covariates, treatment, and outcome is measurable. -/
@[fun_prop] lemma measurable_doseObs_mk_AX {d : ℕ} :
    Measurable (fun p : (Fin d → ℝ) × ℝ × ℝ => DoseObs.mk p.2.2 p.2.1 p.1) := by
  rw [measurable_comap_iff]
  fun_prop

-- @node: map-bind-map-proj
/-- Base-coordinate marginal of a `bind` whose fibre is reattached by a map. -/
lemma map_bind_map_proj {α β δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]
    {m : Measure α} {κ : α → Measure β} {g : α → β → δ} {π : δ → α}
    (_hκ : Measurable κ) (hp : ∀ a, IsProbabilityMeasure (κ a))
    (hg : ∀ a, Measurable (g a))
    (hmap : Measurable fun a => (κ a).map (g a))
    (hπ : Measurable π) (hπg : ∀ a b, π (g a b) = a) :
    (m.bind fun a => (κ a).map (g a)).map π = m := by
  have hdπ : Measurable (fun z => Measure.dirac (π z)) := Measure.measurable_dirac.comp hπ
  have hstep :
      (fun a => ((κ a).map (g a)).bind fun z => Measure.dirac (π z))
        = fun a => Measure.dirac a := by
    funext a
    rw [Measure.bind_dirac_eq_map _ hπ, Measure.map_map hπ (hg a)]
    have hc : (π ∘ g a) = fun _ => a := funext (hπg a)
    rw [hc, Measure.map_const, (hp a).measure_univ, one_smul]
  rw [← Measure.bind_dirac_eq_map _ hπ, Measure.bind_bind hmap.aemeasurable hdπ.aemeasurable]
  rw [hstep, Measure.bind_dirac]

end CausalSmith.Stat.DoseResponseMinimax
