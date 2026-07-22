/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax lower bound: genuine witness definitions
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Base
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.WithDensity

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory
open scoped ENNReal Topology

/-! ## Smooth treatment bump -/

-- @node: dose-bump
/-- A fixed smooth bump supported in `(-1,1)` and equal to one near zero. -/
noncomputable def doseContDiffBump : ContDiffBump (0 : ℝ) :=
  ⟨(1 / 2 : ℝ), 1, by norm_num, by norm_num⟩

-- @node: dose-bump-function
/-- The treatment bump is the fixed smooth bump function evaluated at a real argument. -/
noncomputable def doseBump (z : ℝ) : ℝ :=
  doseContDiffBump z

/-- The treatment bump equals one at the center of the bump. -/
lemma doseBump_zero : doseBump 0 = 1 := by
  unfold doseBump doseContDiffBump
  exact ContDiffBump.one_of_mem_closedBall _ (by simp [Metric.mem_closedBall])

/-- The treatment bump is everywhere nonnegative. -/
lemma doseBump_nonneg (z : ℝ) : 0 ≤ doseBump z := by
  unfold doseBump
  exact doseContDiffBump.nonneg

/-- The treatment bump is everywhere bounded above by one. -/
lemma doseBump_le_one (z : ℝ) : doseBump z ≤ 1 := by
  unfold doseBump
  exact doseContDiffBump.le_one

/-- The absolute value of the treatment bump is everywhere bounded by one. -/
lemma doseBump_abs_le_one (z : ℝ) : |doseBump z| ≤ 1 := by
  rw [abs_of_nonneg (doseBump_nonneg z)]
  exact doseBump_le_one z

/-- The treatment bump vanishes at every point whose distance from the center is at
least one in the normalized coordinate. -/
lemma doseBump_eq_zero_of_one_le_abs {z : ℝ} (hz : 1 ≤ |z|) :
    doseBump z = 0 := by
  unfold doseBump doseContDiffBump
  refine ContDiffBump.zero_of_le_dist _ ?_
  simpa [Real.dist_eq, abs_sub_comm] using hz

/-- The treatment bump is a measurable real-valued function. -/
@[fun_prop] lemma measurable_doseBump : Measurable doseBump := by
  unfold doseBump
  exact (doseContDiffBump.contDiff (n := ⊤)).continuous.measurable

/-! ## Genuine joint law -/

-- @node: dose-witness-mu
/-- The witness conditional mean is a localized treatment bump with amplitude
given by the product of the sign, scale, bandwidth power, and smoothness constant. -/
noncomputable def doseWitnessMu {d : ℕ} (alpha t0 lambda h zeta : ℝ) :
    ℝ → (Fin d → ℝ) → ℝ :=
  fun a _x => zeta * lambda * h ^ alpha * doseBump ((a - t0) / h)

/-- The witness conditional mean is measurable as a function of treatment and
covariates. -/
lemma measurable_doseWitnessMu {d : ℕ} (alpha t0 lambda h zeta : ℝ) :
    Measurable (fun p : ℝ × (Fin d → ℝ) =>
      doseWitnessMu (d := d) alpha t0 lambda h zeta p.1 p.2) := by
  unfold doseWitnessMu
  fun_prop

private lemma measurable_doseObs_support_indicator_A {d : ℕ}
    (y : ℝ) (x : Fin d → ℝ) (S : Set (DoseObs d)) (hS : MeasurableSet S) :
    Measurable fun a : ℝ =>
      ((fun y' : ℝ => DoseObs.mk y' a x) ⁻¹' S).indicator
        (fun _ : ℝ => (1 : ℝ≥0∞)) y := by
  have hmk : Measurable fun a : ℝ => DoseObs.mk y a x := by
    rw [measurable_comap_iff]
    fun_prop
  have hset : MeasurableSet ((fun a : ℝ => DoseObs.mk y a x) ⁻¹' S) :=
    hS.preimage hmk
  convert measurable_const.indicator hset using 1

private lemma measurable_doseObs_support_indicator_pair {d : ℕ}
    (y : ℝ) (S : Set (DoseObs d)) (hS : MeasurableSet S) :
    Measurable fun p : (Fin d → ℝ) × ℝ =>
      ((fun y' : ℝ => DoseObs.mk y' p.2 p.1) ⁻¹' S).indicator
        (fun _ : ℝ => (1 : ℝ≥0∞)) y := by
  have hmk : Measurable fun p : (Fin d → ℝ) × ℝ => DoseObs.mk y p.2 p.1 := by
    rw [measurable_comap_iff]
    fun_prop
  have hset : MeasurableSet
      ((fun p : (Fin d → ℝ) × ℝ => DoseObs.mk y p.2 p.1) ⁻¹' S) :=
    hS.preimage hmk
  convert measurable_const.indicator hset using 1

-- @node: twoPointMean-map-doseObs-measurable
/-- For fixed covariates, the two-point outcome law pushed to observed triples varies
measurably with the treatment value. -/
lemma measurable_twoPointMean_map_doseObs {d : ℕ}
    (B alpha t0 lambda h zeta : ℝ) (x : Fin d → ℝ) :
    Measurable fun a : ℝ =>
      (twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta a x)).map
        (fun y => DoseObs.mk y a x) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro S hS
  unfold twoPointMean doseWitnessMu
  simp_rw [Measure.map_apply (measurable_doseObs_mk _ _) hS]
  simp only [Measure.add_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply]
  simp only [smul_eq_mul]
  exact
    ((by fun_prop :
      Measurable fun a : ℝ =>
        ENNReal.ofReal ((1 + zeta * lambda * h ^ alpha *
          doseBump ((a - t0) / h) / B) / 2)).mul
      (measurable_doseObs_support_indicator_A (d := d) B x S hS)).add
    ((by fun_prop :
      Measurable fun a : ℝ =>
        ENNReal.ofReal ((1 - zeta * lambda * h ^ alpha *
          doseBump ((a - t0) / h) / B) / 2)).mul
      (measurable_doseObs_support_indicator_A (d := d) (-B) x S hS))

-- @node: twoPointMean-map-doseObs-pair-measurable
/-- The probability assigned by the pushed-forward two-point outcome law to any
measurable event is a measurable function of covariates and treatment. -/
lemma measurable_twoPointMean_map_doseObs_pair {d : ℕ}
    (B alpha t0 lambda h zeta : ℝ) (S : Set (DoseObs d)) (hS : MeasurableSet S) :
    Measurable fun p : (Fin d → ℝ) × ℝ =>
      ((twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta p.2 p.1)).map
        (fun y => DoseObs.mk y p.2 p.1)) S := by
  simp_rw [Measure.map_apply (measurable_doseObs_mk _ _) hS]
  unfold twoPointMean doseWitnessMu
  simp only [Measure.add_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply]
  simp only [smul_eq_mul]
  exact
    ((by fun_prop :
      Measurable fun p : (Fin d → ℝ) × ℝ =>
        ENNReal.ofReal ((1 + zeta * lambda * h ^ alpha *
          doseBump ((p.2 - t0) / h) / B) / 2)).mul
      (measurable_doseObs_support_indicator_pair (d := d) B S hS)).add
    ((by fun_prop :
      Measurable fun p : (Fin d → ℝ) × ℝ =>
        ENNReal.ofReal ((1 - zeta * lambda * h ^ alpha *
          doseBump ((p.2 - t0) / h) / B) / 2)).mul
      (measurable_doseObs_support_indicator_pair (d := d) (-B) S hS))

-- @node: dose-x-measure
/-- The witness covariate measure is Lebesgue measure on the unit covariate cube
weighted by the covariate density. -/
noncomputable def doseXMeasure {d : ℕ} (p0 : (Fin d → ℝ) → ℝ) :
    Measure (Fin d → ℝ) :=
  (volume.restrict (cube d)).withDensity fun x => ENNReal.ofReal (p0 x)

-- @node: dose-a-measure
/-- The witness treatment measure is Lebesgue measure on the unit treatment interval
weighted by the treatment density. -/
noncomputable def doseAMeasure (q0 : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity fun a => ENNReal.ofReal (q0 a)

-- @node: dose-outcome-kernel-measurable
/-- Integrating the treatment law against the two-point outcome law gives an outcome
kernel that is measurable as a function of covariates. -/
lemma measurable_doseOutcomeKernel {d : ℕ} (q0 : ℝ → ℝ)
    (B alpha t0 lambda h zeta : ℝ) :
    Measurable fun x : Fin d → ℝ =>
      (doseAMeasure q0).bind fun a =>
        (twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta a x)).map
          (fun y => DoseObs.mk y a x) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro S hS
  rw [show
      (fun x : Fin d → ℝ =>
        ((doseAMeasure q0).bind fun a =>
          (twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta a x)).map
            (fun y => DoseObs.mk y a x)) S)
        =
      fun x =>
        ∫⁻ a, ((twoPointMean B
            (doseWitnessMu (d := d) alpha t0 lambda h zeta a x)).map
              (fun y => DoseObs.mk y a x)) S ∂doseAMeasure q0 by
    funext x
    rw [Measure.bind_apply hS
      (measurable_twoPointMean_map_doseObs (d := d) B alpha t0 lambda h zeta x).aemeasurable]]
  haveI : SFinite (doseAMeasure q0) := by
    unfold doseAMeasure
    infer_instance
  exact Measurable.lintegral_prod_right'
    (measurable_twoPointMean_map_doseObs_pair (d := d) B alpha t0 lambda h zeta S hS)

-- @node: dose-ax-measure
/-- The joint treatment-covariate measure first samples covariates from their witness
measure and then samples treatment from its witness measure. -/
noncomputable def doseAXMeasure {d : ℕ}
    (p0 : (Fin d → ℝ) → ℝ) (q0 : ℝ → ℝ) :
    Measure (ℝ × (Fin d → ℝ)) :=
  (doseXMeasure p0).bind fun x =>
    (doseAMeasure q0).map fun a => (a, x)

-- @node: dose-data-measure
/-- The witness data law samples covariates, then treatment, and then a two-point
outcome distribution whose mean is the witness conditional mean. -/
noncomputable def doseDataMeasure {d : ℕ}
    (p0 : (Fin d → ℝ) → ℝ) (q0 : ℝ → ℝ)
    (B alpha t0 lambda h zeta : ℝ) : Measure (DoseObs d) :=
  (doseXMeasure p0).bind fun x =>
    (doseAMeasure q0).bind fun a =>
      (twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta a x)).map
        (fun y => DoseObs.mk y a x)

-- @node: dose-potential
/-- The witness potential-outcome process returns the observed outcome at the realized
treatment and otherwise returns the witness conditional mean at the queried treatment. -/
noncomputable def dosePotential {d : ℕ} (alpha t0 lambda h zeta : ℝ) :
    ℝ → DoseObs d → ℝ :=
  fun a O => if O.A = a then O.Y else doseWitnessMu (d := d) alpha t0 lambda h zeta a O.X

-- @node: dose-witness
/-- The witness law packages the explicit data law, covariate law, conditional mean,
treatment density, covariate density, and potential-outcome process into one model. -/
noncomputable def doseWitness {d : ℕ}
    (p0 : (Fin d → ℝ) → ℝ) (q0 : ℝ → ℝ)
    (B alpha t0 lambda h zeta : ℝ) : DoseLaw d where
  dataMeasure := doseDataMeasure p0 q0 B alpha t0 lambda h zeta
  PX := doseXMeasure p0
  mu := doseWitnessMu alpha t0 lambda h zeta
  pi := fun a _x => q0 a
  px := p0
  pot := dosePotential alpha t0 lambda h zeta

-- @node: dose-base-probability
/-- If the covariate density is nonnegative on the cube and integrates to one there,
then the witness covariate measure is a probability measure. -/
lemma doseXMeasure_isProbabilityMeasure {d : ℕ}
    {p0 : (Fin d → ℝ) → ℝ}
    (hp0_nonneg : ∀ x ∈ cube d, 0 ≤ p0 x)
    (hp0_int : (∫ x in cube d, p0 x) = 1) :
    IsProbabilityMeasure (doseXMeasure p0) := by
  unfold doseXMeasure
  refine restrict_withDensity_ofReal_isProbabilityMeasure (measurableSet_cube d) hp0_nonneg ?_
  simpa using hp0_int

/-- If the treatment density is nonnegative and integrates to one on the unit interval,
then the witness treatment measure is a probability measure. -/
lemma doseAMeasure_isProbabilityMeasure {q0 : ℝ → ℝ}
    (hq0_nonneg : ∀ a, 0 ≤ q0 a)
    (hq0_int : (∫ a in Set.Icc (0 : ℝ) 1, q0 a) = 1) :
    IsProbabilityMeasure (doseAMeasure q0) := by
  unfold doseAMeasure
  refine restrict_withDensity_ofReal_isProbabilityMeasure measurableSet_Icc ?_ ?_
  · intro a _ha
    exact hq0_nonneg a
  · simpa using hq0_int

end CausalSmith.Stat.DoseResponseMinimax
