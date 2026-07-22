/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax lower bound: treatment-density semantic tie
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Regression

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

variable {d : ℕ}

-- @node: dose-data-ax-marginal
/-- Under a valid two-point outcome construction, marginalizing the witness data law
to treatment and covariates gives exactly the witness treatment-covariate measure. -/
lemma doseDataMeasure_map_AX {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ}
    (hB : 0 < B)
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta).map
        (fun O : DoseObs d => (O.A, O.X)) = doseAXMeasure (d := d) p0 q0 := by
  classical
  let mAX : Measure (ℝ × (Fin d → ℝ)) := doseAXMeasure (d := d) p0 q0
  let κ : Kernel (ℝ × (Fin d → ℝ)) (DoseObs d) :=
    doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta
  let π : DoseObs d → ℝ × (Fin d → ℝ) := fun O => (O.A, O.X)
  have hπ : Measurable π := measurable_doseObs_A.prod measurable_doseObs_X
  ext s hs
  have hpre : MeasurableSet (π ⁻¹' s) := hs.preimage hπ
  rw [Measure.map_apply hπ hs]
  rw [doseDataMeasure_eq_AXbind]
  change (mAX.bind κ) (π ⁻¹' s) = mAX s
  rw [Measure.bind_apply hpre κ.measurable.aemeasurable]
  have hinner :
      (fun p : ℝ × (Fin d → ℝ) => κ p (π ⁻¹' s)) =
        Set.indicator s (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    rw [show κ p =
        (twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta p.1 p.2)).map
          (fun y => DoseObs.mk y p.1 p.2) by rfl]
    rw [Measure.map_apply (measurable_doseObs_mk p.1 p.2) hpre]
    by_cases hp : p ∈ s
    · have hpre_univ :
          (fun y : ℝ => DoseObs.mk y p.1 p.2) ⁻¹' (π ⁻¹' s) = Set.univ := by
        ext y
        simp [π, hp]
      rw [hpre_univ]
      haveI : IsProbabilityMeasure
          (twoPointMean B (doseWitnessMu (d := d) alpha t0 lambda h zeta p.1 p.2)) :=
        twoPointMean_isProbabilityMeasure hB (hmu p.1 p.2)
      simp [Set.indicator, hp]
    · have hpre_empty :
          (fun y : ℝ => DoseObs.mk y p.1 p.2) ⁻¹' (π ⁻¹' s) = ∅ := by
        ext y
        simp [π, hp]
      rw [hpre_empty]
      simp [Set.indicator, hp]
  rw [hinner, lintegral_indicator hs, lintegral_const]
  simp only [one_mul]
  rw [Measure.restrict_apply MeasurableSet.univ]
  simp

-- @node: dose-ax-product
/-- The witness treatment-covariate measure is the product of the treatment measure
and the covariate measure. -/
lemma doseAXMeasure_eq_prod {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ} :
    doseAXMeasure (d := d) p0 q0 = (doseAMeasure q0).prod (doseXMeasure p0) := by
  classical
  let mX : Measure (Fin d → ℝ) := doseXMeasure p0
  let mA : Measure ℝ := doseAMeasure q0
  haveI : SFinite mA := by
    dsimp [mA]
    unfold doseAMeasure
    infer_instance
  haveI : SFinite mX := by
    dsimp [mX]
    unfold doseXMeasure
    infer_instance
  ext s hs
  have hmap : Measurable fun x : Fin d → ℝ => mA.map fun a : ℝ => (a, x) := by
    exact Measurable.map_prodMk_right (μ := mA)
  unfold doseAXMeasure
  change (mX.bind (fun x => mA.map fun a : ℝ => (a, x))) s = mA.prod mX s
  rw [Measure.bind_apply hs hmap.aemeasurable]
  simp_rw [Measure.map_apply measurable_prodMk_right hs]
  exact (Measure.prod_apply_symm (μ := mA) (ν := mX) hs).symm

-- @node: dose-ax-density
/-- If the treatment density is nonnegative and both component densities integrate to
one, then the joint treatment-covariate measure has product density. -/
lemma doseAXMeasure_density {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    (hq0_nonneg : ∀ a, 0 ≤ q0 a)
    (hp0_int : (∫ x in cube d, p0 x) = 1)
    (hq0_int : (∫ a in Set.Icc (0 : ℝ) 1, q0 a) = 1) :
    doseAXMeasure (d := d) p0 q0 =
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (cube d))).withDensity
        (fun p => ENNReal.ofReal (q0 p.1 * p0 p.2)) := by
  classical
  rw [doseAXMeasure_eq_prod (d := d) (p0 := p0) (q0 := q0)]
  let μA : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let μX : Measure (Fin d → ℝ) := volume.restrict (cube d)
  have hq_intg : Integrable q0 μA := by
    refine Integrable.of_integral_ne_zero ?_
    intro hzero
    simp [μA, hzero] at hq0_int
  have hp_intg : Integrable p0 μX := by
    refine Integrable.of_integral_ne_zero ?_
    intro hzero
    simp [μX, hzero] at hp0_int
  have hq_ae : AEMeasurable (fun a => ENNReal.ofReal (q0 a)) μA :=
    hq_intg.aemeasurable.ennreal_ofReal
  have hp_ae : AEMeasurable (fun x => ENNReal.ofReal (p0 x)) μX :=
    hp_intg.aemeasurable.ennreal_ofReal
  unfold doseAMeasure doseXMeasure
  change (μA.withDensity (fun a => ENNReal.ofReal (q0 a))).prod
      (μX.withDensity (fun x => ENNReal.ofReal (p0 x))) =
    (μA.prod μX).withDensity (fun p => ENNReal.ofReal (q0 p.1 * p0 p.2))
  rw [prod_withDensity₀ hq_ae hp_ae]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    exact (ENNReal.ofReal_mul (hq0_nonneg p.1)).symm

-- @node: dose-witness-pi-cond
/-- Under the stated positivity, normalization, and bounded-mean assumptions, the
witness treatment density is a valid conditional treatment density for the witness law. -/
lemma doseWitness_piCond {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ}
    (hB : 0 < B)
    (hq0_nonneg : ∀ a, 0 ≤ q0 a)
    (hp0_int : (∫ x in cube d, p0 x) = 1)
    (hq0_int : (∫ a in Set.Icc (0 : ℝ) 1, q0 a) = 1)
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B) :
    PiIsCondTreatmentDensity (doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta) := by
  classical
  unfold PiIsCondTreatmentDensity doseWitness
  refine ⟨?_, ?_⟩
  · intro a _ha _x _hx
    exact hq0_nonneg a
  · rw [doseDataMeasure_map_AX (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := zeta) hB hmu]
    exact doseAXMeasure_density (d := d) (p0 := p0) (q0 := q0)
      hq0_nonneg hp0_int hq0_int

end CausalSmith.Stat.DoseResponseMinimax
