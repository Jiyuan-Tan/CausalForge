import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Relations among the non-Gaussian and published ACE classes
-/

noncomputable section

open scoped ENNReal
open MeasureTheory

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- [The published ACE comparator class sits inside the broad non-Gaussian class, the
comparison subclass sits inside the comparator class, and when the two code-accuracy exponents
coincide the comparator class and the comparison subclass are one and the same set of
laws](goal).

The inclusions come from monotonicity of the norms in their exponent on a probability space: an
accuracy budget met in the higher exponent is met in the lower one. Their point is that the
paper's result and the published comparator can be compared over exactly the same laws. -/
-- @node: lem:jms-ace-class-relations
theorem jms_ace_class_relations (p : Parameters) (n : ℕ) :
    (∀ m : Model (Xspace := Xspace) p,
      JmsAceClass p n m → NonGaussianClass p n m) ∧
    (∀ m : Model (Xspace := Xspace) p,
      AceComparisonSubclass p n m → JmsAceClass p n m) ∧
    (p.s = (p.r : ENNReal) →
      ∀ m : Model (Xspace := Xspace) p,
        JmsAceClass p n m ↔ AceComparisonSubclass p n m) := by
  have treatment_measurable (m : Model (Xspace := Xspace) p) (j : ℕ) :
      AEStronglyMeasurable
        (fun x ↦ barG p m j x - m.g0 x) (covariateLaw p m) := by
    apply Measurable.aestronglyMeasurable
    exact (((m.gcode_measurable j).max measurable_const).min measurable_const).sub
      m.g0_measurable
  have outcome_measurable (m : Model (Xspace := Xspace) p) (j : ℕ) :
      AEStronglyMeasurable
        (fun x ↦ barQ p m j x - m.q0 x) (covariateLaw p m) := by
    apply Measurable.aestronglyMeasurable
    exact (((m.qcode_measurable j).max measurable_const).min measurable_const).sub
      m.q0_measurable
  have covariate_probability (m : Model (Xspace := Xspace) p) :
      IsProbabilityMeasure (covariateLaw p m) := by
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have treatment_l1 (m : Model (Xspace := Xspace) p) (hm : JmsAceClass p n m) :
      TreatmentCodeRadiusL1At p m n := by
    letI := covariate_probability m
    let f := fun x ↦ barG p m n x - m.g0 x
    have hf : AEStronglyMeasurable f (covariateLaw p m) := treatment_measurable m n
    have hr : (1 : ℝ≥0∞) ≤ (p.r : ℝ≥0∞) := by
      exact_mod_cast (show 1 ≤ p.r from le_trans (by omega) p.r_ge_two)
    have hnorm : eLpNorm f 1 (covariateLaw p m) ≤
        eLpNorm f (p.r : ℝ≥0∞) (covariateLaw p m) :=
      eLpNorm_le_eLpNorm_of_exponent_le hr hf
    have htop : eLpNorm f (p.r : ℝ≥0∞) (covariateLaw p m) < ∞ :=
      lt_of_le_of_lt hm.treatmentCodeRadiusLr (ENNReal.ofReal_lt_top)
    have hmemr : MemLp f (p.r : ℝ≥0∞) (covariateLaw p m) := ⟨hf, htop⟩
    have hmem1 : MemLp f 1 (covariateLaw p m) := hmemr.mono_exponent hr
    have hfint : Integrable f (covariateLaw p m) := memLp_one_iff_integrable.mp hmem1
    refine ⟨?_, ?_⟩
    · simpa [f, Real.norm_eq_abs] using hfint.norm
    · have hofReal : ENNReal.ofReal (∫ x, |f x| ∂covariateLaw p m) ≤
          ENNReal.ofReal (p.eps1n n) := by
        rw [show ENNReal.ofReal (∫ x, |f x| ∂covariateLaw p m) =
            eLpNorm f 1 (covariateLaw p m) by
          rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hfint]
          simp only [Real.norm_eq_abs]]
        exact hnorm.trans hm.treatmentCodeRadiusLr
      have heps : 0 ≤ p.eps1n n := p.eps1_nonneg n hm.n_pos
      simpa [f] using (ENNReal.ofReal_le_ofReal_iff heps).mp hofReal
  constructor
  · intro m hm
    letI := covariate_probability m
    exact
      { n_pos := hm.n_pos
        independentTreatmentNoise := hm.independentTreatmentNoise
        outcomeMeanIndependence := hm.outcomeMeanIndependence
        thetaRange := hm.thetaRange
        gRange := hm.gRange
        qRange := hm.qRange
        etaSubGaussian := hm.etaSubGaussian
        xiSubGaussian := hm.xiSubGaussian
        cumulantSeparation := hm.cumulantSeparation
        treatmentCodeRadiusL1 := treatment_l1 m hm }
  constructor
  · intro m hm
    letI := covariate_probability m
    exact
      { n_pos := hm.n_pos
        independentTreatmentNoise := hm.independentTreatmentNoise
        outcomeMeanIndependence := hm.outcomeMeanIndependence
        thetaRange := hm.thetaRange
        gRange := hm.gRange
        qRange := hm.qRange
        etaSubGaussian := hm.etaSubGaussian
        xiSubGaussian := hm.xiSubGaussian
        cumulantSeparation := hm.cumulantSeparation
        treatmentCodeRadiusLr := by
          exact
            (eLpNorm_le_eLpNorm_of_exponent_le p.r_le_s (treatment_measurable m n)).trans
              hm.treatmentCodeRadius
        outcomeCodeRadiusLr := by
          exact
            (eLpNorm_le_eLpNorm_of_exponent_le p.r_le_s (outcome_measurable m n)).trans
              hm.outcomeCodeRadius }
  · intro hs m
    constructor
    · intro hm
      have hng : NonGaussianClass p n m :=
        (show ∀ m : Model (Xspace := Xspace) p,
            JmsAceClass p n m → NonGaussianClass p n m from by
          intro m' hm'
          exact
            { n_pos := hm'.n_pos
              independentTreatmentNoise := hm'.independentTreatmentNoise
              outcomeMeanIndependence := hm'.outcomeMeanIndependence
              thetaRange := hm'.thetaRange
              gRange := hm'.gRange
              qRange := hm'.qRange
              etaSubGaussian := hm'.etaSubGaussian
              xiSubGaussian := hm'.xiSubGaussian
              cumulantSeparation := hm'.cumulantSeparation
              treatmentCodeRadiusL1 := treatment_l1 m' hm' }) m hm
      refine { toNonGaussianClass := hng, treatmentCodeRadius := ?_, outcomeCodeRadius := ?_ }
      · simpa only [TreatmentCodeRadiusLsAt, TreatmentCodeRadiusLrAt, hs] using
          hm.treatmentCodeRadiusLr
      · simpa only [OutcomeCodeRadiusLsAt, OutcomeCodeRadiusLrAt, hs] using
          hm.outcomeCodeRadiusLr
    · intro hm
      exact
        { n_pos := hm.n_pos
          independentTreatmentNoise := hm.independentTreatmentNoise
          outcomeMeanIndependence := hm.outcomeMeanIndependence
          thetaRange := hm.thetaRange
          gRange := hm.gRange
          qRange := hm.qRange
          etaSubGaussian := hm.etaSubGaussian
          xiSubGaussian := hm.xiSubGaussian
          cumulantSeparation := hm.cumulantSeparation
          treatmentCodeRadiusLr := by
            simpa only [TreatmentCodeRadiusLsAt, TreatmentCodeRadiusLrAt, hs] using
              hm.treatmentCodeRadius
          outcomeCodeRadiusLr := by
            simpa only [OutcomeCodeRadiusLsAt, OutcomeCodeRadiusLrAt, hs] using
              hm.outcomeCodeRadius }

end CausalSmith.Stat.SaPlmCumulantConverse
