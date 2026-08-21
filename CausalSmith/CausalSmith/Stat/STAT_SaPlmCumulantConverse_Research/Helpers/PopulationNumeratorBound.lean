import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.EmpiricalTransformSeries

/-! # Uniform population numerator envelope

This file isolates the population `G` bound used by the adaptive contour risk proof.
-/

noncomputable section

open MeasureTheory

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- The explicit uniform envelope for the population outcome-residual transform. -/
-- @node: populationNumeratorEnvelope
def populationNumeratorEnvelope (p : Parameters) : ℝ :=
  Real.sqrt
    (64 * (p.Cq ^ 4 + 4 * p.Ctheta ^ 4 * p.psieta ^ 4 + 4 * p.psixi ^ 4) +
      2 * Real.exp
        (16 * searchRadius p * p.Cg + 16 * (searchRadius p) ^ 2 * p.psieta ^ 2))

/-- On the search disk, the population numerator is bounded only in terms of
the displayed class constants. -/
-- @node: outcomeResidualTransform_norm_le_populationNumeratorEnvelope
lemma outcomeResidualTransform_norm_le_populationNumeratorEnvelope
    (p : Parameters) (m : Model (Xspace := Xspace) p)
    (hclass : NonGaussianClass p p.n m) {z : ℂ}
    (hz : ‖z‖ ≤ searchRadius p) :
    ‖outcomeResidualTransform p m p.n z‖ ≤ populationNumeratorEnvelope p := by
  let A : ℝ :=
    64 * (p.Cq ^ 4 + 4 * p.Ctheta ^ 4 * p.psieta ^ 4 + 4 * p.psixi ^ 4) +
      2 * Real.exp
        (16 * searchRadius p * p.Cg + 16 * (searchRadius p) ^ 2 * p.psieta ^ 2)
  let E : Obs Xspace → ℝ := fun o ↦
    |outcome o| * Real.exp (2 * searchRadius p * |learnedResidual p m p.n o|)
  have hR : 0 ≤ searchRadius p := by
    unfold searchRadius
    have hR0 : 0 ≤ zeroRadius p := by
      unfold zeroRadius Ak
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg
          (div_nonneg (sq_nonneg _) p.constants_pos.2.2.2.2.2.1.le) _)
    linarith
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hEmeas : Measurable E := by
    dsimp [E]
    exact measurable_snd.snd.abs.mul
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul
          (measurable_snd.fst.sub
            (((m.gcode_measurable p.n).comp measurable_fst).max measurable_const |>.min
              measurable_const)).abs))
  have henv : ∫⁻ o, ENNReal.ofReal ((E o) ^ 2) ∂m.P ≤
      ENNReal.ofReal ((Real.sqrt A) ^ 2) := by
    rw [Real.sq_sqrt hA]
    simpa [A, E] using
      outcome_exp_abs_sq_lintegral_le p m p.n hclass (searchRadius p) hR
  have hEpack := memLp_two_and_eLpNorm_le_of_sq_lintegral_le m.P hEmeas
    (Real.sqrt_nonneg A) henv
  have hEint : Integrable E m.P := hEpack.1.integrable (by norm_num)
  have hZmeas : Measurable (learnedResidual p m p.n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      (((m.gcode_measurable p.n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  have hintegral : ‖∫ o, (outcome o : ℂ) *
        Complex.exp (z * learnedResidual p m p.n o) ∂m.P‖ ≤ ∫ o, E o ∂m.P := by
    apply norm_integral_le_of_norm_le hEint
    filter_upwards [] with o
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    dsimp [E]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    calc
      (z * (learnedResidual p m p.n o : ℂ)).re
          ≤ ‖z‖ * |learnedResidual p m p.n o| := by
            rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
            exact (le_abs_self _).trans (by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (abs_nonneg _))
      _ ≤ 2 * searchRadius p * |learnedResidual p m p.n o| := by
        nlinarith [abs_nonneg (learnedResidual p m p.n o)]
  have hmean : ∫ o, E o ∂m.P ≤ Real.sqrt A := by
    have habs := Causalean.Stat.abs_integral_le_eLpNorm_two hEpack.1
    have htoReal : (eLpNorm E 2 m.P).toReal ≤ Real.sqrt A :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hEpack.2).trans_eq
        (ENNReal.toReal_ofReal (Real.sqrt_nonneg A))
    rw [abs_of_nonneg (integral_nonneg fun _ ↦ by positivity)] at habs
    exact habs.trans htoReal
  unfold outcomeResidualTransform weightedTransform
  exact hintegral.trans (by simpa [populationNumeratorEnvelope, A] using hmean)

end CausalSmith.Stat.SaPlmCumulantConverse
