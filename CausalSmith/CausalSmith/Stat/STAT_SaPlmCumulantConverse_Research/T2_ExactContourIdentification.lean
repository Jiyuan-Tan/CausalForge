import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.Transforms
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.ContourBank
import Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.ArgumentPrinciple
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Exact contour identification
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open Causalean.Mathlib.Analysis.ArgumentPrincipleCircle
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- Every radius in the fixed translated-dyadic bank is positive. -/
lemma contourBank_rho_pos (p : Parameters) (pStar : CertifiedBankInputs p)
    (j : Fin ((contourBank p pStar).JBase + 1)) :
    0 < (contourBank p pStar).rho j := by
  have hR0 : 0 < zeroRadius p := by
    rw [← pStar.R0_value]
    exact lt_of_lt_of_le (by exact_mod_cast pStar.R0Name.lower_pos)
      pStar.R0Name.lower_le_value
  simp only [contourBank, CertifiedReal.add, CertifiedReal.ofRat,
    pStar.R0_value]
  positivity

/-- A weighted exponential transform with bounded measurable weight and
argument is complex differentiable everywhere. -/
lemma weightedTransform_differentiableAt_of_ae_bounded
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P] (W V : Omega → ℝ) (z : ℂ)
    (hW : Measurable W) (hV : Measurable V)
    (CW CV : ℝ) (hCW : 0 ≤ CW) (hCV : 0 ≤ CV)
    (hWbdd : ∀ᵐ o ∂P, |W o| ≤ CW) (hVbdd : ∀ᵐ o ∂P, |V o| ≤ CV) :
    DifferentiableAt ℂ (weightedTransform P W V) z := by
  let bound : Omega → ℝ := fun _ ↦ CW * CV * Real.exp ((‖z‖ + 1) * CV)
  have hbound : Integrable bound P := integrable_const _
  have hFint : Integrable
      (fun o ↦ (W o : ℂ) * Complex.exp (z * (V o : ℂ))) P := by
    apply Integrable.of_bound (by fun_prop) (CW * Real.exp (‖z‖ * CV))
    filter_upwards [hWbdd, hVbdd] with o hwo hvo
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    apply mul_le_mul hwo (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hCW
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      z.re * V o ≤ |z.re * V o| := le_abs_self _
      _ = |z.re| * |V o| := abs_mul _ _
      _ ≤ ‖z‖ * CV := mul_le_mul (Complex.abs_re_le_norm z) hvo
        (abs_nonneg _) (norm_nonneg _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := bound)
    (F := fun w o ↦ (W o : ℂ) * Complex.exp (w * (V o : ℂ)))
    (F' := fun w o ↦ (W o : ℂ) * ((V o : ℂ) * Complex.exp (w * (V o : ℂ))))
    (Metric.ball_mem_nhds z zero_lt_one)
    (by filter_upwards; intro w; fun_prop) hFint (by fun_prop) ?_ hbound ?_).2.differentiableAt
  · filter_upwards [hWbdd, hVbdd] with o hwo hvo
    intro w hw
    dsimp [bound]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, Complex.norm_exp]
    have hwz : ‖w‖ ≤ ‖z‖ + 1 := by
      have hdist : ‖w - z‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      calc
        ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
          simpa only [sub_add_cancel] using norm_add_le (w - z) z
        _ ≤ ‖z‖ + 1 := by linarith
    have hexp : (w * (V o : ℂ)).re ≤ (‖z‖ + 1) * CV := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      calc
        w.re * V o ≤ |w.re * V o| := le_abs_self _
        _ = |w.re| * |V o| := abs_mul _ _
        _ ≤ ‖w‖ * CV := mul_le_mul (Complex.abs_re_le_norm w) hvo
          (abs_nonneg _) (norm_nonneg _)
        _ ≤ (‖z‖ + 1) * CV := mul_le_mul_of_nonneg_right hwz hCV
    calc
      |W o| * (|V o| * Real.exp (w * (V o : ℂ)).re) =
          (|W o| * |V o|) * Real.exp (w * (V o : ℂ)).re := by ring
      _ ≤ (CW * CV) * Real.exp ((‖z‖ + 1) * CV) :=
        mul_le_mul (mul_le_mul hwo hvo (abs_nonneg _) hCW)
          (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (mul_nonneg hCW hCV)
      _ = CW * CV * Real.exp ((‖z‖ + 1) * CV) := rfl
  · filter_upwards [] with o w hw
    refine ((hasDerivAt_const w (W o : ℂ)).fun_mul
      ((Complex.hasDerivAt_exp (w * (V o : ℂ))).comp w
        ((hasDerivAt_id w).mul_const (V o : ℂ)))).congr_deriv ?_
    simp only [Function.comp_apply, id_eq, zero_mul, zero_add, one_mul]
    ring

/-- Take [at least one observation](hyp:hn) and a model in [the non-Gaussian spectral
class](hyp:hclass). Fix one circle of the certified radius bank and suppose [the transform of
the observable learned residual has no zero on that circle](hyp:hF), [the transform of the
treatment-code error has no zero anywhere in the closed disk it bounds](hyp:hH), and [the
residual transform does have at least one zero, counted with multiplicity, strictly
inside](hyp:hcount). Then [the treatment coefficient is exactly identified by the contour
functional built from the residual transform and the outcome-weighted residual transform on
that circle, and that functional is the contour integral of the ratio of the two transforms
around the circle, divided by the number of enclosed residual zeros times two pi i](goal).

Identification is exact rather than asymptotic: no expansion, no remainder, and the value is a
genuine contour integral of observable population transforms, which is what makes a certified
interval-arithmetic evaluation of it a legitimate estimator. -/
-- @node: thm:exact-contour-identification
theorem exact_contour_identification (p : Parameters)
    (m : Model (Xspace := Xspace) p) (n : ℕ) (hn : 1 ≤ n)
    (hclass : NonGaussianClass p n m)
    (pStar : CertifiedBankInputs p)
    (j : Fin ((contourBank p pStar).JBase + 1))
    (hF : ∀ z ∈ sphere (0 : ℂ) ((contourBank p pStar).rho j),
      residualMGF p m n z ≠ 0)
    (hH : ∀ z ∈ closedBall (0 : ℂ) ((contourBank p pStar).rho j),
      nuisanceMGF p m n z ≠ 0)
    (hcount : 1 ≤ zeroMultiplicityCount (residualMGF p m n) 0
      ((contourBank p pStar).rho j)) :
    (m.theta0 : ℂ) = contourFunctional (residualMGF p m n)
      (outcomeResidualTransform p m n) ((contourBank p pStar).rho j)
        (contourBank_rho_pos p pStar j)
        (residualMGF_analyticOn_closedBall p m n hclass
          ((contourBank p pStar).rho j)) hF hcount ∧
    contourFunctional (residualMGF p m n) (outcomeResidualTransform p m n)
        ((contourBank p pStar).rho j)
        (contourBank_rho_pos p pStar j)
        (residualMGF_analyticOn_closedBall p m n hclass
          ((contourBank p pStar).rho j)) hF hcount =
      (contourCount (residualMGF p m n) ((contourBank p pStar).rho j) *
        (2 * (Real.pi : ℂ) * Complex.I))⁻¹ *
          circleIntegral (fun z ↦ outcomeResidualTransform p m n z /
            residualMGF p m n z) 0 ((contourBank p pStar).rho j) := by
  let rho := (contourBank p pStar).rho j
  have hrho : 0 < rho := contourBank_rho_pos p pStar j
  let F := residualMGF p m n
  let G := outcomeResidualTransform p m n
  let H := nuisanceMGF p m n
  let B := contaminationTransform p m n
  let D := treatmentError p m n
  let b : Obs Xspace → ℝ := fun o ↦ outcomeContamination p m n (covariate o)
  have hDmeas : Measurable D := by
    dsimp [D, treatmentError, barG, covariate]
    exact (m.g0_measurable.comp measurable_fst).sub
      (((m.gcode_measurable n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  have hbmeas : Measurable b := by
    dsimp [b]
    exact (m.q0_measurable.sub (measurable_const.mul
      (m.g0_measurable.sub
        (((m.gcode_measurable n).max measurable_const).min measurable_const)))).comp
          measurable_fst
  have hDbdd : ∀ᵐ o ∂m.P, |D o| ≤ 2 * p.Cg := by
    simpa [D] using (l1_nuisance_zero_free p m n hclass).1
  have hbar (x : Xspace) : |barG p m n x| ≤ p.Cg := by
    have hCg : 0 < p.Cg := p.constants_pos.2.1
    rw [abs_le]
    dsimp [barG]
    constructor <;> simp_all <;> linarith
  have hbbdd : ∀ᵐ o ∂m.P,
      |b o| ≤ p.Cq + p.Ctheta * (2 * p.Cg) := by
    have hcov : Measurable (covariate (Xspace := Xspace)) := measurable_fst
    have hq := MeasureTheory.ae_of_ae_map hcov.aemeasurable hclass.qRange
    have hg := MeasureTheory.ae_of_ae_map hcov.aemeasurable hclass.gRange
    filter_upwards [hq, hg] with o hqo hgo
    dsimp [b, outcomeContamination]
    calc
      |m.q0 (covariate o) - m.theta0 *
          (m.g0 (covariate o) - barG p m n (covariate o))|
          ≤ |m.q0 (covariate o)| + |m.theta0| *
              |m.g0 (covariate o) - barG p m n (covariate o)| := by
                simpa [abs_mul] using abs_sub (m.q0 (covariate o))
                  (m.theta0 * (m.g0 (covariate o) - barG p m n (covariate o)))
      _ ≤ p.Cq + p.Ctheta * (2 * p.Cg) := by
        apply add_le_add hqo
        have hmul := mul_le_mul hclass.thetaRange
          ((abs_sub _ _).trans (add_le_add hgo (hbar (covariate o))))
          (abs_nonneg _) p.constants_pos.1.le
        convert hmul using 1 <;> ring
  have hDnonneg : 0 ≤ 2 * p.Cg :=
    mul_nonneg (by norm_num) p.constants_pos.2.1.le
  have hbnonneg : 0 ≤ p.Cq + p.Ctheta * (2 * p.Cg) :=
    add_nonneg p.constants_pos.2.2.1.le
      (mul_nonneg p.constants_pos.1.le hDnonneg)
  have hHdiff (z : ℂ) : DifferentiableAt ℂ H z := by
    have heq : H = weightedTransform m.P (fun _ ↦ 1) D := by
      funext w
      simp [H, nuisanceMGF, weightedTransform, ProbabilityTheory.complexMGF, D]
    rw [heq]
    exact weightedTransform_differentiableAt_of_ae_bounded m.P (fun _ ↦ 1) D z
      measurable_const hDmeas 1 (2 * p.Cg) zero_le_one hDnonneg (by simp) hDbdd
  have hBdiff (z : ℂ) : DifferentiableAt ℂ B z := by
    exact weightedTransform_differentiableAt_of_ae_bounded m.P b D z hbmeas hDmeas
      (p.Cq + p.Ctheta * (2 * p.Cg)) (2 * p.Cg) hbnonneg hDnonneg hbbdd hDbdd
  let Q : ℂ → ℂ := fun z ↦ B z / H z
  have hQdiff (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) rho) :
      DifferentiableAt ℂ Q z :=
    (hBdiff z).div (hHdiff z) (hH z hz)
  have hQdc : DiffContOnCl ℂ Q (ball (0 : ℂ) rho) := by
    constructor
    · intro z hz
      exact (hQdiff z (ball_subset_closedBall hz)).differentiableWithinAt
    · intro z hz
      exact (hQdiff z (closure_ball_subset_closedBall hz)).continuousAt.continuousWithinAt
  have hQzero : circleIntegral Q 0 rho = 0 := hQdc.circleIntegral_eq_zero hrho.le
  have hEntire := residualMGF_analyticOn_closedBall p m n hclass rho
  have hlogcont : ContinuousOn (logDeriv F) (sphere (0 : ℂ) rho) := by
    rw [show logDeriv F = fun z ↦ deriv F z / F z by ext z; simp [logDeriv_apply]]
    exact (hEntire.deriv.continuousOn.mono sphere_subset_closedBall).div
      (hEntire.continuousOn.mono sphere_subset_closedBall) hF
  have hlogCI : CircleIntegrable (logDeriv F) 0 rho :=
    hlogcont.circleIntegrable hrho.le
  have hQCI : CircleIntegrable Q 0 rho :=
    (hQdc.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hrho.le
  have hpoint : EqOn (fun z ↦ G z / F z)
      (fun z ↦ (m.theta0 : ℂ) * logDeriv F z + Q z) (sphere 0 rho) := by
    intro z hz
    have hfac := observable_factorization p m n hclass z
    have hM : treatmentMGF p m z ≠ 0 := by
      intro hMz
      have := hF z hz
      rw [hfac.1, hMz, zero_mul] at this
      exact this rfl
    dsimp [F, G, H, B, Q]
    rw [logDeriv_apply, hfac.2, hfac.1]
    field_simp [hF z hz, hH z (sphere_subset_closedBall hz), hM]
  have hIntegral : circleIntegral (fun z ↦ G z / F z) 0 rho =
      (m.theta0 : ℂ) * circleIntegral (logDeriv F) 0 rho := by
    have hthetaCI : CircleIntegrable
        (fun z ↦ (m.theta0 : ℂ) * logDeriv F z) 0 rho :=
      (continuousOn_const.mul hlogcont).circleIntegrable hrho.le
    rw [circleIntegral.integral_congr hrho.le hpoint,
      circleIntegral.integral_add hthetaCI hQCI,
      circleIntegral.integral_const_mul, hQzero, add_zero]
  have hap : contourCount F rho =
      (zeroMultiplicityCount F 0 rho : ℂ) := by
    exact argumentPrinciple_circle hrho hEntire hF
  have hN : contourCount F rho ≠ 0 := by
    rw [hap]
    exact_mod_cast (Nat.ne_of_gt hcount)
  have hK : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hlog : circleIntegral (logDeriv F) 0 rho =
      contourCount F rho * (2 * (Real.pi : ℂ) * Complex.I) := by
    unfold contourCount normalizedLogDerivCircleIntegral
    field_simp [hK]
  constructor
  · change (m.theta0 : ℂ) = contourFunctional F G rho hrho hEntire hF hcount
    unfold contourFunctional
    dsimp [F, G] at hIntegral hlog hN ⊢
    rw [hIntegral, hlog]
    field_simp [hN, hK]
  · rfl

end CausalSmith.Stat.SaPlmCumulantConverse
