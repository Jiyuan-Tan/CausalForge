import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.Basic

/-!
# Population and empirical analytic transforms

The unweighted transforms use Mathlib's complex MGF.  The two genuinely
weighted transforms are Bochner integrals with a separate weight.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ComplexConjugate

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- Weighted bilateral exponential transform. -/
def weightedTransform [MeasurableSpace Ω] (P : Measure Ω) (W V : Ω → ℝ) (z : ℂ) : ℂ :=
  ∫ w, (W w : ℂ) * Complex.exp (z * V w) ∂P

-- @env: S3
variable (p : Parameters) (m : Model (Xspace := Xspace) p) (n : ℕ)

/-- The moment generating function of the treatment noise — the deviation of the
treatment from its conditional mean given the covariate — evaluated at a complex
argument: the expectation of the exponential of that argument times the
treatment noise. -/
def treatmentMGF (z : ℂ) : ℂ :=
  complexMGF (eta p m) m.P z -- @realizes M(E exp(z eta))

/-- The moment generating function of the treatment-code error at sample size
`n` — the gap between the true treatment regression and the supplied clipped
code — evaluated at a complex argument. -/
def nuisanceMGF (z : ℂ) : ℂ :=
  complexMGF (treatmentError p m n) m.P z -- @realizes H(E exp(z D_n))

/-- The exponential transform of the treatment-code error weighted by the
outcome-side contamination: the expectation of the contamination evaluated at
the covariate times the exponential of the complex argument multiplied by the
treatment-code error. -/
def contaminationTransform (z : ℂ) : ℂ :=
  weightedTransform m.P (fun o ↦ outcomeContamination p m n (covariate o))
    (treatmentError p m n) z -- @realizes B(E[b_n(X) exp(z D_n)])

/-- The moment generating function of the observable learned residual at sample
size `n` — the treatment minus the supplied clipped treatment code evaluated at
the covariate — at a complex argument. -/
def residualMGF (z : ℂ) : ℂ :=
  complexMGF (learnedResidual p m n) m.P z -- @realizes F(E exp(z Z_n))

/-- The exponential transform of the observable learned residual weighted by the
outcome: the expectation of the outcome times the exponential of the complex
argument multiplied by the learned residual. -/
def outcomeResidualTransform (z : ℂ) : ℂ :=
  weightedTransform m.P outcome (learnedResidual p m n) z
  -- @realizes G(E[Y exp(z Z_n)])

/-- The exact Luxemburg envelope gives every real exponential moment of the
treatment noise. -/
lemma eta_integrable_exp (hclass : NonGaussianClass p n m) (t : ℝ) :
    Integrable (fun o ↦ Real.exp (t * eta p m o)) m.P := by
  have hpsi : 0 < p.psieta := p.constants_pos.2.2.2.1
  have hetaMeas : Measurable (eta p m) := by
    unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  apply (hclass.etaSubGaussian.1.mul_const
    (Real.exp (t ^ 2 * p.psieta ^ 2 / 4))).mono'
      ((Real.continuous_exp.measurable.comp
        (measurable_const.fun_mul hetaMeas)).aestronglyMeasurable)
  filter_upwards [] with o
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsquare : 0 ≤ (eta p m o / p.psieta - t * p.psieta / 2) ^ 2 := sq_nonneg _
  field_simp [hpsi.ne'] at hsquare ⊢
  nlinarith

/-- The treatment-noise MGF is entire; this is derived from the class's
Luxemburg envelope rather than assumed as model data. -/
lemma treatmentMGF_entire (hclass : NonGaussianClass p n m) :
    AnalyticOnNhd ℂ (treatmentMGF p m) Set.univ := by
  have hset : integrableExpSet (eta p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, eta_integrable_exp p m n hclass t]
  intro z _hz
  exact analyticAt_complexMGF (by simp [hset])

/-- The learned residual has every real exponential moment. -/
lemma learnedResidual_integrable_exp (hclass : NonGaussianClass p n m) (t : ℝ) :
    Integrable (fun o ↦ Real.exp (t * learnedResidual p m n o)) m.P := by
  have hCg : 0 < p.Cg := p.constants_pos.2.1
  have hcov : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hbar (x : Xspace) : |barG p m n x| ≤ p.Cg := by
    rw [abs_le]
    dsimp [barG]
    constructor <;> simp_all <;> linarith
  have hD : ∀ᵐ o ∂m.P, |treatmentError p m n o| ≤ 2 * p.Cg := by
    have hg := MeasureTheory.ae_of_ae_map hcov.aemeasurable hclass.gRange
    filter_upwards [hg] with o ho
    dsimp [treatmentError]
    calc
      |m.g0 (covariate o) - barG p m n (covariate o)|
          ≤ |m.g0 (covariate o)| + |barG p m n (covariate o)| := abs_sub _ _
      _ ≤ p.Cg + p.Cg := add_le_add ho (hbar _)
      _ = 2 * p.Cg := by ring
  have hZMeas : Measurable (learnedResidual p m n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      (((m.gcode_measurable n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  apply ((eta_integrable_exp p m n hclass t).const_mul
    (Real.exp (|t| * (2 * p.Cg)))).mono'
      ((Real.continuous_exp.measurable.comp
        (measurable_const.fun_mul hZMeas)).aestronglyMeasurable)
  filter_upwards [hD] with o ho
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hres : learnedResidual p m n o = eta p m o + treatmentError p m n o := by
    simp [learnedResidual, eta, treatmentError]
  rw [hres, mul_add]
  have htd : t * treatmentError p m n o ≤ |t| * (2 * p.Cg) := by
    calc
      t * treatmentError p m n o ≤ |t * treatmentError p m n o| := le_abs_self _
      _ = |t| * |treatmentError p m n o| := abs_mul _ _
      _ ≤ |t| * (2 * p.Cg) := mul_le_mul_of_nonneg_left ho (abs_nonneg t)
  linarith

/-- The outcome innovation has every real exponential moment. -/
lemma xi_integrable_exp (hclass : NonGaussianClass p n m) (t : ℝ) :
    Integrable (fun o ↦ Real.exp (t * xi p m o)) m.P := by
  have hpsi : 0 < p.psixi := p.constants_pos.2.2.2.2.1
  apply (hclass.xiSubGaussian.1.mul_const
    (Real.exp (t ^ 2 * p.psixi ^ 2 / 4))).mono'
      ((Real.continuous_exp.measurable.comp_aemeasurable
        (hclass.outcomeMeanIndependence.1.aemeasurable.const_mul t)).aestronglyMeasurable)
  filter_upwards [] with o
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsquare : 0 ≤ (xi p m o / p.psixi - t * p.psixi / 2) ^ 2 := sq_nonneg _
  field_simp [hpsi.ne'] at hsquare ⊢
  nlinarith

/-- The outcome innovation times a learned-residual exponential is integrable. -/
lemma outcomeNoise_weighted_exp_integrable
    (hclass : NonGaussianClass p n m) (z : ℂ) :
    Integrable (fun o ↦ (xi p m o : ℂ) *
      Complex.exp (z * (learnedResidual p m n o : ℂ))) m.P := by
  let e : Obs Xspace → ℂ := fun o ↦
    Complex.exp (z * (learnedResidual p m n o : ℂ))
  have hxiSet : integrableExpSet (xi p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, xi_integrable_exp p m n hclass t]
  have hxi2 : MemLp (xi p m) 2 m.P := by
    apply memLp_of_mem_interior_integrableExpSet
    simp [hxiSet]
  have hZMeas : Measurable (learnedResidual p m n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      (((m.gcode_measurable n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  have he2 : MemLp e 2 m.P := by
    rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
    convert learnedResidual_integrable_exp p m n hclass (2 * z.re) using 1
    ext o
    dsimp [e]
    rw [Complex.norm_exp, sq, ← Real.exp_add]
    congr 1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  exact hxi2.ofReal.integrable_mul he2

/-- Conditional mean independence annihilates the outcome innovation against
the learned-residual exponential weight. -/
lemma outcomeNoise_weighted_exp_eq_zero
    (hclass : NonGaussianClass p n m) (z : ℂ) :
    ∫ o, (xi p m o : ℂ) * Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P = 0 := by
  let e : Obs Xspace → ℂ := fun o ↦
    Complex.exp (z * (learnedResidual p m n o : ℂ))
  have hprod : Integrable (fun o ↦ (xi p m o : ℂ) * e o) m.P := by
    simpa [e] using outcomeNoise_weighted_exp_integrable p m n hclass z
  have hZxT : Measurable[xTSigma (Xspace := Xspace)] (learnedResidual p m n) := by
    change Measurable[MeasurableSpace.comap
      (fun o : Obs Xspace ↦ (covariate o, treatment o)) inferInstance]
      (learnedResidual p m n)
    have h : Measurable (fun xt : Xspace × ℝ ↦ xt.2 - barG p m n xt.1) :=
      measurable_snd.sub
        ((((m.gcode_measurable n).comp measurable_fst).max measurable_const).min
          measurable_const)
    exact h.comp (comap_measurable (fun o : Obs Xspace ↦ (covariate o, treatment o)))
  have heRe : StronglyMeasurable[xTSigma (Xspace := Xspace)] (fun o ↦ (e o).re) := by
    apply Measurable.stronglyMeasurable
    dsimp [e]
    fun_prop
  have heIm : StronglyMeasurable[xTSigma (Xspace := Xspace)] (fun o ↦ (e o).im) := by
    apply Measurable.stronglyMeasurable
    dsimp [e]
    fun_prop
  have hprodRe : Integrable (fun o ↦ xi p m o * (e o).re) m.P := by
    simpa using hprod.re
  have hprodIm : Integrable (fun o ↦ xi p m o * (e o).im) m.P := by
    simpa using hprod.im
  have hzero (w : Obs Xspace → ℝ)
      (hw : StronglyMeasurable[xTSigma (Xspace := Xspace)] w)
      (hprodw : Integrable (fun o ↦ xi p m o * w o) m.P) :
      ∫ o, xi p m o * w o ∂m.P = 0 := by
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_right
      (μ := m.P) (m := xTSigma (Xspace := Xspace)) hw hprodw
        hclass.outcomeMeanIndependence.1
    calc
      ∫ o, xi p m o * w o ∂m.P =
          ∫ o, (@MeasureTheory.condExp (Obs Xspace) ℝ
            (xTSigma (Xspace := Xspace)) inferInstance _ _ m.P
            (fun o ↦ xi p m o * w o)) o ∂m.P := by
              rw [MeasureTheory.integral_condExp (show xTSigma (Xspace := Xspace) ≤
                (inferInstance : MeasurableSpace (Obs Xspace)) from
                  Measurable.comap_le (measurable_fst.prodMk measurable_snd.fst))]
      _ = ∫ o, (@MeasureTheory.condExp (Obs Xspace) ℝ
            (xTSigma (Xspace := Xspace)) inferInstance _ _ m.P (xi p m)) o * w o ∂m.P :=
          integral_congr_ae hpull
      _ = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hclass.outcomeMeanIndependence.2] with o ho
        simp [ho]
  apply Complex.ext
  · change (∫ o, (xi p m o : ℂ) * e o ∂m.P).re = 0
    calc
      _ = ∫ o, ((xi p m o : ℂ) * e o).re ∂m.P := by
        simpa only [RCLike.re_eq_complex_re] using (integral_re hprod).symm
      _ = ∫ o, xi p m o * (e o).re ∂m.P := by simp
      _ = 0 := hzero (fun o ↦ (e o).re) heRe hprodRe
  · change (∫ o, (xi p m o : ℂ) * e o ∂m.P).im = 0
    calc
      _ = ∫ o, ((xi p m o : ℂ) * e o).im ∂m.P := by
        simpa only [RCLike.im_eq_complex_im] using (integral_im hprod).symm
      _ = ∫ o, xi p m o * (e o).im ∂m.P := by simp
      _ = 0 := hzero (fun o ↦ (e o).im) heIm hprodIm

/-- The residual complex MGF is entire under the paper's exponential-moment
envelope; this is derived from its construction rather than assumed. -/
lemma residualMGF_analyticOn_closedBall (hclass : NonGaussianClass p n m) (rho : ℝ) :
    AnalyticOnNhd ℂ (residualMGF p m n) (closedBall (0 : ℂ) rho) := by
  have hpsi : 0 < p.psieta := p.constants_pos.2.2.2.1
  have hCg : 0 < p.Cg := p.constants_pos.2.1
  have hetaMeas : Measurable (eta p m) := by
    unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  have hetaAll (t : ℝ) :
      Integrable (fun o ↦ Real.exp (t * eta p m o)) m.P := by
    apply (hclass.etaSubGaussian.1.mul_const
      (Real.exp (t ^ 2 * p.psieta ^ 2 / 4))).mono'
        ((Real.continuous_exp.measurable.comp
          (measurable_const.fun_mul hetaMeas)).aestronglyMeasurable)
    filter_upwards [] with o
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsquare : 0 ≤ (eta p m o / p.psieta - t * p.psieta / 2) ^ 2 := sq_nonneg _
    field_simp [hpsi.ne'] at hsquare ⊢
    nlinarith
  have hcov : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hbar (x : Xspace) : |barG p m n x| ≤ p.Cg := by
    rw [abs_le]
    dsimp [barG]
    constructor <;> simp_all <;> linarith
  have hD : ∀ᵐ o ∂m.P, |treatmentError p m n o| ≤ 2 * p.Cg := by
    have hg := MeasureTheory.ae_of_ae_map hcov.aemeasurable hclass.gRange
    filter_upwards [hg] with o ho
    dsimp [treatmentError]
    calc
      |m.g0 (covariate o) - barG p m n (covariate o)|
          ≤ |m.g0 (covariate o)| + |barG p m n (covariate o)| := abs_sub _ _
      _ ≤ p.Cg + p.Cg := add_le_add ho (hbar _)
      _ = 2 * p.Cg := by ring
  have hZAll (t : ℝ) :
      Integrable (fun o ↦ Real.exp (t * learnedResidual p m n o)) m.P := by
    have hZMeas : Measurable (learnedResidual p m n) := by
      unfold learnedResidual treatment barG covariate
      exact measurable_snd.fst.sub
        (((m.gcode_measurable n).comp measurable_fst).max measurable_const |>.min
          measurable_const)
    apply ((hetaAll t).const_mul (Real.exp (|t| * (2 * p.Cg)))).mono'
      ((Real.continuous_exp.measurable.comp
        (measurable_const.fun_mul hZMeas)).aestronglyMeasurable)
    filter_upwards [hD] with o ho
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hres : learnedResidual p m n o = eta p m o + treatmentError p m n o := by
      simp [learnedResidual, eta, treatmentError]
    rw [hres, mul_add]
    have htd : t * treatmentError p m n o ≤ |t| * (2 * p.Cg) := by
      calc
        t * treatmentError p m n o ≤ |t * treatmentError p m n o| := le_abs_self _
        _ = |t| * |treatmentError p m n o| := abs_mul _ _
        _ ≤ |t| * (2 * p.Cg) := mul_le_mul_of_nonneg_left ho (abs_nonneg t)
    linarith
  have hset : integrableExpSet (learnedResidual p m n) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, hZAll t]
  unfold residualMGF
  have han := analyticOnNhd_complexMGF
    (X := learnedResidual p m n) (μ := m.P)
  rw [hset, interior_univ] at han
  apply han.mono
  intro z hz
  trivial

/-- Split empirical unweighted transform. -/
def empiricalF (data : Fin n → Obs Xspace) (I : Finset (Fin n)) (z : ℂ) : ℂ :=
  (I.card : ℂ)⁻¹ * ∑ i ∈ I, Complex.exp (z * learnedResidual p m n (data i))
  -- @realizes Fhat(split-fold empirical residual transform)

/-- Split empirical outcome-weighted transform. -/
def empiricalG (data : Fin n → Obs Xspace) (I : Finset (Fin n)) (z : ℂ) : ℂ :=
  (I.card : ℂ)⁻¹ * ∑ i ∈ I,
    (outcome (data i) : ℂ) * Complex.exp (z * learnedResidual p m n (data i))
  -- @realizes Ghat(split-fold empirical outcome transform)

/-- Multiplicity-adjusted transform-zero instrument. -/
-- @node: def:zero-instrument
def zeroInstrument (M : ℂ → ℂ) (z0 : ℂ) (ell : ℕ)
    (_hell : 1 ≤ ell) (_hz : M z0 = 0)
    (_hmult : analyticOrderNatAt M z0 = ell) (w : ℂ) : ℂ :=
  w ^ (ell - 1) * Complex.exp (z0 * w)
  -- @realizes z0(candidate complex zero)
  -- @realizes ell(positive zero multiplicity)
  -- @realizes Jzero(w^(ell-1) exp(z0*w))

/-- Independence of the treatment noise and covariates factors the learned-residual MGF. -/
lemma residualMGF_eq_treatmentMGF_mul_nuisanceMGF
    (hclass : NonGaussianClass p n m) (z : ℂ) :
    residualMGF p m n z = treatmentMGF p m z * nuisanceMGF p m n z := by
  have heta : Measurable (eta p m) := by
    unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  have hX : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hD : Measurable (fun x : Xspace ↦ m.g0 x - barG p m n x) := by
    exact m.g0_measurable.sub
      (((m.gcode_measurable n).max measurable_const).min measurable_const)
  have hind := hclass.independentTreatmentNoise.integral_fun_comp_mul_comp
    (f := fun e : ℝ ↦ Complex.exp (z * (e : ℂ)))
    (g := fun x : Xspace ↦ Complex.exp (z * (m.g0 x - barG p m n x : ℝ)))
    heta.aemeasurable hX.aemeasurable
    (by fun_prop)
    ((Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp hD))).aestronglyMeasurable)
  rw [residualMGF, treatmentMGF, nuisanceMGF, complexMGF]
  calc
    (∫ o, Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P) =
        ∫ o, Complex.exp (z * (eta p m o : ℂ)) *
          Complex.exp (z * (m.g0 (covariate o) - barG p m n (covariate o) : ℝ)) ∂m.P := by
      apply integral_congr_ae
      filter_upwards [] with o
      rw [← Complex.exp_add]
      congr 2
      simp only [learnedResidual, eta]
      rw [← mul_add]
      congr 1
      push_cast
      ring
    _ = _ := hind

/-- The bounded covariate contamination times a learned-residual exponential
is integrable. -/
lemma contamination_weighted_exp_integrable
    (hclass : NonGaussianClass p n m) (z : ℂ) :
    Integrable (fun o ↦ (outcomeContamination p m n (covariate o) : ℂ) *
      Complex.exp (z * (learnedResidual p m n o : ℂ))) m.P := by
  have hcov : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hbar (x : Xspace) : |barG p m n x| ≤ p.Cg := by
    have hCg : 0 < p.Cg := p.constants_pos.2.1
    rw [abs_le]
    dsimp [barG]
    constructor <;> simp_all <;> linarith
  have hq := MeasureTheory.ae_of_ae_map hcov.aemeasurable hclass.qRange
  have hg := MeasureTheory.ae_of_ae_map hcov.aemeasurable hclass.gRange
  have hb : ∀ᵐ o ∂m.P,
      ‖(outcomeContamination p m n (covariate o) : ℂ)‖ ≤
        p.Cq + p.Ctheta * (2 * p.Cg) := by
    filter_upwards [hq, hg] with o hqo hgo
    rw [Complex.norm_real]
    dsimp [outcomeContamination]
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
  have hbMeas : Measurable
      (fun o ↦ (outcomeContamination p m n (covariate o) : ℂ)) := by
    apply Complex.measurable_ofReal.comp
    exact (m.q0_measurable.sub (measurable_const.mul
      (m.g0_measurable.sub
        (((m.gcode_measurable n).max measurable_const).min measurable_const)))).comp hcov
  have hexp : Integrable
      (fun o ↦ Complex.exp (z * (learnedResidual p m n o : ℂ))) m.P := by
    have hZMeas : Measurable (learnedResidual p m n) := by
      unfold learnedResidual treatment barG covariate
      exact measurable_snd.fst.sub
        (((m.gcode_measurable n).comp measurable_fst).max measurable_const |>.min
          measurable_const)
    apply (learnedResidual_integrable_exp p m n hclass z.re).mono'
      ((Complex.continuous_exp.measurable.comp
        (measurable_const.mul
          (Complex.measurable_ofReal.comp hZMeas))).aestronglyMeasurable)
    filter_upwards [] with o
    simp [Complex.norm_exp]
  exact hexp.bdd_mul hbMeas.aestronglyMeasurable hb

/-- The covariate contamination term factors from the treatment-noise exponential. -/
lemma contamination_weighted_factorization
    (hclass : NonGaussianClass p n m) (z : ℂ) :
    weightedTransform m.P (fun o ↦ outcomeContamination p m n (covariate o))
      (learnedResidual p m n) z =
        treatmentMGF p m z * contaminationTransform p m n z := by
  have heta : Measurable (eta p m) := by
    unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  have hX : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hD : Measurable (fun x : Xspace ↦ m.g0 x - barG p m n x) := by
    exact m.g0_measurable.sub
      (((m.gcode_measurable n).max measurable_const).min measurable_const)
  have hb : Measurable (fun x : Xspace ↦ outcomeContamination p m n x) := by
    exact m.q0_measurable.sub (measurable_const.mul hD)
  have hind := hclass.independentTreatmentNoise.integral_fun_comp_mul_comp
    (f := fun e : ℝ ↦ Complex.exp (z * (e : ℂ)))
    (g := fun x : Xspace ↦ (outcomeContamination p m n x : ℂ) *
      Complex.exp (z * (m.g0 x - barG p m n x : ℝ)))
    heta.aemeasurable hX.aemeasurable
    (by fun_prop)
    ((Complex.measurable_ofReal.comp hb).mul
      (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp hD))) |>.aestronglyMeasurable)
  rw [weightedTransform, treatmentMGF, contaminationTransform, complexMGF]
  calc
    (∫ o, (outcomeContamination p m n (covariate o) : ℂ) *
        Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P) =
      ∫ o, Complex.exp (z * (eta p m o : ℂ)) *
        ((outcomeContamination p m n (covariate o) : ℂ) *
          Complex.exp (z * (m.g0 (covariate o) - barG p m n (covariate o) : ℝ))) ∂m.P := by
      apply integral_congr_ae
      filter_upwards [] with o
      have he : Complex.exp (z * (learnedResidual p m n o : ℂ)) =
          Complex.exp (z * (eta p m o : ℂ)) *
            Complex.exp (z * (m.g0 (covariate o) - barG p m n (covariate o) : ℝ)) := by
        rw [← Complex.exp_add]
        congr 2
        rw [← mul_add]
        congr 1
        simp only [learnedResidual, eta]
        push_cast
        ring
      rw [he]
      ring
    _ = _ := hind

open Causalean.Mathlib.Analysis.ArgumentPrincipleCircle in
/-- The normalized logarithmic-derivative integral used as the contour count. -/
def contourCount (F : ℂ → ℂ) (rho : ℝ) : ℂ :=
  normalizedLogDerivCircleIntegral F 0 rho
  -- @realizes NC((2*pi*i)^-1 contour integral F'/F)

/-- Observable normalized contour ratio. -/
-- @node: def:contour-functional
def contourFunctional (F G : ℂ → ℂ) (rho : ℝ)
    (_hrho : 0 < rho)
    (_hEntire : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) rho))
    (_hzero : ∀ z ∈ sphere (0 : ℂ) rho, F z ≠ 0)
    (_hcount : 1 ≤
      Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.zeroMultiplicityCount F 0 rho) : ℂ :=
  (contourCount F rho * (2 * (Real.pi : ℂ) * Complex.I))⁻¹ *
    circleIntegral (fun z ↦ G z / F z) 0 rho
  -- @realizes Cj(positively oriented circle centered at zero with radius rho)
  -- @realizes thetaC(normalized observable contour functional)

/-- Observable factorization of the learned-residual transforms. -/
-- @node: lem:observable-factorization
lemma observable_factorization (hclass : NonGaussianClass p n m) :
    ∀ z : ℂ,
      residualMGF p m n z = treatmentMGF p m z * nuisanceMGF p m n z ∧
      outcomeResidualTransform p m n z =
        (m.theta0 : ℂ) * deriv (residualMGF p m n) z +
          treatmentMGF p m z * contaminationTransform p m n z := by
  intro z
  constructor
  · exact residualMGF_eq_treatmentMGF_mul_nuisanceMGF p m n hclass z
  have hZset : integrableExpSet (learnedResidual p m n) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, learnedResidual_integrable_exp p m n hclass t]
  have hzmem : z.re ∈ interior (integrableExpSet (learnedResidual p m n) m.P) := by
    simp [hZset]
  have hZexp : Integrable (fun o ↦ (learnedResidual p m n o : ℂ) *
      Complex.exp (z * (learnedResidual p m n o : ℂ))) m.P := by
    simpa using integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hzmem 1
  have hderiv : deriv (residualMGF p m n) z =
      ∫ o, (learnedResidual p m n o : ℂ) *
        Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P := by
    exact (hasDerivAt_complexMGF hzmem).deriv
  have hbexp := contamination_weighted_exp_integrable p m n hclass z
  have hxiexp := outcomeNoise_weighted_exp_integrable p m n hclass z
  have hthetaZ : Integrable (fun o ↦ (m.theta0 : ℂ) *
      ((learnedResidual p m n o : ℂ) *
        Complex.exp (z * (learnedResidual p m n o : ℂ)))) m.P :=
    hZexp.const_mul _
  have hthetaInt :
      (∫ o, (m.theta0 : ℂ) * ((learnedResidual p m n o : ℂ) *
        Complex.exp (z * (learnedResidual p m n o : ℂ))) ∂m.P) =
        (m.theta0 : ℂ) * deriv (residualMGF p m n) z := by
    calc
      _ = (m.theta0 : ℂ) * ∫ o, (learnedResidual p m n o : ℂ) *
          Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P :=
            integral_const_mul _ _
      _ = _ := by rw [← hderiv]
  rw [outcomeResidualTransform, weightedTransform]
  calc
    (∫ o, (outcome o : ℂ) *
        Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P) =
      ∫ o, ((m.theta0 : ℂ) * (learnedResidual p m n o : ℂ) +
          (outcomeContamination p m n (covariate o) : ℂ) + (xi p m o : ℂ)) *
        Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P := by
          apply integral_congr_ae
          filter_upwards [] with o
          congr 1
          simp only [learnedResidual, outcomeContamination, xi, eta,
            treatment, outcome, covariate]
          push_cast
          ring
    _ = ∫ o, (m.theta0 : ℂ) * ((learnedResidual p m n o : ℂ) *
          Complex.exp (z * (learnedResidual p m n o : ℂ))) +
        (outcomeContamination p m n (covariate o) : ℂ) *
          Complex.exp (z * (learnedResidual p m n o : ℂ)) +
        (xi p m o : ℂ) *
          Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P := by
            apply integral_congr_ae
            filter_upwards [] with o
            ring
    _ = ∫ o, (m.theta0 : ℂ) * ((learnedResidual p m n o : ℂ) *
          Complex.exp (z * (learnedResidual p m n o : ℂ))) ∂m.P +
        ∫ o, (outcomeContamination p m n (covariate o) : ℂ) *
          Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P +
        ∫ o, (xi p m o : ℂ) *
          Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P := by
            calc
              _ = (∫ o, (m.theta0 : ℂ) * ((learnedResidual p m n o : ℂ) *
                    Complex.exp (z * (learnedResidual p m n o : ℂ))) +
                  (outcomeContamination p m n (covariate o) : ℂ) *
                    Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P) +
                  ∫ o, (xi p m o : ℂ) *
                    Complex.exp (z * (learnedResidual p m n o : ℂ)) ∂m.P := by
                      convert integral_add (hthetaZ.add hbexp) hxiexp using 1 <;>
                        simp [Pi.add_apply]
              _ = _ := by rw [integral_add hthetaZ hbexp]
    _ = (m.theta0 : ℂ) * deriv (residualMGF p m n) z +
          treatmentMGF p m z * contaminationTransform p m n z := by
            rw [hthetaInt,
              outcomeNoise_weighted_exp_eq_zero p m n hclass z,
              add_zero]
            congr 1
            simpa [weightedTransform] using
              contamination_weighted_factorization p m n hclass z

/-- Direct L1 control keeps the nuisance transform uniformly away from zero
and preserves analytic zero multiplicities. -/
-- @node: lem:l1-nuisance-zero-free
lemma l1_nuisance_zero_free (hclass : NonGaussianClass p n m) :
    let R1 := searchRadius p
    let eps0 := (4 * R1 * Real.exp (2 * p.Cg * R1))⁻¹
      -- @realizes eps0(exact fixed stability radius)
    (∀ᵐ o ∂m.P, |treatmentError p m n o| ≤ 2 * p.Cg) ∧
    (∫ o, |treatmentError p m n o| ∂m.P ≤ p.eps1n n) ∧
    (∀ z : ℂ, ‖z‖ ≤ R1 →
      ‖nuisanceMGF p m n z - 1‖ ≤
        R1 * Real.exp (2 * p.Cg * R1) * p.eps1n n) ∧
    (p.eps1n n ≤ eps0 →
      (∀ z : ℂ, ‖z‖ ≤ R1 → 3 / 4 ≤ ‖nuisanceMGF p m n z‖) ∧
      (∀ z : ℂ, ‖z‖ ≤ R1 →
        analyticOrderAt (residualMGF p m n) z = analyticOrderAt (treatmentMGF p m) z)) := by
  dsimp
  have hCg : 0 < p.Cg := p.constants_pos.2.1
  have hR1 : 0 < searchRadius p := by
    have hR0 : 0 ≤ zeroRadius p := by
      unfold zeroRadius Ak
      apply mul_nonneg
      · apply Real.rpow_nonneg
        positivity
      · apply Real.rpow_nonneg
        exact div_nonneg (sq_nonneg _) p.constants_pos.2.2.2.2.2.1.le
    unfold searchRadius
    linarith
  have hcov : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hbar (x : Xspace) : |barG p m n x| ≤ p.Cg := by
    rw [abs_le]
    dsimp [barG]
    constructor <;> simp_all <;> linarith
  have hD : ∀ᵐ o ∂m.P, |treatmentError p m n o| ≤ 2 * p.Cg := by
    have hg := MeasureTheory.ae_of_ae_map hcov.aemeasurable hclass.gRange
    filter_upwards [hg] with o ho
    dsimp [treatmentError]
    calc
      |m.g0 (covariate o) - barG p m n (covariate o)|
          ≤ |m.g0 (covariate o)| + |barG p m n (covariate o)| := abs_sub _ _
      _ ≤ p.Cg + p.Cg := add_le_add ho (hbar _)
      _ = 2 * p.Cg := by ring
  have hL1 : ∫ o, |treatmentError p m n o| ∂m.P ≤ p.eps1n n := by
    rw [show (∫ o, |treatmentError p m n o| ∂m.P) =
        ∫ x, |barG p m n x - m.g0 x| ∂covariateLaw p m by
      rw [covariateLaw, integral_map hcov.aemeasurable]
      · congr 1
        funext o
        simp [treatmentError, abs_sub_comm]
      · exact hclass.treatmentCodeRadiusL1.1.aestronglyMeasurable]
    exact hclass.treatmentCodeRadiusL1.2
  have hDmeas : Measurable (treatmentError p m n) := by
    unfold treatmentError barG covariate
    exact (m.g0_measurable.comp measurable_fst).sub
      (((m.gcode_measurable n).comp measurable_fst).max measurable_const |>.min measurable_const)
  have hDint : Integrable (fun o ↦ |treatmentError p m n o|) m.P := by
    have hi := hclass.treatmentCodeRadiusL1.1.comp_aemeasurable hcov.aemeasurable
    convert hi using 1
    ext o
    simp [treatmentError, abs_sub_comm]
  have hMGFBound : ∀ z : ℂ, ‖z‖ ≤ searchRadius p →
      ‖nuisanceMGF p m n z - 1‖ ≤ searchRadius p *
        Real.exp (2 * p.Cg * searchRadius p) * p.eps1n n := by
    intro z hz
    have hexp : Integrable
        (fun o ↦ Complex.exp (z * (treatmentError p m n o : ℂ))) m.P := by
      apply Integrable.of_bound (by fun_prop) (Real.exp (‖z‖ * (2 * p.Cg)))
      filter_upwards [hD] with o ho
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      calc
        z.re * treatmentError p m n o ≤ |z.re * treatmentError p m n o| := le_abs_self _
        _ = |z.re| * |treatmentError p m n o| := abs_mul _ _
        _ ≤ ‖z‖ * (2 * p.Cg) := mul_le_mul (Complex.abs_re_le_norm z) ho
          (abs_nonneg _) (norm_nonneg _)
    rw [nuisanceMGF, complexMGF, show (1 : ℂ) = ∫ _ : Obs Xspace, (1 : ℂ) ∂m.P by simp,
      ← integral_sub hexp (integrable_const 1)]
    calc
      ‖∫ o, Complex.exp (z * (treatmentError p m n o : ℂ)) - 1 ∂m.P‖
          ≤ ∫ o, (searchRadius p * Real.exp (2 * p.Cg * searchRadius p)) *
              |treatmentError p m n o| ∂m.P := by
            apply norm_integral_le_of_norm_le
            · simpa only [mul_assoc] using hDint.const_mul
                (searchRadius p * Real.exp (2 * p.Cg * searchRadius p))
            filter_upwards [hD] with o ho
            calc
              ‖Complex.exp (z * (treatmentError p m n o : ℂ)) - 1‖
                  ≤ ‖z * (treatmentError p m n o : ℂ)‖ *
                      Real.exp ‖z * (treatmentError p m n o : ℂ)‖ := by
                    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp
                      (z * (treatmentError p m n o : ℂ)) 1
              _ ≤ (searchRadius p * Real.exp (2 * p.Cg * searchRadius p)) *
                    |treatmentError p m n o| := by
                  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                  have hprod : ‖z‖ * |treatmentError p m n o| ≤
                      2 * p.Cg * searchRadius p := by
                    nlinarith [norm_nonneg z, abs_nonneg (treatmentError p m n o)]
                  have hcoef : ‖z‖ * Real.exp (‖z‖ * |treatmentError p m n o|) ≤
                      searchRadius p * Real.exp (2 * p.Cg * searchRadius p) :=
                    mul_le_mul hz (Real.exp_le_exp.mpr hprod)
                      (Real.exp_pos _).le hR1.le
                  calc
                    ‖z‖ * |treatmentError p m n o| *
                        Real.exp (‖z‖ * |treatmentError p m n o|) =
                      (‖z‖ * Real.exp (‖z‖ * |treatmentError p m n o|)) *
                        |treatmentError p m n o| := by ring
                    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
      _ = (searchRadius p * Real.exp (2 * p.Cg * searchRadius p)) *
            ∫ o, |treatmentError p m n o| ∂m.P := by rw [integral_const_mul]
      _ ≤ searchRadius p * Real.exp (2 * p.Cg * searchRadius p) * p.eps1n n := by
        gcongr
  refine ⟨hD, hL1, hMGFBound, ?_⟩
  intro heps
  have hAway : ∀ z : ℂ, ‖z‖ ≤ searchRadius p →
      3 / 4 ≤ ‖nuisanceMGF p m n z‖ := by
    intro z hz
    have hA : 0 < searchRadius p * Real.exp (2 * p.Cg * searchRadius p) :=
      mul_pos hR1 (Real.exp_pos _)
    have hquarter : searchRadius p * Real.exp (2 * p.Cg * searchRadius p) *
        p.eps1n n ≤ 1 / 4 := by
      calc
        searchRadius p * Real.exp (2 * p.Cg * searchRadius p) * p.eps1n n ≤
            searchRadius p * Real.exp (2 * p.Cg * searchRadius p) *
              (4 * searchRadius p * Real.exp (2 * p.Cg * searchRadius p))⁻¹ :=
          mul_le_mul_of_nonneg_left heps hA.le
        _ = 1 / 4 := by field_simp
    have hb := (hMGFBound z hz).trans hquarter
    have hrev := norm_sub_norm_le (1 : ℂ) (nuisanceMGF p m n z)
    rw [norm_sub_rev] at hrev
    norm_num at hrev ⊢
    linarith
  refine ⟨hAway, ?_⟩
  intro z hz
  have hDbdd : ∀ᵐ o ∂m.P, treatmentError p m n o ∈
      Set.Icc (-2 * p.Cg) (2 * p.Cg) := by
    filter_upwards [hD] with o ho
    rw [abs_le] at ho
    constructor <;> linarith
  have hDall (t : ℝ) : Integrable
      (fun o ↦ Real.exp (t * treatmentError p m n o)) m.P :=
    integrable_exp_mul_of_mem_Icc hDmeas.aemeasurable hDbdd
  have hDset : integrableExpSet (treatmentError p m n) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, hDall t]
  have hHan : AnalyticAt ℂ (nuisanceMGF p m n) z := by
    apply analyticAt_complexMGF
    simp [hDset]
  have hetaMeas : Measurable (eta p m) := by
    unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  have hpsi : 0 < p.psieta := p.constants_pos.2.2.2.1
  have hetaAll (t : ℝ) : Integrable (fun o ↦ Real.exp (t * eta p m o)) m.P := by
    apply (hclass.etaSubGaussian.1.mul_const
      (Real.exp (t ^ 2 * p.psieta ^ 2 / 4))).mono' (by fun_prop)
    filter_upwards [] with o
    simp only [Real.norm_eq_abs, Real.abs_exp]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsquare : 0 ≤ (eta p m o / p.psieta - t * p.psieta / 2) ^ 2 := sq_nonneg _
    field_simp [hpsi.ne'] at hsquare ⊢
    nlinarith
  have hetaSet : integrableExpSet (eta p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, hetaAll t]
  have hMan : AnalyticAt ℂ (treatmentMGF p m) z := by
    apply analyticAt_complexMGF
    simp [hetaSet]
  have hHne : nuisanceMGF p m n z ≠ 0 := by
    intro hzero
    have := hAway z hz
    rw [hzero, norm_zero] at this
    norm_num at this
  have hfac : residualMGF p m n = treatmentMGF p m * nuisanceMGF p m n := by
    funext w
    exact residualMGF_eq_treatmentMGF_mul_nuisanceMGF p m n hclass w
  rw [hfac, analyticOrderAt_mul hMan hHan,
    hHan.analyticOrderAt_eq_zero.mpr hHne, add_zero]

end CausalSmith.Stat.SaPlmCumulantConverse
