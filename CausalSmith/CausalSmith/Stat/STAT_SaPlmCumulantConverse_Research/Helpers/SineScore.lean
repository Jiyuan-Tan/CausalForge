import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Basic
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.Transforms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Causalean.Stat.Concentration.Chebyshev

/-!
# Bounded sine-score estimators
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- The sample average of a real-valued function of one observation: the sum of its values
over the units in the sample, divided by the sample size. -/
def empiricalMean (n : ℕ) (f : Obs Xspace → ℝ) (data : Fin n → Obs Xspace) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (data i)

/-- Shared clipped ratio engine for a sine score. -/
def thetaHatAt (p : Parameters) (m : Model (Xspace := Xspace) p) (n : ℕ)
    (t threshold : ℝ) (data : Fin n → Obs Xspace) : ℝ :=
  let den := empiricalMean n
    (fun o ↦ learnedResidual p m n o * Real.sin (t * learnedResidual p m n o)) data
  let num := empiricalMean n
    (fun o ↦ outcome o * Real.sin (t * learnedResidual p m n o)) data
  if threshold ≤ den then min (max (num / den) (-p.Ctheta)) p.Ctheta else 0

/-- Fixed-mixture sine estimator at frequency `pi/2`. -/
-- @node: def:sine-estimator
def thetaHatSin (p : Parameters) (m : Model (Xspace := Xspace) p)
    (data : Fin p.n → Obs Xspace) : ℝ :=
  thetaHatAt p m p.n (Real.pi / 2) (Real.exp (-Real.pi ^ 2 / 8) / 4) data
  -- @realizes thetahatSin(clipped sine-moment ratio in [-Ctheta,Ctheta])

/-- Symmetric Rademacher probability law. -/
def rademacherLaw : Measure ℝ :=
  (ENNReal.ofReal (1 / 2 : ℝ)) • Measure.dirac (-1 : ℝ) +
    (ENNReal.ofReal (1 / 2 : ℝ)) • Measure.dirac (1 : ℝ)

/-- [The symmetric Rademacher law — equal mass one half on minus one and on plus one — is a
probability measure, its total mass being one](goal). -/
instance : IsProbabilityMeasure rademacherLaw where
  measure_univ := by simpa [rademacherLaw] using ENNReal.inv_two_add_inv_two

/-- The symmetric Rademacher law has complex MGF `cosh`. -/
lemma complexMGF_rademacherLaw (z : ℂ) :
    complexMGF id rademacherLaw z = Complex.cosh z := by
  unfold complexMGF rademacherLaw
  have hneg : Integrable (fun ω : ℝ ↦ Complex.exp (z * (id ω : ℂ)))
      (ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  have hpos : Integrable (fun ω : ℝ ↦ Complex.exp (z * (id ω : ℂ)))
      (ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  simp only [id_eq] at hneg hpos ⊢
  rw [integral_add_measure hneg hpos, integral_smul_measure, integral_smul_measure]
  change ((ENNReal.ofReal (1 / 2 : ℝ)).toReal : ℂ) *
      (∫ x : ℝ, Complex.exp (z * (x : ℂ)) ∂Measure.dirac (-1)) +
    ((ENNReal.ofReal (1 / 2 : ℝ)).toReal : ℂ) *
      (∫ x : ℝ, Complex.exp (z * (x : ℂ)) ∂Measure.dirac 1) = _
  simp only [integral_dirac,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [Complex.cosh]
  norm_num
  ring

/-- The standard Gaussian, written with the explicit variance literal
`⟨1, zero_le_one⟩`, is a probability measure.

This restates Mathlib's generic instance for that particular spelling.
Instance synthesis runs at instance transparency, where the
anonymous-constructor term is not recognised as an `ℝ≥0`, so the generic
instance does not fire on it; naming the instance explicitly elaborates the
variance argument at default transparency. -/
instance gaussianReal_one_isProbabilityMeasure :
    IsProbabilityMeasure (gaussianReal 0 ⟨1, zero_le_one⟩) :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _

/-- Gaussian--Rademacher treatment-noise path. -/
def gaussianRademacherLaw (a : ℝ) : Measure ℝ :=
  Measure.map (fun x : ℝ × ℝ ↦ Real.sqrt (1 - a ^ 2) * x.1 + a * x.2)
    ((gaussianReal 0 ⟨1, zero_le_one⟩).prod rademacherLaw)
  -- @realizes etaSeq(centered Gaussian-Rademacher triangular noise path)

/-- The Gaussian--Rademacher path has the advertised product MGF. -/
lemma complexMGF_gaussianRademacherLaw {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (z : ℂ) :
    complexMGF id (gaussianRademacherLaw a) z =
      Complex.exp (((1 - a ^ 2 : ℝ) : ℂ) * z ^ 2 / 2) *
        Complex.cosh ((a : ℂ) * z) := by
  unfold gaussianRademacherLaw
  rw [complexMGF_id_map (by fun_prop)]
  unfold complexMGF
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
  rw [show (fun x : ℝ × ℝ ↦
      Complex.exp (z * (↑(Real.sqrt (1 - a ^ 2)) * ↑x.1 + ↑a * ↑x.2))) =
      fun x ↦ Complex.exp ((z * ↑(Real.sqrt (1 - a ^ 2))) * ↑x.1) *
        Complex.exp ((z * ↑a) * ↑x.2) by
    funext x
    rw [mul_add, Complex.exp_add]
    congr 2 <;> ring]
  rw [show (∫ x : ℝ × ℝ,
      Complex.exp ((z * ↑(Real.sqrt (1 - a ^ 2))) * ↑x.1) *
        Complex.exp ((z * ↑a) * ↑x.2)
      ∂(gaussianReal 0 ⟨1, zero_le_one⟩).prod rademacherLaw) =
      (∫ x : ℝ, Complex.exp ((z * ↑(Real.sqrt (1 - a ^ 2))) * ↑x)
        ∂gaussianReal 0 ⟨1, zero_le_one⟩) *
      ∫ y : ℝ, Complex.exp ((z * ↑a) * ↑y) ∂rademacherLaw by
    simpa using (integral_prod_mul
      (μ := gaussianReal 0 ⟨1, zero_le_one⟩) (ν := rademacherLaw) (L := ℂ)
      (fun x : ℝ ↦ Complex.exp ((z * ↑(Real.sqrt (1 - a ^ 2))) * ↑x))
      (fun y : ℝ ↦ Complex.exp ((z * ↑a) * ↑y)))]
  change complexMGF id (gaussianReal 0 ⟨1, zero_le_one⟩)
      (z * ↑(Real.sqrt (1 - a ^ 2))) *
    complexMGF id rademacherLaw (z * ↑a) = _
  -- The variance argument is the anonymous-constructor term `⟨1, zero_le_one⟩`,
  -- which blocks rewriting inside the goal; generalise it away first.
  have hgauss : ∀ v : NNReal, v = 1 → ∀ w : ℂ,
      complexMGF id (gaussianReal 0 v) w = Complex.exp (w ^ 2 / 2) := by
    rintro v rfl w
    rw [complexMGF_id_gaussianReal]
    norm_num
  refine (congrArg₂ (· * ·) (hgauss _ rfl (z * ↑(Real.sqrt (1 - a ^ 2))))
    (complexMGF_rademacherLaw (z * ↑a))).trans ?_
  have hsqrt : Real.sqrt (1 - a ^ 2) ^ 2 = 1 - a ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  have hsqrtC : (↑(Real.sqrt (1 - a ^ 2)) : ℂ) ^ 2 =
      Complex.ofReal (1 - a ^ 2) := by
    calc
      (↑(Real.sqrt (1 - a ^ 2)) : ℂ) ^ 2 =
          Complex.ofReal (Real.sqrt (1 - a ^ 2) ^ 2) := by norm_cast
      _ = Complex.ofReal (1 - a ^ 2) := congrArg Complex.ofReal hsqrt
  apply congrArg₂ (· * ·)
  · apply congrArg Complex.exp
    rw [mul_pow, hsqrtC]
    ring
  · congr 1
    ring

/-- Every real exponential moment exists along the explicit path. -/
lemma gaussianRademacher_integrable_exp (a t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) (gaussianRademacherLaw a) := by
  unfold gaussianRademacherLaw
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  have hG : Integrable
      (fun x : ℝ ↦ Real.exp ((t * Real.sqrt (1 - a ^ 2)) * x))
      (gaussianReal 0 ⟨1, zero_le_one⟩) := integrable_exp_mul_gaussianReal _
  have hR : Integrable (fun y : ℝ ↦ Real.exp ((t * a) * y))
      rademacherLaw := by
    unfold rademacherLaw
    rw [integrable_add_measure]
    constructor
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
  have hp := Integrable.mul_prod hG hR
  apply hp.congr
  filter_upwards [] with x
  rw [← Real.exp_add]
  congr 1
  ring

/-- The third derivative at zero of `a tanh(a z)` is `-2a^4`. -/
lemma iteratedDeriv_three_scaled_tanh (a : ℝ) :
    iteratedDeriv 3 (fun z : ℂ ↦ (a : ℂ) *
      Complex.sinh ((a : ℂ) * z) / Complex.cosh ((a : ℂ) * z)) 0 =
      (-2 * a ^ 4 : ℝ) := by
  let q0 : ℂ → ℂ := fun z ↦ (a : ℂ) * Complex.sinh ((a : ℂ) * z) /
    Complex.cosh ((a : ℂ) * z)
  let q1 : ℂ → ℂ := fun z ↦ (a : ℂ) ^ 2 /
    Complex.cosh ((a : ℂ) * z) ^ 2
  let q2 : ℂ → ℂ := fun z ↦ -2 * (a : ℂ) ^ 3 *
    Complex.sinh ((a : ℂ) * z) / Complex.cosh ((a : ℂ) * z) ^ 3
  have hcosh : ∀ᶠ z : ℂ in 𝓝 0, Complex.cosh ((a : ℂ) * z) ≠ 0 := by
    apply (isOpen_ne.preimage (Complex.continuous_cosh.comp
      (continuous_const.mul continuous_id))).mem_nhds
    simp
  have hd01 : deriv q0 =ᶠ[𝓝 0] q1 := by
    filter_upwards [hcosh] with z hz
    have hlin : HasDerivAt (fun w : ℂ ↦ (a : ℂ) * w) (a : ℂ) z := by
      simpa using (hasDerivAt_id z).const_mul (a : ℂ)
    have hsinh := (Complex.hasDerivAt_sinh ((a : ℂ) * z)).comp z hlin
    have hcos := (Complex.hasDerivAt_cosh ((a : ℂ) * z)).comp z hlin
    have hnum := hsinh.const_mul (a : ℂ)
    rw [show deriv q0 z =
        (((a : ℂ) ^ 2 * Complex.cosh ((a : ℂ) * z)) *
          Complex.cosh ((a : ℂ) * z) -
          ((a : ℂ) * Complex.sinh ((a : ℂ) * z)) *
            ((a : ℂ) * Complex.sinh ((a : ℂ) * z))) /
          Complex.cosh ((a : ℂ) * z) ^ 2 from
      ((hnum.fun_div hcos hz).congr_deriv (by
        simp only [Function.comp_apply]; ring)).deriv]
    dsimp [q1]
    field_simp
    rw [Complex.cosh_sq_sub_sinh_sq]
    ring
  have hd12 : deriv q1 =ᶠ[𝓝 0] q2 := by
    filter_upwards [hcosh] with z hz
    have hlin : HasDerivAt (fun w : ℂ ↦ (a : ℂ) * w) (a : ℂ) z := by
      simpa using (hasDerivAt_id z).const_mul (a : ℂ)
    have hcos := (Complex.hasDerivAt_cosh ((a : ℂ) * z)).comp z hlin
    have hden := hcos.fun_pow 2
    rw [show deriv q1 z =
        -(a : ℂ) ^ 2 *
          (2 * Complex.cosh ((a : ℂ) * z) *
            ((a : ℂ) * Complex.sinh ((a : ℂ) * z))) /
          (Complex.cosh ((a : ℂ) * z) ^ 2) ^ 2 from
      (((hasDerivAt_const z ((a : ℂ) ^ 2)).fun_div hden
        (pow_ne_zero 2 hz)).congr_deriv (by
          simp only [Function.comp_apply, Pi.pow_apply]; ring)).deriv]
    dsimp [q2]
    field_simp
  have hd2 : deriv q2 0 = (-2 * a ^ 4 : ℝ) := by
    have hlin : HasDerivAt (fun w : ℂ ↦ (a : ℂ) * w) (a : ℂ) 0 := by
      simpa using (hasDerivAt_id 0).const_mul (a : ℂ)
    have hsinh := (Complex.hasDerivAt_sinh ((a : ℂ) * 0)).comp 0 hlin
    have hcos := (Complex.hasDerivAt_cosh ((a : ℂ) * 0)).comp 0 hlin
    have hnum := hsinh.const_mul (-2 * (a : ℂ) ^ 3)
    have hden := hcos.fun_pow 3
    dsimp [q2]
    rw [show deriv (fun z : ℂ ↦ -2 * (a : ℂ) ^ 3 *
        Complex.sinh ((a : ℂ) * z) / Complex.cosh ((a : ℂ) * z) ^ 3) 0 =
        -2 * (a : ℂ) ^ 4 from
      ((hnum.fun_div hden (by simp)).congr_deriv (by
        simp only [Function.comp_apply]; norm_num; ring)).deriv]
    norm_num
  change iteratedDeriv 3 q0 0 = (-2 * a ^ 4 : ℝ)
  rw [show 3 = 2 + 1 by omega, iteratedDeriv_succ']
  rw [hd01.iteratedDeriv_eq 2]
  rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ']
  rw [hd12.iteratedDeriv_eq 1]
  simpa [iteratedDeriv_succ] using hd2

/-- The fourth logarithmic derivative of the Gaussian--Rademacher MGF is
the Rademacher fourth cumulant `-2a^4`. -/
lemma gaussianRademacher_logMGF_fourth (a c : ℝ) :
    (iteratedDeriv 4 (fun z : ℂ ↦
      Complex.log (Complex.exp ((c : ℂ) * z ^ 2 / 2) *
        Complex.cosh ((a : ℂ) * z))) 0).re = -2 * a ^ 4 := by
  let F : ℂ → ℂ := fun z ↦ Complex.exp ((c : ℂ) * z ^ 2 / 2) *
    Complex.cosh ((a : ℂ) * z)
  let L : ℂ → ℂ := fun z ↦ Complex.log (F z)
  let q : ℂ → ℂ := fun z ↦ (c : ℂ) * z +
    (a : ℂ) * Complex.sinh ((a : ℂ) * z) / Complex.cosh ((a : ℂ) * z)
  have hslit : ∀ᶠ z : ℂ in 𝓝 0, F z ∈ Complex.slitPlane := by
    have hcont : ContinuousAt F 0 := by dsimp [F]; fun_prop
    exact hcont.eventually (Complex.isOpen_slitPlane.mem_nhds (by simpa [F]))
  have hderiv : deriv L =ᶠ[𝓝 0] q := by
    filter_upwards [hslit] with z hz
    have hzcosh : Complex.cosh ((a : ℂ) * z) ≠ 0 := by
      intro hzero
      have : F z = 0 := by simp [F, hzero]
      rw [this] at hz
      simpa using hz
    have hsq := (hasDerivAt_id z).fun_pow 2
    have hquad : HasDerivAt (fun w : ℂ ↦ (c : ℂ) * w ^ 2 / 2)
        ((c : ℂ) * z) z :=
      ((hsq.const_mul (c : ℂ)).div_const 2).congr_deriv (by
        simp only [id_eq]; ring)
    have hexp := (Complex.hasDerivAt_exp ((c : ℂ) * z ^ 2 / 2)).comp z hquad
    have hlin : HasDerivAt (fun w : ℂ ↦ (a : ℂ) * w) (a : ℂ) z := by
      simpa using (hasDerivAt_id z).const_mul (a : ℂ)
    have hcos := (Complex.hasDerivAt_cosh ((a : ℂ) * z)).comp z hlin
    have hF : HasDerivAt F
        (Complex.exp ((c : ℂ) * z ^ 2 / 2) * ((c : ℂ) * z) *
            Complex.cosh ((a : ℂ) * z) +
          Complex.exp ((c : ℂ) * z ^ 2 / 2) *
            (Complex.sinh ((a : ℂ) * z) * (a : ℂ))) z := by
      exact hexp.fun_mul hcos
    change deriv (Complex.log ∘ F) z = q z
    rw [Complex.deriv_log_comp_eq_logDeriv hF.differentiableAt hz]
    simp only [logDeriv, Pi.div_apply, hF.deriv]
    dsimp [F, q]
    have hzcosh' : Complex.cosh (z * (a : ℂ)) ≠ 0 := by simpa [mul_comm] using hzcosh
    field_simp [Complex.exp_ne_zero, hzcosh']
  change (iteratedDeriv 4 L 0).re = -2 * a ^ 4
  rw [show 4 = 3 + 1 by omega, iteratedDeriv_succ']
  rw [hderiv.iteratedDeriv_eq 3]
  have hq : q = (fun z : ℂ ↦ (c : ℂ) * z) +
      (fun z : ℂ ↦ (a : ℂ) * Complex.sinh ((a : ℂ) * z) /
        Complex.cosh ((a : ℂ) * z)) := by
    funext z
    rfl
  rw [hq, iteratedDeriv_add (by fun_prop) (by
    apply ContDiffAt.div (by fun_prop) (by fun_prop)
    simp)]
  rw [show iteratedDeriv 3 (fun z : ℂ ↦ (c : ℂ) * z) 0 = 0 by
    rw [iteratedDeriv_const_mul_field]
    norm_num [iteratedDeriv_succ]]
  rw [iteratedDeriv_three_scaled_tanh]
  norm_num [Complex.mul_re]
  calc
    ((↑a : ℂ) ^ 4).re = (Complex.ofReal (a ^ 4)).re := by
      congr 1
      norm_cast
    _ = a ^ 4 := Complex.ofReal_re _

/-- Transport the explicit path transform across the model's noise law. -/
lemma treatmentMGF_eq_gaussianRademacher (p : Parameters)
    (m : Model (Xspace := Xspace) p) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hlaw : m.P.map (eta p m) = gaussianRademacherLaw a) :
    treatmentMGF p m = fun z ↦
      Complex.exp (((1 - a ^ 2 : ℝ) : ℂ) * z ^ 2 / 2) *
        Complex.cosh ((a : ℂ) * z) := by
  funext z
  unfold treatmentMGF
  rw [← complexMGF_id_map (by
    unfold eta treatment covariate
    exact (measurable_snd.fst.sub
      (m.g0_measurable.comp measurable_fst)).aemeasurable), hlaw]
  exact complexMGF_gaussianRademacherLaw ha0 ha1 z

/-- The model cumulants inherit the explicit fourth logarithmic derivative. -/
lemma model_gaussianRademacher_fourth_cumulant (p : Parameters)
    (m : Model (Xspace := Xspace) p) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hlaw : m.P.map (eta p m) = gaussianRademacherLaw a) :
    fourthCumulant p m = -2 * a ^ 4 := by
  have hmgf := treatmentMGF_eq_gaussianRademacher p m ha0 ha1 hlaw
  unfold treatmentMGF at hmgf
  rw [fourthCumulant]
  simp_rw [congrFun hmgf]
  exact gaussianRademacher_logMGF_fourth a (1 - a ^ 2)

/-- Suppose [the cumulant order recorded in the parameter block is four](hyp:hk) and the
treatment noise of the model is distributed as the Gaussian--Rademacher path with mixing
weight [strictly positive](hyp:ha0) and [at most one](hyp:ha1), namely [an independent standard
normal scaled by the square root of one minus the squared weight plus a symmetric sign variable
scaled by the weight](hyp:hlaw). Then [the model's treatment-noise cumulant of that order is
minus twice the fourth power of the mixing weight](goal), so it is strictly negative and
quantifies how far the noise sits from Gaussian. -/
lemma model_gaussianRademacher_kappa_four (p : Parameters)
    (m : Model (Xspace := Xspace) p) {a : ℝ} (hk : p.k = 4)
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hlaw : m.P.map (eta p m) = gaussianRademacherLaw a) :
    kappaEta p m = -2 * a ^ 4 := by
  have hmgf := treatmentMGF_eq_gaussianRademacher p m ha0 ha1 hlaw
  unfold treatmentMGF at hmgf
  rw [kappaEta, hk]
  simp_rw [congrFun hmgf]
  exact gaussianRademacher_logMGF_fourth a (1 - a ^ 2)

/-- The explicit transform has its first positive imaginary-axis zero at
`pi/(2a)`. -/
lemma gaussianRademacher_first_characteristic_zero {a : ℝ} (ha : 0 < a) :
    let t := Real.pi / (2 * a)
    (Complex.exp (((1 - a ^ 2 : ℝ) : ℂ) * (Complex.I * t) ^ 2 / 2) *
        Complex.cosh ((a : ℂ) * (Complex.I * t)) = 0) ∧
      ∀ u ∈ Ioo (0 : ℝ) t,
        Complex.exp (((1 - a ^ 2 : ℝ) : ℂ) * (Complex.I * u) ^ 2 / 2) *
          Complex.cosh ((a : ℂ) * (Complex.I * u)) ≠ 0 := by
  dsimp only
  constructor
  · have ha0 : (a : ℂ) ≠ 0 := mod_cast ne_of_gt ha
    rw [show (a : ℂ) * (Complex.I * (Real.pi / (2 * a) : ℝ)) =
        Complex.I * (Real.pi / 2 : ℝ) by
      push_cast
      field_simp]
    apply mul_eq_zero_of_right
    rw [show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring, Complex.cosh_mul_I]
    simp
  · intro u hu
    apply mul_ne_zero (Complex.exp_ne_zero _)
    have hau0 : 0 < a * u := mul_pos ha hu.1
    have hau1 : a * u < Real.pi / 2 := by
      have h := mul_lt_mul_of_pos_left hu.2 ha
      field_simp [ne_of_gt ha] at h
      linarith
    rw [show (a : ℂ) * (Complex.I * (u : ℂ)) =
        Complex.I * ((a * u : ℝ) : ℂ) by
      push_cast
      ring]
    rw [show Complex.I * ((a * u : ℝ) : ℂ) =
        ((a * u : ℝ) : ℂ) * Complex.I by ring, Complex.cosh_mul_I]
    exact_mod_cast ne_of_gt
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hau1⟩)

/-- The derivative at the first zero is the purely imaginary signal `I*A`. -/
lemma gaussianRademacher_deriv_at_first_zero {a : ℝ} (ha : 0 < a) :
    let t := Real.pi / (2 * a)
    let A := a * Real.exp (-(1 - a ^ 2) * Real.pi ^ 2 / (8 * a ^ 2))
    deriv (fun z : ℂ ↦
      Complex.exp (((1 - a ^ 2 : ℝ) : ℂ) * z ^ 2 / 2) *
        Complex.cosh ((a : ℂ) * z)) (Complex.I * t) = Complex.I * A := by
  dsimp only
  let z0 : ℂ := Complex.I * (Real.pi / (2 * a) : ℝ)
  have haC : (a : ℂ) ≠ 0 := mod_cast ne_of_gt ha
  have haz : (a : ℂ) * z0 = Complex.I * ((Real.pi / 2 : ℝ) : ℂ) := by
    dsimp [z0]
    push_cast
    field_simp [haC]
  have hzsq : z0 ^ 2 = -(((Real.pi ^ 2 / (4 * a ^ 2) : ℝ) : ℂ)) := by
    dsimp [z0]
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring
  have hquad : HasDerivAt (fun z : ℂ ↦
      (((1 - a ^ 2 : ℝ) : ℂ) * z ^ 2 / 2))
      (((1 - a ^ 2 : ℝ) : ℂ) * z0) z0 :=
    (((((hasDerivAt_id z0).fun_pow 2).const_mul
      (((1 - a ^ 2 : ℝ) : ℂ))).div_const 2)).congr_deriv (by
        simp only [id_eq]; ring)
  have hexp := (Complex.hasDerivAt_exp _).comp z0 hquad
  have hlin : HasDerivAt (fun z : ℂ ↦ (a : ℂ) * z) a z0 := by
    simpa using (hasDerivAt_id z0).const_mul (a : ℂ)
  have hcosh := (Complex.hasDerivAt_cosh ((a : ℂ) * z0)).comp z0 hlin
  change deriv (fun z : ℂ ↦
      Complex.exp (((1 - a ^ 2 : ℝ) : ℂ) * z ^ 2 / 2) *
        Complex.cosh ((a : ℂ) * z)) z0 = _
  have hd : HasDerivAt (fun z : ℂ ↦
      Complex.exp (((1 - a ^ 2 : ℝ) : ℂ) * z ^ 2 / 2) *
        Complex.cosh ((a : ℂ) * z))
      (Complex.exp (((1 - a ^ 2 : ℝ) : ℂ) * z0 ^ 2 / 2) *
          (((1 - a ^ 2 : ℝ) : ℂ) * z0) * Complex.cosh ((a : ℂ) * z0) +
        Complex.exp (((1 - a ^ 2 : ℝ) : ℂ) * z0 ^ 2 / 2) *
          (Complex.sinh ((a : ℂ) * z0) * (a : ℂ))) z0 := by
    exact hexp.fun_mul hcosh
  rw [hd.deriv, haz]
  rw [show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring]
  rw [Complex.cosh_mul_I, Complex.sinh_mul_I, hzsq]
  rw [show (((1 - a ^ 2 : ℝ) : ℂ) *
      -((Real.pi ^ 2 / (4 * a ^ 2) : ℝ) : ℂ) / 2) =
      ((-(1 - a ^ 2) * Real.pi ^ 2 / (8 * a ^ 2) : ℝ) : ℂ) by
    push_cast
    ring]
  rw [← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero,
    ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one]
  rw [← Complex.ofReal_exp]
  push_cast
  ring

/-- A zero of the characteristic function annihilates every deterministic
translate of the sine score. -/
lemma integral_sin_shift_eq_zero (p : Parameters)
    (m : Model (Xspace := Xspace) p) (t d : ℝ)
    (hzero : treatmentMGF p m (Complex.I * t) = 0) :
    ∫ o, Real.sin (t * (eta p m o + d)) ∂m.P = 0 := by
  let E : Obs Xspace → ℂ := fun o ↦
    Complex.exp ((Complex.I * t) * (eta p m o + d))
  have hEmeas : Measurable E := by
    apply Complex.continuous_exp.measurable.comp
    apply Measurable.mul measurable_const
    exact (Complex.measurable_ofReal.comp
      (measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst))).add
        measurable_const
  have hEint : Integrable E m.P := by
    apply (integrable_const (μ := m.P) (c := (1 : ℝ))).mono'
      hEmeas.aestronglyMeasurable
    filter_upwards [] with o
    simp [E, Complex.norm_exp]
  have hshift : ∫ o, E o ∂m.P = 0 := by
    calc
      ∫ o, E o ∂m.P = ∫ o, Complex.exp ((Complex.I * t) * eta p m o) *
          Complex.exp ((Complex.I * t) * d) ∂m.P := by
        apply integral_congr_ae
        filter_upwards [] with o
        dsimp [E]
        rw [← Complex.exp_add]
        congr 1
        ring
      _ = (∫ o, Complex.exp ((Complex.I * t) * eta p m o) ∂m.P) *
          Complex.exp ((Complex.I * t) * d) := integral_mul_const _ _
      _ = treatmentMGF p m (Complex.I * t) *
          Complex.exp ((Complex.I * t) * d) := by rfl
      _ = 0 := by rw [hzero]; simp
  calc
    ∫ o, Real.sin (t * (eta p m o + d)) ∂m.P =
        ∫ o, (E o).im ∂m.P := by
      apply integral_congr_ae
      filter_upwards [] with o
      dsimp [E]
      rw [Complex.exp_im]
      norm_num [Complex.mul_re, Complex.mul_im]
    _ = (∫ o, E o ∂m.P).im := by
      simpa only [RCLike.im_eq_complex_im] using integral_im hEint
    _ = 0 := by rw [hshift]; simp

/-- Exact-law transport supplies all exponential moments needed to
differentiate the characteristic function. -/
lemma eta_integrable_exp_gaussianRademacher (p : Parameters)
    (m : Model (Xspace := Xspace) p) {a : ℝ}
    (hlaw : m.P.map (eta p m) = gaussianRademacherLaw a) (s : ℝ) :
    Integrable (fun o ↦ Real.exp (s * eta p m o)) m.P := by
  have heta : AEMeasurable (eta p m) m.P := by
    unfold eta treatment covariate
    exact (measurable_snd.fst.sub
      (m.g0_measurable.comp measurable_fst)).aemeasurable
  have hLaw : Integrable (fun x : ℝ ↦ Real.exp (s * x))
      (m.P.map (eta p m)) := by
    rw [hlaw]
    exact gaussianRademacher_integrable_exp a s
  exact hLaw.comp_aemeasurable heta

/-- The first weighted characteristic moment at the first zero is `I*A`. -/
lemma eta_cexp_moment_at_first_zero (p : Parameters)
    (m : Model (Xspace := Xspace) p) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hlaw : m.P.map (eta p m) = gaussianRademacherLaw a) :
    let t := Real.pi / (2 * a)
    let A := a * Real.exp (-(1 - a ^ 2) * Real.pi ^ 2 / (8 * a ^ 2))
    ∫ o, (eta p m o : ℂ) *
      Complex.exp ((Complex.I * t) * (eta p m o : ℂ)) ∂m.P = Complex.I * A := by
  dsimp only
  let z0 : ℂ := Complex.I * (Real.pi / (2 * a) : ℝ)
  have hset : integrableExpSet (eta p m) m.P = Set.univ := by
    ext s
    simp [integrableExpSet, eta_integrable_exp_gaussianRademacher p m hlaw s]
  have hz : z0.re ∈ interior (integrableExpSet (eta p m) m.P) := by
    simp [hset]
  have hmgf := treatmentMGF_eq_gaussianRademacher p m ha0 ha1 hlaw
  unfold treatmentMGF at hmgf
  calc
    (∫ o, (eta p m o : ℂ) *
        Complex.exp ((Complex.I * (Real.pi / (2 * a) : ℝ)) *
          (eta p m o : ℂ)) ∂m.P) =
        iteratedDeriv 1 (complexMGF (eta p m) m.P) z0 := by
      rw [iteratedDeriv_complexMGF hz 1]
      apply integral_congr_ae
      filter_upwards [] with o
      dsimp [z0]
      simp
    _ = deriv (complexMGF (eta p m) m.P) z0 := by
      simp [iteratedDeriv_succ]
    _ = deriv (fun z : ℂ ↦
        Complex.exp (((1 - a ^ 2 : ℝ) : ℂ) * z ^ 2 / 2) *
          Complex.cosh ((a : ℂ) * z)) z0 := by
      exact congrArg (fun F : ℂ → ℂ ↦ deriv F z0) hmgf
    _ = Complex.I * (a : ℂ) *
        (Real.exp (-(1 - a ^ 2) * Real.pi ^ 2 / (8 * a ^ 2)) : ℂ) := by
      convert gaussianRademacher_deriv_at_first_zero ha0 using 1 <;>
        simp [z0] <;> push_cast <;> ring
    _ = Complex.I *
        ((a * Real.exp (-(1 - a ^ 2) * Real.pi ^ 2 / (8 * a ^ 2)) : ℝ) : ℂ) := by
      push_cast
      ring

/-- Independence transports the derivative signal through the bounded
treatment-code error. -/
-- @node: learnedResidual_sine_denominator_identity
lemma learnedResidual_sine_denominator_identity (p : Parameters)
    (m : Model (Xspace := Xspace) p) (n : ℕ) (t A : ℝ)
    (hzero : treatmentMGF p m (Complex.I * t) = 0)
    (hmoment : ∫ o, (eta p m o : ℂ) *
      Complex.exp ((Complex.I * t) * (eta p m o : ℂ)) ∂m.P = Complex.I * A)
    (hetaInt : Integrable (eta p m) m.P)
    (hind : IndependentTreatmentNoise p m) (hg : GRange p m) :
    ∫ o, learnedResidual p m n o * Real.sin (t * learnedResidual p m n o) ∂m.P =
      A * ∫ o, Real.cos (t * treatmentError p m n o) ∂m.P := by
  let D0 : Xspace → ℝ := fun x ↦ m.g0 x - barG p m n x
  have heta : Measurable (eta p m) := by
    unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  have hD0 : Measurable D0 := by
    exact m.g0_measurable.sub
      (((m.gcode_measurable n).max measurable_const).min measurable_const)
  have hX : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hDae : ∀ᵐ o ∂m.P, |treatmentError p m n o| ≤ 2 * p.Cg := by
    have hbar (x : Xspace) : |barG p m n x| ≤ p.Cg := by
      have hCg : 0 < p.Cg := p.constants_pos.2.1
      rw [abs_le]
      dsimp [barG]
      constructor <;> simp_all <;> linarith
    have hcov := MeasureTheory.ae_of_ae_map hX.aemeasurable hg
    filter_upwards [hcov] with o ho
    unfold treatmentError
    exact (abs_sub _ _).trans (by linarith [hbar (covariate o)])
  have hDint : Integrable (treatmentError p m n) m.P := by
    apply (integrable_const (μ := m.P) (c := 2 * p.Cg)).mono'
      ((hD0.comp hX).aestronglyMeasurable)
    exact hDae
  have hfac1 := hind.integral_fun_comp_mul_comp
    (f := fun e : ℝ ↦ (e : ℂ) * Complex.exp ((Complex.I * t) * (e : ℂ)))
    (g := fun x : Xspace ↦ Complex.exp ((Complex.I * t) * (D0 x : ℂ)))
    heta.aemeasurable hX.aemeasurable (by fun_prop) (by fun_prop)
  have hfac2 := hind.integral_fun_comp_mul_comp
    (f := fun e : ℝ ↦ Complex.exp ((Complex.I * t) * (e : ℂ)))
    (g := fun x : Xspace ↦ (D0 x : ℂ) *
      Complex.exp ((Complex.I * t) * (D0 x : ℂ)))
    heta.aemeasurable hX.aemeasurable (by fun_prop) (by fun_prop)
  have hEeMeas : AEStronglyMeasurable (fun o ↦
      Complex.exp ((Complex.I * t) * (eta p m o : ℂ))) m.P :=
    (Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp heta))).aestronglyMeasurable
  have hEdMeas : AEStronglyMeasurable (fun o ↦
      Complex.exp ((Complex.I * t) * (D0 (covariate o) : ℂ))) m.P :=
    (Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp
        (hD0.comp hX)))).aestronglyMeasurable
  have hEeBound : ∀ᵐ o ∂m.P,
      ‖Complex.exp ((Complex.I * t) * (eta p m o : ℂ))‖ ≤ 1 := by
    filter_upwards [] with o
    simp [Complex.norm_exp, Complex.mul_re]
  have hEdBound : ∀ᵐ o ∂m.P,
      ‖Complex.exp ((Complex.I * t) * (D0 (covariate o) : ℂ))‖ ≤ 1 := by
    filter_upwards [] with o
    simp [Complex.norm_exp, Complex.mul_re]
  have hcomplex : ∫ o, (learnedResidual p m n o : ℂ) *
      Complex.exp ((Complex.I * t) * (learnedResidual p m n o : ℂ)) ∂m.P =
      (Complex.I * A) * ∫ o,
        Complex.exp ((Complex.I * t) * (treatmentError p m n o : ℂ)) ∂m.P := by
    rw [show (∫ o, (learnedResidual p m n o : ℂ) *
        Complex.exp ((Complex.I * t) * (learnedResidual p m n o : ℂ)) ∂m.P) =
      (∫ o, ((eta p m o : ℂ) *
          Complex.exp ((Complex.I * t) * (eta p m o : ℂ))) *
        Complex.exp ((Complex.I * t) * (D0 (covariate o) : ℂ)) ∂m.P) +
      ∫ o, Complex.exp ((Complex.I * t) * (eta p m o : ℂ)) *
        ((D0 (covariate o) : ℂ) *
          Complex.exp ((Complex.I * t) * (D0 (covariate o) : ℂ))) ∂m.P by
      rw [← integral_add]
      apply integral_congr_ae
      filter_upwards [] with o
      have hZ : learnedResidual p m n o = eta p m o + D0 (covariate o) := by
        simp [learnedResidual, eta, D0, treatment, covariate]
      rw [hZ, Complex.ofReal_add, mul_add, Complex.exp_add]
      ring
      · exact ((hetaInt.ofReal.bdd_mul hEeMeas hEeBound).bdd_mul
          hEdMeas hEdBound).congr (by
            filter_upwards [] with o
            ac_rfl)
      · have hDw := hDint.ofReal.bdd_mul hEdMeas hEdBound
        exact (hDw.bdd_mul hEeMeas hEeBound).congr (by
          filter_upwards [] with o
          simp only [D0, treatmentError, covariate]
          ac_rfl)]
    change
      (∫ o, (fun e : ℝ ↦ (e : ℂ) * Complex.exp ((Complex.I * t) * (e : ℂ)))
          (eta p m o) *
        (fun x : Xspace ↦ Complex.exp ((Complex.I * t) * (D0 x : ℂ)))
          (covariate o) ∂m.P) +
      (∫ o, (fun e : ℝ ↦ Complex.exp ((Complex.I * t) * (e : ℂ)))
          (eta p m o) *
        (fun x : Xspace ↦ (D0 x : ℂ) *
          Complex.exp ((Complex.I * t) * (D0 x : ℂ))) (covariate o) ∂m.P) = _
    rw [show (∫ o, (fun e : ℝ ↦ (e : ℂ) *
        Complex.exp ((Complex.I * t) * (e : ℂ))) (eta p m o) *
        (fun x : Xspace ↦ Complex.exp ((Complex.I * t) * (D0 x : ℂ)))
          (covariate o) ∂m.P) = _ from hfac1]
    rw [show (∫ o, (fun e : ℝ ↦ Complex.exp ((Complex.I * t) * (e : ℂ)))
        (eta p m o) * (fun x : Xspace ↦ (D0 x : ℂ) *
          Complex.exp ((Complex.I * t) * (D0 x : ℂ))) (covariate o) ∂m.P) = _
      from hfac2]
    change (∫ o, (eta p m o : ℂ) *
        Complex.exp ((Complex.I * t) * (eta p m o : ℂ)) ∂m.P) *
      (∫ o, Complex.exp ((Complex.I * t) * (D0 (covariate o) : ℂ)) ∂m.P) +
      (∫ o, Complex.exp ((Complex.I * t) * (eta p m o : ℂ)) ∂m.P) *
      (∫ o, (D0 (covariate o) : ℂ) *
        Complex.exp ((Complex.I * t) * (D0 (covariate o) : ℂ)) ∂m.P) = _
    rw [hmoment]
    change (Complex.I * A) * _ + treatmentMGF p m (Complex.I * t) * _ = _
    rw [hzero, zero_mul, add_zero]
    congr 1
  have hZint : Integrable (fun o ↦ (learnedResidual p m n o : ℂ) *
      Complex.exp ((Complex.I * t) * (learnedResidual p m n o : ℂ))) m.P := by
    have hZreal : Integrable (learnedResidual p m n) m.P := by
      have heq : learnedResidual p m n = eta p m + treatmentError p m n := by
        funext o
        simp [learnedResidual, eta, treatmentError, treatment, covariate]
      rw [heq]
      exact hetaInt.add hDint
    have hEZMeas : AEStronglyMeasurable (fun o ↦
        Complex.exp ((Complex.I * t) * (learnedResidual p m n o : ℂ))) m.P := by
      have hZmeas : Measurable (learnedResidual p m n) := by
        unfold learnedResidual treatment covariate barG
        exact measurable_snd.fst.sub
          ((((m.gcode_measurable n).comp measurable_fst).max measurable_const).min
            measurable_const)
      apply (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp _))).aestronglyMeasurable
      exact hZmeas
    have hEZBound : ∀ᵐ o ∂m.P,
        ‖Complex.exp ((Complex.I * t) * (learnedResidual p m n o : ℂ))‖ ≤ 1 := by
      filter_upwards [] with o
      simp [Complex.norm_exp, Complex.mul_re]
    exact (hZreal.ofReal.bdd_mul hEZMeas hEZBound).congr (by
      filter_upwards [] with o
      ac_rfl)
  calc
    ∫ o, learnedResidual p m n o * Real.sin (t * learnedResidual p m n o) ∂m.P =
        ∫ o, ((learnedResidual p m n o : ℂ) *
          Complex.exp ((Complex.I * t) * (learnedResidual p m n o : ℂ))).im ∂m.P := by
      apply integral_congr_ae
      filter_upwards [] with o
      rw [Complex.mul_im, Complex.exp_re, Complex.exp_im]
      norm_num [Complex.mul_re, Complex.mul_im]
    _ = (∫ o, (learnedResidual p m n o : ℂ) *
          Complex.exp ((Complex.I * t) * (learnedResidual p m n o : ℂ)) ∂m.P).im := by
      exact integral_im hZint
    _ = ((Complex.I * A) * ∫ o,
        Complex.exp ((Complex.I * t) * (treatmentError p m n o : ℂ)) ∂m.P).im := by
      rw [hcomplex]
    _ = A * ∫ o, Real.cos (t * treatmentError p m n o) ∂m.P := by
      have hEint : Integrable (fun o ↦
          Complex.exp ((Complex.I * t) * (treatmentError p m n o : ℂ))) m.P := by
        apply (integrable_const (μ := m.P) (c := (1 : ℝ))).mono'
          ((Complex.continuous_exp.measurable.comp
            (measurable_const.mul (Complex.measurable_ofReal.comp
              (hD0.comp hX)))).aestronglyMeasurable)
        filter_upwards [] with o
        simp [Complex.norm_exp, Complex.mul_re]
      have hre : (∫ o,
          Complex.exp ((Complex.I * t) * (treatmentError p m n o : ℂ)) ∂m.P).re =
          ∫ o, Real.cos (t * treatmentError p m n o) ∂m.P := by
        calc
          _ = ∫ o, (Complex.exp ((Complex.I * t) *
              (treatmentError p m n o : ℂ))).re ∂m.P := (integral_re hEint).symm
          _ = _ := by
            apply integral_congr_ae
            filter_upwards [] with o
            rw [Complex.exp_re]
            norm_num [Complex.mul_re, Complex.mul_im]
      rw [Complex.mul_im, hre]
      norm_num [Complex.mul_re, Complex.mul_im]

/-- The direct `L¹` radius keeps the population denominator above half of
its uncontaminated signal. -/
-- @node: learnedResidual_sine_denominator_lower
lemma learnedResidual_sine_denominator_lower (p : Parameters)
    (m : Model (Xspace := Xspace) p) (n : ℕ) (t A : ℝ)
    (ht : 0 < t) (hA : 0 < A)
    (hdenId : ∫ o, learnedResidual p m n o *
        Real.sin (t * learnedResidual p m n o) ∂m.P =
      A * ∫ o, Real.cos (t * treatmentError p m n o) ∂m.P)
    (hL1 : TreatmentCodeRadiusL1At p m n)
    (hsmall : t * p.eps1n n ≤ 1 / 2) :
    A / 2 ≤ ∫ o, learnedResidual p m n o *
      Real.sin (t * learnedResidual p m n o) ∂m.P := by
  have hcov : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hDmeas : Measurable (treatmentError p m n) := by
    unfold treatmentError barG covariate
    exact (m.g0_measurable.comp measurable_fst).sub
      ((((m.gcode_measurable n).comp measurable_fst).max measurable_const).min
        measurable_const)
  have hDabsInt : Integrable (fun o ↦ |treatmentError p m n o|) m.P := by
    have hi := hL1.1.comp_aemeasurable hcov.aemeasurable
    convert hi using 1
    ext o
    simp [treatmentError, abs_sub_comm]
  have hDmean : ∫ o, |treatmentError p m n o| ∂m.P ≤ p.eps1n n := by
    rw [show (∫ o, |treatmentError p m n o| ∂m.P) =
        ∫ x, |barG p m n x - m.g0 x| ∂covariateLaw p m by
      rw [covariateLaw, integral_map hcov.aemeasurable]
      · congr 1
        funext o
        simp [treatmentError, abs_sub_comm]
      · exact hL1.1.aestronglyMeasurable]
    exact hL1.2
  have hcosInt : Integrable (fun o ↦ Real.cos (t * treatmentError p m n o)) m.P := by
    apply (integrable_const (μ := m.P) (c := (1 : ℝ))).mono'
      ((Real.continuous_cos.measurable.comp
        (measurable_const.mul hDmeas)).aestronglyMeasurable)
    filter_upwards [] with o
    exact Real.abs_cos_le_one _
  have htDInt : Integrable (fun o ↦ |t * treatmentError p m n o|) m.P := by
    exact (hDabsInt.const_mul t).congr (by
      filter_upwards [] with o
      simp [abs_mul, abs_of_pos ht])
  have hcosLower : 1 - t * p.eps1n n ≤
      ∫ o, Real.cos (t * treatmentError p m n o) ∂m.P := by
    calc
      1 - t * p.eps1n n ≤ 1 - t * ∫ o, |treatmentError p m n o| ∂m.P := by
        gcongr
      _ = ∫ o, (1 - |t * treatmentError p m n o|) ∂m.P := by
        rw [integral_sub (integrable_const 1) htDInt]
        simp only [integral_const, probReal_univ, one_smul]
        rw [show (∫ o, |t * treatmentError p m n o| ∂m.P) =
            t * ∫ o, |treatmentError p m n o| ∂m.P by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with o
          simp [abs_mul, abs_of_pos ht]]
      _ ≤ ∫ o, Real.cos (t * treatmentError p m n o) ∂m.P := by
        apply integral_mono ((integrable_const 1).sub htDInt) hcosInt
        intro o
        have h := Real.abs_cos_sub_cos_le (t * treatmentError p m n o) 0
        simp only [Real.cos_zero, sub_zero] at h
        have hlow : -|t * treatmentError p m n o| ≤
            Real.cos (t * treatmentError p m n o) - 1 := neg_le_of_abs_le h
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          add_le_add_right hlow 1
  rw [hdenId]
  have hhalf : 1 / 2 ≤ ∫ o,
      Real.cos (t * treatmentError p m n o) ∂m.P := by
    linarith
  nlinarith

end CausalSmith.Stat.SaPlmCumulantConverse
