import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.SineScore
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.SineRisk
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.EmpiricalTransform

/-!
# Gaussian--Rademacher sine-score benchmark

This module assembles the explicit transform identities and the generic
clipped-ratio risk bound for the local-to-Gaussian path.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- The Gaussian--Rademacher path has a uniform second-moment envelope. -/
-- @node: gaussianRademacher_second_lintegral_le
lemma gaussianRademacher_second_lintegral_le {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂gaussianRademacherLaw a ≤ 4 := by
  -- The variance argument is the anonymous-constructor term `⟨1, zero_le_one⟩`,
  -- which blocks rewriting inside the goal; generalise it away first.
  have hgauss : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 ⟨1, zero_le_one⟩ = 1 := by
    have key : ∀ v : NNReal, v = 1 → ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = 1 := by
      rintro v rfl
      have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
      change Var[id; gaussianReal 0 1] = 1 at hv
      rw [variance_eq_integral measurable_id.aemeasurable] at hv
      simp only [integral_id_gaussianReal, id_eq, sub_zero] at hv
      exact hv
    exact key _ rfl
  unfold gaussianRademacherLaw
  rw [lintegral_map
    (by fun_prop : Measurable (fun x : ℝ ↦ ENNReal.ofReal (x ^ 2))) (by fun_prop)]
  rw [lintegral_prod (fun z : ℝ × ℝ ↦
      ENNReal.ofReal ((Real.sqrt (1 - a ^ 2) * z.1 + a * z.2) ^ 2))
    ((by fun_prop : Measurable (fun z : ℝ × ℝ ↦
      ENNReal.ofReal ((Real.sqrt (1 - a ^ 2) * z.1 + a * z.2) ^ 2))).aemeasurable)]
  simp only [rademacherLaw, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac]
  have hsqrt2 : Real.sqrt (1 - a ^ 2) ^ 2 = 1 - a ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  have hpoint (x : ℝ) :
      ENNReal.ofReal (1 / 2) • ENNReal.ofReal
            ((Real.sqrt (1 - a ^ 2) * x + a * -1) ^ 2) +
          ENNReal.ofReal (1 / 2) • ENNReal.ofReal
            ((Real.sqrt (1 - a ^ 2) * x + a * 1) ^ 2) ≤
        ENNReal.ofReal (2 * x ^ 2 + 2) := by
    simp only [smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_add (mul_nonneg (by positivity) (sq_nonneg _))
        (mul_nonneg (by positivity) (sq_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (Real.sqrt (1 - a ^ 2) * x - a),
      sq_nonneg (Real.sqrt (1 - a ^ 2) * x + a)]
  refine (lintegral_mono hpoint).trans_eq ?_
  have hsqint : Integrable (fun x : ℝ ↦ x ^ 2)
      (gaussianReal 0 ⟨1, zero_le_one⟩) := by
    simpa only [id_eq, Real.norm_eq_abs, sq_abs] using
      (memLp_id_gaussianReal (μ := 0) (v := ⟨1, zero_le_one⟩) 2).integrable_sq
  have h2sq : Integrable (fun x : ℝ ↦ 2 * x ^ 2)
      (gaussianReal 0 ⟨1, zero_le_one⟩) := hsqint.const_mul 2
  have h2 : Integrable (fun _x : ℝ ↦ (2 : ℝ))
      (gaussianReal 0 ⟨1, zero_le_one⟩) := integrable_const 2
  have hsum : Integrable (fun x : ℝ ↦ 2 * x ^ 2 + 2)
      (gaussianReal 0 ⟨1, zero_le_one⟩) := h2sq.add h2
  rw [← ofReal_integral_eq_lintegral_ofReal hsum
    (Filter.Eventually.of_forall fun x ↦ by
      change 0 ≤ 2 * x ^ 2 + 2
      nlinarith [sq_nonneg x])]
  rw [integral_add h2sq h2, integral_const_mul, hgauss]
  norm_num

/-- At a characteristic zero, the sine-score regression remainder is centered. -/
-- @node: sine_remainder_centered_of_mgf_zero
lemma sine_remainder_centered_of_mgf_zero
    (p : Parameters) (m : Model (Xspace := Xspace) p) (n : ℕ) (t : ℝ)
    (hzero : treatmentMGF p m (Complex.I * t) = 0)
    (hind : IndependentTreatmentNoise p m) (hout : OutcomeMeanIndependence p m)
    (htheta : ThetaRange p m) (hg : GRange p m) (hq : QRange p m) :
    ∫ o, (outcome o - m.theta0 * learnedResidual p m n o) *
      Real.sin (t * learnedResidual p m n o) ∂m.P = 0 := by
  let D0 : Xspace → ℝ := fun x ↦ m.g0 x - barG p m n x
  let b0 : Xspace → ℝ := fun x ↦ m.q0 x - m.theta0 * D0 x
  let J : Obs Xspace → ℝ := fun o ↦ Real.sin (t * learnedResidual p m n o)
  have heta : Measurable (eta p m) := by
    unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  have hX : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hD : Measurable D0 := m.g0_measurable.sub
    (((m.gcode_measurable n).max measurable_const).min measurable_const)
  have hb : Measurable b0 := m.q0_measurable.sub (measurable_const.mul hD)
  have hsin : ∫ o, Real.sin (t * eta p m o) ∂m.P = 0 := by
    simpa using integral_sin_shift_eq_zero p m t 0 hzero
  have hcos : ∫ o, Real.cos (t * eta p m o) ∂m.P = 0 := by
    have hE : Integrable (fun o ↦ Complex.exp ((Complex.I * t) * eta p m o)) m.P := by
      apply (integrable_const (μ := m.P) (c := (1 : ℝ))).mono'
        (by fun_prop : Measurable (fun o ↦ Complex.exp
          ((Complex.I * t) * eta p m o))).aestronglyMeasurable
      filter_upwards [] with o
      simp [Complex.norm_exp, Complex.mul_re]
    have hre : (∫ o, Complex.exp ((Complex.I * t) * eta p m o) ∂m.P).re = 0 := by
      change (treatmentMGF p m (Complex.I * t)).re = 0
      rw [hzero]
      rfl
    calc
      _ = ∫ o, (Complex.exp ((Complex.I * t) * eta p m o)).re ∂m.P := by
        apply integral_congr_ae
        filter_upwards [] with o
        rw [Complex.exp_re]
        norm_num [Complex.mul_re, Complex.mul_im]
      _ = (∫ o, Complex.exp ((Complex.I * t) * eta p m o) ∂m.P).re :=
        integral_re hE
      _ = 0 := hre
  have hbInt : Integrable (fun o ↦ b0 (covariate o)) m.P := by
    apply (integrable_const (μ := m.P)
      (c := p.Cq + p.Ctheta * (2 * p.Cg))).mono'
      (hb.comp hX).aestronglyMeasurable
    have hg' := MeasureTheory.ae_of_ae_map hX.aemeasurable hg
    have hq' := MeasureTheory.ae_of_ae_map hX.aemeasurable hq
    filter_upwards [hg', hq'] with o hgo hqo
    have hbar : |barG p m n (covariate o)| ≤ p.Cg := by
      have hpCg := p.constants_pos.2.1
      rw [abs_le]
      dsimp [barG]
      constructor <;> simp_all <;> linarith
    have hD0 : |D0 (covariate o)| ≤ 2 * p.Cg := by
      dsimp [D0]
      exact (abs_sub _ _).trans (by linarith)
    rw [Real.norm_eq_abs]
    dsimp [b0]
    calc
      _ ≤ |m.q0 (covariate o)| + |m.theta0| * |D0 (covariate o)| := by
        simpa [abs_mul] using abs_sub (m.q0 (covariate o)) (m.theta0 * D0 (covariate o))
      _ ≤ _ := add_le_add hqo
        (mul_le_mul htheta hD0 (abs_nonneg _) p.constants_pos.1.le)
  have hbJ : ∫ o, b0 (covariate o) * J o ∂m.P = 0 := by
    have hfacSin := hind.integral_fun_comp_mul_comp
      (f := fun e : ℝ ↦ Real.sin (t * e))
      (g := fun x : Xspace ↦ b0 x * Real.cos (t * D0 x))
      heta.aemeasurable hX.aemeasurable (by fun_prop) (by fun_prop)
    have hfacCos := hind.integral_fun_comp_mul_comp
      (f := fun e : ℝ ↦ Real.cos (t * e))
      (g := fun x : Xspace ↦ b0 x * Real.sin (t * D0 x))
      heta.aemeasurable hX.aemeasurable (by fun_prop) (by fun_prop)
    have htermSin : Integrable (fun o ↦ Real.sin (t * eta p m o) *
        (b0 (covariate o) * Real.cos (t * D0 (covariate o)))) m.P := by
      refine (hbInt.bdd_mul
        (f := fun o ↦ Real.sin (t * eta p m o) * Real.cos (t * D0 (covariate o)))
        (c := 1) (by fun_prop) ?_).congr ?_
      · filter_upwards [] with o
        rw [Real.norm_eq_abs, abs_mul]
        nlinarith [Real.abs_sin_le_one (t * eta p m o),
          Real.abs_cos_le_one (t * D0 (covariate o)),
          abs_nonneg (Real.sin (t * eta p m o)),
          abs_nonneg (Real.cos (t * D0 (covariate o)))]
      · filter_upwards [] with o
        ring
    have htermCos : Integrable (fun o ↦ Real.cos (t * eta p m o) *
        (b0 (covariate o) * Real.sin (t * D0 (covariate o)))) m.P := by
      refine (hbInt.bdd_mul
        (f := fun o ↦ Real.cos (t * eta p m o) * Real.sin (t * D0 (covariate o)))
        (c := 1) (by fun_prop) ?_).congr ?_
      · filter_upwards [] with o
        rw [Real.norm_eq_abs, abs_mul]
        nlinarith [Real.abs_cos_le_one (t * eta p m o),
          Real.abs_sin_le_one (t * D0 (covariate o)),
          abs_nonneg (Real.cos (t * eta p m o)),
          abs_nonneg (Real.sin (t * D0 (covariate o)))]
      · filter_upwards [] with o
        ring
    rw [show (∫ o, b0 (covariate o) * J o ∂m.P) =
        (∫ o, Real.sin (t * eta p m o) *
          (b0 (covariate o) * Real.cos (t * D0 (covariate o))) ∂m.P) +
        ∫ o, Real.cos (t * eta p m o) *
          (b0 (covariate o) * Real.sin (t * D0 (covariate o))) ∂m.P by
      rw [← integral_add htermSin htermCos]
      apply integral_congr_ae
      filter_upwards [] with o
      have hZ : learnedResidual p m n o = eta p m o + D0 (covariate o) := by
        simp [learnedResidual, eta, D0, treatmentError]
      simp only [J, hZ, mul_add, Real.sin_add]
      ring_nf]
    rw [hfacSin, hfacCos, hsin, hcos]
    ring
  have hJmeas : StronglyMeasurable[xTSigma (Xspace := Xspace)] J := by
    apply Measurable.stronglyMeasurable
    dsimp [J]
    change Measurable[MeasurableSpace.comap
      (fun o : Obs Xspace ↦ (covariate o, treatment o)) inferInstance]
      (fun o ↦ Real.sin (t * learnedResidual p m n o))
    have hbarMeas : Measurable (barG p m n) :=
      ((m.gcode_measurable n).max measurable_const).min measurable_const
    have hbase : Measurable (fun xt : Xspace × ℝ ↦
        Real.sin (t * (xt.2 - barG p m n xt.1))) :=
      Real.continuous_sin.measurable.comp
        (measurable_const.mul (measurable_snd.sub (hbarMeas.comp measurable_fst)))
    simpa [learnedResidual, treatment, covariate, Function.comp_def] using
      hbase.comp (comap_measurable (fun o : Obs Xspace ↦
        (covariate o, treatment o)))
  have hJambient : Measurable J := by
    have hbarMeas : Measurable (barG p m n) :=
      ((m.gcode_measurable n).max measurable_const).min measurable_const
    dsimp [J]
    exact Real.continuous_sin.measurable.comp
      (measurable_const.mul (measurable_snd.fst.sub
        (hbarMeas.comp measurable_fst)))
  have hbJint : Integrable (fun o ↦ b0 (covariate o) * J o) m.P := by
    exact hbInt.mul_bdd hJambient.aestronglyMeasurable
      (Filter.Eventually.of_forall fun o ↦ by
        simpa [J, Real.norm_eq_abs] using
          Real.abs_sin_le_one (t * learnedResidual p m n o))
  have hxiJint : Integrable (fun o ↦ xi p m o * J o) m.P := by
    exact hout.1.mul_bdd hJambient.aestronglyMeasurable
      (Filter.Eventually.of_forall fun o ↦ by
        simpa [J, Real.norm_eq_abs] using
          Real.abs_sin_le_one (t * learnedResidual p m n o)
      )
  have hxiJ : ∫ o, xi p m o * J o ∂m.P = 0 := by
    have hXTle : xTSigma (Xspace := Xspace) ≤
        (inferInstance : MeasurableSpace (Obs Xspace)) :=
      Measurable.comap_le (measurable_fst.prodMk measurable_snd.fst)
    haveI : SigmaFinite (m.P.trim hXTle) := inferInstance
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_right
      (μ := m.P) (m := xTSigma (Xspace := Xspace)) hJmeas hxiJint hout.1
    calc
      _ = ∫ o, (@condExp (Obs Xspace) ℝ (xTSigma (Xspace := Xspace))
          inferInstance _ _ m.P (fun o ↦ xi p m o * J o)) o ∂m.P := by
        symm
        exact integral_condExp (Measurable.comap_le
          (measurable_fst.prodMk measurable_snd.fst))
      _ = ∫ o, (@condExp (Obs Xspace) ℝ (xTSigma (Xspace := Xspace))
          inferInstance _ _ m.P (xi p m)) o * J o ∂m.P := integral_congr_ae hpull
      _ = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hout.2] with o ho
        simp [ho]
  rw [show (fun o ↦ (outcome o - m.theta0 * learnedResidual p m n o) * J o) =
      fun o ↦ b0 (covariate o) * J o + xi p m o * J o by
    funext o
    simp [b0, D0, J, xi, learnedResidual, eta, treatmentError]
    ring]
  rw [integral_add hbJint hxiJint]
  rw [hbJ, hxiJ]
  simp

/-- Suppose [the treatment noise has second moment at most four](hyp:hetaSq), [the treatment
coefficient lies within its range bound](hyp:htheta), [the treatment regression is uniformly
bounded](hyp:hg), [the outcome regression is uniformly bounded](hyp:hq), and [the outcome noise
is sub-Gaussian with the stated scale](hyp:hxi). Then [the two sine scores — the learned
treatment residual times the sine of the frequency times that residual, and the residualized
outcome times the same sine — are measurable and square integrable, with squared second moments
at most eight plus sixteen times the squared treatment-regression bound, and at most four times
the squared combined outcome bound plus four times the squared outcome-noise scale,
respectively](goal). -/
-- @node: sine_score_memLp_of_eta_second_lintegral_le
lemma sine_score_memLp_of_eta_second_lintegral_le
    (p : Parameters) (m : Model (Xspace := Xspace) p) (n : ℕ) (t : ℝ)
    (hetaSq : ∫⁻ o, ENNReal.ofReal ((eta p m o) ^ 2) ∂m.P ≤ 4)
    (htheta : ThetaRange p m) (hg : GRange p m) (hq : QRange p m)
    (hxi : XiSubGaussian p m) :
    let W := fun o ↦ learnedResidual p m n o * Real.sin (t * learnedResidual p m n o)
    let R := fun o ↦ (outcome o - m.theta0 * learnedResidual p m n o) *
      Real.sin (t * learnedResidual p m n o)
    Measurable W ∧ Measurable R ∧ MemLp W 2 m.P ∧ MemLp R 2 m.P ∧
      (eLpNorm W 2 m.P).toReal ^ 2 ≤ 8 + 16 * p.Cg ^ 2 ∧
      (eLpNorm R 2 m.P).toReal ^ 2 ≤
        4 * (p.Cq + 2 * p.Ctheta * p.Cg) ^ 2 + 4 * p.psixi ^ 2 := by
  dsimp only
  let W : Obs Xspace → ℝ := fun o ↦
    learnedResidual p m n o * Real.sin (t * learnedResidual p m n o)
  let R : Obs Xspace → ℝ := fun o ↦
    (outcome o - m.theta0 * learnedResidual p m n o) *
      Real.sin (t * learnedResidual p m n o)
  have heta : Measurable (eta p m) := by
    unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  have hZ : Measurable (learnedResidual p m n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      ((((m.gcode_measurable n).comp measurable_fst).max measurable_const).min
        measurable_const)
  have hWmeas : Measurable W := by dsimp [W]; fun_prop
  have hRmeas : Measurable R := by
    dsimp [R, outcome]
    fun_prop
  have hcov : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hbar (x : Xspace) : |barG p m n x| ≤ p.Cg := by
    have hCg := p.constants_pos.2.1
    rw [abs_le]
    dsimp [barG]
    constructor <;> simp_all <;> linarith
  have hD : ∀ᵐ o ∂m.P, |treatmentError p m n o| ≤ 2 * p.Cg := by
    have hg' := MeasureTheory.ae_of_ae_map hcov.aemeasurable hg
    filter_upwards [hg'] with o ho
    exact (abs_sub _ _).trans (by linarith [hbar (covariate o)])
  have hWSq : ∫⁻ o, ENNReal.ofReal ((W o) ^ 2) ∂m.P ≤
      ENNReal.ofReal ((Real.sqrt (8 + 16 * p.Cg ^ 2)) ^ 2) := by
    calc
      _ ≤ ∫⁻ o, ENNReal.ofReal
          (2 * (eta p m o) ^ 2 + 8 * p.Cg ^ 2) ∂m.P := by
        apply lintegral_mono_ae
        filter_upwards [hD] with o hDo
        apply ENNReal.ofReal_le_ofReal
        have hZeq : learnedResidual p m n o =
            eta p m o + treatmentError p m n o := by
          simp [learnedResidual, eta, treatmentError]
        dsimp [W]
        have hs := Real.abs_sin_le_one (t * learnedResidual p m n o)
        have hCg : 0 ≤ p.Cg := p.constants_pos.2.1.le
        have hDsq : treatmentError p m n o ^ 2 ≤ (2 * p.Cg) ^ 2 :=
          (by simpa only [sq_abs] using
            ((sq_le_sq₀ (abs_nonneg (treatmentError p m n o))
              (by positivity : 0 ≤ |2 * p.Cg|)).2
                (by simpa [abs_of_nonneg (by positivity : 0 ≤ 2 * p.Cg)] using hDo)))
        rw [hZeq]
        have hs' := Real.abs_sin_le_one
          (t * (eta p m o + treatmentError p m n o))
        have hsSq : Real.sin (t * (eta p m o + treatmentError p m n o)) ^ 2 ≤ 1 := by
          simpa only [sq_abs, one_pow] using
            ((sq_le_sq₀ (abs_nonneg (Real.sin
              (t * (eta p m o + treatmentError p m n o)))) zero_le_one).2 hs')
        nlinarith [sq_nonneg (eta p m o - treatmentError p m n o)]
      _ = 2 * (∫⁻ o, ENNReal.ofReal ((eta p m o) ^ 2) ∂m.P) +
          ENNReal.ofReal (8 * p.Cg ^ 2) := by
        rw [show (fun o ↦ ENNReal.ofReal
            (2 * (eta p m o) ^ 2 + 8 * p.Cg ^ 2)) =
            fun o ↦ 2 * ENNReal.ofReal ((eta p m o) ^ 2) +
              ENNReal.ofReal (8 * p.Cg ^ 2) by
          funext o
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
          norm_num]
        rw [lintegral_add_left
          (measurable_const.fun_mul ((heta.pow_const 2).ennreal_ofReal)),
          lintegral_const_mul'' 2
            ((heta.pow_const 2).ennreal_ofReal.aemeasurable)]
        simp
      _ ≤ ENNReal.ofReal (8 + 16 * p.Cg ^ 2) := by
        calc
          _ ≤ 2 * 4 + ENNReal.ofReal (8 * p.Cg ^ 2) := by gcongr
          _ = ENNReal.ofReal (8 + 8 * p.Cg ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8)]
            norm_num
          _ ≤ ENNReal.ofReal (8 + 16 * p.Cg ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            nlinarith [sq_nonneg p.Cg]
      _ = _ := by
        rw [Real.sq_sqrt]
        positivity
  have hWpack := memLp_two_and_eLpNorm_le_of_sq_lintegral_le m.P hWmeas
    (Real.sqrt_nonneg _) hWSq
  have hxiMeas : Measurable (xi p m) := by
    unfold xi outcome covariate eta treatment
    exact measurable_snd.snd.sub (m.q0_measurable.comp measurable_fst) |>.sub
      (measurable_const.mul
        (measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)))
  have hxiExp : ∫ o, Real.exp ((xi p m o) ^ 2 / p.psixi ^ 2) ∂m.P ≤ 2 := by
    let f := fun o : Obs Xspace ↦ Real.exp ((xi p m o) ^ 2 / p.psixi ^ 2)
    calc
      ∫ o, f o ∂m.P = ∫ o, (@condExp (Obs Xspace) ℝ
          (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P f) o ∂m.P := by
        symm
        exact integral_condExp hcov.comap_le
      _ ≤ ∫ _o, (2 : ℝ) ∂m.P := integral_mono_ae
        (integrable_condExp) (integrable_const 2) (by exact hxi.2)
      _ = 2 := by simp
  have hxiSq : ∫⁻ o, ENNReal.ofReal ((xi p m o) ^ 2) ∂m.P ≤
      ENNReal.ofReal (2 * p.psixi ^ 2) := by
    have hxiSqInt : Integrable (fun o ↦ (xi p m o) ^ 2) m.P := by
      have hpsi : 0 < p.psixi := p.constants_pos.2.2.2.2.1
      apply (hxi.1.const_mul (max 1 (p.psixi ^ 2))).mono'
        (hxiMeas.pow_const 2).aestronglyMeasurable
      filter_upwards [] with o
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hexp := Real.add_one_le_exp ((xi p m o) ^ 2 / p.psixi ^ 2)
      have hpsiSq : 0 < p.psixi ^ 2 := sq_pos_of_pos hpsi
      have hscaled : (xi p m o) ^ 2 / p.psixi ^ 2 ≤
          Real.exp ((xi p m o) ^ 2 / p.psixi ^ 2) := by linarith
      calc
        (xi p m o) ^ 2 = p.psixi ^ 2 * ((xi p m o) ^ 2 / p.psixi ^ 2) := by
          field_simp [hpsi.ne']
        _ ≤ p.psixi ^ 2 * Real.exp ((xi p m o) ^ 2 / p.psixi ^ 2) :=
          mul_le_mul_of_nonneg_left hscaled hpsiSq.le
        _ ≤ Real.exp ((xi p m o) ^ 2 / p.psixi ^ 2) *
            max 1 (p.psixi ^ 2) := by
          have he : 0 ≤ Real.exp ((xi p m o) ^ 2 / p.psixi ^ 2) := (Real.exp_pos _).le
          nlinarith [le_max_right (1 : ℝ) (p.psixi ^ 2)]
        _ = max 1 (p.psixi ^ 2) *
            Real.exp ((xi p m o) ^ 2 / p.psixi ^ 2) := by ring
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · apply ENNReal.ofReal_le_ofReal
      have hmom := luxemburg_even_moment_integral_le (xi p m) hxiMeas
        p.constants_pos.2.2.2.2.1 hxi.1 hxiExp 1
      simpa [abs_sq] using hmom
    · exact hxiSqInt
    · exact Filter.Eventually.of_forall fun _ ↦ sq_nonneg _
  let B : ℝ := p.Cq + 2 * p.Ctheta * p.Cg
  have htheta0 : 0 ≤ p.Ctheta := p.constants_pos.1.le
  have hCg0 : 0 ≤ p.Cg := p.constants_pos.2.1.le
  have hq0 : 0 ≤ p.Cq := p.constants_pos.2.2.1.le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg' := MeasureTheory.ae_of_ae_map hcov.aemeasurable hg
  have hq' := MeasureTheory.ae_of_ae_map hcov.aemeasurable hq
  have hRSq : ∫⁻ o, ENNReal.ofReal ((R o) ^ 2) ∂m.P ≤
      ENNReal.ofReal ((Real.sqrt (4 * B ^ 2 + 4 * p.psixi ^ 2)) ^ 2) := by
    calc
      _ ≤ ∫⁻ o, ENNReal.ofReal (2 * B ^ 2 + 2 * (xi p m o) ^ 2) ∂m.P := by
        apply lintegral_mono_ae
        filter_upwards [hD, hg', hq'] with o hDo hgo hqo
        apply ENNReal.ofReal_le_ofReal
        have hb : |m.q0 (covariate o) - m.theta0 * treatmentError p m n o| ≤ B := by
          calc
            _ ≤ |m.q0 (covariate o)| + |m.theta0| *
                |treatmentError p m n o| := by
              rw [← abs_mul]
              exact abs_sub _ _
            _ ≤ B := by
              dsimp [B]
              have hm : |m.theta0| * |treatmentError p m n o| ≤
                  p.Ctheta * (2 * p.Cg) :=
                mul_le_mul htheta hDo (abs_nonneg _) htheta0
              nlinarith
        have hbSq : (m.q0 (covariate o) -
            m.theta0 * treatmentError p m n o) ^ 2 ≤ B ^ 2 :=
          (by simpa only [sq_abs] using
            ((sq_le_sq₀ (abs_nonneg _) hB).2 hb))
        have hdecomp : outcome o - m.theta0 * learnedResidual p m n o =
            (m.q0 (covariate o) - m.theta0 * treatmentError p m n o) + xi p m o := by
          simp [xi, learnedResidual, treatmentError, eta, outcome]
          ring
        dsimp [R]
        rw [hdecomp]
        have hs := Real.abs_sin_le_one (t * learnedResidual p m n o)
        have hsSq : Real.sin (t * learnedResidual p m n o) ^ 2 ≤ 1 := by
          simpa [sq_abs] using
            ((sq_le_sq₀ (abs_nonneg (Real.sin (t * learnedResidual p m n o)))
              (by norm_num : (0 : ℝ) ≤ |1|)).2 (by simpa using hs))
        nlinarith [sq_nonneg
          ((m.q0 (covariate o) - m.theta0 * treatmentError p m n o) - xi p m o)]
      _ = ENNReal.ofReal (2 * B ^ 2) +
          2 * (∫⁻ o, ENNReal.ofReal ((xi p m o) ^ 2) ∂m.P) := by
        rw [show (fun o ↦ ENNReal.ofReal
            (2 * B ^ 2 + 2 * (xi p m o) ^ 2)) =
            fun o ↦ ENNReal.ofReal (2 * B ^ 2) +
              2 * ENNReal.ofReal ((xi p m o) ^ 2) by
          funext o
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
          norm_num]
        rw [lintegral_add_left measurable_const,
          lintegral_const_mul'' 2
            ((hxiMeas.pow_const 2).ennreal_ofReal.aemeasurable)]
        simp
      _ ≤ ENNReal.ofReal (4 * B ^ 2 + 4 * p.psixi ^ 2) := by
        calc
          _ ≤ ENNReal.ofReal (2 * B ^ 2) +
              2 * ENNReal.ofReal (2 * p.psixi ^ 2) := by gcongr
          _ = ENNReal.ofReal (2 * B ^ 2 + 4 * p.psixi ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
              ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4)]
            norm_num
            ring
          _ ≤ ENNReal.ofReal (4 * B ^ 2 + 4 * p.psixi ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            nlinarith [sq_nonneg B]
      _ = _ := by rw [Real.sq_sqrt]; positivity
  have hRpack := memLp_two_and_eLpNorm_le_of_sq_lintegral_le m.P hRmeas
    (Real.sqrt_nonneg _) hRSq
  have hWreal : (eLpNorm W 2 m.P).toReal ≤ Real.sqrt (8 + 16 * p.Cg ^ 2) := by
    rw [← ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    exact (ENNReal.toReal_le_toReal hWpack.1.eLpNorm_ne_top (by simp)).2 hWpack.2
  have hRreal : (eLpNorm R 2 m.P).toReal ≤
      Real.sqrt (4 * B ^ 2 + 4 * p.psixi ^ 2) := by
    rw [← ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    exact (ENNReal.toReal_le_toReal hRpack.1.eLpNorm_ne_top (by simp)).2 hRpack.2
  have hWnorm := (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg _)).2 hWreal
  have hRnorm := (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg _)).2 hRreal
  rw [Real.sq_sqrt (by positivity : 0 ≤ 8 + 16 * p.Cg ^ 2)] at hWnorm
  rw [Real.sq_sqrt (by positivity : 0 ≤ 4 * B ^ 2 + 4 * p.psixi ^ 2)] at hRnorm
  simpa only [W, R, B] using
    ⟨hWmeas, hRmeas, hWpack.1, hRpack.1, hWnorm, hRnorm⟩

/-- [The sine-score estimator at a given frequency and denominator threshold is exactly the
generic clipped ratio rule applied to two sample averages: the average of the learned treatment
residual times the sine of the frequency times that residual as denominator, and the average of
the residualized outcome times the same sine as numerator correction](goal), which is what lets
the generic risk bound for clipped ratios be applied to it. -/
-- @node: thetaHatAt_eq_clippedRatioFromScores
lemma thetaHatAt_eq_clippedRatioFromScores
    (p : Parameters) (m : Model (Xspace := Xspace) p) (n : ℕ)
    (t threshold : ℝ) (data : Fin n → Obs Xspace) :
    thetaHatAt p m n t threshold data =
      clippedRatioFromScores p.Ctheta m.theta0 n threshold
        (fun o ↦ learnedResidual p m n o *
          Real.sin (t * learnedResidual p m n o))
        (fun o ↦ (outcome o - m.theta0 * learnedResidual p m n o) *
          Real.sin (t * learnedResidual p m n o)) data := by
  unfold thetaHatAt clippedRatioFromScores empiricalMean
  dsimp only
  have hnum : (n : ℝ)⁻¹ * ∑ i,
      outcome (data i) * Real.sin (t * learnedResidual p m n (data i)) =
      m.theta0 * ((n : ℝ)⁻¹ * ∑ i,
        learnedResidual p m n (data i) *
          Real.sin (t * learnedResidual p m n (data i))) +
      (n : ℝ)⁻¹ * ∑ i,
        (outcome (data i) - m.theta0 * learnedResidual p m n (data i)) *
          Real.sin (t * learnedResidual p m n (data i)) := by
    calc
      _ = (n : ℝ)⁻¹ * ∑ i,
          (m.theta0 * learnedResidual p m n (data i) *
              Real.sin (t * learnedResidual p m n (data i)) +
            (outcome (data i) - m.theta0 * learnedResidual p m n (data i)) *
              Real.sin (t * learnedResidual p m n (data i))) := by
        apply congrArg ((n : ℝ)⁻¹ * ·)
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (n : ℝ)⁻¹ *
          ((∑ i, m.theta0 * (learnedResidual p m n (data i) *
              Real.sin (t * learnedResidual p m n (data i)))) +
            ∑ i, (outcome (data i) - m.theta0 * learnedResidual p m n (data i)) *
              Real.sin (t * learnedResidual p m n (data i))) := by
        rw [Finset.sum_add_distrib]
        congr 2
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by
        rw [← Finset.mul_sum]
        ring
  rw [hnum]

/-- The complete path conclusion shared by the benchmark lemma and the
local-to-Gaussian partial theorem. -/
def GaussianRademacherPathConclusion (p : Parameters)
    (m : Model (Xspace := Xspace) p) (a C : ℝ) : Prop :=
  let t := Real.pi / (2 * a)
  let A := a * Real.exp (-(1 - a ^ 2) * Real.pi ^ 2 / (8 * a ^ 2))
  let deltaA := 2 * a ^ 4
  treatmentMGF p m =
      (fun z ↦ Complex.exp (((1 - a ^ 2 : ℝ) : ℂ) * z ^ 2 / 2) *
        Complex.cosh ((a : ℂ) * z)) ∧
    kappaEta p m = -2 * a ^ 4 ∧
    0 < t ∧ treatmentMGF p m (Complex.I * t) = 0 ∧
    (∀ u ∈ Ioo (0 : ℝ) t, treatmentMGF p m (Complex.I * u) ≠ 0) ∧
    (∀ d : ℝ, ∫ o, Real.sin (t * (eta p m o + d)) ∂m.P = 0) ∧
    (t * p.eps1n p.n ≤ 1 / 2 →
      (∫ o, learnedResidual p m p.n o *
          Real.sin (t * learnedResidual p m p.n o) ∂m.P =
        A * ∫ o, Real.cos (t * treatmentError p m p.n o) ∂m.P) ∧
      A / 2 ≤ ∫ o, learnedResidual p m p.n o *
          Real.sin (t * learnedResidual p m p.n o) ∂m.P ∧
      mseRisk m p.n (thetaHatAt p m p.n t (A / 4)) ≤
        ENNReal.ofReal (C * min 1 ((p.n : ℝ)⁻¹ * (a ^ 2)⁻¹ *
          Real.exp ((1 - a ^ 2) * Real.pi ^ 2 / (4 * a ^ 2)))) ∧
      p.eps1n p.n ≤ deltaA ^ (1 / 4 : ℝ) / (2 ^ (1 / 4 : ℝ) * Real.pi) ∧
      mseRisk m p.n (thetaHatAt p m p.n t (A / 4)) ≤
        ENNReal.ofReal (C * min 1 ((p.n : ℝ)⁻¹ * deltaA ^ (-1 / 2 : ℝ) *
          Real.exp (Real.pi ^ 2 * Real.sqrt 2 / 4 * deltaA ^ (-1 / 2 : ℝ)))))

set_option maxHeartbeats 800000 in
/-- Path-specific MGF, cumulant, annihilation, denominator, and risk benchmark. -/
-- @node: lem:gaussian-rademacher-l1-benchmark
lemma gaussian_rademacher_l1_benchmark (Ctheta Cg Cq psixi : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : Parameters), p.Ctheta = Ctheta → p.Cg = Cg →
        p.Cq = Cq → p.psixi = psixi → p.k = 4 →
      ∀ (a : ℝ), a ∈ Ioc (0 : ℝ) 1 →
      ∀ (m : Model (Xspace := Xspace) p),
        m.P.map (eta p m) = gaussianRademacherLaw a →
        IidSampling p.n m.P (iidLaw m p.n) →
        IndependentTreatmentNoise p m → OutcomeMeanIndependence p m →
        ThetaRange p m → GRange p m → QRange p m →
        XiSubGaussian p m → TreatmentCodeRadiusL1At p m p.n →
        GaussianRademacherPathConclusion p m a C := by
  let K : ℝ := 4 * (Cq + 2 * Ctheta * Cg) ^ 2 + 4 * psixi ^ 2 +
    Ctheta ^ 2 * (8 + 16 * Cg ^ 2)
  let C : ℝ := 1 + 64 * K + 4 * Ctheta ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro p hpTheta hpG hpQ hpXi hk a ha m hlaw _hiid hind hout htheta hg hq hxi hL1
  have ha0 : 0 < a := ha.1
  have ha1 : a ≤ 1 := ha.2
  let t : ℝ := Real.pi / (2 * a)
  let A : ℝ := a * Real.exp (-(1 - a ^ 2) * Real.pi ^ 2 / (8 * a ^ 2))
  let W : Obs Xspace → ℝ := fun o ↦ learnedResidual p m p.n o *
    Real.sin (t * learnedResidual p m p.n o)
  let R : Obs Xspace → ℝ := fun o ↦
    (outcome o - m.theta0 * learnedResidual p m p.n o) *
      Real.sin (t * learnedResidual p m p.n o)
  have ht : 0 < t := div_pos Real.pi_pos (mul_pos zero_lt_two ha0)
  have hA : 0 < A := mul_pos ha0 (Real.exp_pos _)
  have hmgf := treatmentMGF_eq_gaussianRademacher p m ha0 ha1 hlaw
  have hkappa := model_gaussianRademacher_kappa_four p m hk ha0 ha1 hlaw
  have hzero := gaussianRademacher_first_characteristic_zero ha0
  have hshift : ∀ d : ℝ, ∫ o, Real.sin (t * (eta p m o + d)) ∂m.P = 0 := by
    intro d
    exact integral_sin_shift_eq_zero p m t d (by
      rw [hmgf]
      exact hzero.1)
  dsimp [GaussianRademacherPathConclusion]
  refine ⟨hmgf, hkappa, ht, ?_, ?_, hshift, ?_⟩
  · rw [hmgf]
    exact hzero.1
  · intro u hu
    rw [hmgf]
    exact hzero.2 u hu
  · intro hsmall
    have hetaInt : Integrable (eta p m) m.P := by
      have hp := eta_integrable_exp_gaussianRademacher p m hlaw 1
      have hn := eta_integrable_exp_gaussianRademacher p m hlaw (-1)
      apply (hp.add hn).mono' (by
        unfold eta treatment covariate
        exact (measurable_snd.fst.sub
          (m.g0_measurable.comp measurable_fst)).aestronglyMeasurable)
      filter_upwards [] with o
      simp only [Pi.add_apply, one_mul, neg_mul, Real.norm_eq_abs]
      by_cases ho : 0 ≤ eta p m o
      · rw [abs_of_nonneg ho]
        linarith [Real.add_one_le_exp (eta p m o), Real.exp_pos (-eta p m o)]
      · rw [abs_of_neg (lt_of_not_ge ho)]
        linarith [Real.add_one_le_exp (-eta p m o), Real.exp_pos (eta p m o)]
    have hmoment : ∫ o, (eta p m o : ℂ) *
        Complex.exp ((Complex.I * t) * (eta p m o : ℂ)) ∂m.P = Complex.I * A := by
      exact eta_cexp_moment_at_first_zero p m ha0 ha1 hlaw
    have hdenId := learnedResidual_sine_denominator_identity
      p m p.n t A (by rw [hmgf]; exact hzero.1) hmoment hetaInt hind hg
    have hdenLower := learnedResidual_sine_denominator_lower
      p m p.n t A ht hA hdenId hL1 (by simpa only [t] using hsmall)
    have hremMean : ∫ o, R o ∂m.P = 0 := by
      simpa only [R] using sine_remainder_centered_of_mgf_zero
        p m p.n t (by rw [hmgf]; exact hzero.1) hind hout htheta hg hq
    have hetaSq : ∫⁻ o, ENNReal.ofReal ((eta p m o) ^ 2) ∂m.P ≤ 4 := by
      have heta : Measurable (eta p m) := by
        unfold eta treatment covariate
        exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
      calc
        _ = ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂(m.P.map (eta p m)) := by
          rw [lintegral_map (by fun_prop) heta]
        _ = ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂gaussianRademacherLaw a := by
          rw [hlaw]
        _ ≤ 4 := gaussianRademacher_second_lintegral_le ha0 ha1
    have hscore := sine_score_memLp_of_eta_second_lintegral_le
      p m p.n t hetaSq htheta hg hq hxi
    have hWmean : ∫ o, W o ∂m.P = ∫ o, learnedResidual p m p.n o *
        Real.sin (t * learnedResidual p m p.n o) ∂m.P := rfl
    have hriskRaw := clippedRatioFromScores_lintegral_le m.P
      p.Ctheta m.theta0 A p.n W R (∫ o, W o ∂m.P)
      (by exact p.n_pos) htheta hA (by simpa only [W, t] using hdenLower)
      hscore.1 hscore.2.1 hscore.2.2.1 hscore.2.2.2.1 rfl hremMean
    have hrisk : mseRisk m p.n (thetaHatAt p m p.n t (A / 4)) ≤
        ENNReal.ofReal (16 / A ^ 2) * (p.n : ENNReal)⁻¹ *
          (ENNReal.ofReal ((eLpNorm R 2 m.P).toReal ^ 2) +
            ENNReal.ofReal (p.Ctheta ^ 2) *
              ENNReal.ofReal ((eLpNorm W 2 m.P).toReal ^ 2)) := by
      unfold mseRisk iidLaw
      simpa only [thetaHatAt_eq_clippedRatioFromScores p m p.n t (A / 4)] using hriskRaw
    have hriskFirst : mseRisk m p.n (thetaHatAt p m p.n t (A / 4)) ≤
        ENNReal.ofReal (C * min 1 ((p.n : ℝ)⁻¹ * (a ^ 2)⁻¹ *
          Real.exp ((1 - a ^ 2) * Real.pi ^ 2 / (4 * a ^ 2)))) := by
      let x : ℝ := (p.n : ℝ)⁻¹ * (a ^ 2)⁻¹ *
          Real.exp ((1 - a ^ 2) * Real.pi ^ 2 / (4 * a ^ 2))
      have hscoreBound :
          ENNReal.ofReal ((eLpNorm R 2 m.P).toReal ^ 2) +
              ENNReal.ofReal (p.Ctheta ^ 2) *
                ENNReal.ofReal ((eLpNorm W 2 m.P).toReal ^ 2) ≤
            ENNReal.ofReal K := by
        calc
          _ ≤ ENNReal.ofReal
                (4 * (p.Cq + 2 * p.Ctheta * p.Cg) ^ 2 + 4 * p.psixi ^ 2) +
              ENNReal.ofReal (p.Ctheta ^ 2) *
                ENNReal.ofReal (8 + 16 * p.Cg ^ 2) := by
            gcongr
            · exact hscore.2.2.2.2.2
            · exact hscore.2.2.2.2.1
          _ = ENNReal.ofReal K := by
            rw [← ENNReal.ofReal_mul (sq_nonneg p.Ctheta),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            dsimp [K]
            rw [hpTheta, hpG, hpQ, hpXi]
      have hlocal : mseRisk m p.n (thetaHatAt p m p.n t (A / 4)) ≤
          ENNReal.ofReal (16 * K * x) := by
        calc
          _ ≤ ENNReal.ofReal (16 / A ^ 2) * (p.n : ENNReal)⁻¹ *
              (ENNReal.ofReal ((eLpNorm R 2 m.P).toReal ^ 2) +
                ENNReal.ofReal (p.Ctheta ^ 2) *
                  ENNReal.ofReal ((eLpNorm W 2 m.P).toReal ^ 2)) := hrisk
          _ ≤ ENNReal.ofReal (16 / A ^ 2) * (p.n : ENNReal)⁻¹ *
              ENNReal.ofReal K := by gcongr
          _ = ENNReal.ofReal (16 * K * x) := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos
              (by exact_mod_cast p.n_pos : (0 : ℝ) < p.n)]
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 / A ^ 2),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            dsimp [x, A]
            let q : ℝ := (1 - a ^ 2) * Real.pi ^ 2 / (8 * a ^ 2)
            have hneg : Real.exp (-(1 - a ^ 2) * Real.pi ^ 2 / (8 * a ^ 2)) =
                (Real.exp q)⁻¹ := by
              rw [show -(1 - a ^ 2) * Real.pi ^ 2 / (8 * a ^ 2) = -q by
                dsimp [q]; ring, Real.exp_neg]
            have htwo : Real.exp ((1 - a ^ 2) * Real.pi ^ 2 / (4 * a ^ 2)) =
                (Real.exp q) ^ 2 := by
              rw [← Real.exp_nat_mul]
              congr 1
              dsimp [q]
              field_simp [ha0.ne']
              ring
            rw [hneg, htwo]
            field_simp [ha0.ne', Real.exp_ne_zero q]
      have hglobal : mseRisk m p.n (thetaHatAt p m p.n t (A / 4)) ≤
          ENNReal.ofReal (4 * p.Ctheta ^ 2) := by
        unfold mseRisk iidLaw
        rw [show thetaHatAt p m p.n t (A / 4) =
            clippedRatioFromScores p.Ctheta m.theta0 p.n (A / 4) W R by
          funext data
          exact thetaHatAt_eq_clippedRatioFromScores p m p.n t (A / 4) data]
        calc
          _ ≤ ∫⁻ _data : Fin p.n → Obs Xspace,
              ENNReal.ofReal (4 * p.Ctheta ^ 2)
              ∂Measure.pi (fun _ : Fin p.n ↦ m.P) := by
            apply lintegral_mono
            intro data
            exact ENNReal.ofReal_le_ofReal
              (clippedRatioFromScores_sq_le_global p.Ctheta m.theta0 A
                p.n W R (∫ o, W o ∂m.P) htheta data)
          _ = _ := by simp
      have hx : 0 ≤ x := by dsimp [x]; positivity
      by_cases hx1 : x ≤ 1
      · rw [min_eq_right hx1]
        exact hlocal.trans (ENNReal.ofReal_le_ofReal (by
          have hKC : 16 * K ≤ C := by dsimp [C]; nlinarith
          exact mul_le_mul_of_nonneg_right hKC hx))
      · rw [min_eq_left (le_of_not_ge hx1)]
        exact hglobal.trans (ENNReal.ofReal_le_ofReal (by
          dsimp [C]
          rw [hpTheta]
          nlinarith))
    refine ⟨?_, ?_, hriskFirst, ?_, ?_⟩
    · simpa only [t, A] using hdenId
    · simpa only [t, A] using hdenLower
    · have heps : p.eps1n p.n ≤ a / Real.pi := by
        have hpos : 0 < Real.pi / (2 * a) := ht
        have hsmall' : p.eps1n p.n * (Real.pi / (2 * a)) ≤ 1 / 2 := by
          simpa [mul_comm] using hsmall
        have := (le_div_iff₀ hpos).2 hsmall'
        field_simp [ha0.ne', Real.pi_ne_zero] at this ⊢
        nlinarith [Real.pi_pos]
      have hroot : (2 * a ^ 4) ^ (1 / 4 : ℝ) =
          2 ^ (1 / 4 : ℝ) * a := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (by positivity : 0 ≤ a ^ 4)]
        congr 1
        convert Real.pow_rpow_inv_natCast ha0.le (by norm_num : (4 : ℕ) ≠ 0) using 1
        norm_num
      rw [hroot]
      have htwoRoot : 0 < (2 : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_pos_of_pos (by norm_num) _
      field_simp [htwoRoot.ne', Real.pi_ne_zero]
      field_simp [Real.pi_ne_zero] at heps
      exact heps
    · let y : ℝ := (p.n : ℝ)⁻¹ * (2 * a ^ 4) ^ (-1 / 2 : ℝ) *
          Real.exp (Real.pi ^ 2 * Real.sqrt 2 / 4 *
            (2 * a ^ 4) ^ (-1 / 2 : ℝ))
      have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := by norm_num
      have hdeltaHalf : (2 * a ^ 4) ^ (-1 / 2 : ℝ) =
          (Real.sqrt 2 * a ^ 2)⁻¹ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
          Real.rpow_neg (by positivity) (1 / 2 : ℝ)]
        congr 1
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (by positivity : 0 ≤ a ^ 4)]
        have htwoHalf : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by
          exact (Real.sqrt_eq_rpow 2).symm
        have haHalf : (a ^ 4) ^ (1 / 2 : ℝ) = a ^ 2 := by
          rw [show a ^ 4 = (a ^ 2) ^ 2 by ring]
          convert Real.pow_rpow_inv_natCast (sq_nonneg a)
            (by norm_num : (2 : ℕ) ≠ 0) using 1
          norm_num
        rw [htwoHalf, haHalf]
      have hxy : (p.n : ℝ)⁻¹ * (a ^ 2)⁻¹ *
          Real.exp ((1 - a ^ 2) * Real.pi ^ 2 / (4 * a ^ 2)) ≤ y := by
        dsimp [y]
        rw [hdeltaHalf]
        have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
        have haSq : 0 < a ^ 2 := sq_pos_of_pos ha0
        have hpi : 4 ≤ Real.pi ^ 2 := by
          nlinarith [Real.two_le_pi, Real.pi_pos]
        have hexp : Real.sqrt 2 ≤ Real.exp (Real.pi ^ 2 / 4) := by
          have hsqrtLe : Real.sqrt 2 ≤ 2 := by nlinarith [hsqrt2, Real.sqrt_nonneg 2]
          exact hsqrtLe.trans (by
            have := Real.add_one_le_exp (Real.pi ^ 2 / 4)
            nlinarith)
        have hn0 : 0 ≤ (p.n : ℝ)⁻¹ := by positivity
        have hfactor : (a ^ 2)⁻¹ *
              Real.exp ((1 - a ^ 2) * Real.pi ^ 2 / (4 * a ^ 2)) ≤
            (Real.sqrt 2 * a ^ 2)⁻¹ *
              Real.exp (Real.pi ^ 2 * Real.sqrt 2 / 4 *
                (Real.sqrt 2 * a ^ 2)⁻¹) := by
          have hexpEq : Real.exp (Real.pi ^ 2 * Real.sqrt 2 / 4 *
                (Real.sqrt 2 * a ^ 2)⁻¹) =
              Real.exp ((1 - a ^ 2) * Real.pi ^ 2 / (4 * a ^ 2)) *
                Real.exp (Real.pi ^ 2 / 4) := by
            rw [← Real.exp_add]
            congr 1
            field_simp [hsqrtPos.ne', ha0.ne']
            nlinarith [hsqrt2]
          rw [hexpEq]
          have he0 : 0 < Real.exp ((1 - a ^ 2) * Real.pi ^ 2 / (4 * a ^ 2)) :=
            Real.exp_pos _
          field_simp [hsqrtPos.ne', ha0.ne']
          nlinarith
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfactor hn0
      exact hriskFirst.trans (ENNReal.ofReal_le_ofReal (by
        have hC0 := hC.le
        exact mul_le_mul_of_nonneg_left (min_le_min le_rfl hxy) hC0))

end CausalSmith.Stat.SaPlmCumulantConverse
