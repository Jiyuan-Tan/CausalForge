import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.GaussianRademacherBenchmark

/-!
# Symmetric Gaussian-mixture reduction
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- Equal mixture of `N(-1,1)` and `N(1,1)`. -/
def symmetricGaussianMixture : Measure ℝ :=
  (ENNReal.ofReal (1 / 2 : ℝ)) • gaussianReal (-1) (1 : NNReal) +
    (ENNReal.ofReal (1 / 2 : ℝ)) • gaussianReal 1 (1 : NNReal)

/-- [The symmetric Gaussian mixture — equal weight on a unit-variance normal centred at minus
one and on a unit-variance normal centred at plus one — is a probability measure, its total
mass being one](goal). -/
instance : IsProbabilityMeasure symmetricGaussianMixture where
  measure_univ := by
    simpa [symmetricGaussianMixture] using ENNReal.inv_two_add_inv_two

private lemma complexMGF_symmetricGaussianMixture (z : ℂ) :
    complexMGF id symmetricGaussianMixture z =
      Complex.exp (z ^ 2 / 2) * Complex.cosh z := by
  unfold complexMGF symmetricGaussianMixture
  have hint (u : ℝ) : Integrable
      (fun x : ℝ ↦ Complex.exp (z * (x : ℂ)))
      (gaussianReal u (1 : NNReal)) := by
    apply (integrable_exp_mul_gaussianReal (v := (1 : NNReal)) z.re).mono'
      (by fun_prop)
    filter_upwards [] with x
    simp [Complex.norm_exp, Complex.mul_re]
  have hneg := (hint (-1)).smul_measure
    (by simp : ENNReal.ofReal (1 / 2 : ℝ) ≠ ⊤)
  have hpos := (hint 1).smul_measure
    (by simp : ENNReal.ofReal (1 / 2 : ℝ) ≠ ⊤)
  simp only [id_eq]
  rw [integral_add_measure hneg hpos, integral_smul_measure, integral_smul_measure]
  change ((ENNReal.ofReal (1 / 2 : ℝ)).toReal : ℂ) *
      complexMGF id (gaussianReal (-1) (1 : NNReal)) z +
    ((ENNReal.ofReal (1 / 2 : ℝ)).toReal : ℂ) *
      complexMGF id (gaussianReal 1 (1 : NNReal)) z = _
  rw [complexMGF_id_gaussianReal, complexMGF_id_gaussianReal]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    one_mul, neg_mul]
  rw [Complex.cosh]
  norm_num
  change (1 / 2 : ℂ) * Complex.exp (-z + z ^ 2 / 2) +
      (1 / 2 : ℂ) * Complex.exp (z + z ^ 2 / 2) =
    Complex.exp (z ^ 2 / 2) * ((Complex.exp z + Complex.exp (-z)) / 2)
  rw [show -z + z ^ 2 / 2 = z ^ 2 / 2 + -z by ring,
    show z + z ^ 2 / 2 = z ^ 2 / 2 + z by ring,
    Complex.exp_add, Complex.exp_add]
  ring

private lemma treatmentMGF_eq_symmetricGaussianMixture (p : Parameters)
    (m : Model (Xspace := Xspace) p)
    (hlaw : m.P.map (eta p m) = symmetricGaussianMixture) :
    treatmentMGF p m = fun z ↦ Complex.exp (z ^ 2 / 2) * Complex.cosh z := by
  funext z
  unfold treatmentMGF
  rw [← complexMGF_id_map (by
    unfold eta treatment covariate
    exact (measurable_snd.fst.sub
      (m.g0_measurable.comp measurable_fst)).aemeasurable), hlaw]
  exact complexMGF_symmetricGaussianMixture z

private lemma symmetricGaussianMixture_integrable_exp (s : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (s * x)) symmetricGaussianMixture := by
  unfold symmetricGaussianMixture
  apply Integrable.add_measure
  · exact (integrable_exp_mul_gaussianReal s).smul_measure (by simp)
  · exact (integrable_exp_mul_gaussianReal s).smul_measure (by simp)

private lemma eta_integrable_exp_symmetricGaussianMixture (p : Parameters)
    (m : Model (Xspace := Xspace) p)
    (hlaw : m.P.map (eta p m) = symmetricGaussianMixture) (s : ℝ) :
    Integrable (fun o ↦ Real.exp (s * eta p m o)) m.P := by
  have heta : AEMeasurable (eta p m) m.P := by
    unfold eta treatment covariate
    exact (measurable_snd.fst.sub
      (m.g0_measurable.comp measurable_fst)).aemeasurable
  have hLaw : Integrable (fun x : ℝ ↦ Real.exp (s * x))
      (m.P.map (eta p m)) := by
    rw [hlaw]
    exact symmetricGaussianMixture_integrable_exp s
  exact hLaw.comp_aemeasurable heta

private lemma eta_cexp_moment_symmetricGaussianMixture (p : Parameters)
    (m : Model (Xspace := Xspace) p)
    (hlaw : m.P.map (eta p m) = symmetricGaussianMixture) :
    ∫ o, (eta p m o : ℂ) * Complex.exp
        ((Complex.I * (Real.pi / 2 : ℝ)) * (eta p m o : ℂ)) ∂m.P =
      Complex.I * Real.exp (-Real.pi ^ 2 / 8) := by
  let z0 : ℂ := Complex.I * (Real.pi / 2 : ℝ)
  have hset : integrableExpSet (eta p m) m.P = Set.univ := by
    ext s
    simp [integrableExpSet,
      eta_integrable_exp_symmetricGaussianMixture p m hlaw s]
  have hz : z0.re ∈ interior (integrableExpSet (eta p m) m.P) := by
    simp [hset]
  have hmgf := treatmentMGF_eq_symmetricGaussianMixture p m hlaw
  unfold treatmentMGF at hmgf
  calc
    _ = iteratedDeriv 1 (complexMGF (eta p m) m.P) z0 := by
      rw [iteratedDeriv_complexMGF hz 1]
      apply integral_congr_ae
      filter_upwards [] with o
      simp [z0]
    _ = deriv (complexMGF (eta p m) m.P) z0 := by
      simp [iteratedDeriv_succ]
    _ = deriv (fun z : ℂ ↦ Complex.exp (z ^ 2 / 2) * Complex.cosh z) z0 := by
      exact congrArg (fun F : ℂ → ℂ ↦ deriv F z0) hmgf
    _ = Complex.I * Real.exp (-Real.pi ^ 2 / 8) := by
      rw [show deriv (fun z : ℂ ↦ Complex.exp (z ^ 2 / 2) * Complex.cosh z) z0 =
          Complex.exp (z0 ^ 2 / 2) * z0 * Complex.cosh z0 +
            Complex.exp (z0 ^ 2 / 2) * Complex.sinh z0 by
        convert ((Complex.hasDerivAt_exp (z0 ^ 2 / 2)).comp z0 (by
          convert ((hasDerivAt_id z0).pow 2).div_const 2 using 1 <;> ring)).fun_mul
            (Complex.hasDerivAt_cosh z0) |>.deriv using 1 <;>
          simp only [id_eq, Function.comp_apply, Pi.pow_apply] <;> ring]
      have hcosh : Complex.cosh z0 = 0 := by
        dsimp [z0]
        rw [show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
          ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring,
          Complex.cosh_mul_I]
        simp
      have hsinh : Complex.sinh z0 = Complex.I := by
        dsimp [z0]
        rw [show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
          ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring,
          Complex.sinh_mul_I]
        simp
      rw [hcosh, hsinh]
      simp only [mul_zero, add_zero]
      rw [show z0 ^ 2 / 2 = ((-Real.pi ^ 2 / 8 : ℝ) : ℂ) by
        dsimp [z0]
        push_cast
        rw [mul_pow, Complex.I_sq]
        ring, Complex.ofReal_exp]
      push_cast
      ring


/-- The stipulated symmetric mixture has a uniform second-moment envelope. -/
-- @node: symmetricGaussianMixture_second_lintegral_le
lemma symmetricGaussianMixture_second_lintegral_le :
    ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂symmetricGaussianMixture ≤ 4 := by
  have hsecond (u : ℝ) :
      ∫ x : ℝ, x ^ 2 ∂gaussianReal u (1 : NNReal) = 1 + u ^ 2 := by
    have hsq : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal u (1 : NNReal)) := by
      simpa only [id_eq, Real.norm_eq_abs, sq_abs] using
        (memLp_id_gaussianReal (μ := u) (v := (1 : NNReal)) 2).integrable_sq
    have hcenter : Integrable (fun x : ℝ ↦ (x - u) ^ 2)
        (gaussianReal u (1 : NNReal)) := by
      exact ((memLp_id_gaussianReal (μ := u) (v := (1 : NNReal)) 2).sub
        (memLp_const u)).integrable_sq
    have hid : Integrable (fun x : ℝ ↦ x) (gaussianReal u (1 : NNReal)) := by
      exact (memLp_id_gaussianReal (μ := u) (v := (1 : NNReal)) 1).integrable (by norm_num)
    have hv := variance_fun_id_gaussianReal (μ := u) (v := (1 : NNReal))
    rw [variance_eq_integral measurable_id'.aemeasurable] at hv
    simp only [integral_id_gaussianReal] at hv
    calc
      ∫ x : ℝ, x ^ 2 ∂gaussianReal u (1 : NNReal) =
          ∫ x : ℝ, ((x - u) ^ 2 + 2 * u * x - u ^ 2)
            ∂gaussianReal u (1 : NNReal) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = 1 + u ^ 2 := by
        calc
          _ = (∫ x : ℝ, (x - u) ^ 2 + 2 * u * x
                ∂gaussianReal u (1 : NNReal)) -
              ∫ _x : ℝ, u ^ 2 ∂gaussianReal u (1 : NNReal) :=
            integral_sub (hcenter.add (hid.const_mul _)) (integrable_const _)
          _ = ((∫ x : ℝ, (x - u) ^ 2 ∂gaussianReal u (1 : NNReal)) +
                ∫ x : ℝ, 2 * u * x ∂gaussianReal u (1 : NNReal)) -
              ∫ _x : ℝ, u ^ 2 ∂gaussianReal u (1 : NNReal) := by
            rw [integral_add hcenter (hid.const_mul _)]
          _ = 1 + u ^ 2 := by
            rw [integral_const_mul, integral_id_gaussianReal]
            simp [hv]
            ring
  have hlin (u : ℝ) :
      ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂gaussianReal u (1 : NNReal) =
        ENNReal.ofReal (1 + u ^ 2) := by
    have hsq : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal u (1 : NNReal)) := by
      simpa only [id_eq, Real.norm_eq_abs, sq_abs] using
        (memLp_id_gaussianReal (μ := u) (v := (1 : NNReal)) 2).integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hsq
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg x), hsecond]
  unfold symmetricGaussianMixture
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    hlin, hlin]
  simp only [smul_eq_mul]
  norm_num only [neg_sq, one_pow]
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hhalf]
  have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
  have hfirst : ENNReal.ofReal (1 + 1 : ℝ) ≤ (2 : ENNReal) := by
    rw [htwo]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hsecond' : ENNReal.ofReal (2 : ℝ) ≤ (2 : ENNReal) := by rw [htwo]
  calc
    _ ≤ (1 : ENNReal) * 2 + (1 : ENNReal) * 2 := by
      gcongr
      all_goals first
        | exact hfirst
        | exact hsecond'
        | exact (by simpa [div_eq_mul_inv] using
            (ENNReal.inv_le_one (a := (2 : ENNReal))).2 (by norm_num))
    _ ≤ 4 := by norm_num


/-- [Once the range bound for the treatment coefficient, the two regression bounds, and the
outcome-noise scale are fixed, one constant works for every sample size: for any model in which
the treatment noise follows the symmetric two-component Gaussian mixture, the data are drawn
independently, the usual regularity conditions of the non-Gaussian class hold, and the
treatment code is accurate in mean to within one over pi, the fourth cumulant of the treatment
noise is exactly minus two, the treatment moment generating function vanishes at the imaginary
point i times pi over two, the population sine score equals `exp(-π²/8)` times the average
cosine of the treatment-code error, that score is bounded below by half of `exp(-π²/8)`, and
the resulting clipped sine estimator has mean squared error at most the constant divided by the
sample size](goal).

The vanishing moment generating function is what makes the mixture a benchmark: it kills the
first-order sine remainder, so the sine score is a valid denominator and the parametric rate
follows from the fixed lower bound on it. -/
-- @node: prop:symmetric-mixture-reduction
theorem symmetric_mixture_reduction (Ctheta Cg Cq psixi : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : Parameters), p.Ctheta = Ctheta → p.Cg = Cg →
        p.Cq = Cq → p.psixi = psixi →
      ∀ (m : Model (Xspace := Xspace) p),
        m.P.map (eta p m) = symmetricGaussianMixture →
        IidSampling p.n m.P (iidLaw m p.n) →
        IndependentTreatmentNoise p m → OutcomeMeanIndependence p m →
        ThetaRange p m → GRange p m → QRange p m →
        XiSubGaussian p m → TreatmentCodeRadiusL1At p m p.n →
        p.eps1n p.n ≤ 1 / Real.pi →
        fourthCumulant p m = -2 ∧
        treatmentMGF p m (Complex.I * (Real.pi / 2 : ℝ)) = 0 ∧
        ∫ o, learnedResidual p m p.n o *
            Real.sin (Real.pi * learnedResidual p m p.n o / 2) ∂m.P =
          Real.exp (-Real.pi ^ 2 / 8) *
            ∫ o, Real.cos (Real.pi * treatmentError p m p.n o / 2) ∂m.P ∧
        Real.exp (-Real.pi ^ 2 / 8) / 2 ≤
          ∫ o, learnedResidual p m p.n o *
            Real.sin (Real.pi * learnedResidual p m p.n o / 2) ∂m.P ∧
        mseRisk m p.n (thetaHatSin p m) ≤ ENNReal.ofReal (C / p.n) := by
  let A : ℝ := Real.exp (-Real.pi ^ 2 / 8)
  let K : ℝ := 4 * (Cq + 2 * Ctheta * Cg) ^ 2 + 4 * psixi ^ 2 +
    Ctheta ^ 2 * (8 + 16 * Cg ^ 2)
  let C : ℝ := 1 + 16 / A ^ 2 * K
  have hA : 0 < A := Real.exp_pos _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro p hpTheta hpG hpQ hpXi m hlaw _hiid hind hout htheta hg hq hxi hL1 hsmall
  let t : ℝ := Real.pi / 2
  let W : Obs Xspace → ℝ := fun o ↦ learnedResidual p m p.n o *
    Real.sin (t * learnedResidual p m p.n o)
  let R : Obs Xspace → ℝ := fun o ↦
    (outcome o - m.theta0 * learnedResidual p m p.n o) *
      Real.sin (t * learnedResidual p m p.n o)
  have ht : 0 < t := div_pos Real.pi_pos zero_lt_two
  have hmgf := treatmentMGF_eq_symmetricGaussianMixture p m hlaw
  have hzero : treatmentMGF p m (Complex.I * t) = 0 := by
    rw [hmgf]
    dsimp [t]
    rw [show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring,
      Complex.cosh_mul_I]
    simp
  have hkappa : fourthCumulant p m = -2 := by
    unfold treatmentMGF at hmgf
    rw [fourthCumulant]
    simp_rw [congrFun hmgf]
    simpa using gaussianRademacher_logMGF_fourth 1 1
  have hetaInt : Integrable (eta p m) m.P := by
    have hp := eta_integrable_exp_symmetricGaussianMixture p m hlaw 1
    have hn := eta_integrable_exp_symmetricGaussianMixture p m hlaw (-1)
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
    simpa only [t, A] using eta_cexp_moment_symmetricGaussianMixture p m hlaw
  have hdenId := learnedResidual_sine_denominator_identity
    p m p.n t A hzero hmoment hetaInt hind hg
  have htSmall : t * p.eps1n p.n ≤ 1 / 2 := by
    dsimp [t]
    calc
      Real.pi / 2 * p.eps1n p.n ≤ Real.pi / 2 * (1 / Real.pi) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = 1 / 2 := by field_simp [Real.pi_ne_zero]
  have hdenLower := learnedResidual_sine_denominator_lower
    p m p.n t A ht hA hdenId hL1 htSmall
  have hremMean : ∫ o, R o ∂m.P = 0 := by
    simpa only [R] using sine_remainder_centered_of_mgf_zero
      p m p.n t hzero hind hout htheta hg hq
  have hetaMeas : Measurable (eta p m) := by
    unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  have hetaSq : ∫⁻ o, ENNReal.ofReal ((eta p m o) ^ 2) ∂m.P ≤ 4 := by
    calc
      _ = ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂(m.P.map (eta p m)) := by
        rw [lintegral_map (by fun_prop) hetaMeas]
      _ = ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂symmetricGaussianMixture := by
        rw [hlaw]
      _ ≤ 4 := symmetricGaussianMixture_second_lintegral_le
  have hscore := sine_score_memLp_of_eta_second_lintegral_le
    p m p.n t hetaSq htheta hg hq hxi
  have hriskRaw := clippedRatioFromScores_lintegral_le m.P
    p.Ctheta m.theta0 A p.n W R (∫ o, W o ∂m.P)
    p.n_pos htheta hA (by simpa only [W] using hdenLower)
    hscore.1 hscore.2.1 hscore.2.2.1 hscore.2.2.2.1 rfl hremMean
  have hrisk : mseRisk m p.n (thetaHatSin p m) ≤
      ENNReal.ofReal (16 / A ^ 2) * (p.n : ENNReal)⁻¹ *
        (ENNReal.ofReal ((eLpNorm R 2 m.P).toReal ^ 2) +
          ENNReal.ofReal (p.Ctheta ^ 2) *
            ENNReal.ofReal ((eLpNorm W 2 m.P).toReal ^ 2)) := by
    unfold mseRisk iidLaw thetaHatSin
    rw [show thetaHatAt p m p.n (Real.pi / 2)
        (Real.exp (-Real.pi ^ 2 / 8) / 4) =
        clippedRatioFromScores p.Ctheta m.theta0 p.n (A / 4) W R by
      funext data
      simpa only [W, R, t, A] using
        thetaHatAt_eq_clippedRatioFromScores p m p.n t (A / 4) data]
    exact hriskRaw
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
  have hnR : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hriskFinal : mseRisk m p.n (thetaHatSin p m) ≤
      ENNReal.ofReal (C / p.n) := by
    calc
      _ ≤ ENNReal.ofReal (16 / A ^ 2) * (p.n : ENNReal)⁻¹ *
          (ENNReal.ofReal ((eLpNorm R 2 m.P).toReal ^ 2) +
            ENNReal.ofReal (p.Ctheta ^ 2) *
              ENNReal.ofReal ((eLpNorm W 2 m.P).toReal ^ 2)) := hrisk
      _ ≤ ENNReal.ofReal (16 / A ^ 2) * (p.n : ENNReal)⁻¹ *
          ENNReal.ofReal K := by gcongr
      _ = ENNReal.ofReal ((16 / A ^ 2 * K) / p.n) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hnR,
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 / A ^ 2),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (C / p.n) := ENNReal.ofReal_le_ofReal (by
        have hn0 : (0 : ℝ) ≤ p.n := hnR.le
        apply div_le_div_of_nonneg_right _ hn0
        dsimp [C]
        linarith)
  refine ⟨hkappa, hzero, ?_, ?_, hriskFinal⟩
  · simpa only [t, A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdenId
  · simpa only [t, A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdenLower

end CausalSmith.Stat.SaPlmCumulantConverse
