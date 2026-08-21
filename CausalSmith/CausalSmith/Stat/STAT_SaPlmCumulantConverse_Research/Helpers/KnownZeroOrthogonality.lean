import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.KnownZeroConditional

/-!
# Moment and outcome assembly for known-zero instruments
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- For a law [in the paper's non-Gaussian class](hyp:hclass), at a point where
the [moment generating function of the treatment noise vanishes](hyp:hz) with
[multiplicity exactly the given order](hyp:hmult), that order being [at least
one](hyp:hell), the [expected product of the observable learned residual with the
zero instrument evaluated at that residual equals the derivative of that order of
the treatment-noise transform at the point, times the transform of the
treatment-code error at the same point](goal).

The instrument is the residual raised to one less than the multiplicity, times
the exponential of the point times the residual, so the expectation is the
matching derivative of the learned-residual transform, which factors into the
treatment-noise and treatment-code-error transforms. -/
lemma zeroInstrument_learnedResidual_integral_eq (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n ell : ℕ) (hclass : NonGaussianClass p n m) (z0 : ℂ) (hell : 1 ≤ ell)
    (hz : treatmentMGF p m z0 = 0)
    (hmult : analyticOrderNatAt (treatmentMGF p m) z0 = ell) :
    ∫ o, (learnedResidual p m n o : ℂ) *
        zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
          (learnedResidual p m n o) ∂m.P =
      iteratedDeriv ell (treatmentMGF p m) z0 * nuisanceMGF p m n z0 := by
  have hZset : integrableExpSet (learnedResidual p m n) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, learnedResidual_integrable_exp p m n hclass t]
  have hzZ : z0.re ∈ interior (integrableExpSet (learnedResidual p m n) m.P) := by
    simp [hZset]
  have hDset : integrableExpSet (treatmentError p m n) m.P = Set.univ := by
    have hDmeas : Measurable (treatmentError p m n) := by
      unfold treatmentError covariate barG
      exact (m.g0_measurable.sub
        (((m.gcode_measurable n).max measurable_const).min measurable_const)).comp measurable_fst
    have hbar (x : Xspace) : |barG p m n x| ≤ p.Cg := by
      have hCg : 0 < p.Cg := p.constants_pos.2.1
      rw [abs_le]
      dsimp [barG]
      constructor <;> simp_all <;> linarith
    have hD : ∀ᵐ o ∂m.P, treatmentError p m n o ∈ Set.Icc (-2 * p.Cg) (2 * p.Cg) := by
      have hg := MeasureTheory.ae_of_ae_map measurable_fst.aemeasurable hclass.gRange
      filter_upwards [hg] with o ho
      rw [Set.mem_Icc]
      have hb : |treatmentError p m n o| ≤ 2 * p.Cg := by
        dsimp [treatmentError]
        calc
          |m.g0 (covariate o) - barG p m n (covariate o)| ≤
              |m.g0 (covariate o)| + |barG p m n (covariate o)| := abs_sub _ _
          _ ≤ p.Cg + p.Cg := add_le_add ho (hbar _)
          _ = 2 * p.Cg := by ring
      rw [abs_le] at hb
      simpa only [neg_mul] using hb
    ext t
    simp [integrableExpSet, integrable_exp_mul_of_mem_Icc hDmeas.aemeasurable hD]
  have hMset : integrableExpSet (eta p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, eta_integrable_exp p m n hclass t]
  have hMan : AnalyticAt ℂ (treatmentMGF p m) z0 :=
    analyticAt_complexMGF (by simp [hMset])
  have hHan : AnalyticAt ℂ (nuisanceMGF p m n) z0 :=
    analyticAt_complexMGF (by simp [hDset])
  have hzero := treatmentMGF_iteratedDeriv_eq_zero_of_lt_order
    p m n ell hclass z0 hell hmult
  rw [show (∫ o, (learnedResidual p m n o : ℂ) *
        zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
          (learnedResidual p m n o) ∂m.P) =
      iteratedDeriv ell (residualMGF p m n) z0 by
    unfold residualMGF
    rw [iteratedDeriv_complexMGF hzZ]
    apply integral_congr_ae
    filter_upwards [] with o
    simp only [zeroInstrument]
    rw [← mul_assoc, ← pow_succ']
    congr 2
    omega]
  rw [show residualMGF p m n = treatmentMGF p m * nuisanceMGF p m n by
    funext z
    exact residualMGF_eq_treatmentMGF_mul_nuisanceMGF p m n hclass z]
  rw [iteratedDeriv_mul hMan.contDiffAt hHan.contDiffAt]
  rw [Finset.sum_eq_single ell]
  · simp
  · intro j hj hjne
    have hjlt : j < ell := by
      have := Finset.mem_range.mp hj
      omega
    simp [hzero j hjlt]
  · simp

/-- For a law [in the paper's non-Gaussian class](hyp:hclass), at a point where
the [moment generating function of the treatment noise vanishes](hyp:hz) with
[multiplicity exactly the given order](hyp:hmult), that order being [at least
one](hyp:hell), the [product of the outcome noise with the zero instrument
evaluated at the observable learned residual is integrable and has expectation
zero](goal).

The outcome noise has conditional mean zero given the covariate–treatment pair,
and the learned residual is a function of that pair, so the two are orthogonal. -/
lemma outcomeNoise_zeroInstrument_integrable_and_integral_eq_zero (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n ell : ℕ) (hclass : NonGaussianClass p n m) (z0 : ℂ) (hell : 1 ≤ ell)
    (hz : treatmentMGF p m z0 = 0)
    (hmult : analyticOrderNatAt (treatmentMGF p m) z0 = ell) :
    Integrable (fun o ↦ (xi p m o : ℂ) *
      zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
        (learnedResidual p m n o)) m.P ∧
      ∫ o, (xi p m o : ℂ) *
        zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
          (learnedResidual p m n o) ∂m.P = 0 := by
  let J : Obs Xspace → ℂ := fun o ↦
    zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
      (learnedResidual p m n o)
  have hxiSet : integrableExpSet (xi p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, xi_integrable_exp p m n hclass t]
  have hxi2 : MemLp (xi p m) 2 m.P := by
    apply memLp_of_mem_interior_integrableExpSet
    simp [hxiSet]
  have hZset : integrableExpSet (learnedResidual p m n) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, learnedResidual_integrable_exp p m n hclass t]
  have hZmeas : Measurable (learnedResidual p m n) := by
    unfold learnedResidual treatment barG covariate
    exact measurable_snd.fst.sub
      (((m.gcode_measurable n).comp measurable_fst).max measurable_const |>.min
        measurable_const)
  have hJ2 : MemLp J 2 m.P := by
    rw [memLp_two_iff_integrable_sq_norm (by
      dsimp [J, zeroInstrument]
      exact (((Complex.measurable_ofReal.comp hZmeas).pow_const _).mul
        (Complex.continuous_exp.measurable.comp
          (measurable_const.mul (Complex.measurable_ofReal.comp hZmeas)))).aestronglyMeasurable)]
    have hz2 : 2 * z0.re ∈
        interior (integrableExpSet (learnedResidual p m n) m.P) := by
      simp [hZset]
    have hK := integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
      hz2 (2 * (ell - 1))
    apply hK.congr
    filter_upwards [] with o
    dsimp [J, zeroInstrument]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp]
    rw [sq]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      |learnedResidual p m n o| ^ (2 * (ell - 1)) *
          Real.exp (2 * z0.re * learnedResidual p m n o) =
        (|learnedResidual p m n o| ^ (ell - 1) *
          |learnedResidual p m n o| ^ (ell - 1)) *
        (Real.exp (z0.re * learnedResidual p m n o) *
          Real.exp (z0.re * learnedResidual p m n o)) := by
            rw [← pow_add, ← Real.exp_add]
            congr 2 <;> ring
      _ = _ := by ring
  have hprod : Integrable (fun o ↦ (xi p m o : ℂ) * J o) m.P :=
    hxi2.ofReal.integrable_mul hJ2
  refine ⟨hprod, ?_⟩
  have hZxT : Measurable[xTSigma (Xspace := Xspace)] (learnedResidual p m n) := by
    change Measurable[MeasurableSpace.comap
      (fun o : Obs Xspace ↦ (covariate o, treatment o)) inferInstance]
      (learnedResidual p m n)
    have h : Measurable (fun xt : Xspace × ℝ ↦ xt.2 - barG p m n xt.1) :=
      measurable_snd.sub
        ((((m.gcode_measurable n).comp measurable_fst).max measurable_const).min
          measurable_const)
    exact h.comp (comap_measurable (fun o : Obs Xspace ↦ (covariate o, treatment o)))
  have hJre : StronglyMeasurable[xTSigma (Xspace := Xspace)] (fun o ↦ (J o).re) := by
    apply Measurable.stronglyMeasurable
    dsimp [J, zeroInstrument]
    fun_prop
  have hJim : StronglyMeasurable[xTSigma (Xspace := Xspace)] (fun o ↦ (J o).im) := by
    apply Measurable.stronglyMeasurable
    dsimp [J, zeroInstrument]
    fun_prop
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
  · change (∫ o, (xi p m o : ℂ) * J o ∂m.P).re = 0
    calc
      _ = ∫ o, ((xi p m o : ℂ) * J o).re ∂m.P := by
        simpa only [RCLike.re_eq_complex_re] using (integral_re hprod).symm
      _ = ∫ o, xi p m o * (J o).re ∂m.P := by simp
      _ = 0 := hzero (fun o ↦ (J o).re) hJre (by simpa using hprod.re)
  · change (∫ o, (xi p m o : ℂ) * J o ∂m.P).im = 0
    calc
      _ = ∫ o, ((xi p m o : ℂ) * J o).im ∂m.P := by
        simpa only [RCLike.im_eq_complex_im] using (integral_im hprod).symm
      _ = ∫ o, xi p m o * (J o).im ∂m.P := by simp
      _ = 0 := hzero (fun o ↦ (J o).im) hJim (by simpa using hprod.im)
/-- For a law [in the paper's non-Gaussian class](hyp:hclass), at a point where
the [moment generating function of the treatment noise vanishes](hyp:hz) with
[multiplicity exactly the given order](hyp:hmult), that order being [at least
one](hyp:hell), the [product of the outcome-side contamination, a function of the
covariate alone, with the zero instrument evaluated at the observable learned
residual is integrable and has expectation zero](goal).

At such a zero the instrument has conditional mean zero given the covariate, so
multiplying it by any covariate-measurable weight leaves the mean at zero. -/
lemma contamination_zeroInstrument_integrable_and_integral_eq_zero (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n ell : ℕ) (hclass : NonGaussianClass p n m) (z0 : ℂ) (hell : 1 ≤ ell)
    (hz : treatmentMGF p m z0 = 0)
    (hmult : analyticOrderNatAt (treatmentMGF p m) z0 = ell) :
    Integrable (fun o ↦ (outcomeContamination p m n (covariate o) : ℂ) *
      zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
        (learnedResidual p m n o)) m.P ∧
      ∫ o, (outcomeContamination p m n (covariate o) : ℂ) *
        zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
          (learnedResidual p m n o) ∂m.P = 0 := by
  let J : Obs Xspace → ℂ := fun o ↦
    zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
      (learnedResidual p m n o)
  let b : Obs Xspace → ℂ := fun o ↦
    (outcomeContamination p m n (covariate o) : ℂ)
  have hZset : integrableExpSet (learnedResidual p m n) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, learnedResidual_integrable_exp p m n hclass t]
  have hzZ : z0.re ∈ interior (integrableExpSet (learnedResidual p m n) m.P) := by
    simp [hZset]
  have hJint : Integrable J m.P := by
    simpa [J, zeroInstrument] using
      integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hzZ (ell - 1)
  have hDmeas : Measurable (fun x : Xspace ↦ m.g0 x - barG p m n x) :=
    m.g0_measurable.sub (((m.gcode_measurable n).max measurable_const).min measurable_const)
  have hbX : Measurable (fun x : Xspace ↦ (outcomeContamination p m n x : ℂ)) := by
    exact Complex.measurable_ofReal.comp
      (m.q0_measurable.sub (measurable_const.mul hDmeas))
  have hb : Measurable b := hbX.comp measurable_fst
  have hbar (x : Xspace) : |barG p m n x| ≤ p.Cg := by
    have hCg : 0 < p.Cg := p.constants_pos.2.1
    rw [abs_le]
    dsimp [barG]
    constructor <;> simp_all <;> linarith
  have hbBound : ∀ᵐ o ∂m.P,
      ‖b o‖ ≤ p.Cq + p.Ctheta * (2 * p.Cg) := by
    have hcov : Measurable (covariate (Xspace := Xspace)) := measurable_fst
    have hq := MeasureTheory.ae_of_ae_map hcov.aemeasurable hclass.qRange
    have hg := MeasureTheory.ae_of_ae_map hcov.aemeasurable hclass.gRange
    filter_upwards [hq, hg] with o hqo hgo
    rw [show ‖b o‖ = |m.q0 (covariate o) - m.theta0 *
        (m.g0 (covariate o) - barG p m n (covariate o))| by
      dsimp [b, outcomeContamination]
      rw [Complex.norm_real, Real.norm_eq_abs]]
    calc
      _ ≤ |m.q0 (covariate o)| + |m.theta0| *
          |m.g0 (covariate o) - barG p m n (covariate o)| := by
            simpa [abs_mul] using abs_sub (m.q0 (covariate o))
              (m.theta0 * (m.g0 (covariate o) - barG p m n (covariate o)))
      _ ≤ p.Cq + p.Ctheta * (2 * p.Cg) := by
        apply add_le_add hqo
        have hmul := mul_le_mul hclass.thetaRange
          ((abs_sub _ _).trans (add_le_add hgo (hbar (covariate o))))
          (abs_nonneg _) p.constants_pos.1.le
        convert hmul using 1 <;> ring
  have hbJ : Integrable (fun o ↦ b o * J o) m.P :=
    hJint.bdd_mul hb.aestronglyMeasurable hbBound
  refine ⟨by simpa [b, J] using hbJ, ?_⟩
  have hmle : MeasurableSpace.comap covariate inferInstance ≤
      (inferInstance : MeasurableSpace (Obs Xspace)) :=
    Measurable.comap_le measurable_fst
  let br : Obs Xspace → ℝ := fun o ↦ outcomeContamination p m n (covariate o)
  have hbrsub : StronglyMeasurable[MeasurableSpace.comap covariate inferInstance] br := by
    apply Measurable.stronglyMeasurable
    exact (m.q0_measurable.sub (measurable_const.mul hDmeas)).comp
      (comap_measurable covariate)
  have hcondJ := zeroInstrument_condExp_learnedResidual_eq_zero p m n ell hclass z0 hell hz hmult
  have hcondRe : (@MeasureTheory.condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P
      (fun o ↦ (J o).re)) =ᵐ[m.P] 0 := by
    have hcomm := Complex.reCLM.comp_condExp_comm
      (m := MeasurableSpace.comap covariate inferInstance) hJint
    filter_upwards [hcondJ, hcomm] with o hJo hco
    change Complex.reCLM (@MeasureTheory.condExp (Obs Xspace) ℂ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P J o) =
        (@MeasureTheory.condExp (Obs Xspace) ℝ
          (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P
          (fun o ↦ (J o).re)) o at hco
    rw [hJo] at hco
    exact hco.symm
  have hcondIm : (@MeasureTheory.condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P
      (fun o ↦ (J o).im)) =ᵐ[m.P] 0 := by
    have hcomm := Complex.imCLM.comp_condExp_comm
      (m := MeasurableSpace.comap covariate inferInstance) hJint
    filter_upwards [hcondJ, hcomm] with o hJo hco
    change Complex.imCLM (@MeasureTheory.condExp (Obs Xspace) ℂ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P J o) =
        (@MeasureTheory.condExp (Obs Xspace) ℝ
          (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P
          (fun o ↦ (J o).im)) o at hco
    rw [hJo] at hco
    exact hco.symm
  have hzero (w : Obs Xspace → ℝ) (hw : Integrable w m.P)
      (hbrw : Integrable (fun o ↦ br o * w o) m.P)
      (hcw : (@MeasureTheory.condExp (Obs Xspace) ℝ
        (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P w) =ᵐ[m.P] 0) :
      ∫ o, br o * w o ∂m.P = 0 := by
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := m.P) (m := MeasurableSpace.comap covariate inferInstance)
      hbrsub hbrw hw
    calc
      ∫ o, br o * w o ∂m.P = ∫ o, (@MeasureTheory.condExp (Obs Xspace) ℝ
          (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P
          (fun o ↦ br o * w o)) o ∂m.P := by rw [MeasureTheory.integral_condExp hmle]
      _ = ∫ o, br o * (@MeasureTheory.condExp (Obs Xspace) ℝ
          (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P w) o ∂m.P :=
        integral_congr_ae hpull
      _ = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hcw] with o ho
        simp [ho]
  apply Complex.ext
  · change (∫ o, b o * J o ∂m.P).re = 0
    calc
      _ = ∫ o, (b o * J o).re ∂m.P := by
        simpa only [RCLike.re_eq_complex_re] using (integral_re hbJ).symm
      _ = ∫ o, br o * (J o).re ∂m.P := by
        apply integral_congr_ae
        filter_upwards [] with o
        simp [b, br]
      _ = 0 := hzero (fun o ↦ (J o).re) hJint.re (by simpa [b, br] using hbJ.re) hcondRe
  · change (∫ o, b o * J o ∂m.P).im = 0
    calc
      _ = ∫ o, (b o * J o).im ∂m.P := by
        simpa only [RCLike.im_eq_complex_im] using (integral_im hbJ).symm
      _ = ∫ o, br o * (J o).im ∂m.P := by
        apply integral_congr_ae
        filter_upwards [] with o
        simp [b, br]
      _ = 0 := hzero (fun o ↦ (J o).im) hJint.im (by simpa [b, br] using hbJ.im) hcondIm

/-- For a law [in the paper's non-Gaussian class](hyp:hclass), at a point where
the [moment generating function of the treatment noise vanishes](hyp:hz) with
[multiplicity exactly the given order](hyp:hmult), that order being [at least
one](hyp:hell), the [expected product of the outcome with the zero instrument
evaluated at the observable learned residual equals the treatment-effect
parameter times the expected product of that residual with the same
instrument](goal).

This is the moment equation the estimator inverts: decomposing the outcome into
the treatment-effect term, the covariate-measurable contamination and the outcome
noise, the last two contribute nothing against the instrument. -/
lemma outcome_zeroInstrument_integral_eq_theta_mul (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n ell : ℕ) (hclass : NonGaussianClass p n m) (z0 : ℂ) (hell : 1 ≤ ell)
    (hz : treatmentMGF p m z0 = 0)
    (hmult : analyticOrderNatAt (treatmentMGF p m) z0 = ell) :
    ∫ o, (outcome o : ℂ) *
        zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
          (learnedResidual p m n o) ∂m.P =
      (m.theta0 : ℂ) * ∫ o, (learnedResidual p m n o : ℂ) *
        zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
          (learnedResidual p m n o) ∂m.P := by
  let J : Obs Xspace → ℂ := fun o ↦
    zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
      (learnedResidual p m n o)
  have hZset : integrableExpSet (learnedResidual p m n) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, learnedResidual_integrable_exp p m n hclass t]
  have hzZ : z0.re ∈ interior (integrableExpSet (learnedResidual p m n) m.P) := by
    simp [hZset]
  have hZJ : Integrable (fun o ↦ (learnedResidual p m n o : ℂ) * J o) m.P := by
    have hbase := integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hzZ ell
    apply hbase.congr
    filter_upwards [] with o
    dsimp [J, zeroInstrument]
    rw [← mul_assoc, ← pow_succ']
    congr 2
    omega
  have hbJ := contamination_zeroInstrument_integrable_and_integral_eq_zero p m n ell hclass z0 hell hz hmult
  have hxiJ := outcomeNoise_zeroInstrument_integrable_and_integral_eq_zero p m n ell hclass z0 hell hz hmult
  have hbJ' : Integrable (fun o ↦
      (outcomeContamination p m n (covariate o) : ℂ) * J o) m.P := by
    simpa [J] using hbJ.1
  have hxiJ' : Integrable (fun o ↦ (xi p m o : ℂ) * J o) m.P := by
    simpa [J] using hxiJ.1
  have hthetaZJ : Integrable
      (fun o ↦ (m.theta0 : ℂ) * ((learnedResidual p m n o : ℂ) * J o)) m.P :=
    hZJ.const_mul _
  calc
    ∫ o, (outcome o : ℂ) * J o ∂m.P =
        ∫ o, ((m.theta0 : ℂ) * ((learnedResidual p m n o : ℂ) * J o) +
          (outcomeContamination p m n (covariate o) : ℂ) * J o) +
          (xi p m o : ℂ) * J o ∂m.P := by
            apply integral_congr_ae
            filter_upwards [] with o
            congr 1
            simp only [learnedResidual, outcomeContamination, xi, eta,
              treatment, outcome, covariate]
            push_cast
            ring
    _ = (∫ o, (m.theta0 : ℂ) * ((learnedResidual p m n o : ℂ) * J o) +
          (outcomeContamination p m n (covariate o) : ℂ) * J o ∂m.P) +
        ∫ o, (xi p m o : ℂ) * J o ∂m.P := by
          convert integral_add (hthetaZJ.add hbJ') hxiJ' using 1 <;>
            simp [Pi.add_apply]
    _ = (∫ o, (m.theta0 : ℂ) * ((learnedResidual p m n o : ℂ) * J o) ∂m.P) +
        (∫ o, (outcomeContamination p m n (covariate o) : ℂ) * J o ∂m.P) +
        ∫ o, (xi p m o : ℂ) * J o ∂m.P := by
          rw [integral_add hthetaZJ hbJ']
    _ = (m.theta0 : ℂ) * ∫ o, (learnedResidual p m n o : ℂ) * J o ∂m.P := by
      rw [show (∫ o, (outcomeContamination p m n (covariate o) : ℂ) * J o ∂m.P) = 0 by
          simpa [J] using hbJ.2,
        show (∫ o, (xi p m o : ℂ) * J o ∂m.P) = 0 by simpa [J] using hxiJ.2,
        add_zero, add_zero]
      exact integral_const_mul _ _




end CausalSmith.Stat.SaPlmCumulantConverse
