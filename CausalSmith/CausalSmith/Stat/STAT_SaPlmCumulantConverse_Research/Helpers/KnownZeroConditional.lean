import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.Transforms

/-!
# Conditional annihilation for known-zero instruments
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- All transform derivatives below a positive analytic zero order vanish. -/
lemma treatmentMGF_iteratedDeriv_eq_zero_of_lt_order
    (p : Parameters) (m : Model (Xspace := Xspace) p) (n ell : ℕ)
    (hclass : NonGaussianClass p n m) (z0 : ℂ) (hell : 1 ≤ ell)
    (hmult : analyticOrderNatAt (treatmentMGF p m) z0 = ell) :
    ∀ j < ell, iteratedDeriv j (treatmentMGF p m) z0 = 0 := by
  have hset : integrableExpSet (eta p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, eta_integrable_exp p m n hclass t]
  have hzmem : z0.re ∈ interior (integrableExpSet (eta p m) m.P) := by
    simp [hset]
  have han : AnalyticAt ℂ (treatmentMGF p m) z0 :=
    analyticAt_complexMGF hzmem
  have hfinite : analyticOrderAt (treatmentMGF p m) z0 ≠ ⊤ := by
    intro htop
    have hzero : analyticOrderNatAt (treatmentMGF p m) z0 = 0 := by
      simp [analyticOrderNatAt, htop]
    rw [hmult] at hzero
    omega
  intro j hj
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).mp
    (show (↑ell : ℕ∞) ≤ analyticOrderAt (treatmentMGF p m) z0 by
      rw [← Nat.cast_analyticOrderNatAt hfinite, hmult]) j hj

/-- A transform zero of order `ell` annihilates its polynomial-exponential
instrument after every deterministic real shift. -/
lemma zeroInstrument_integral_add_eq_zero
    (p : Parameters) (m : Model (Xspace := Xspace) p) (n ell : ℕ)
    (hclass : NonGaussianClass p n m) (z0 : ℂ) (hell : 1 ≤ ell)
    (hz : treatmentMGF p m z0 = 0)
    (hmult : analyticOrderNatAt (treatmentMGF p m) z0 = ell) (d : ℝ) :
    ∫ o, zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
      ((eta p m o + d : ℝ) : ℂ) ∂m.P = 0 := by
  have hset : integrableExpSet (eta p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, eta_integrable_exp p m n hclass t]
  have hzmem : z0.re ∈ interior (integrableExpSet (eta p m) m.P) := by
    simp [hset]
  have hzero := treatmentMGF_iteratedDeriv_eq_zero_of_lt_order
    p m n ell hclass z0 hell hmult
  simp only [zeroInstrument]
  have hfun : ∀ o, (((eta p m o + d : ℝ) : ℂ) ^ (ell - 1) *
      Complex.exp (z0 * ((eta p m o + d : ℝ) : ℂ))) =
      Complex.exp (z0 * d) * ∑ j ∈ Finset.range ell,
        ((ell - 1).choose j : ℂ) * (d : ℂ) ^ (ell - 1 - j) *
          ((eta p m o : ℂ) ^ j * Complex.exp (z0 * (eta p m o : ℂ))) := by
    intro o
    rw [show ((eta p m o + d : ℝ) : ℂ) = (eta p m o : ℂ) + d by
      push_cast; rfl, add_pow, Finset.sum_mul]
    rw [show Complex.exp (z0 * ((eta p m o : ℂ) + d)) =
        Complex.exp (z0 * d) * Complex.exp (z0 * (eta p m o : ℂ)) by
      rw [mul_add, Complex.exp_add]; ring]
    rw [Finset.mul_sum, Nat.sub_add_cancel hell]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
  rw [show (∫ o, Complex.exp (z0 * d) * (∑ j ∈ Finset.range ell,
      ((ell - 1).choose j : ℂ) * (d : ℂ) ^ (ell - 1 - j) *
        ((eta p m o : ℂ) ^ j * Complex.exp (z0 * (eta p m o : ℂ)))) ∂m.P) =
      Complex.exp (z0 * d) * ∫ o, (∑ j ∈ Finset.range ell,
      ((ell - 1).choose j : ℂ) * (d : ℂ) ^ (ell - 1 - j) *
        ((eta p m o : ℂ) ^ j * Complex.exp (z0 * (eta p m o : ℂ)))) ∂m.P by
    exact integral_const_mul _ _]
  have hint (j : ℕ) : Integrable (fun o ↦ (eta p m o : ℂ) ^ j *
      Complex.exp (z0 * (eta p m o : ℂ))) m.P :=
    integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hzmem j
  rw [integral_finset_sum]
  · apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro i hi
    calc
      _ = (((ell - 1).choose i : ℂ) * (d : ℂ) ^ (ell - 1 - i)) *
          ∫ a, ((eta p m a : ℂ) ^ i *
            Complex.exp (z0 * (eta p m a : ℂ))) ∂m.P := by
              exact integral_const_mul _ _
      _ = 0 := by
        apply mul_eq_zero_of_right
        rw [← iteratedDeriv_complexMGF hzmem]
        exact hzero i (Finset.mem_range.mp hi)
  · intro j hj
    exact (hint j).const_mul _

/-- For a model in [the broad non-Gaussian class](hyp:hclass) and a complex point where [the
treatment-noise moment generating function vanishes](hyp:hz) to [a known order](hyp:hmult) that
is [at least one](hyp:hell), [the transform-zero instrument evaluated at the observable learned
residual has conditional mean zero given the covariates, almost surely](goal).

Conditioning on the covariates freezes the treatment-code error, and the instrument's mean over
the treatment noise vanishes at every shift because all derivatives of the transform below the
known order vanish at the zero. -/
lemma zeroInstrument_condExp_learnedResidual_eq_zero (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n ell : ℕ) (hclass : NonGaussianClass p n m) (z0 : ℂ) (hell : 1 ≤ ell)
    (hz : treatmentMGF p m z0 = 0)
    (hmult : analyticOrderNatAt (treatmentMGF p m) z0 = ell) :
    (@MeasureTheory.condExp (Obs Xspace) ℂ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P
      (fun o ↦ zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
        (learnedResidual p m n o))) =ᵐ[m.P] 0 := by
  let J : Obs Xspace → ℂ := fun o ↦
    zeroInstrument (treatmentMGF p m) z0 ell hell hz hmult
      (learnedResidual p m n o)
  have hset : integrableExpSet (eta p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, eta_integrable_exp p m n hclass t]
  have hzmem : z0.re ∈ interior (integrableExpSet (eta p m) m.P) := by
    simp [hset]
  have hzero := treatmentMGF_iteratedDeriv_eq_zero_of_lt_order
    p m n ell hclass z0 hell hmult
  have hJint : Integrable J m.P := by
    have hZset : integrableExpSet (learnedResidual p m n) m.P = Set.univ := by
      ext t
      simp [integrableExpSet, learnedResidual_integrable_exp p m n hclass t]
    have hzZ : z0.re ∈ interior (integrableExpSet (learnedResidual p m n) m.P) := by
      simp [hZset]
    simpa [J, zeroInstrument] using
      integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hzZ (ell - 1)
  have hmle : MeasurableSpace.comap covariate inferInstance ≤
      (inferInstance : MeasurableSpace (Obs Xspace)) :=
    Measurable.comap_le measurable_fst
  have hcond : (0 : Obs Xspace → ℂ) =ᵐ[m.P]
      @MeasureTheory.condExp (Obs Xspace) ℂ
        (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P J := by
    apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hmle hJint
    · intro s hs hfin
      exact integrableOn_zero
    · intro s hs hfin
      change (∫ _x in s, (0 : ℂ) ∂m.P) = ∫ x in s, J x ∂m.P
      rw [integral_zero]
      symm
      rcases hs with ⟨t, ht, rfl⟩
      rw [show ∫ o in covariate ⁻¹' t, J o ∂m.P =
          ∫ o, J o * (Set.indicator t (fun _ ↦ (1 : ℂ))) (covariate o) ∂m.P by
        rw [← integral_indicator (hmle _ (show MeasurableSet[MeasurableSpace.comap covariate inferInstance]
          (covariate ⁻¹' t) from ⟨t, ht, rfl⟩))]
        apply integral_congr_ae
        filter_upwards [] with o
        by_cases ho : covariate o ∈ t <;> simp [Set.indicator, ho]]
      have hfun : ∀ o, J o * (Set.indicator t (fun _ ↦ (1 : ℂ))) (covariate o) =
          ∑ j ∈ Finset.range ell,
            ((eta p m o : ℂ) ^ j * Complex.exp (z0 * (eta p m o : ℂ))) *
            (((ell - 1).choose j : ℂ) *
              (treatmentError p m n o : ℂ) ^ (ell - 1 - j) *
              Complex.exp (z0 * (treatmentError p m n o : ℂ)) *
              (Set.indicator t (fun _ ↦ (1 : ℂ))) (covariate o)) := by
        intro o
        dsimp [J, zeroInstrument]
        rw [show learnedResidual p m n o = eta p m o + treatmentError p m n o by
          simp [learnedResidual, eta, treatmentError]]
        push_cast
        rw [add_pow]
        rw [show Complex.exp (z0 * ((eta p m o : ℂ) + (treatmentError p m n o : ℂ))) =
            Complex.exp (z0 * (eta p m o : ℂ)) *
              Complex.exp (z0 * (treatmentError p m n o : ℂ)) by
          rw [mul_add, Complex.exp_add]]
        rw [Nat.sub_add_cancel hell]
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hfun), integral_finset_sum]
      · apply Finset.sum_eq_zero
        intro j hj
        have heta : Measurable (eta p m) := by
          unfold eta treatment covariate
          exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
        have hX : Measurable (covariate (Xspace := Xspace)) := measurable_fst
        have hD : Measurable (fun x : Xspace ↦ m.g0 x - barG p m n x) :=
          m.g0_measurable.sub (((m.gcode_measurable n).max measurable_const).min measurable_const)
        have hDc : Measurable (fun x : Xspace ↦
            ((m.g0 x - barG p m n x : ℝ) : ℂ)) := by
          change Measurable (Complex.ofReal ∘ fun x : Xspace ↦ m.g0 x - barG p m n x)
          exact Complex.measurable_ofReal.comp hD
        have hgmeas : Measurable (fun x : Xspace ↦ ((ell - 1).choose j : ℂ) *
            ((m.g0 x - barG p m n x : ℝ) : ℂ) ^ (ell - 1 - j) *
            Complex.exp (z0 * ((m.g0 x - barG p m n x : ℝ) : ℂ)) *
            Set.indicator t (fun _ ↦ (1 : ℂ)) x) := by
          apply Measurable.mul
          · exact ((measurable_const.mul (hDc.pow_const (ell - 1 - j))).mul
              (Complex.continuous_exp.measurable.comp
                (measurable_const.mul hDc)))
          · exact measurable_const.indicator ht
        have hind := hclass.independentTreatmentNoise.integral_fun_comp_mul_comp
          (f := fun e : ℝ ↦ (e : ℂ) ^ j * Complex.exp (z0 * (e : ℂ)))
          (g := fun x : Xspace ↦ ((ell - 1).choose j : ℂ) *
            ((m.g0 x - barG p m n x : ℝ) : ℂ) ^ (ell - 1 - j) *
            Complex.exp (z0 * ((m.g0 x - barG p m n x : ℝ) : ℂ)) *
            Set.indicator t (fun _ ↦ (1 : ℂ)) x)
          heta.aemeasurable hX.aemeasurable (by fun_prop)
          hgmeas.aestronglyMeasurable
        rw [show (∫ o, ((eta p m o : ℂ) ^ j * Complex.exp (z0 * (eta p m o : ℂ))) *
              (((ell - 1).choose j : ℂ) * (treatmentError p m n o : ℂ) ^ (ell - 1 - j) *
                Complex.exp (z0 * (treatmentError p m n o : ℂ)) *
                Set.indicator t (fun _ ↦ (1 : ℂ)) (covariate o)) ∂m.P) =
            (∫ o, (eta p m o : ℂ) ^ j * Complex.exp (z0 * (eta p m o : ℂ)) ∂m.P) *
              ∫ o, ((ell - 1).choose j : ℂ) * (treatmentError p m n o : ℂ) ^ (ell - 1 - j) *
                Complex.exp (z0 * (treatmentError p m n o : ℂ)) *
                Set.indicator t (fun _ ↦ (1 : ℂ)) (covariate o) ∂m.P by
          simpa [treatmentError] using hind]
        apply mul_eq_zero_of_left
        rw [← iteratedDeriv_complexMGF hzmem]
        exact hzero j (Finset.mem_range.mp hj)
      · intro j hj
        have heta : Measurable (eta p m) := by
          unfold eta treatment covariate
          exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
        have hX : Measurable (covariate (Xspace := Xspace)) := measurable_fst
        have hDmeas : Measurable (fun x : Xspace ↦ m.g0 x - barG p m n x) :=
          m.g0_measurable.sub (((m.gcode_measurable n).max measurable_const).min measurable_const)
        have hDc : Measurable (fun x : Xspace ↦
            ((m.g0 x - barG p m n x : ℝ) : ℂ)) := by
          change Measurable (Complex.ofReal ∘ fun x : Xspace ↦ m.g0 x - barG p m n x)
          exact Complex.measurable_ofReal.comp hDmeas
        let f : ℝ → ℂ := fun e ↦ (e : ℂ) ^ j * Complex.exp (z0 * (e : ℂ))
        let g : Xspace → ℂ := fun x ↦ ((ell - 1).choose j : ℂ) *
          ((m.g0 x - barG p m n x : ℝ) : ℂ) ^ (ell - 1 - j) *
          Complex.exp (z0 * ((m.g0 x - barG p m n x : ℝ) : ℂ)) *
          Set.indicator t (fun _ ↦ (1 : ℂ)) x
        have hfint : Integrable (fun o ↦ f (eta p m o)) m.P := by
          simpa [f] using
            integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hzmem j
        have hbar (x : Xspace) : |barG p m n x| ≤ p.Cg := by
          have hCg : 0 < p.Cg := p.constants_pos.2.1
          rw [abs_le]
          dsimp [barG]
          constructor <;> simp_all <;> linarith
        have hDae : ∀ᵐ o ∂m.P, |treatmentError p m n o| ≤ 2 * p.Cg := by
          have hg0 := MeasureTheory.ae_of_ae_map hX.aemeasurable hclass.gRange
          filter_upwards [hg0] with o ho
          dsimp [treatmentError]
          calc
            |m.g0 (covariate o) - barG p m n (covariate o)| ≤
                |m.g0 (covariate o)| + |barG p m n (covariate o)| := abs_sub _ _
            _ ≤ p.Cg + p.Cg := add_le_add ho (hbar _)
            _ = 2 * p.Cg := by ring
        have hgmeas : Measurable g := by
          dsimp [g]
          apply Measurable.mul
          · exact ((measurable_const.mul (hDc.pow_const (ell - 1 - j))).mul
              (Complex.continuous_exp.measurable.comp
                (measurable_const.mul hDc)))
          · exact measurable_const.indicator ht
        have hgint : Integrable (fun o ↦ g (covariate o)) m.P := by
          have hbound : ∀ᵐ o ∂m.P, ‖g (covariate o)‖ ≤
              ((ell - 1).choose j : ℝ) * (2 * p.Cg) ^ (ell - 1 - j) *
                Real.exp (‖z0‖ * (2 * p.Cg)) := by
            filter_upwards [hDae] with o hDo
            dsimp [g]
            by_cases hot : covariate o ∈ t
            · rw [Set.indicator_of_mem hot]
              simp only [mul_one, norm_mul, Complex.norm_natCast, Complex.norm_pow,
                Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
              have hCg0 : 0 ≤ 2 * p.Cg := mul_nonneg (by norm_num) p.constants_pos.2.1.le
              have hpw := pow_le_pow_left₀ (abs_nonneg (treatmentError p m n o)) hDo
                (ell - 1 - j)
              have hexp : Real.exp ((z0 * (treatmentError p m n o : ℂ)).re) ≤
                  Real.exp (‖z0‖ * (2 * p.Cg)) := by
                apply Real.exp_le_exp.mpr
                calc
                  (z0 * (treatmentError p m n o : ℂ)).re ≤
                      |(z0 * (treatmentError p m n o : ℂ)).re| := le_abs_self _
                  _ ≤ ‖z0 * (treatmentError p m n o : ℂ)‖ := Complex.abs_re_le_norm _
                  _ = ‖z0‖ * |treatmentError p m n o| := by
                    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                  _ ≤ ‖z0‖ * (2 * p.Cg) :=
                    mul_le_mul_of_nonneg_left hDo (norm_nonneg z0)
              simpa [treatmentError, mul_assoc] using mul_le_mul_of_nonneg_left
                (mul_le_mul hpw hexp (Real.exp_pos _).le (pow_nonneg hCg0 _))
                (show (0 : ℝ) ≤ ((ell - 1).choose j : ℝ) from Nat.cast_nonneg _)
            · rw [Set.indicator_of_notMem hot, mul_zero, norm_zero]
              exact mul_nonneg
                (mul_nonneg (Nat.cast_nonneg _)
                  (pow_nonneg (mul_nonneg (by norm_num) p.constants_pos.2.1.le) _))
                (Real.exp_pos _).le
          have hg1 := (integrable_const (μ := m.P) (1 : ℂ)).bdd_mul
            (c := ((ell - 1).choose j : ℝ) * (2 * p.Cg) ^ (ell - 1 - j) *
              Real.exp (‖z0‖ * (2 * p.Cg)))
            (hgmeas.comp hX).aestronglyMeasurable hbound
          simpa only [Pi.mul_apply, mul_one, Function.comp_def] using hg1
        have hfg := (hclass.independentTreatmentNoise.comp
          (by fun_prop : Measurable f) hgmeas).integrable_mul hfint hgint
        exact hfg
    · exact aestronglyMeasurable_zero
  exact hcond.symm


end CausalSmith.Stat.SaPlmCumulantConverse
