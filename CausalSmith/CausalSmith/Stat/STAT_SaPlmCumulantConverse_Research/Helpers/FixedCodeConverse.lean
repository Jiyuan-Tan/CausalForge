import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.HardSubmodel

/-!
# Fixed-code non-Gaussian minimax converse

This module packages the affine-Gaussian two-point construction while retaining
both supplied nuisance-code functions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

/-- A positive inverse-sample-size minimax lower bound on every nonempty broad
non-Gaussian class with both supplied codes fixed. -/
lemma fixed_code_non_gaussian_minimax_lower
    (r : ℕ) (delta Ctheta Cg Cq psieta psixi : ℝ) (hpsixi : 0 < psixi) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Xspace : Type*} [MeasurableSpace Xspace]
        (p : Parameters), p.r = r → p.delta = delta → p.Ctheta = Ctheta →
        p.Cg = Cg → p.Cq = Cq → p.psieta = psieta → p.psixi = psixi →
      ∀ (base : Model (Xspace := Xspace) p),
        IidSampling p.n base.P (iidLaw base p.n) →
        ({m : Model (Xspace := Xspace) p |
          NonGaussianClass p p.n m ∧
            barG p m p.n = barG p base p.n ∧
              barQ p m p.n = barQ p base p.n}).Nonempty →
        2 ≤ p.n →
        ENNReal.ofReal (c / p.n) ≤ minimaxRisk p p.n base.gcode base.qcode := by
  let c0 : ℝ := if 0 < Ctheta then min Ctheta 1 else 1
  let C0 : ℝ := max 1 (16 * psieta ^ 2 / psixi ^ 2)
  let tau : ℝ := psixi / 4
  let K : ℝ := C0 * c0 ^ 2
  obtain ⟨cK, hcK, hlecam⟩ := Causalean.Stat.Minimax.le_cam_two_point_mse K
  refine ⟨cK * c0 ^ 2, ?_, ?_⟩
  · apply mul_pos hcK
    apply sq_pos_of_pos
    dsimp [c0]
    split_ifs with h
    · exact lt_min h zero_lt_one
    · norm_num
  intro Xspace inst p hr hdelta hCtheta hCg hCq hpsieta hp base _hiid hlaws hn
  subst r
  subst delta
  subst Ctheta
  subst Cg
  subst Cq
  subst psieta
  subst psixi
  have hc0_le : c0 ≤ p.Ctheta := by
    simp only [c0, if_pos p.constants_pos.1]
    exact min_le_left _ _
  have hc0_pos : 0 < c0 := by
    simp only [c0, if_pos p.constants_pos.1]
    exact lt_min p.constants_pos.1 zero_lt_one
  have htau_pos : 0 < tau := by
    dsimp [tau]
    linarith [p.constants_pos.2.2.2.2.1]
  have hC0_coeff : 16 * p.psieta ^ 2 / p.psixi ^ 2 ≤ C0 :=
    le_max_right _ _
  rcases hlaws with ⟨hardBase, hhard, hgcode, hqcode⟩
  let thetaMinus : ℝ := -c0 / (2 * Real.sqrt p.n)
  let thetaPlus : ℝ := c0 / (2 * Real.sqrt p.n)
  let m0 := affineGaussianModel hardBase thetaMinus tau
  let m1 := affineGaussianModel hardBase thetaPlus tau
  have hsqrt_pos : 0 < Real.sqrt p.n :=
    Real.sqrt_pos.2 (by exact_mod_cast (show 0 < p.n by omega))
  have hsqrt_ge : 1 ≤ Real.sqrt p.n :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ p.n by omega))
  have htminus : |thetaMinus| ≤ c0 := by
    dsimp [thetaMinus]
    rw [abs_div, abs_neg, abs_of_pos hc0_pos,
      abs_of_pos (mul_pos zero_lt_two hsqrt_pos)]
    apply (div_le_iff₀ (mul_pos zero_lt_two hsqrt_pos)).2
    nlinarith
  have htplus : |thetaPlus| ≤ c0 := by
    dsimp [thetaPlus]
    rw [abs_div, abs_of_pos hc0_pos,
      abs_of_pos (mul_pos zero_lt_two hsqrt_pos)]
    apply (div_le_iff₀ (mul_pos zero_lt_two hsqrt_pos)).2
    nlinarith
  have hm0 : m0 ∈ {m : Model (Xspace := Xspace) p |
      NonGaussianClass p p.n m ∧
        barG p m p.n = barG p base p.n ∧ barQ p m p.n = barQ p base p.n} := by
    refine ⟨affineGaussianModel_nonGaussianClass_quarter hardBase p.n hhard
      thetaMinus (htminus.trans hc0_le), ?_, ?_⟩
    · exact hgcode
    · exact hqcode
  have hm1 : m1 ∈ {m : Model (Xspace := Xspace) p |
      NonGaussianClass p p.n m ∧
        barG p m p.n = barG p base p.n ∧ barQ p m p.n = barQ p base p.n} := by
    refine ⟨affineGaussianModel_nonGaussianClass_quarter hardBase p.n hhard
      thetaPlus (htplus.trans hc0_le), ?_, ?_⟩
    · exact hgcode
    · exact hqcode
  have hsep : |thetaPlus - thetaMinus| = c0 / Real.sqrt p.n := by
    have heq : thetaPlus - thetaMinus = c0 / Real.sqrt p.n := by
      dsimp [thetaPlus, thetaMinus]
      field_simp [ne_of_gt hsqrt_pos]
      ring
    rw [heq, abs_of_pos (div_pos hc0_pos hsqrt_pos)]
  have hKLraw := affineGaussianModel_iid_kl_le hardBase p.n
    hhard.etaSubGaussian thetaMinus thetaPlus tau htau_pos
  have hnreal : 0 < (p.n : ℝ) := by positivity
  have hsqrt_sq : (Real.sqrt p.n) ^ 2 = (p.n : ℝ) :=
    Real.sq_sqrt hnreal.le
  have hsep_sq : (thetaPlus - thetaMinus) ^ 2 = c0 ^ 2 / (p.n : ℝ) := by
    rw [← sq_abs (thetaPlus - thetaMinus), hsep, div_pow, hsqrt_sq]
  have hKL : InformationTheory.klDiv (iidLaw m0 p.n) (iidLaw m1 p.n) ≤
      ENNReal.ofReal (C0 * c0 ^ 2) := by
    refine hKLraw.trans ?_
    apply ENNReal.ofReal_le_ofReal
    dsimp [m0, m1, tau] at hKLraw ⊢
    rw [hsep_sq]
    have hpsi : 0 < p.psixi := p.constants_pos.2.2.2.2.1
    calc
      (p.n : ℝ) * ((c0 ^ 2 / (p.n : ℝ) * (2 * p.psieta ^ 2)) /
          (2 * (p.psixi / 4) ^ 2)) =
          (16 * p.psieta ^ 2 / p.psixi ^ 2) * c0 ^ 2 := by
            field_simp [ne_of_gt hnreal, ne_of_gt hpsi]
            ring
      _ ≤ C0 * c0 ^ 2 :=
        mul_le_mul_of_nonneg_right hC0_coeff (sq_nonneg _)
  letI : IsProbabilityMeasure (iidLaw m0 p.n) := by
    unfold iidLaw
    infer_instance
  letI : IsProbabilityMeasure (iidLaw m1 p.n) := by
    unfold iidLaw
    infer_instance
  have hbody : ∀ T : (Fin p.n → Obs Xspace) → ℝ, Measurable T →
      Integrable (fun s ↦ (T s - m0.theta0) ^ 2) (iidLaw m0 p.n) →
      Integrable (fun s ↦ (T s - m1.theta0) ^ 2) (iidLaw m1 p.n) →
      cK * (m1.theta0 - m0.theta0) ^ 2 ≤
        max (∫ s, (T s - m0.theta0) ^ 2 ∂iidLaw m0 p.n)
          (∫ s, (T s - m1.theta0) ^ 2 ∂iidLaw m1 p.n) := by
    exact hlecam (iidLaw m0 p.n) (iidLaw m1 p.n) m0.theta0 m1.theta0 hKL
  have hlow := minimaxRiskOn_two_point_lower p p.n _ m0 m1 hm0 hm1
    p.Ctheta cK p.constants_pos.1.le
    (by exact hm0.1.thetaRange)
    (by exact hm1.1.thetaRange) hbody
  have hscaled : ENNReal.ofReal (cK * c0 ^ 2 / p.n) ≤
      minimaxRiskOn p p.n {m : Model (Xspace := Xspace) p |
        NonGaussianClass p p.n m ∧
          barG p m p.n = barG p base p.n ∧ barQ p m p.n = barQ p base p.n} := by
    convert hlow using 1
    congr 1
    dsimp [m0, m1, thetaMinus, thetaPlus]
    field_simp [ne_of_gt hnreal, ne_of_gt hsqrt_pos]
    rw [hsqrt_sq]
    ring
  exact hscaled

/-- A positive inverse-sample-size lower bound for every nonempty fixed-code
published ACE class, uniform over the covariate space. -/
lemma fixed_code_ace_minimax_lower
    (r : ℕ) (delta Ctheta Cg Cq psieta psixi : ℝ) (hpsixi : 0 < psixi) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Xspace : Type*} [MeasurableSpace Xspace]
        (p : Parameters), p.r = r → p.delta = delta → p.Ctheta = Ctheta →
        p.Cg = Cg → p.Cq = Cq → p.psieta = psieta → p.psixi = psixi →
      ∀ (base : Model (Xspace := Xspace) p),
        ({m : Model (Xspace := Xspace) p |
          JmsAceClass p p.n m ∧ barG p m p.n = barG p base p.n ∧
            barQ p m p.n = barQ p base p.n}).Nonempty →
        2 ≤ p.n →
        ENNReal.ofReal (c / p.n) ≤ minimaxRiskOn p p.n
          {m : Model (Xspace := Xspace) p |
            JmsAceClass p p.n m ∧ barG p m p.n = barG p base p.n ∧
              barQ p m p.n = barQ p base p.n} := by
  let c0 : ℝ := if 0 < Ctheta then min Ctheta 1 else 1
  let C0 : ℝ := max 1 (16 * psieta ^ 2 / psixi ^ 2)
  let tau : ℝ := psixi / 4
  let K : ℝ := C0 * c0 ^ 2
  obtain ⟨cK, hcK, hlecam⟩ := Causalean.Stat.Minimax.le_cam_two_point_mse K
  refine ⟨cK * c0 ^ 2, mul_pos hcK ?_, ?_⟩
  · exact sq_pos_of_pos (by
      dsimp [c0]
      split_ifs with h
      · exact lt_min h zero_lt_one
      · norm_num)
  intro Xspace inst p hr hdelta hCtheta hCg hCq hpsieta hp base hlaws hn
  subst r; subst delta; subst Ctheta; subst Cg; subst Cq; subst psieta; subst psixi
  have hc0_le : c0 ≤ p.Ctheta := by
    simp only [c0, if_pos p.constants_pos.1]
    exact min_le_left _ _
  have hc0_pos : 0 < c0 := by
    simp only [c0, if_pos p.constants_pos.1]
    exact lt_min p.constants_pos.1 zero_lt_one
  have htau_pos : 0 < tau := by
    dsimp [tau]
    linarith [p.constants_pos.2.2.2.2.1]
  have hC0_coeff : 16 * p.psieta ^ 2 / p.psixi ^ 2 ≤ C0 := le_max_right _ _
  rcases hlaws with ⟨hardBase, hhard, hgcode, hqcode⟩
  let thetaMinus : ℝ := -c0 / (2 * Real.sqrt p.n)
  let thetaPlus : ℝ := c0 / (2 * Real.sqrt p.n)
  let m0 := affineGaussianModel hardBase thetaMinus tau
  let m1 := affineGaussianModel hardBase thetaPlus tau
  have hsqrt_pos : 0 < Real.sqrt p.n :=
    Real.sqrt_pos.2 (by exact_mod_cast (show 0 < p.n by omega))
  have hsqrt_ge : 1 ≤ Real.sqrt p.n :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ p.n by omega))
  have htminus : |thetaMinus| ≤ c0 := by
    dsimp [thetaMinus]
    rw [abs_div, abs_neg, abs_of_pos hc0_pos,
      abs_of_pos (mul_pos zero_lt_two hsqrt_pos)]
    apply (div_le_iff₀ (mul_pos zero_lt_two hsqrt_pos)).2
    nlinarith
  have htplus : |thetaPlus| ≤ c0 := by
    dsimp [thetaPlus]
    rw [abs_div, abs_of_pos hc0_pos,
      abs_of_pos (mul_pos zero_lt_two hsqrt_pos)]
    apply (div_le_iff₀ (mul_pos zero_lt_two hsqrt_pos)).2
    nlinarith
  let laws : Set (Model (Xspace := Xspace) p) :=
    {m | JmsAceClass p p.n m ∧ barG p m p.n = barG p base p.n ∧
      barQ p m p.n = barQ p base p.n}
  have hm0 : m0 ∈ laws := by
    refine ⟨affineGaussianModel_jmsAceClass_quarter hardBase p.n hhard thetaMinus
      (htminus.trans hc0_le), ?_, ?_⟩
    · exact hgcode
    · exact hqcode
  have hm1 : m1 ∈ laws := by
    refine ⟨affineGaussianModel_jmsAceClass_quarter hardBase p.n hhard thetaPlus
      (htplus.trans hc0_le), ?_, ?_⟩
    · exact hgcode
    · exact hqcode
  have hsep : |thetaPlus - thetaMinus| = c0 / Real.sqrt p.n := by
    have heq : thetaPlus - thetaMinus = c0 / Real.sqrt p.n := by
      dsimp [thetaPlus, thetaMinus]
      field_simp [ne_of_gt hsqrt_pos]
      ring
    rw [heq, abs_of_pos (div_pos hc0_pos hsqrt_pos)]
  have hKLraw := affineGaussianModel_iid_kl_le hardBase p.n
    hhard.etaSubGaussian thetaMinus thetaPlus tau htau_pos
  have hnreal : 0 < (p.n : ℝ) := by positivity
  have hsqrt_sq : (Real.sqrt p.n) ^ 2 = (p.n : ℝ) := Real.sq_sqrt hnreal.le
  have hsep_sq : (thetaPlus - thetaMinus) ^ 2 = c0 ^ 2 / (p.n : ℝ) := by
    rw [← sq_abs (thetaPlus - thetaMinus), hsep, div_pow, hsqrt_sq]
  have hKL : InformationTheory.klDiv (iidLaw m0 p.n) (iidLaw m1 p.n) ≤
      ENNReal.ofReal (C0 * c0 ^ 2) := by
    refine hKLraw.trans ?_
    apply ENNReal.ofReal_le_ofReal
    dsimp [m0, m1, tau] at hKLraw ⊢
    rw [hsep_sq]
    have hpsi : 0 < p.psixi := p.constants_pos.2.2.2.2.1
    calc
      (p.n : ℝ) * ((c0 ^ 2 / (p.n : ℝ) * (2 * p.psieta ^ 2)) /
          (2 * (p.psixi / 4) ^ 2)) =
          (16 * p.psieta ^ 2 / p.psixi ^ 2) * c0 ^ 2 := by
            field_simp [ne_of_gt hnreal, ne_of_gt hpsi]
            ring
      _ ≤ C0 * c0 ^ 2 := mul_le_mul_of_nonneg_right hC0_coeff (sq_nonneg _)
  letI : IsProbabilityMeasure (iidLaw m0 p.n) := by unfold iidLaw; infer_instance
  letI : IsProbabilityMeasure (iidLaw m1 p.n) := by unfold iidLaw; infer_instance
  have hbody : ∀ T : (Fin p.n → Obs Xspace) → ℝ, Measurable T →
      Integrable (fun s ↦ (T s - m0.theta0) ^ 2) (iidLaw m0 p.n) →
      Integrable (fun s ↦ (T s - m1.theta0) ^ 2) (iidLaw m1 p.n) →
      cK * (m1.theta0 - m0.theta0) ^ 2 ≤
        max (∫ s, (T s - m0.theta0) ^ 2 ∂iidLaw m0 p.n)
          (∫ s, (T s - m1.theta0) ^ 2 ∂iidLaw m1 p.n) := by
    exact hlecam (iidLaw m0 p.n) (iidLaw m1 p.n) m0.theta0 m1.theta0 hKL
  have hlow := minimaxRiskOn_two_point_lower p p.n laws m0 m1 hm0 hm1
    p.Ctheta cK p.constants_pos.1.le
    (by exact hm0.1.thetaRange)
    (by exact hm1.1.thetaRange) hbody
  convert hlow using 1
  congr 1
  dsimp [m0, m1, thetaMinus, thetaPlus]
  field_simp [ne_of_gt hnreal, ne_of_gt hsqrt_pos]
  rw [hsqrt_sq]
  ring

end CausalSmith.Stat.SaPlmCumulantConverse
