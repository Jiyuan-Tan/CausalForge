import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.AffineGaussianOutcomePath
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Luxemburg control for the affine Gaussian outcome path

This file supplies the explicit exponential-square calculation needed to put
the fresh Gaussian outcome residual in the paper's conditional sub-Gaussian
class.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- At standard deviation `psi / 4`, a centered Gaussian's exponential-square
moment at Luxemburg scale `psi` is finite and at most two. -/
lemma gaussian_exp_sq_integrable_and_integral_le_two (psi : ℝ) (hpsi : 0 < psi) :
    Integrable (fun z : ℝ ↦ Real.exp (z ^ 2 / psi ^ 2))
        (gaussianReal 0 ⟨(psi / 4) ^ 2, sq_nonneg (psi / 4)⟩) ∧
      ∫ z, Real.exp (z ^ 2 / psi ^ 2)
          ∂(gaussianReal 0 ⟨(psi / 4) ^ 2, sq_nonneg (psi / 4)⟩) ≤ 2 := by
  let v : NNReal := ⟨(psi / 4) ^ 2, sq_nonneg (psi / 4)⟩
  have hvval : (v : ℝ) = (psi / 4) ^ 2 := rfl
  have hv : v ≠ 0 := by
    intro hv0
    have hval : ((psi / 4) ^ 2 : ℝ) = 0 :=
      congrArg (fun x : NNReal ↦ (x : ℝ)) hv0
    nlinarith [mul_pos hpsi hpsi]
  have hb : 0 < (7 / psi ^ 2 : ℝ) := by positivity
  have hdom : Integrable (fun z : ℝ ↦ Real.exp (-(7 / psi ^ 2) * z ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hdensity : ∀ z : ℝ,
      gaussianPDFReal 0 v z * Real.exp (z ^ 2 / psi ^ 2) =
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          Real.exp (-(7 / psi ^ 2) * z ^ 2) := by
    intro z
    rw [gaussianPDFReal]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    rw [hvval]
    field_simp [ne_of_gt hpsi]
    ring
  have hintDensity : Integrable
      (fun z : ℝ ↦ gaussianPDFReal 0 v z * Real.exp (z ^ 2 / psi ^ 2)) := by
    apply (hdom.const_mul (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹).congr
    exact Filter.Eventually.of_forall fun z ↦ (hdensity z).symm
  have hint : Integrable (fun z : ℝ ↦ Real.exp (z ^ 2 / psi ^ 2))
      (gaussianReal 0 v) := by
    rw [gaussianReal_of_var_ne_zero _ hv,
      integrable_withDensity_iff (measurable_gaussianPDF 0 v)
        (Filter.Eventually.of_forall fun x ↦ by simp [gaussianPDF])]
    simpa [toReal_gaussianPDF, mul_comm] using hintDensity
  refine ⟨hint, ?_⟩
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hdensity), integral_const_mul,
    integral_gaussian (7 / psi ^ 2)]
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi * (v : ℝ)) := Real.sqrt_nonneg _
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := by positivity
  have hroot : Real.sqrt (Real.pi / (7 / psi ^ 2)) ≤
      2 * Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsquare : (2 * Real.sqrt (2 * Real.pi * (v : ℝ))) ^ 2 =
          4 * (2 * Real.pi * (v : ℝ)) := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          norm_num
      rw [hsquare, hvval]
      field_simp [ne_of_gt hpsi]
      nlinarith [Real.pi_pos, sq_pos_of_pos hpsi]
  calc
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.sqrt (Real.pi / (7 / psi ^ 2)) ≤
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          (2 * Real.sqrt (2 * Real.pi * (v : ℝ))) := by
            gcongr
    _ = 2 := by field_simp

/-- The affine Gaussian model at scale `psi / 4` satisfies the exact
conditional Luxemburg requirement at scale `psi`. -/
lemma affineGaussianModel_xiSubGaussian_quarter {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta : ℝ) (hpsi : 0 < p.psixi) :
    XiSubGaussian p (affineGaussianModel base theta (p.psixi / 4)) := by
  let m := affineGaussianModel base theta (p.psixi / 4)
  let f : ℝ → ℝ := fun z ↦ Real.exp (z ^ 2 / p.psixi ^ 2)
  have hf : Measurable f := by fun_prop
  have hgauss := gaussian_exp_sq_integrable_and_integral_le_two p.psixi hpsi
  have hximeas : Measurable (xi p m) := by
    exact (((measurable_snd.comp measurable_snd).sub
          (base.q0_measurable.comp measurable_fst)).sub
        (measurable_const.mul
          ((measurable_fst.comp measurable_snd).sub
            (base.g0_measurable.comp measurable_fst))))
  have hint : Integrable (fun o ↦ f (xi p m o)) m.P := by
    have hmap : Integrable f (m.P.map (xi p m)) := by
      rw [show m.P.map (xi p m) =
        gaussianReal 0 ⟨(p.psixi / 4) ^ 2, sq_nonneg (p.psixi / 4)⟩ by
          simpa [m] using affineGaussianModel_map_xi base theta (p.psixi / 4)]
      exact hgauss.1
    exact hmap.comp_aemeasurable hximeas.aemeasurable
  refine ⟨hint, ?_⟩
  have hind : IndepFun (f ∘ xi p m) covariate m.P := by
    have h := (affineGaussianModel_indep_xi_xt base theta (p.psixi / 4)).comp
      hf measurable_fst
    simpa [Function.comp_def, m] using h
  change Indep (MeasurableSpace.comap (f ∘ xi p m) inferInstance)
    (MeasurableSpace.comap covariate inferInstance) m.P at hind
  have hstrong : StronglyMeasurable[MeasurableSpace.comap (f ∘ xi p m) inferInstance]
      (f ∘ xi p m) := (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  have hcovle : MeasurableSpace.comap (covariate : Obs Xspace → Xspace) inferInstance ≤
      (inferInstance : MeasurableSpace (Obs Xspace)) := measurable_fst.comap_le
  haveI : SigmaFinite (m.P.trim hcovle) := inferInstance
  have hce := MeasureTheory.condExp_indep_eq
    (μ := m.P) (m₁ := MeasurableSpace.comap (f ∘ xi p m) inferInstance)
    (m₂ := MeasurableSpace.comap covariate inferInstance) (f := f ∘ xi p m)
    (hf.comp hximeas).comap_le hcovle hstrong hind
  have hmean : ∫ o, f (xi p m o) ∂m.P ≤ 2 := by
    have hmap := integral_map (μ := m.P) (φ := xi p m) (f := f)
      hximeas.aemeasurable hf.aestronglyMeasurable
    rw [affineGaussianModel_map_xi base theta (p.psixi / 4)] at hmap
    rw [← hmap]
    exact hgauss.2
  filter_upwards [hce] with o ho
  change m.P[f ∘ xi p m | MeasurableSpace.comap covariate inferInstance] o ≤ 2
  rw [ho]
  simpa [Function.comp_def] using hmean

/-- The quarter-scale affine family remains in the broad non-Gaussian class
throughout the original target range. -/
lemma affineGaussianModel_nonGaussianClass_quarter {p : Parameters}
    (base : Model (Xspace := Xspace) p) (n : ℕ)
    (hbase : NonGaussianClass p n base) (theta : ℝ)
    (htheta : |theta| ≤ p.Ctheta) :
    NonGaussianClass p n (affineGaussianModel base theta (p.psixi / 4)) :=
  affineGaussianModel_nonGaussianClass base n hbase theta (p.psixi / 4) htheta
    (affineGaussianModel_xiSubGaussian_quarter base theta p.constants_pos.2.2.2.2.1)

/-- The quarter-scale affine family remains in the published ACE comparator
class throughout the original target range. -/
lemma affineGaussianModel_jmsAceClass_quarter {p : Parameters}
    (base : Model (Xspace := Xspace) p) (n : ℕ)
    (hbase : JmsAceClass p n base) (theta : ℝ)
    (htheta : |theta| ≤ p.Ctheta) :
    JmsAceClass p n (affineGaussianModel base theta (p.psixi / 4)) :=
  affineGaussianModel_jmsAceClass base n hbase theta (p.psixi / 4) htheta
    (affineGaussianModel_xiSubGaussian_quarter base theta p.constants_pos.2.2.2.2.1)

end CausalSmith.Stat.SaPlmCumulantConverse
