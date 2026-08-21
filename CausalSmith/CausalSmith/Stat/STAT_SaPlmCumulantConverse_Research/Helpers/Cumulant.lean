import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Basic
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.Transforms
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.ComplexAnalysisLocal
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.LuxemburgMGF
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Cumulants and transform-zero localization
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped Topology

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- The treatment-noise transform is entire, normalized at the origin, and
obeys the quadratic exponential envelope supplied by the Luxemburg bound. -/
lemma treatmentMGF_entire_normalized_bound (p : Parameters)
    (m : Model (Xspace := Xspace) p) (n : ℕ) (hclass : NonGaussianClass p n m) :
    AnalyticOnNhd ℂ (treatmentMGF p m) Set.univ ∧
      treatmentMGF p m 0 = 1 ∧
      ∀ z : ℂ, ‖treatmentMGF p m z‖ ≤
        Real.exp (4 * p.psieta ^ 2 * ‖z‖ ^ 2) := by
  have hψ : 0 < p.psieta := p.constants_pos.2.2.2.1
  have hetaMeas : Measurable (eta p m) := by
    unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  have hmx : MeasurableSpace.comap (fun o : Obs Xspace ↦ o.1) inferInstance ≤
      (inferInstance : MeasurableSpace (Obs Xspace)) := Measurable.comap_le measurable_fst
  have hgint : Integrable (fun o : Obs Xspace ↦ m.g0 (covariate o)) m.P :=
    MeasureTheory.integrable_condExp.congr m.g0_condMean
  have hetaInt : Integrable (eta p m) m.P := m.treatment_integrable.sub hgint
  have hcenter : ∫ o, eta p m o ∂m.P = 0 := by
    have hgIntegral : (∫ o, m.g0 (covariate o) ∂m.P) =
        ∫ o, treatment o ∂m.P := by
      calc
        (∫ o, m.g0 (covariate o) ∂m.P) =
            ∫ o, (@MeasureTheory.condExp (Obs Xspace) ℝ
              (MeasurableSpace.comap (fun o : Obs Xspace ↦ o.1) inferInstance)
              inferInstance _ _ m.P (fun o ↦ o.2.1)) o ∂m.P :=
          integral_congr_ae m.g0_condMean.symm
        _ = ∫ o, treatment o ∂m.P := MeasureTheory.integral_condExp hmx
    change ∫ o, o.2.1 - m.g0 o.1 ∂m.P = 0
    rw [integral_sub m.treatment_integrable (by simpa [covariate] using hgint)]
    change (∫ o, treatment o ∂m.P) - ∫ o, m.g0 (covariate o) ∂m.P = 0
    rw [hgIntegral, sub_self]
  have htilt (t : ℝ) : Integrable (fun o ↦ Real.exp (t * eta p m o)) m.P :=
    integrable_exp_mul_of_luxemburg_sq hψ hetaMeas hclass.etaSubGaussian.1 t
  have hmgf (t : ℝ) :
      ∫ o, Real.exp (t * eta p m o) ∂m.P ≤
        Real.exp (4 * p.psieta ^ 2 * t ^ 2) :=
    integral_exp_mul_le_exp_four_mul_sq_of_luxemburg hψ hetaMeas hetaInt
      hclass.etaSubGaussian.1 hclass.etaSubGaussian.2 hcenter t
  have hetaSet : integrableExpSet (eta p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, htilt t]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    unfold treatmentMGF
    apply analyticAt_complexMGF
    simp [hetaSet]
  · unfold treatmentMGF
    simpa using (complexMGF_ofReal (X := eta p m) (μ := m.P) 0)
  · intro z
    calc
      ‖treatmentMGF p m z‖ ≤ mgf (eta p m) m.P z.re := norm_complexMGF_le_mgf
      _ = ∫ o, Real.exp (z.re * eta p m o) ∂m.P := rfl
      _ ≤ Real.exp (4 * p.psieta ^ 2 * z.re ^ 2) := hmgf z.re
      _ ≤ Real.exp (4 * p.psieta ^ 2 * ‖z‖ ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hre := Complex.abs_re_le_norm z
        have hsquares : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
          rw [← sq_abs]
          exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hre
        gcongr

/-- A separated cumulant forces a transform zero in the explicit disk. -/
-- @node: lem:zero-localization
lemma zero_localization (p : Parameters) (m : Model (Xspace := Xspace) p)
    (hpsi : EtaSubGaussian p m) (hsep : CumulantSeparation p m) :
    ∃ z : ℂ, ‖z‖ ≤ zeroRadius p ∧ treatmentMGF p m z = 0 := by
  have hk : 3 ≤ p.k := by
    rw [p.k_eq]
    simpa only [Nat.reduceAdd] using Nat.add_le_add_right p.r_ge_two 1
  have hψ : 0 < p.psieta := p.constants_pos.2.2.2.1
  have hδ : 0 < p.delta := p.constants_pos.2.2.2.2.2.1
  have hetaMeas : Measurable (eta p m) := by
    unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  have hmx : MeasurableSpace.comap (fun o : Obs Xspace ↦ o.1) inferInstance ≤
      (inferInstance : MeasurableSpace (Obs Xspace)) := by
    exact Measurable.comap_le
      (show Measurable (fun o : Obs Xspace ↦ o.1) from measurable_fst)
  have hgint : Integrable (fun o : Obs Xspace ↦ m.g0 (covariate o)) m.P := by
    exact MeasureTheory.integrable_condExp.congr m.g0_condMean
  have hetaInt : Integrable (eta p m) m.P := by
    exact m.treatment_integrable.sub hgint
  have hcenter : ∫ o, eta p m o ∂m.P = 0 := by
    have hgIntegral : (∫ o, m.g0 (covariate o) ∂m.P) =
        ∫ o, treatment o ∂m.P := by
      calc
        (∫ o, m.g0 (covariate o) ∂m.P) =
            ∫ o, (@MeasureTheory.condExp (Obs Xspace) ℝ
              (MeasurableSpace.comap (fun o : Obs Xspace ↦ o.1) inferInstance)
              inferInstance _ _ m.P (fun o ↦ o.2.1)) o ∂m.P :=
          integral_congr_ae m.g0_condMean.symm
        _ = ∫ o, treatment o ∂m.P := MeasureTheory.integral_condExp hmx
    change ∫ o, o.2.1 - m.g0 o.1 ∂m.P = 0
    rw [integral_sub m.treatment_integrable (by simpa [covariate] using hgint)]
    change (∫ o, treatment o ∂m.P) - ∫ o, m.g0 (covariate o) ∂m.P = 0
    rw [hgIntegral, sub_self]
  have htilt (t : ℝ) : Integrable (fun o ↦ Real.exp (t * eta p m o)) m.P :=
    integrable_exp_mul_of_luxemburg_sq hψ hetaMeas hpsi.1 t
  have hmgf (t : ℝ) :
      ∫ o, Real.exp (t * eta p m o) ∂m.P ≤
        Real.exp (4 * p.psieta ^ 2 * t ^ 2) :=
    integral_exp_mul_le_exp_four_mul_sq_of_luxemburg
      hψ hetaMeas hetaInt hpsi.1 hpsi.2 hcenter t
  have hetaSet : integrableExpSet (eta p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, htilt t]
  have hMan : AnalyticOnNhd ℂ (treatmentMGF p m) Set.univ := by
    intro z hz
    unfold treatmentMGF
    apply analyticAt_complexMGF
    simp [hetaSet]
  have hMzero : treatmentMGF p m 0 = 1 := by
    unfold treatmentMGF
    simpa using (complexMGF_ofReal (X := eta p m) (μ := m.P) 0)
  have hMbound (z : ℂ) :
      ‖treatmentMGF p m z‖ ≤ Real.exp (4 * p.psieta ^ 2 * ‖z‖ ^ 2) := by
    calc
      ‖treatmentMGF p m z‖ ≤ mgf (eta p m) m.P z.re := norm_complexMGF_le_mgf
      _ = ∫ o, Real.exp (z.re * eta p m o) ∂m.P := rfl
      _ ≤ Real.exp (4 * p.psieta ^ 2 * z.re ^ 2) := hmgf z.re
      _ ≤ Real.exp (4 * p.psieta ^ 2 * ‖z‖ ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hre := Complex.abs_re_le_norm z
        have hsquares : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
          rw [← sq_abs]
          exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hre
        gcongr
  have hR : 0 < zeroRadius p := by
    unfold zeroRadius Ak
    positivity
  by_contra hno
  push_neg at hno
  have hzeroFree : ∀ z ∈ ball (0 : ℂ) (zeroRadius p), treatmentMGF p m z ≠ 0 := by
    intro z hz hMz
    exact hno z (le_of_lt (by simpa [mem_ball, dist_zero_right] using hz)) hMz
  letI : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  let u : ℂ → ℝ := fun z ↦ Real.log ‖treatmentMGF p m z‖
  have hu : InnerProductSpace.HarmonicOnNhd u (ball (0 : ℂ) (zeroRadius p)) := by
    intro z hz
    exact (hMan z (mem_univ z)).harmonicAt_log_norm (hzeroFree z hz)
  obtain ⟨F, hFan, hFre⟩ := hu.exists_analyticOnNhd_ball_re_eq
  let f : ℂ → ℂ := fun z ↦ F z - F 0
  have hfAn : AnalyticOnNhd ℂ f (ball (0 : ℂ) (zeroRadius p)) := by
    exact hFan.sub analyticOnNhd_const
  have hF0re : (F 0).re = 0 := by
    have h := hFre (show (0 : ℂ) ∈ ball 0 (zeroRadius p) by simpa using hR)
    simpa [u, hMzero] using h
  have hfre : ∀ z ∈ ball (0 : ℂ) (zeroRadius p),
      (f z).re = Real.log ‖treatmentMGF p m z‖ := by
    intro z hz
    simp [f, hFre hz, hF0re, u]
  have hfzero : f 0 = 0 := by simp [f]
  have hmaps : MapsTo f (ball (0 : ℂ) (zeroRadius p))
      {w : ℂ | w.re ≤ 4 * p.psieta ^ 2 * zeroRadius p ^ 2} := by
    intro z hz
    rw [mem_setOf_eq, hfre z hz]
    have hnpos : 0 < ‖treatmentMGF p m z‖ := norm_pos_iff.mpr (hzeroFree z hz)
    apply (Real.log_le_iff_le_exp hnpos).mpr
    exact (hMbound z).trans (Real.exp_le_exp.mpr (by
      have hzR : ‖z‖ < zeroRadius p := by simpa [mem_ball, dist_zero_right] using hz
      have hsquares : ‖z‖ ^ 2 ≤ zeroRadius p ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hzR.le
      gcongr))
  have hinner : 0 < zeroRadius p / 2 := half_pos hR
  have hfDiffCl : DiffContOnCl ℂ f (ball (0 : ℂ) (zeroRadius p / 2)) := by
    apply hfAn.differentiableOn.diffContOnCl_ball
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right]
    linarith
  have hfSphere : ∀ z ∈ sphere (0 : ℂ) (zeroRadius p / 2),
      ‖f z‖ ≤ 8 * p.psieta ^ 2 * zeroRadius p ^ 2 := by
    intro z hz
    have hzinner : z ∈ ball (0 : ℂ) (zeroRadius p) := by
      rw [mem_ball, dist_zero_right]
      have : ‖z‖ = zeroRadius p / 2 := by simpa [mem_sphere, dist_zero_right] using hz
      linarith
    have hbc := Complex.borelCaratheodory_zero
      (f := f) (M := 4 * p.psieta ^ 2 * zeroRadius p ^ 2)
      (by positivity) hfAn.differentiableOn hmaps hR hzinner hfzero
    have hzNorm : ‖z‖ = zeroRadius p / 2 := by
      simpa [mem_sphere, dist_zero_right] using hz
    rw [hzNorm] at hbc
    convert hbc using 1 <;> field_simp <;> ring
  have hderivBound := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    p.k hinner hfDiffCl hfSphere
  have hlocalSlit : ∀ᶠ z in 𝓝 (0 : ℂ), treatmentMGF p m z ∈ Complex.slitPlane := by
    have htend : Tendsto (treatmentMGF p m) (𝓝 0) (𝓝 (treatmentMGF p m 0)) :=
      (hMan 0 (mem_univ 0)).continuousAt
    rw [hMzero] at htend
    exact htend (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  obtain ⟨ε, hε, hεslit⟩ : ∃ ε > 0, ball (0 : ℂ) ε ⊆
      {z | treatmentMGF p m z ∈ Complex.slitPlane} := by
    rw [Metric.eventually_nhds_iff] at hlocalSlit
    exact hlocalSlit
  let ε' := min ε (zeroRadius p)
  have hε' : 0 < ε' := lt_min hε hR
  have hlogAn : AnalyticOnNhd ℂ (fun z ↦ Complex.log (treatmentMGF p m z))
      (ball (0 : ℂ) ε') := by
    apply (hMan.mono (subset_univ _)).clog
    intro z hz
    exact hεslit (by
      rw [mem_ball, dist_zero_right] at hz ⊢
      exact hz.trans_le (min_le_left _ _))
  have hdiffAn : AnalyticOnNhd ℂ
      (fun z ↦ f z - Complex.log (treatmentMGF p m z)) (ball (0 : ℂ) ε') :=
    (hfAn.mono (by
      intro z hz
      rw [mem_ball, dist_zero_right] at hz ⊢
      exact hz.trans_le (min_le_right _ _))).sub hlogAn
  have hdiffRe : ∀ z ∈ ball (0 : ℂ) ε',
      (f z - Complex.log (treatmentMGF p m z)).re = 0 := by
    intro z hz
    rw [Complex.sub_re, Complex.log_re]
    rw [hfre z (by
      rw [mem_ball, dist_zero_right] at hz ⊢
      exact hz.trans_le (min_le_right _ _)), sub_self]
  obtain ⟨c, hc⟩ := hdiffAn.eq_const_of_re_eq_const hdiffRe isOpen_ball
    (Metric.isConnected_ball hε')
  have hc0 : c = 0 := by
    have h := hc 0 (show (0 : ℂ) ∈ ball 0 ε' by simpa using hε')
    simpa [hfzero, hMzero] using h.symm
  have heventEq : f =ᶠ[𝓝 (0 : ℂ)] fun z ↦ Complex.log (treatmentMGF p m z) := by
    filter_upwards [Metric.ball_mem_nhds 0 hε'] with z hz
    have h := hc z hz
    rw [hc0] at h
    simpa using sub_eq_zero.mp h
  have hkderiv : iteratedDeriv p.k f 0 =
      iteratedDeriv p.k (fun z ↦ Complex.log (treatmentMGF p m z)) 0 :=
    heventEq.iteratedDeriv_eq p.k
  rw [hkderiv] at hderivBound
  have hkappaBound : |kappaEta p m| ≤
      p.k.factorial * (8 * p.psieta ^ 2 * zeroRadius p ^ 2) /
        (zeroRadius p / 2) ^ p.k := by
    unfold kappaEta
    exact (Complex.abs_re_le_norm _).trans hderivBound
  have hkm2 : p.k - 2 ≠ 0 := by omega
  have hkadd : p.k - 2 + 2 = p.k := by omega
  have hcast : ((p.k - 2 : ℕ) : ℝ) = (p.k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ p.k)]
    norm_num
  have hbasePos : 0 < (2 ^ (p.k + 4) * p.k.factorial : ℝ) := by positivity
  have hratioPos : 0 < p.psieta ^ 2 / p.delta := div_pos (sq_pos_of_pos hψ) hδ
  have hAkPow : Ak p.k ^ (p.k - 2) =
      (2 ^ (p.k + 4) * p.k.factorial : ℝ) := by
    unfold Ak
    rw [← hcast]
    exact Real.rpow_inv_natCast_pow hbasePos.le hkm2
  have hratioPow :
      ((p.psieta ^ 2 / p.delta) ^ (((p.k : ℝ) - 2)⁻¹)) ^ (p.k - 2) =
        p.psieta ^ 2 / p.delta := by
    rw [← hcast]
    exact Real.rpow_inv_natCast_pow hratioPos.le hkm2
  have hRPow : zeroRadius p ^ (p.k - 2) =
      (2 ^ (p.k + 4) * p.k.factorial : ℝ) *
        (p.psieta ^ 2 / p.delta) := by
    unfold zeroRadius
    rw [mul_pow, hAkPow, hratioPow]
  have hRpowk : zeroRadius p ^ p.k =
      ((2 ^ (p.k + 4) * p.k.factorial : ℝ) *
        (p.psieta ^ 2 / p.delta)) * zeroRadius p ^ 2 := by
    conv_lhs => rw [← hkadd, pow_add, hRPow]
  have hcalc :
      p.k.factorial * (8 * p.psieta ^ 2 * zeroRadius p ^ 2) /
          (zeroRadius p / 2) ^ p.k = p.delta / 2 := by
    rw [div_pow, hRpowk]
    field_simp [hR.ne', hψ.ne', hδ.ne', Nat.factorial_ne_zero]
    ring
  have hkappaHalf : |kappaEta p m| ≤ p.delta / 2 := by
    simpa [hcalc] using hkappaBound
  have hkappaLt : |kappaEta p m| < p.delta := hkappaHalf.trans_lt (by linarith)
  exact (not_lt_of_ge hsep) hkappaLt

end CausalSmith.Stat.SaPlmCumulantConverse
