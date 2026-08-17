/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module

public import Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.ArgumentPrinciple
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Straight-line homotopy invariance and Rouché's theorem on a circle

This module proves that the normalized logarithmic-derivative count is unchanged
along a boundary-zero-free straight-line homotopy, then derives Rouché's
standard strict-boundary comparison theorem.
-/

@[expose] public section

noncomputable section

open Metric Set
open scoped Topology

namespace Causalean.Mathlib.Analysis.ArgumentPrincipleCircle

/-- This is the straight-line interpolation between two complex-valued functions, indexed from
the first endpoint at time zero to the second endpoint at time one. -/
def straightLineHomotopy (f g : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (1 - (t : ℂ)) * f z + (t : ℂ) * g z

/-- Two analytic complex functions have equal normalized logarithmic-derivative circle integrals
when every function on their straight-line interpolation is nonzero on the boundary circle. -/
theorem normalizedLogDerivCircleIntegral_eq_of_straightLineHomotopy {f g : ℂ → ℂ}
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hboundary : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere c R,
      straightLineHomotopy f g t z ≠ 0) :
    normalizedLogDerivCircleIntegral f c R =
      normalizedLogDerivCircleIntegral g c R := by
  let J : ℝ → ℂ := fun t ↦
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∫ θ in Icc 0 (2 * Real.pi), deriv (circleMap c R) θ *
        (((1 - (t : ℂ)) * deriv f (circleMap c R θ) +
            (t : ℂ) * deriv g (circleMap c R θ)) /
          straightLineHomotopy f g t (circleMap c R θ))
  have hf_circle : Continuous (fun θ : ℝ ↦ f (circleMap c R θ)) := by
    simpa only [Function.comp_def] using
      hf.continuousOn.comp_continuous (continuous_circleMap c R)
        (fun θ ↦ circleMap_mem_closedBall c hR.le θ)
  have hg_circle : Continuous (fun θ : ℝ ↦ g (circleMap c R θ)) := by
    simpa only [Function.comp_def] using
      hg.continuousOn.comp_continuous (continuous_circleMap c R)
        (fun θ ↦ circleMap_mem_closedBall c hR.le θ)
  have hdf_circle : Continuous (fun θ : ℝ ↦ deriv f (circleMap c R θ)) := by
    simpa only [Function.comp_def] using
      hf.deriv.continuousOn.comp_continuous (continuous_circleMap c R)
        (fun θ ↦ circleMap_mem_closedBall c hR.le θ)
  have hdg_circle : Continuous (fun θ : ℝ ↦ deriv g (circleMap c R θ)) := by
    simpa only [Function.comp_def] using
      hg.deriv.continuousOn.comp_continuous (continuous_circleMap c R)
        (fun θ ↦ circleMap_mem_closedBall c hR.le θ)
  have hJ_restrict : Continuous (Set.restrict (Icc (0 : ℝ) 1) J) := by
    apply Continuous.const_mul
    apply continuous_parametric_integral_of_continuous
    · have ht : Continuous
          (fun a : {t : ℝ // t ∈ Icc 0 1} × ℝ ↦ (a.1.val : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
      apply Continuous.mul
      · simp only [deriv_circleMap]
        fun_prop
      · apply Continuous.div
        · exact ((continuous_const.sub ht).mul (hdf_circle.comp continuous_snd)).add
            (ht.mul (hdg_circle.comp continuous_snd))
        · have hcont : Continuous fun a : {t : ℝ // t ∈ Icc 0 1} × ℝ ↦
              (1 - (a.1.val : ℂ)) * f (circleMap c R a.2) +
                (a.1.val : ℂ) * g (circleMap c R a.2) :=
            ((continuous_const.sub ht).mul (hf_circle.comp continuous_snd)).add
              (ht.mul (hg_circle.comp continuous_snd))
          simpa only [straightLineHomotopy] using hcont
        · rintro ⟨⟨t, ht⟩, θ⟩
          exact hboundary t ht (circleMap c R θ) (circleMap_mem_sphere c hR.le θ)
    · exact isCompact_Icc
  have hJ_cont : ContinuousOn J (Icc (0 : ℝ) 1) :=
    continuousOn_iff_continuous_restrict.mpr hJ_restrict
  have hderiv (t : ℝ) (z : ℂ) (hz : z ∈ sphere c R) :
      deriv (straightLineHomotopy f g t) z =
        (1 - (t : ℂ)) * deriv f z + (t : ℂ) * deriv g z := by
    have hzf : DifferentiableAt ℂ f z :=
      (hf z (sphere_subset_closedBall hz)).differentiableAt
    have hzg : DifferentiableAt ℂ g z :=
      (hg z (sphere_subset_closedBall hz)).differentiableAt
    rw [show straightLineHomotopy f g t =
        (fun w ↦ (1 - (t : ℂ)) * f w) + (fun w ↦ (t : ℂ) * g w) by rfl]
    rw [deriv_add (hzf.const_mul _) (hzg.const_mul _),
      deriv_const_mul _ hzf, deriv_const_mul _ hzg]
  have hJ_eq (t : ℝ) :
      J t = normalizedLogDerivCircleIntegral (straightLineHomotopy f g t) c R := by
    dsimp only [J]
    rw [normalizedLogDerivCircleIntegral, circleIntegral_def_Icc]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ
    simp only [smul_eq_mul, logDeriv_apply]
    rw [hderiv t (circleMap c R θ) (circleMap_mem_sphere c hR.le θ)]
  have hanalytic (t : ℝ) :
      AnalyticOnNhd ℂ (straightLineHomotopy f g t) (closedBall c R) := by
    exact (analyticOnNhd_const.mul hf).add (analyticOnNhd_const.mul hg)
  have hJ_nat (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      J t = (zeroMultiplicityCount (straightLineHomotopy f g t) c R : ℂ) :=
    (hJ_eq t).trans (argumentPrinciple_circle hR (hanalytic t) (hboundary t ht))
  have hf_boundary : ∀ z ∈ sphere c R, f z ≠ 0 := by
    intro z hz
    simpa [straightLineHomotopy] using hboundary 0 (by simp) z hz
  have hg_boundary : ∀ z ∈ sphere c R, g z ≠ 0 := by
    intro z hz
    simpa [straightLineHomotopy] using hboundary 1 (by simp) z hz
  let nf := zeroMultiplicityCount f c R
  let ng := zeroMultiplicityCount g c R
  have hJ0 : J 0 = (nf : ℂ) := by
    have h := hJ_nat 0 (by simp)
    have hH : straightLineHomotopy f g 0 = f := by
      funext z
      simp [straightLineHomotopy]
    rw [hH] at h
    simpa only [nf] using h
  have hJ1 : J 1 = (ng : ℂ) := by
    have h := hJ_nat 1 (by simp)
    have hH : straightLineHomotopy f g 1 = g := by
      funext z
      simp [straightLineHomotopy]
    rw [hH] at h
    simpa only [ng] using h
  have hK_cont : ContinuousOn (fun t ↦ (J t).re) (Icc (0 : ℝ) 1) :=
    Complex.continuous_re.comp_continuousOn hJ_cont
  have hcounts : nf = ng := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hy : (nf : ℝ) + 1 / 2 ∈ Icc ((J 0).re) ((J 1).re) := by
        rw [hJ0, hJ1]
        simp only [Complex.natCast_re]
        constructor
        · norm_num
        · have hgap : nf + 1 ≤ ng := Nat.add_one_le_iff.mpr hlt
          have hgap' : (nf + 1 : ℕ) ≤ (ng : ℝ) := by exact_mod_cast hgap
          push_cast at hgap'
          linarith
      obtain ⟨t, ht, heq⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
        hK_cont hy
      have hnat := congrArg Complex.re (hJ_nat t ht)
      have hreal :
          (zeroMultiplicityCount (straightLineHomotopy f g t) c R : ℝ) =
            (nf : ℝ) + 1 / 2 := by
        simpa only [Complex.natCast_re] using hnat.symm.trans heq
      have hlo : nf < zeroMultiplicityCount (straightLineHomotopy f g t) c R := by
        exact_mod_cast (show (nf : ℝ) <
          (zeroMultiplicityCount (straightLineHomotopy f g t) c R : ℝ) by linarith)
      have hhi : zeroMultiplicityCount (straightLineHomotopy f g t) c R < nf + 1 := by
        exact_mod_cast (show
          (zeroMultiplicityCount (straightLineHomotopy f g t) c R : ℝ) < (nf + 1 : ℕ) by
            push_cast
            linarith)
      omega
    · have hy : (ng : ℝ) + 1 / 2 ∈ Icc ((J 1).re) ((J 0).re) := by
        rw [hJ0, hJ1]
        simp only [Complex.natCast_re]
        constructor
        · norm_num
        · have hgap : ng + 1 ≤ nf := Nat.add_one_le_iff.mpr hgt
          have hgap' : (ng + 1 : ℕ) ≤ (nf : ℝ) := by exact_mod_cast hgap
          push_cast at hgap'
          linarith
      obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
        hK_cont hy
      have hnat := congrArg Complex.re (hJ_nat t ht)
      have hreal :
          (zeroMultiplicityCount (straightLineHomotopy f g t) c R : ℝ) =
            (ng : ℝ) + 1 / 2 := by
        simpa only [Complex.natCast_re] using hnat.symm.trans heq
      have hlo : ng < zeroMultiplicityCount (straightLineHomotopy f g t) c R := by
        exact_mod_cast (show (ng : ℝ) <
          (zeroMultiplicityCount (straightLineHomotopy f g t) c R : ℝ) by linarith)
      have hhi : zeroMultiplicityCount (straightLineHomotopy f g t) c R < ng + 1 := by
        exact_mod_cast (show
          (zeroMultiplicityCount (straightLineHomotopy f g t) c R : ℝ) < (ng + 1 : ℕ) by
            push_cast
            linarith)
      omega
  calc
    normalizedLogDerivCircleIntegral f c R = (nf : ℂ) := by
      simpa [nf] using argumentPrinciple_circle hR hf hf_boundary
    _ = (ng : ℂ) := by rw [hcounts]
    _ = normalizedLogDerivCircleIntegral g c R := by
      simpa [ng] using (argumentPrinciple_circle hR hg hg_boundary).symm

/-- Two analytic complex functions have the same multiplicity-weighted number of interior zeros
when every function on their straight-line interpolation is nonzero on the boundary circle. -/
theorem zeroMultiplicityCount_eq_of_straightLineHomotopy {f g : ℂ → ℂ}
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hboundary : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere c R,
      straightLineHomotopy f g t z ≠ 0) :
    zeroMultiplicityCount f c R = zeroMultiplicityCount g c R := by
  have hf_boundary : ∀ z ∈ sphere c R, f z ≠ 0 := by
    intro z hz
    simpa [straightLineHomotopy] using hboundary 0 (by simp) z hz
  have hg_boundary : ∀ z ∈ sphere c R, g z ≠ 0 := by
    intro z hz
    simpa [straightLineHomotopy] using hboundary 1 (by simp) z hz
  have hcast : (zeroMultiplicityCount f c R : ℂ) =
      (zeroMultiplicityCount g c R : ℂ) := by
    rw [← argumentPrinciple_circle hR hf hf_boundary,
      normalizedLogDerivCircleIntegral_eq_of_straightLineHomotopy hR hf hg hboundary,
      argumentPrinciple_circle hR hg hg_boundary]
  exact_mod_cast hcast

/-- **Rouché's theorem for a circle.** If the boundary discrepancy between two analytic complex
functions is strictly smaller than the boundary magnitude of the first, they have the same
multiplicity-weighted number of zeros inside the disk. -/
theorem rouche_circle {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hrouche : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    zeroMultiplicityCount f c R = zeroMultiplicityCount g c R := by
  apply zeroMultiplicityCount_eq_of_straightLineHomotopy hR hf hg
  intro t ht z hz hzero
  have hzero' : f z + (t : ℂ) * (g z - f z) = 0 := by
    rw [← hzero]
    simp only [straightLineHomotopy]
    ring
  have hfeq : f z = -(t : ℂ) * (g z - f z) := by
    linear_combination hzero'
  have hnorm : ‖f z‖ = t * ‖g z - f z‖ := by
    calc
      ‖f z‖ = ‖-(t : ℂ) * (g z - f z)‖ := congrArg norm hfeq
      _ = t * ‖g z - f z‖ := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hle : ‖f z‖ ≤ ‖g z - f z‖ := by
    rw [hnorm]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (g z - f z))
  exact (not_lt_of_ge hle) (hrouche z hz)

/-- Under Rouché's strict boundary inequality, two analytic complex functions have equal
normalized logarithmic-derivative circle integrals. -/
theorem normalizedLogDerivCircleIntegral_eq_of_rouche {f g : ℂ → ℂ}
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hrouche : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    normalizedLogDerivCircleIntegral f c R =
      normalizedLogDerivCircleIntegral g c R := by
  have hf_boundary : ∀ z ∈ sphere c R, f z ≠ 0 := by
    intro z hz hzero
    have h := hrouche z hz
    rw [hzero] at h
    have h' : ‖g z‖ < 0 := by simpa using h
    exact (not_lt_of_ge (norm_nonneg _)) h'
  have hg_boundary : ∀ z ∈ sphere c R, g z ≠ 0 := by
    intro z hz hzero
    have := hrouche z hz
    rw [hzero, zero_sub, norm_neg] at this
    exact (lt_irrefl _) this
  rw [argumentPrinciple_circle hR hf hf_boundary,
    argumentPrinciple_circle hR hg hg_boundary,
    rouche_circle hR hf hg hrouche]

end Causalean.Mathlib.Analysis.ArgumentPrincipleCircle
