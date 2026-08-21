import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Local finite-product and disk estimates

These are the two bounded local complex-analysis builds used by the contour
bank. They are not external interfaces.
-/

noncomputable section

open Metric Set
open scoped Topology

namespace CausalSmith.Stat.SaPlmCumulantConverse

/-- One radius-`R` Blaschke factor. -/
def blaschkeFactor (R : ℝ) (a z : ℂ) : ℂ :=
  (R : ℂ) * (z - a) / ((R : ℂ) ^ 2 - star a * z)

/-- A finite radius-`R` Blaschke product. -/
def blaschkeProduct {N : ℕ} (R : ℝ) (a : Fin N → ℂ) (z : ℂ) : ℂ :=
  ∏ i, blaschkeFactor R (a i) z

/-- Inside the defining disk, a Blaschke factor vanishes exactly at its
listed zero. -/
lemma blaschkeFactor_eq_zero_iff (R : ℝ) (a z : ℂ)
    (hR : 0 < R) (ha : ‖a‖ < R) (hz : ‖z‖ < R) :
    blaschkeFactor R a z = 0 ↔ z = a := by
  have hden : (R : ℂ) ^ 2 - star a * z ≠ 0 := by
    intro hzero
    have heq : (R : ℂ) ^ 2 = star a * z := sub_eq_zero.mp hzero
    have hn := congrArg norm heq
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      norm_mul, norm_star] at hn
    have hprodlt : ‖a‖ * ‖z‖ < R * R := calc
      ‖a‖ * ‖z‖ ≤ R * ‖z‖ :=
        mul_le_mul_of_nonneg_right ha.le (norm_nonneg z)
      _ < R * R := mul_lt_mul_of_pos_left hz hR
    nlinarith
  unfold blaschkeFactor
  rw [div_eq_zero_iff]
  constructor
  · rintro (hnum | hden')
    · have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
      exact sub_eq_zero.mp ((mul_eq_zero.mp hnum).resolve_left hR')
    · exact False.elim (hden hden')
  · intro hza
    left
    simp [hza]

/-- On a [disk of positive radius](hyp:hR) whose [prescribed zero lies strictly
inside it](hyp:ha), at any [point of the closed disk](hyp:hz) the [modulus of the
Blaschke factor is at least the distance from the point to the zero, divided by
the radius plus the modulus of the point](goal). -/
lemma norm_blaschkeFactor_ge (R : ℝ) (a z : ℂ)
    (hR : 0 < R) (ha : ‖a‖ < R) (hz : ‖z‖ ≤ R) :
    ‖blaschkeFactor R a z‖ ≥ ‖z - a‖ / (R + ‖z‖) := by
  unfold blaschkeFactor
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hden : ‖(R : ℂ) ^ 2 - star a * z‖ ≤ R * (R + ‖z‖) := by
    calc
      ‖(R : ℂ) ^ 2 - star a * z‖
          ≤ ‖(R : ℂ) ^ 2‖ + ‖star a * z‖ := norm_sub_le _ _
      _ = R ^ 2 + ‖a‖ * ‖z‖ := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
          norm_mul, norm_star]
      _ ≤ R ^ 2 + R * ‖z‖ := by gcongr
      _ = R * (R + ‖z‖) := by ring
  have hsum : 0 < R + ‖z‖ := add_pos_of_pos_of_nonneg hR (norm_nonneg _)
  by_cases hza : z = a
  · simp [hza]
  have hdenne : (R : ℂ) ^ 2 - star a * z ≠ 0 := by
    intro hzero
    have heq : (R : ℂ) ^ 2 = star a * z := sub_eq_zero.mp hzero
    have hn := congrArg norm heq
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      norm_mul, norm_star] at hn
    nlinarith [norm_nonneg a, norm_nonneg z]
  have hdenpos : 0 < ‖(R : ℂ) ^ 2 - star a * z‖ := norm_pos_iff.mpr hdenne
  change ‖z - a‖ / (R + ‖z‖) ≤ R * ‖z - a‖ /
    ‖(R : ℂ) ^ 2 - star a * z‖
  rw [div_le_div_iff₀ hsum hdenpos]
  calc
    ‖z - a‖ * ‖(R : ℂ) ^ 2 - star a * z‖
        ≤ ‖z - a‖ * (R * (R + ‖z‖)) :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ = R * ‖z - a‖ * (R + ‖z‖) := by ring

/-- For a [disk of positive radius](hyp:hR) and a finite list of [prescribed
zeros all lying strictly inside it](hyp:ha), the corresponding finite Blaschke
product [is analytic on a neighbourhood of every point of the open disk](goal):
its only possible singularities sit outside the closed disk. -/
lemma analyticOnNhd_blaschkeProduct {N : ℕ} (R : ℝ) (a : Fin N → ℂ)
    (hR : 0 < R) (ha : ∀ i, ‖a i‖ < R) :
    AnalyticOnNhd ℂ (blaschkeProduct R a) (ball 0 R) := by
  intro z hz
  have hfac : ∀ i ∈ Finset.univ,
      AnalyticAt ℂ (fun w ↦ blaschkeFactor R (a i) w) z := by
    intro i hi
    apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · intro hzero
      have heq : (R : ℂ) ^ 2 = star (a i) * z := sub_eq_zero.mp hzero
      have hn := congrArg norm heq
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
        norm_mul, norm_star] at hn
      have hzle : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hz
      have hprodlt : ‖a i‖ * ‖z‖ < R * R := calc
        ‖a i‖ * ‖z‖ ≤ R * ‖z‖ :=
          mul_le_mul_of_nonneg_right (ha i).le (norm_nonneg z)
        _ < R * R := mul_lt_mul_of_pos_left hzle hR
      nlinarith
  change AnalyticAt ℂ (fun w ↦ ∏ i, blaschkeFactor R (a i) w) z
  have hp := Finset.analyticAt_prod Finset.univ hfac
  rw [show (∏ i ∈ Finset.univ, (fun w ↦ blaschkeFactor R (a i) w)) =
      (fun w ↦ ∏ i, blaschkeFactor R (a i) w) by
    funext w
    simp] at hp
  exact hp

/-- For a [disk of positive radius](hyp:hR) whose [prescribed zeros all lie
strictly inside it](hyp:ha), at any [point on the boundary circle](hyp:hz) the
finite Blaschke product [has modulus exactly one](goal). -/
lemma norm_blaschkeProduct_eq_one_of_mem_sphere {N : ℕ} (R : ℝ)
    (a : Fin N → ℂ) (hR : 0 < R) (ha : ∀ i, ‖a i‖ < R)
    {z : ℂ} (hz : z ∈ sphere 0 R) :
    ‖blaschkeProduct R a z‖ = 1 := by
  rw [blaschkeProduct, norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  unfold blaschkeFactor
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hzR : ‖z‖ = R := by simpa [mem_sphere, dist_zero_right] using hz
  have hzSq : Complex.normSq z = R ^ 2 := by
    rw [← Complex.sq_norm, hzR]
  have hden : ‖(R : ℂ) ^ 2 - star (a i) * z‖ = R * ‖z - a i‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hR.le (norm_nonneg _))]
    rw [Complex.sq_norm, mul_pow, Complex.sq_norm]
    rw [Complex.normSq_sub]
    simp only [map_pow, Complex.normSq_ofReal, Complex.normSq_mul,
      Complex.normSq_conj, map_mul, starRingEnd_apply, star_star]
    rw [Complex.normSq_sub]
    rw [hzSq]
    simp [Complex.star_def, Complex.normSq_apply, Complex.mul_re]
    have hRre : ((R : ℂ) ^ 2).re = R ^ 2 := by
      rw [pow_two]
      simp [Complex.mul_re]
      ring
    have hRim : ((R : ℂ) ^ 2).im = 0 := by
      rw [pow_two]
      simp [Complex.mul_im]
    rw [hRre, hRim]
    norm_num
    ring
  rw [hden]
  have hne : z ≠ a i := by
    intro hza
    rw [hza] at hzR
    linarith [ha i]
  rw [mul_div_assoc]
  field_simp [hR.ne', norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)]

/-- For a [disk of positive radius](hyp:hR) whose [prescribed zeros all lie
strictly inside it](hyp:ha), the finite Blaschke product [has modulus at most one
at the centre of the disk](goal), since each factor there has modulus at most
one. -/
lemma norm_blaschkeProduct_zero_le_one {N : ℕ} (R : ℝ)
    (a : Fin N → ℂ) (hR : 0 < R) (ha : ∀ i, ‖a i‖ < R) :
    ‖blaschkeProduct R a 0‖ ≤ 1 := by
  rw [blaschkeProduct]
  rw [show ‖∏ i, blaschkeFactor R (a i) 0‖ =
      Finset.univ.prod (fun i ↦ ‖blaschkeFactor R (a i) 0‖) by
        simpa using norm_prod Finset.univ (fun i ↦ blaschkeFactor R (a i) 0)]
  apply Finset.prod_le_one
  · intro i _
    exact norm_nonneg _
  · intro i _
    unfold blaschkeFactor
    rw [norm_div, norm_mul]
    simp only [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      mul_zero, sub_zero, norm_pow]
    have hR0 : R ≠ 0 := ne_of_gt hR
    rw [div_le_one (by positivity)]
    nlinarith [ha i]

/-- Harnack bound for the real part of a holomorphic function on a disk. -/
lemma harnack_re_le_of_nonneg_re (h : ℂ → ℂ) (R R1 : ℝ)
    (hR : 0 < R) (hR1 : 0 ≤ R1) (hsmall : R1 < R)
    (han : AnalyticOnNhd ℂ h (ball 0 R))
    (hnonneg : ∀ z ∈ ball (0 : ℂ) R, 0 ≤ (h z).re) :
    ∀ z : ℂ, ‖z‖ ≤ R1 →
      (h z).re ≤ ((R + R1) / (R - R1)) * (h 0).re := by
  intro z hz
  have hzR : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    exact hz.trans_lt hsmall
  have hzero : 0 ≤ (h 0).re := hnonneg 0 (by simpa using hR)
  by_cases hz0 : ‖z‖ = 0
  · have : z = 0 := norm_eq_zero.mp hz0
    subst z
    have hden : 0 < R - R1 := sub_pos.mpr hsmall
    have hfac : 1 ≤ (R + R1) / (R - R1) := by
      rw [le_div_iff₀ hden]
      linarith
    simpa using mul_le_mul_of_nonneg_right hfac hzero
  have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz0)
  have hdenz : 0 < R - ‖z‖ := sub_pos.mpr (mem_ball_zero_iff.mp hzR)
  have hden1 : 0 < R - R1 := sub_pos.mpr hsmall
  refine le_of_forall_pos_le_add fun eps heps ↦ ?_
  let delta : ℝ := eps * (R - ‖z‖) / (2 * ‖z‖)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdiff : DifferentiableOn ℂ (fun w ↦ h 0 - h w) (ball 0 R) := by
    intro w hw
    exact (differentiableAt_const (c := h 0) |>.sub
      (han w hw).differentiableAt).differentiableWithinAt
  have hmaps : MapsTo (fun w ↦ h 0 - h w) (ball 0 R)
      {w : ℂ | w.re ≤ (h 0).re + delta} := by
    intro w hw
    change (h 0).re - (h w).re ≤ (h 0).re + delta
    have := hnonneg w hw
    linarith
  have hbc := Complex.borelCaratheodory_zero (M := (h 0).re + delta)
    (add_pos_of_nonneg_of_pos hzero hdelta) hdiff hmaps hR hzR (by simp)
  have hre : (h z).re - (h 0).re ≤ ‖h 0 - h z‖ := by
    calc
      (h z).re - (h 0).re = -(h 0 - h z).re := by simp
      _ ≤ |(h 0 - h z).re| := neg_le_abs _
      _ ≤ ‖h 0 - h z‖ := Complex.abs_re_le_norm _
  have hraw : (h z).re ≤ (h 0).re +
      2 * ((h 0).re + delta) * ‖z‖ / (R - ‖z‖) := by
    linarith
  have hR1bound :
      (h 0).re + 2 * (h 0).re * ‖z‖ / (R - ‖z‖) ≤
        ((R + R1) / (R - R1)) * (h 0).re := by
    have hratio : (R + ‖z‖) / (R - ‖z‖) ≤ (R + R1) / (R - R1) := by
      rw [div_le_div_iff₀ hdenz hden1]
      nlinarith
    have hid : (h 0).re + 2 * (h 0).re * ‖z‖ / (R - ‖z‖) =
        ((R + ‖z‖) / (R - ‖z‖)) * (h 0).re := by
      field_simp
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hratio hzero
  have hdeltaTerm : 2 * delta * ‖z‖ / (R - ‖z‖) = eps := by
    dsimp [delta]
    field_simp
  calc
    (h z).re ≤ (h 0).re + 2 * ((h 0).re + delta) * ‖z‖ / (R - ‖z‖) := hraw
    _ = ((h 0).re + 2 * (h 0).re * ‖z‖ / (R - ‖z‖)) + eps := by
      rw [← hdeltaTerm]
      ring
    _ ≤ ((R + R1) / (R - R1)) * (h 0).re + eps := by
      simpa [add_comm] using add_le_add_right hR1bound eps

/-- Log-modulus lower bound for a bounded zero-free holomorphic function. -/
lemma log_norm_ge_of_zero_free_ball (f : ℂ → ℂ) (A R R1 : ℝ)
    (hR : 0 < R) (hR1 : 0 ≤ R1) (hsmall : R1 < R)
    (han : AnalyticOnNhd ℂ f (ball 0 R))
    (hzero : ∀ z ∈ ball (0 : ℂ) R, f z ≠ 0)
    (hupper : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ Real.exp A)
    (hone : 1 ≤ ‖f 0‖) :
    ∀ z : ℂ, ‖z‖ ≤ R1 →
      -(((R + R1) / (R - R1)) - 1) * A ≤ Real.log ‖f z‖ := by
  letI : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  let u : ℂ → ℝ := fun z ↦ A - Real.log ‖f z‖
  have hu : InnerProductSpace.HarmonicOnNhd u (ball (0 : ℂ) R) := by
    intro z hz
    exact InnerProductSpace.harmonicAt_const A |>.sub
      ((han z hz).harmonicAt_log_norm (hzero z hz))
  obtain ⟨H, hHan, hHre⟩ := hu.exists_analyticOnNhd_ball_re_eq
  have hHnonneg : ∀ z ∈ ball (0 : ℂ) R, 0 ≤ (H z).re := by
    intro z hz
    rw [show (H z).re = u z from hHre hz]
    dsimp [u]
    have hnormpos : 0 < ‖f z‖ := norm_pos_iff.mpr (hzero z hz)
    exact sub_nonneg.mpr ((Real.log_le_iff_le_exp hnormpos).mpr (hupper z hz))
  have hRzero : (0 : ℂ) ∈ ball 0 R := by simpa using hR
  have hlog0 : 0 ≤ Real.log ‖f 0‖ := Real.log_nonneg hone
  intro z hz
  have hHar := harnack_re_le_of_nonneg_re H R R1 hR hR1 hsmall hHan hHnonneg z hz
  rw [show (H z).re = u z from hHre (by
        rw [mem_ball_zero_iff]
        exact hz.trans_lt hsmall),
      show (H 0).re = u 0 from hHre hRzero] at hHar
  dsimp [u] at hHar
  have hfac : 0 ≤ (R + R1) / (R - R1) - 1 := by
    have hden : 0 < R - R1 := sub_pos.mpr hsmall
    rw [sub_nonneg, le_div_iff₀ hden]
    linarith
  nlinarith

end CausalSmith.Stat.SaPlmCumulantConverse
