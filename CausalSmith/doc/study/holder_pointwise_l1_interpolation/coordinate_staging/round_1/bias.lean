/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation.Kernel
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation.Taylor
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Kernel bias bound for multivariate Hölder functions

Internal implementation layer for the multivariate Hölder pointwise-to-local-mass interpolation theorem.
-/

namespace Causalean.Stat.Nonparametric.HolderInterpolation.Internal

open MeasureTheory
open scoped BigOperators Pointwise Manifold ContDiff

/-- A moment-cancelling product kernel approximates any multivariate Hölder
function at an interior point with an error bounded by a constant times the
Hölder radius and the bandwidth raised to the smoothness exponent. -/
lemma holder_taylor_bias {d : ℕ} {γ M r : ℝ} {x0 : Fin d → ℝ} {S : Set (Fin d → ℝ)}
    {k : ℝ → ℝ} {B : ℝ}
    (hγ : 0 < γ) (hM : 0 < M) (hr : 0 < r) (hS : supBall x0 r ⊆ S)
    (hk_cont : Continuous k) (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mass : (∫ u in Set.Icc (-1 : ℝ) 1, k u) = 1)
    (hk_mom : ∀ j : ℕ, 1 ≤ j → j ≤ ⌈γ⌉₊ - 1 →
      (∫ u in Set.Icc (-1 : ℝ) 1, u ^ j * k u) = 0)
    (hB : ∀ u : ℝ, |k u| ≤ B) (hB0 : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : (Fin d → ℝ) → ℝ, HolderBallStd g γ M S →
      ∀ h : ℝ, 0 < h → h ≤ r →
        |g x0 - ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u)|
          ≤ C * M * h ^ γ := by
  classical
  have hfacne : (Nat.factorial (⌈γ⌉₊ - 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  refine ⟨B ^ d * (volume (supBall (0 : Fin d → ℝ) 1)).toReal / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ),
    ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (pow_nonneg hB0 d) ENNReal.toReal_nonneg) (Nat.cast_nonneg _)
  · intro g hg h hh hhr
    have hKcont : Continuous (prodKernel k d) := prodKernel_continuous hk_cont
    have hg_contS : ContinuousOn g S := hg.1.continuousOn
    -- open cube of radius `r` around `x0`, contained in `S`.
    set U : Set (Fin d → ℝ) := {x | ∀ i, |x i - x0 i| < r} with hU_def
    have hUopen : IsOpen U := by
      rw [hU_def, Set.setOf_forall]
      exact isOpen_iInter_of_finite (fun i => isOpen_lt (by fun_prop) continuous_const)
    have hUS : U ⊆ S := by
      intro x hx
      simp only [hU_def, Set.mem_setOf_eq] at hx
      exact hS (fun i => le_of_lt (hx i))
    -- Taylor polynomial in `u`.
    set P : (Fin d → ℝ) → ℝ := fun u => ∑ j ∈ Finset.range (⌈γ⌉₊ - 1 + 1),
        (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j g x0 (fun _ => h • u) with hP_def
    have hDcont : ∀ j : ℕ,
        Continuous (fun u : Fin d → ℝ => iteratedFDeriv ℝ j g x0 (fun _ => h • u)) := by
      intro j
      exact (iteratedFDeriv ℝ j g x0).cont.comp
        (continuous_pi (fun _ => continuous_id.const_smul h))
    have hPcont : Continuous P := by
      rw [hP_def]
      exact continuous_finset_sum _ (fun j _ => continuous_const.mul (hDcont j))
    have hmaps : Set.MapsTo (fun u => x0 + h • u) (supBall (0 : Fin d → ℝ) 1) S := by
      intro u hu
      refine hS (fun i => ?_)
      have he : (x0 + h • u) i - x0 i = h * u i := by simp [Pi.add_apply, Pi.smul_apply]
      rw [he, abs_mul, abs_of_pos hh]
      have hui : |u i| ≤ 1 := by simpa using hu i
      calc h * |u i| ≤ h * 1 := mul_le_mul_of_nonneg_left hui hh.le
        _ = h := mul_one h
        _ ≤ r := hhr
    have hgcomp : ContinuousOn (fun u => g (x0 + h • u)) (supBall (0 : Fin d → ℝ) 1) :=
      hg_contS.comp (by fun_prop) hmaps
    have hI_g : IntegrableOn (fun u => prodKernel k d u * g (x0 + h • u))
        (supBall (0 : Fin d → ℝ) 1) :=
      (hKcont.continuousOn.mul hgcomp).integrableOn_compact (isCompact_supBall 0 1)
    have hI_P : IntegrableOn (fun u => prodKernel k d u * P u) (supBall (0 : Fin d → ℝ) 1) :=
      (hKcont.mul hPcont).continuousOn.integrableOn_compact (isCompact_supBall 0 1)
    -- Mass identity: `∫ K·P = g x0`.
    have hmass_P : ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * P u = g x0 := by
      have hzero : ∀ b ∈ Finset.range (⌈γ⌉₊ - 1 + 1), b ≠ 0 →
          (∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u *
            ((1 / (Nat.factorial b : ℝ)) * iteratedFDeriv ℝ b g x0 (fun _ => h • u))) = 0 := by
        intro b hb hb0
        have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
        have hbm : b ≤ ⌈γ⌉₊ - 1 := by have := Finset.mem_range.mp hb; omega
        have hre : ∀ u : Fin d → ℝ, prodKernel k d u *
              ((1 / (Nat.factorial b : ℝ)) * iteratedFDeriv ℝ b g x0 (fun _ => h • u))
            = (1 / (Nat.factorial b : ℝ)) *
              (prodKernel k d u * iteratedFDeriv ℝ b g x0 (fun _ => h • u)) := fun u => by ring
        simp_rw [hre]
        rw [MeasureTheory.integral_const_mul,
          integral_diagonal_taylor_term_cube hk_cont hk_supp hk_mom g x0 h hb1 hbm, mul_zero]
      have hsum : ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * P u
          = ∑ j ∈ Finset.range (⌈γ⌉₊ - 1 + 1), ∫ u in supBall (0 : Fin d → ℝ) 1,
              prodKernel k d u *
                ((1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j g x0 (fun _ => h • u)) := by
        simp only [hP_def, Finset.mul_sum]
        refine MeasureTheory.integral_finset_sum _ (fun j _ => ?_)
        exact ((hKcont.mul (continuous_const.mul (hDcont j))).continuousOn).integrableOn_compact
          (isCompact_supBall 0 1)
      rw [hsum, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos _)) hzero]
      simp only [Nat.factorial_zero, Nat.cast_one, one_div, inv_one, one_mul,
        iteratedFDeriv_zero_apply]
      rw [MeasureTheory.integral_mul_const, prodKernel_mass_cube hk_supp hk_mass, one_mul]
    -- Rewrite the bias as `∫ K·(P - g(x0+h•u))`.
    have hbias_eq : g x0 - ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u)
        = ∫ u in supBall (0 : Fin d → ℝ) 1,
            (prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u)) := by
      rw [MeasureTheory.integral_sub hI_P hI_g, hmass_P]
    -- Per-point bound (a.e. on the cube via the open interior).
    have hpp : ∀ᵐ u ∂(volume.restrict (supBall (0 : Fin d → ℝ) 1)),
        |prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u)|
          ≤ B ^ d * ((M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) * ‖h • u‖ ^ γ) := by
      filter_upwards [ae_lt_one_on_cube] with u hu
      have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x0 + t • (h • u) ∈ U := by
        intro t ht
        simp only [hU_def, Set.mem_setOf_eq]
        intro i
        have he : (x0 + t • (h • u)) i - x0 i = t * (h * u i) := by
          simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
        rw [he, abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_pos hh]
        have hb : h * |u i| < h := by simpa using mul_lt_mul_of_pos_left (hu i) hh
        calc t * (h * |u i|) ≤ 1 * (h * |u i|) :=
              mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hh.le (abs_nonneg _))
          _ = h * |u i| := one_mul _
          _ < h := hb
          _ ≤ r := hhr
      have hcrux := holder_line_taylor hγ hg hUopen hUS x0 (h • u) hseg
      have hPeq : (∑ j ∈ Finset.range (⌈γ⌉₊ - 1 + 1),
          (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j g x0 (fun _ => h • u)) = P u := by
        rw [hP_def]
      rw [hPeq] at hcrux
      have hfactor : |prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u)|
          = |prodKernel k d u| * |P u - g (x0 + h • u)| := by rw [← mul_sub, abs_mul]
      rw [hfactor]
      refine mul_le_mul (prodKernel_abs_le hB u) ?_ (abs_nonneg _) (pow_nonneg hB0 d)
      rw [abs_sub_comm]; exact hcrux
    -- Integrability of the pointwise bound.
    have hbound_cont : Continuous (fun u : Fin d → ℝ =>
        B ^ d * ((M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) * ‖h • u‖ ^ γ)) :=
      continuous_const.mul (continuous_const.mul
        (((continuous_id.const_smul h).norm).rpow_const (fun _ => Or.inr hγ.le)))
    -- `∫ ‖h•u‖^γ ≤ vol(cube)·h^γ`.
    have hnorm_int : ∫ u in supBall (0 : Fin d → ℝ) 1, ‖h • u‖ ^ γ
        ≤ (volume (supBall (0 : Fin d → ℝ) 1)).toReal * h ^ γ := by
      have hle : ∫ u in supBall (0 : Fin d → ℝ) 1, ‖h • u‖ ^ γ
          ≤ ∫ _u in supBall (0 : Fin d → ℝ) 1, h ^ γ := by
        refine MeasureTheory.integral_mono_of_nonneg
          (ae_of_all _ (fun u => Real.rpow_nonneg (norm_nonneg _) _))
          (continuous_const.continuousOn.integrableOn_compact (isCompact_supBall 0 1)) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_supBall 0 1)] with u hu
        have hunorm : ‖u‖ ≤ 1 := by
          rw [pi_norm_le_iff_of_nonneg (by norm_num)]
          intro i; simpa using hu i
        have hhu : ‖h • u‖ ≤ h := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
          calc h * ‖u‖ ≤ h * 1 := mul_le_mul_of_nonneg_left hunorm hh.le
            _ = h := mul_one h
        exact Real.rpow_le_rpow (norm_nonneg _) hhu hγ.le
      rwa [MeasureTheory.setIntegral_const, smul_eq_mul] at hle
    -- Assemble.
    rw [hbias_eq]
    calc |∫ u in supBall (0 : Fin d → ℝ) 1,
            (prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u))|
        = ‖∫ u in supBall (0 : Fin d → ℝ) 1,
            (prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u))‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ u in supBall (0 : Fin d → ℝ) 1,
            ‖prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ u in supBall (0 : Fin d → ℝ) 1,
            |prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u)| := by
          simp_rw [Real.norm_eq_abs]
      _ ≤ ∫ u in supBall (0 : Fin d → ℝ) 1,
            B ^ d * ((M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) * ‖h • u‖ ^ γ) :=
          MeasureTheory.integral_mono_of_nonneg (ae_of_all _ (fun u => abs_nonneg _))
            (hbound_cont.continuousOn.integrableOn_compact (isCompact_supBall 0 1)) hpp
      _ = B ^ d * ((M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) *
            ∫ u in supBall (0 : Fin d → ℝ) 1, ‖h • u‖ ^ γ) := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ ≤ B ^ d * ((M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) *
            ((volume (supBall (0 : Fin d → ℝ) 1)).toReal * h ^ γ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hB0 d)
          exact mul_le_mul_of_nonneg_left hnorm_int
            (div_nonneg hM.le (Nat.cast_nonneg _))
      _ = B ^ d * (volume (supBall (0 : Fin d → ℝ) 1)).toReal / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)
            * M * h ^ γ := by
          field_simp

end Causalean.Stat.Nonparametric.HolderInterpolation.Internal
