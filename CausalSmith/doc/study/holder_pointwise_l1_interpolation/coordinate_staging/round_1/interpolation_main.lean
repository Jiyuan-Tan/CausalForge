/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation.Kernel
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation.Optimization
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation.Bias
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Hölder pointwise-to-local-mass interpolation

This file proves the reusable multivariate Hölder pointwise-to-local-mass
interpolation theorem used by nonparametric minimax lower bounds.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators Pointwise Manifold ContDiff

open HolderInterpolation.Internal

/- **Hölder pointwise ⟹ local `L¹` mass interpolation.** For `γ, M, r > 0` and a
cube neighbourhood `supBall x0 r ⊆ S`, there is a constant `c_H > 0` (depending
only on `γ, d, M, r`, uniform over the Hölder ball) such that for every `g` in the
standard `⌈γ⌉-1`-convention Hölder ball `HolderBallStd g γ M S`,
`c_H · |g x0|^{1 + d/γ} ≤ ∫_{supBall x0 r} |g|`.

This is the generic Tsybakov two-point / Assouad lower-bound primitive; it is not
tied to any estimand type and specializes (e.g. `g = τ_P - τ_Q`) across runs. -/
/-- A function in a multivariate Hölder ball that is large at an interior point
must have local absolute-integral mass at least a positive constant times that
pointwise magnitude to the power one plus dimension divided by smoothness. The
constant depends only on smoothness, dimension, the Hölder radius, and the local
cube radius, not on the particular function.

This is the generic Tsybakov two-point and Assouad lower-bound primitive, stated
without tying it to a causal estimand. -/
theorem holder_point_l1_interpolation {d : ℕ} {γ M r : ℝ} {x0 : Fin d → ℝ}
    {S : Set (Fin d → ℝ)}
    (hγ : 0 < γ) (hM : 0 < M) (hr : 0 < r) (hS : supBall x0 r ⊆ S) :
    ∃ cH : ℝ, 0 < cH ∧ ∀ g : (Fin d → ℝ) → ℝ,
      HolderBallStd g γ M S →
      cH * |g x0| ^ (1 + (d : ℝ) / γ) ≤ ∫ x in supBall x0 r, |g x| := by
  classical
  -- Milestone 1: the moment-cancelling 1-D kernel and its tensorization `K = prodKernel k d`.
  obtain ⟨k, hk_cont, hk_supp, hk_mass, hk_mom⟩ :=
    exists_moment_cancelling_kernel_1d (⌈γ⌉₊ - 1)
  -- `k` is bounded (continuous with support in `[-1,1]`).
  have hcs : HasCompactSupport k := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro x hx
    apply hk_supp
    rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · rw [not_le] at hx; rw [lt_abs]; right; linarith
    · rw [not_le] at hx; rw [lt_abs]; left; linarith
  obtain ⟨C0, hC0⟩ := hk_cont.bounded_above_of_compact_support hcs
  set B := max C0 0 with hBdef
  have hB : ∀ u, |k u| ≤ B :=
    fun u => le_trans (by simpa [Real.norm_eq_abs] using hC0 u) (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  -- `B > 0`: else `k ≡ 0`, contradicting unit mass.
  have hBpos : 0 < B := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hk0 : ∀ u, k u = 0 := by
        intro u
        have hle : |k u| ≤ 0 := by rw [h]; exact hB u
        exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun u _ => hk0 u)] at hk_mass
      simp at hk_mass
  have hBd : 0 < B ^ d := pow_pos hBpos d
  -- Milestone 2: the uniform bias constant `C`.
  obtain ⟨C, hC0nn, hCbias⟩ :=
    holder_taylor_bias hγ hM hr hS hk_cont hk_supp hk_mass hk_mom hB hB0
  -- Milestone 3: choose the optimal bandwidth constant `cstar`.
  have hMrpow_pos : 0 < M ^ ((1 : ℝ) / γ) := Real.rpow_pos_of_pos hM _
  have hC1 : (0 : ℝ) < C + 1 := by positivity
  have hden_pos : (0 : ℝ) < 4 * (C + 1) * M := by positivity
  have hb_pos : 0 < (1 / (4 * (C + 1) * M)) ^ ((1 : ℝ) / γ) :=
    Real.rpow_pos_of_pos (by positivity) _
  set cstar := min (r / M ^ ((1 : ℝ) / γ)) ((1 / (4 * (C + 1) * M)) ^ ((1 : ℝ) / γ))
    with hcstar_def
  have hcstar_pos : 0 < cstar := lt_min (div_pos hr hMrpow_pos) hb_pos
  refine ⟨(3 / (4 * B ^ d)) * cstar ^ d, ?_, ?_⟩
  · exact mul_pos (div_pos (by norm_num) (mul_pos (by norm_num) hBd)) (pow_pos hcstar_pos d)
  · intro g hg
    set Δ := |g x0| with hΔdef
    have hΔnn : 0 ≤ Δ := by rw [hΔdef]; exact abs_nonneg _
    rcases hΔnn.lt_or_eq with hΔpos | hΔ0
    swap
    · -- `Δ = 0`: RHS ≥ 0.
      rw [← hΔ0, Real.zero_rpow (by positivity : (1 : ℝ) + (d : ℝ) / γ ≠ 0), mul_zero]
      exact MeasureTheory.setIntegral_nonneg (measurableSet_supBall x0 r)
        (fun x _ => abs_nonneg _)
    · -- `Δ > 0`.
      have hx0S : x0 ∈ S := hS (mem_supBall_self x0 hr.le)
      have hΔM : Δ ≤ M := by
        have h0 := hg.2.1 0 (Nat.zero_le _) x0 hx0S
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
        rw [hΔdef]; exact h0
      set h := cstar * Δ ^ ((1 : ℝ) / γ) with hh_def
      have hh_pos : 0 < h := mul_pos hcstar_pos (Real.rpow_pos_of_pos hΔpos _)
      -- `h ≤ r`.
      have hh_le_r : h ≤ r := by
        rw [hh_def]
        have hΔle : Δ ^ ((1 : ℝ) / γ) ≤ M ^ ((1 : ℝ) / γ) :=
          Real.rpow_le_rpow hΔnn hΔM (one_div_nonneg.mpr hγ.le)
        have hne := hMrpow_pos.ne'
        calc cstar * Δ ^ ((1 : ℝ) / γ)
            ≤ cstar * M ^ ((1 : ℝ) / γ) := mul_le_mul_of_nonneg_left hΔle hcstar_pos.le
          _ ≤ (r / M ^ ((1 : ℝ) / γ)) * M ^ ((1 : ℝ) / γ) :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) hMrpow_pos.le
          _ = r := by field_simp
      -- Remainder `C·M·hᵞ ≤ Δ/4`.
      have hpow : (Δ ^ ((1 : ℝ) / γ)) ^ γ = Δ := by
        rw [← Real.rpow_mul hΔnn, one_div_mul_cancel hγ.ne', Real.rpow_one]
      have hhg : h ^ γ = cstar ^ γ * Δ := by
        rw [hh_def, Real.mul_rpow hcstar_pos.le (Real.rpow_nonneg hΔnn _), hpow]
      have hcstar_g : cstar ^ γ ≤ 1 / (4 * (C + 1) * M) := by
        have h2 : cstar ^ γ ≤ ((1 / (4 * (C + 1) * M)) ^ ((1 : ℝ) / γ)) ^ γ :=
          Real.rpow_le_rpow hcstar_pos.le (min_le_right _ _) hγ.le
        rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hγ.ne', Real.rpow_one] at h2
      have hrem : C * M * h ^ γ ≤ Δ / 4 := by
        have hge : C * M * cstar ^ γ ≤ C * M * (1 / (4 * (C + 1) * M)) :=
          mul_le_mul_of_nonneg_left hcstar_g (by positivity)
        have heq : C * M * (1 / (4 * (C + 1) * M)) = C / (4 * (C + 1)) := by
          field_simp
        rw [heq] at hge
        have hle14 : C / (4 * (C + 1)) ≤ 1 / 4 := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (C + 1))]; nlinarith [hC0nn]
        have hCMc : C * M * cstar ^ γ ≤ 1 / 4 := le_trans hge hle14
        rw [hhg]
        calc C * M * (cstar ^ γ * Δ) = (C * M * cstar ^ γ) * Δ := by ring
          _ ≤ (1 / 4) * Δ := mul_le_mul_of_nonneg_right hCMc hΔnn
          _ = Δ / 4 := by ring
      -- Bias and change-of-variables combine into the `l1` hypothesis.
      have hbias := hCbias g hg h hh_pos hh_le_r
      have hbias' : |g x0 - ∫ u in supBall (0 : Fin d → ℝ) 1,
          prodKernel k d u * g (x0 + h • u)| ≤ Δ / 4 := le_trans hbias hrem
      have hVlow : 3 * Δ / 4 ≤ |∫ u in supBall (0 : Fin d → ℝ) 1,
          prodKernel k d u * g (x0 + h • u)| := by
        have h1 := abs_sub_abs_le_abs_sub (g x0)
          (∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u))
        rw [← hΔdef] at h1
        linarith [le_trans h1 hbias']
      have hsm := smoothed_abs_le hr hS (prodKernel_abs_le hB) g hg h hh_pos hh_le_r
      have hbound : 3 * Δ / 4 ≤ B ^ d * h⁻¹ ^ d * ∫ x in supBall x0 r, |g x| :=
        le_trans hVlow hsm
      have hfin := l1_lower_of_bias_bound hγ hBd hΔpos hcstar_pos hh_def hbound
      rw [hΔdef]
      exact hfin


end Causalean.Stat.Nonparametric
