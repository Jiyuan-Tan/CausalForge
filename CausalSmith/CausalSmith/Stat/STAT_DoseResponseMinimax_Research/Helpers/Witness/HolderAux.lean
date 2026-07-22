/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax lower bound: generic Hölder-ball and cube helpers

Pure, reusable facts about `HolderBall1D`/`HolderBallND` (radius monotonicity,
constant functions) and the covariate cube `[0,1]^d`, used to assemble the witness's
model-class membership. None of these touch the data law; they are the generic
analytic plumbing shared by the membership proof.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Base
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory
open scoped ENNReal

/-- The all-zero covariate vector lies in the unit covariate cube in every dimension. -/
lemma zero_mem_cube {d : ℕ} : (fun _ : Fin d => (0 : ℝ)) ∈ cube d := by
  intro i; exact ⟨le_rfl, zero_le_one⟩

/-- If the treatment-window radius is nonnegative, the window contains its center point. -/
lemma center_mem_doseWindow {t0 eps0 : ℝ} (heps : 0 ≤ eps0) :
    t0 ∈ doseWindow t0 eps0 := by
  constructor <;> linarith

/-- The unit covariate cube is compact in every finite dimension. -/
lemma isCompact_cube (d : ℕ) : IsCompact (cube d) := by
  have hEq : cube d = Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => (1 : ℝ)) := by
    ext x
    exact ⟨fun hx => ⟨fun i => (hx i).1, fun i => (hx i).2⟩, fun hx i => ⟨hx.1 i, hx.2 i⟩⟩
  rw [hEq]; exact isCompact_Icc

/-- The unit covariate cube has finite Lebesgue volume in every finite dimension. -/
lemma volume_cube_lt_top (d : ℕ) : volume (cube d) < ∞ :=
  (isCompact_cube d).measure_lt_top

/-- A univariate function that belongs to a Hölder ball of a given radius also belongs
to any larger-radius Hölder ball of the same smoothness order on the same set. -/
lemma HolderBall1D_mono_radius (f : ℝ → ℝ) {order M M' : ℝ} {S : Set ℝ}
    (h : HolderBall1D f order M S) (hMM : M ≤ M') : HolderBall1D f order M' S := by
  rcases h with ⟨hcont, hder, hhol⟩
  refine ⟨hcont, fun j hj x hx => (hder j hj x hx).trans hMM, fun x hx y hy => ?_⟩
  have hr : 0 ≤ |x - y| ^ (order - ((⌈order⌉₊ - 1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (abs_nonneg _) _
  exact (hhol x hx y hy).trans (mul_le_mul_of_nonneg_right hMM hr)

/-- A multivariate function that belongs to a Hölder ball of a given radius also belongs
to any larger-radius Hölder ball of the same smoothness order on the same set. -/
lemma HolderBallND_mono_radius {d : ℕ} (f : (Fin d → ℝ) → ℝ) {order M M' : ℝ}
    {S : Set (Fin d → ℝ)} (h : HolderBallND f order M S) (hMM : M ≤ M') :
    HolderBallND f order M' S := by
  rcases h with ⟨hcont, hder, hhol⟩
  refine ⟨hcont, fun j hj x hx => (hder j hj x hx).trans hMM, fun x hx y hy => ?_⟩
  have hr : 0 ≤ ‖x - y‖ ^ (order - ((⌈order⌉₊ - 1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (norm_nonneg _) _
  exact (hhol x hx y hy).trans (mul_le_mul_of_nonneg_right hMM hr)

/-- A constant multivariate function belongs to a Hölder ball whenever the absolute
size of the constant is at most the ball radius and the radius is nonnegative. -/
lemma HolderBallND_const {d : ℕ} (c order M : ℝ) (S : Set (Fin d → ℝ))
    (hc : |c| ≤ M) (hM : 0 ≤ M) :
    HolderBallND (fun _ : Fin d → ℝ => c) order M S := by
  refine ⟨contDiffOn_const, fun j hj x hx => ?_, fun x hx y hy => ?_⟩
  · cases j with
    | zero => simpa [norm_iteratedFDeriv_zero] using hc
    | succ j => simpa [iteratedFDeriv_succ_const] using hM
  · have hconst :
        iteratedFDeriv ℝ (⌈order⌉₊ - 1) (fun _ : Fin d → ℝ => c) x =
          iteratedFDeriv ℝ (⌈order⌉₊ - 1) (fun _ : Fin d → ℝ => c) y := by
      cases ⌈order⌉₊ - 1 with
      | zero => simp [iteratedFDeriv_zero_eq_comp]
      | succ k => simp [iteratedFDeriv_succ_const]
    rw [hconst, sub_self, norm_zero]
    exact mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _)

end CausalSmith.Stat.DoseResponseMinimax
