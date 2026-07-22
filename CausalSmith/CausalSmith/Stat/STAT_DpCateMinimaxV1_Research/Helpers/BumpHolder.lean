/- Copyright (c) 2026 Jiyuan Tan. All rights reserved. -/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.BumpHolderAux

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open scoped Topology

set_option maxHeartbeats 800000 in
-- The explicit iterated-Fréchet scaling normalization is elaboration-intensive.
private lemma scaledCausalCubeBump_holder {d : ℕ} (s gamma M : ℝ)
    (hs : 0 < s) (hsg : s ≤ gamma) (_hM : 0 < M) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c h : ℝ) (x0 : Fin d → ℝ),
      |c| * A ≤ M → 0 < h → h ≤ 1 →
      HolderBallStd
        (fun x => c * h ^ gamma * causalCubeBump (fun i => (x i - x0 i) / h))
        s M (cube d) := by
  classical
  let k := ⌈s⌉₊ - 1
  let D : ℕ → ℝ := fun j => Classical.choose (causalCubeBump_deriv_bound (d := d) j)
  have hD0 : ∀ j, 0 ≤ D j := fun j =>
    (Classical.choose_spec (causalCubeBump_deriv_bound (d := d) j)).1
  have hD : ∀ j u, ‖iteratedFDeriv ℝ j (causalCubeBump (d := d)) u‖ ≤ D j := fun j =>
    (Classical.choose_spec (causalCubeBump_deriv_bound (d := d) j)).2
  rcases causalCubeBump_deriv_holder (d := d) s hs with ⟨H, hH0, hH⟩
  let S := ∑ j ∈ Finset.range (k + 1), D j
  let A := max H (max S 1)
  have hA1 : 1 ≤ A := (le_max_right S 1).trans (le_max_right H (max S 1))
  refine ⟨A, lt_of_lt_of_le zero_lt_one hA1, ?_⟩
  intro c h x0 hc hh hh1
  have hh0 : h ≠ 0 := hh.ne'
  have hcinv : 0 ≤ h⁻¹ := inv_nonneg.mpr hh.le
  have hpow_nonneg (r : ℝ) : 0 ≤ h ^ r := Real.rpow_nonneg hh.le r
  have hform (j : ℕ) (x : Fin d → ℝ) :
      iteratedFDeriv ℝ j
          (fun x => c * h ^ gamma * causalCubeBump (fun i => (x i - x0 i) / h)) x =
        (c * h ^ gamma) • ((h⁻¹) ^ j •
          iteratedFDeriv ℝ j causalCubeBump (fun i => (x i - x0 i) / h)) := by
    let g : (Fin d → ℝ) → ℝ := fun z => causalCubeBump (h⁻¹ • z)
    have hg : ContDiff ℝ (j : WithTop ℕ∞) g :=
      (causalCubeBump_contDiff (d := d)).of_le (WithTop.coe_le_coe.mpr le_top) |>.comp
        (by fun_prop)
    have hfun : (fun x : Fin d → ℝ =>
        c * h ^ gamma * causalCubeBump (fun i => (x i - x0 i) / h)) =
        fun x => (c * h ^ gamma) • g (x - x0) := by
      funext x
      change c * h ^ gamma * causalCubeBump _ = c * h ^ gamma * causalCubeBump _
      congr 1
      apply congrArg causalCubeBump
      funext i
      simp [Pi.smul_apply, div_eq_mul_inv]
      ring
    rw [hfun]
    have hgt : ContDiff ℝ (j : WithTop ℕ∞) (fun z => g (z - x0)) :=
      hg.comp (by fun_prop)
    rw [iteratedFDeriv_const_smul_apply' hgt.contDiffAt]
    rw [iteratedFDeriv_comp_sub j x0 x]
    rw [show iteratedFDeriv ℝ j g = fun z => (h⁻¹) ^ j •
        iteratedFDeriv ℝ j causalCubeBump (h⁻¹ • z) by
      exact iteratedFDeriv_comp_const_smul h⁻¹
        ((causalCubeBump_contDiff (d := d)).of_le (WithTop.coe_le_coe.mpr le_top))]
    apply congrArg (fun r => (c * h ^ gamma) • r)
    apply congrArg (fun q : Fin d → ℝ =>
      (h⁻¹) ^ j • iteratedFDeriv ℝ j causalCubeBump q)
    funext i
    simp [Pi.smul_apply, div_eq_mul_inv]
    ring
  refine ⟨?_, ?_, ?_⟩
  · change ContDiffOn ℝ (⌈s⌉₊ - 1)
      (fun x => (c * h ^ gamma) •
        causalCubeBump (fun i => (x i - x0 i) / h)) (cube d)
    apply ContDiff.contDiffOn
    apply ContDiff.const_smul
    have hi : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : Fin d → ℝ => (fun i => (y i - x0 i) / h)) := by fun_prop
    exact ((causalCubeBump_contDiff (d := d)).comp hi).of_le
      ((tsub_le_self : (⌈s⌉₊ : WithTop ℕ∞) - 1 ≤ ⌈s⌉₊).trans
        (WithTop.coe_le_coe.mpr le_top))
  · intro j hj x _
    rw [hform]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_pow, abs_inv, abs_of_pos hh]
    have hjk : j ≤ k := hj
    have hjS : D j ≤ S := Finset.single_le_sum (fun i _ => hD0 i)
      (by simp [S, Finset.mem_range, Nat.lt_succ_of_le hjk])
    have hjA : D j ≤ A := hjS.trans ((le_max_left S 1).trans (le_max_right H (max S 1)))
    have hjs : (j : ℝ) ≤ s := by
      have hklt : k < ⌈s⌉₊ := by
        dsimp [k]
        have := Nat.ceil_pos.mpr hs
        omega
      exact (Nat.cast_le.mpr hjk).trans (Nat.lt_ceil.mp hklt).le
    have hscale : h ^ gamma * (h⁻¹) ^ j ≤ 1 := by
      have hg_j : (j : ℝ) ≤ gamma := hjs.trans hsg
      have hp : h ^ gamma ≤ h ^ (j : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' hh.le hh1 (Nat.cast_nonneg j) hg_j
      calc
        h ^ gamma * (h⁻¹) ^ j ≤ h ^ (j : ℝ) * (h⁻¹) ^ j := by
          exact mul_le_mul_of_nonneg_right hp (pow_nonneg hcinv j)
        _ = 1 := by rw [Real.rpow_natCast, ← mul_pow, mul_inv_cancel₀ hh0, one_pow]
    change |c * h ^ gamma| *
      (h⁻¹ ^ j * ‖iteratedFDeriv ℝ j causalCubeBump
        (fun i => (x i - x0 i) / h)‖) ≤ M
    calc
      |c * h ^ gamma| * (h⁻¹ ^ j * ‖iteratedFDeriv ℝ j causalCubeBump _‖)
          = |c| * (h ^ gamma * (h⁻¹) ^ j) * ‖iteratedFDeriv ℝ j causalCubeBump _‖ := by
            rw [abs_mul, abs_of_nonneg (hpow_nonneg gamma)]
            ring
      _ ≤ |c| * 1 * D j := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hscale (abs_nonneg c))
          (hD j _) (norm_nonneg _) (mul_nonneg (abs_nonneg c) zero_le_one)
      _ ≤ |c| * A := by
        simpa using mul_le_mul_of_nonneg_left hjA (abs_nonneg c)
      _ ≤ M := hc
  · intro x _ y _
    rw [hform, hform]
    rw [← smul_sub, ← smul_sub, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_pow, abs_inv, abs_of_pos hh]
    have htop := hH (fun i => (x i - x0 i) / h) (fun i => (y i - x0 i) / h)
    have hHA : H ≤ A := le_max_left _ _
    have hklt : k < ⌈s⌉₊ := by
      dsimp [k]
      have := Nat.ceil_pos.mpr hs
      omega
    have hk_s : (k : ℝ) < s := Nat.lt_ceil.mp hklt
    have hq0 : 0 ≤ s - (k : ℝ) := by linarith
    have hvec : (fun i => (x i - x0 i) / h) - (fun i => (y i - x0 i) / h) =
        h⁻¹ • (x - y) := by
      ext i
      simp [Pi.smul_apply, div_eq_mul_inv]
      ring
    have hdist : ‖(fun i => (x i - x0 i) / h) - (fun i => (y i - x0 i) / h)‖ =
        ‖x - y‖ / h := by
      rw [hvec, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
      field_simp [hh0]
    have hpowers : h ^ gamma * (h⁻¹) ^ k * (h ^ (s - (k : ℝ)))⁻¹ =
        h ^ (gamma - s) := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hh.le,
        ← Real.rpow_neg hh.le, ← Real.rpow_add hh, ← Real.rpow_add hh]
      congr 1
      ring
    have hcancel : h ^ gamma * (h⁻¹) ^ k * (‖x - y‖ / h) ^ (s - (k : ℝ)) =
        h ^ (gamma - s) * ‖x - y‖ ^ (s - (k : ℝ)) := by
      rw [Real.div_rpow (norm_nonneg _) hh.le]
      rw [div_eq_mul_inv]
      rw [show h ^ gamma * (h⁻¹) ^ k *
          (‖x - y‖ ^ (s - (k : ℝ)) * (h ^ (s - (k : ℝ)))⁻¹) =
          (h ^ gamma * (h⁻¹) ^ k * (h ^ (s - (k : ℝ)))⁻¹) *
            ‖x - y‖ ^ (s - (k : ℝ)) by ring, hpowers]
    change |c * h ^ gamma| * (h⁻¹ ^ k *
      ‖iteratedFDeriv ℝ k causalCubeBump (fun i => (x i - x0 i) / h) -
        iteratedFDeriv ℝ k causalCubeBump (fun i => (y i - x0 i) / h)‖) ≤
      M * ‖x - y‖ ^ (s - (k : ℝ))
    calc
      |c * h ^ gamma| * (h⁻¹ ^ k * ‖iteratedFDeriv ℝ k causalCubeBump _ -
          iteratedFDeriv ℝ k causalCubeBump _‖)
          ≤ |c| * h ^ gamma * (h⁻¹) ^ k *
              (H * (‖x - y‖ / h) ^ (s - (k : ℝ))) := by
            rw [abs_mul, abs_of_nonneg (hpow_nonneg gamma)]
            have ht : ‖iteratedFDeriv ℝ k causalCubeBump
                (fun i => (x i - x0 i) / h) - iteratedFDeriv ℝ k causalCubeBump
                (fun i => (y i - x0 i) / h)‖ ≤
                H * (‖x - y‖ / h) ^ (s - (k : ℝ)) := by
              simpa [hdist] using htop
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left ht (pow_nonneg hcinv k))
              (mul_nonneg (abs_nonneg c) (hpow_nonneg gamma))
      _ = |c| * H * (h ^ gamma * (h⁻¹) ^ k *
            (‖x - y‖ / h) ^ (s - (k : ℝ))) := by ring
      _ = |c| * H * (h ^ (gamma - s) * ‖x - y‖ ^ (s - (k : ℝ))) := by rw [hcancel]
      _ ≤ |c| * A * ‖x - y‖ ^ (s - (k : ℝ)) := by
        have hgs : 0 ≤ gamma - s := sub_nonneg.mpr hsg
        have hp_le : h ^ (gamma - s) ≤ 1 := Real.rpow_le_one hh.le hh1 hgs
        have hR : 0 ≤ ‖x - y‖ ^ (s - (k : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
        calc
          |c| * H * (h ^ (gamma - s) * ‖x - y‖ ^ (s - (k : ℝ)))
              ≤ |c| * H * (1 * ‖x - y‖ ^ (s - (k : ℝ))) := by gcongr
          _ ≤ |c| * A * ‖x - y‖ ^ (s - (k : ℝ)) := by
            simpa only [one_mul, mul_assoc] using
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hHA (abs_nonneg c)) hR
      _ ≤ M * ‖x - y‖ ^ (s - (k : ℝ)) := by gcongr

/-- A single positive amplitude works for the bump at both smoothness levels. -/
lemma causalCubeBump_holder_profiles {d : ℕ} (beta gamma L : ℝ)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) (hbg : beta ≤ gamma) (hL : 0 < L) :
    ∃ cB : ℝ, 0 < cB ∧ ∀ (h : ℝ) (x0 : Fin d → ℝ), 0 < h → h ≤ 1 →
      (∀ x : Fin d → ℝ,
        |cB * h ^ gamma * causalCubeBump (fun i => (x i - x0 i) / h)| ≤ 1 / 2) ∧
      HolderBallStd (fun x => cB * h ^ gamma *
          causalCubeBump (fun i => (x i - x0 i) / h)) beta L (cube d) ∧
      HolderBallStd (fun x => cB * h ^ gamma *
          causalCubeBump (fun i => (x i - x0 i) / h)) gamma L (cube d) := by
  rcases scaledCausalCubeBump_holder (d := d) beta gamma L hbeta hbg hL with ⟨Aβ, hAβ, hβ⟩
  rcases scaledCausalCubeBump_holder (d := d) gamma gamma L hgamma le_rfl hL with ⟨Aγ, hAγ, hγ⟩
  let cB := min (1 / 2) (min (L / Aβ) (L / Aγ))
  have hcB : 0 < cB := by positivity
  refine ⟨cB, hcB, ?_⟩
  intro h x0 hh hh1
  have hcHalf : cB ≤ 1 / 2 := min_le_left _ _
  have hcβ : cB * Aβ ≤ L := by
    have := min_le_left (L / Aβ) (L / Aγ)
    have hc : cB ≤ L / Aβ := (min_le_right (1 / 2) _).trans this
    calc cB * Aβ ≤ (L / Aβ) * Aβ := by gcongr
      _ = L := by field_simp [hAβ.ne']
  have hcγ : cB * Aγ ≤ L := by
    have := min_le_right (L / Aβ) (L / Aγ)
    have hc : cB ≤ L / Aγ := (min_le_right (1 / 2) _).trans this
    calc cB * Aγ ≤ (L / Aγ) * Aγ := by gcongr
      _ = L := by field_simp [hAγ.ne']
  have hbnd : ∀ x : Fin d → ℝ,
      |cB * h ^ gamma * causalCubeBump (fun i => (x i - x0 i) / h)| ≤ 1 / 2 := by
    intro x
    have hp : h ^ gamma ≤ 1 := Real.rpow_le_one hh.le hh1 hgamma.le
    have hB0 := (causalCubeBump_bounds (fun i => (x i - x0 i) / h)).1
    have hB := (causalCubeBump_bounds (fun i => (x i - x0 i) / h)).2
    rw [abs_mul, abs_mul, abs_of_pos hcB, abs_of_nonneg (Real.rpow_nonneg hh.le gamma),
      abs_of_nonneg (causalCubeBump_bounds _).1]
    calc
      cB * h ^ gamma * causalCubeBump _ ≤ (1 / 2) * h ^ gamma * causalCubeBump _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcHalf (Real.rpow_nonneg hh.le gamma)) hB0
      _ ≤ (1 / 2) * 1 * causalCubeBump _ := by
        exact mul_le_mul_of_nonneg_right (by simpa using hp) hB0
      _ ≤ 1 / 2 := by nlinarith
  refine ⟨hbnd, ?_, ?_⟩
  · exact hβ cB h x0 (by simpa [abs_of_pos hcB] using hcβ) hh hh1
  · exact hγ cB h x0 (by simpa [abs_of_pos hcB] using hcγ) hh hh1

end CausalSmith.Stat.DpCateMinimax
