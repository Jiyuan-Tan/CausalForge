/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax lower bound: the isolated bump-Hölder classical gate

This file carries the ONE clearly-marked classical analytic gate of the whole
two-point construction: the scaled smooth bump
`a ↦ ζ·λ·h^α·ψ((a-t_0)/h)` lies in the order-`α`, radius-`M` Hölder ball on the
evaluation window, uniformly in `h ≤ 1`, for a fixed small amplitude `λ`. Mathlib's
`ContDiffBump` API supplies the smooth compact bump `ψ = doseBump` and all of its
derivative/`C^∞` facts, but the classical scaled Hölder-ball estimate for an
*arbitrary positive real* order `α` (the statement that the `h^α` normalization makes
the `α`-Hölder seminorm `h`-independent) is not available in Mathlib as a proved
lemma; it is the single substrate gate left here. Membership, separation, KL, and Le
Cam assembly are all proved downstream from this gate.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Core
import Mathlib.Analysis.Calculus.MeanValue

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory
open scoped Topology

private lemma doseBump_contDiff_top :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) doseBump := by
  simpa [doseBump] using doseContDiffBump.contDiff (n := ⊤)

private lemma doseBump_contDiff_nat (j : ℕ) :
    ContDiff ℝ (j : WithTop ℕ∞) doseBump :=
  doseBump_contDiff_top.of_le (WithTop.coe_le_coe.mpr le_top)

private lemma doseBump_iteratedDeriv_hasCompactSupport (j : ℕ) :
    HasCompactSupport (iteratedDeriv j doseBump) := by
  induction j with
  | zero =>
      simpa [iteratedDeriv_zero, doseBump] using doseContDiffBump.hasCompactSupport
  | succ j ih =>
      simpa [Nat.succ_eq_add_one, iteratedDeriv_succ] using ih.deriv

private lemma doseBump_iteratedDeriv_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, |iteratedDeriv j doseBump z| ≤ C := by
  classical
  have hcont : Continuous (iteratedDeriv j doseBump) :=
    doseBump_contDiff_top.continuous_iteratedDeriv j (WithTop.coe_le_coe.mpr le_top)
  rcases hcont.bounded_above_of_compact_support
      (doseBump_iteratedDeriv_hasCompactSupport j) with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z
  have hz : |iteratedDeriv j doseBump z| ≤ C := by
    simpa [Real.norm_eq_abs] using hC z
  exact hz.trans (le_max_left _ _)

private lemma iteratedDeriv_scaledBump (c h t0 : ℝ) (_hh : h ≠ 0) (j : ℕ) (a : ℝ) :
    iteratedDeriv j (fun a : ℝ => c * doseBump ((a - t0) / h)) a =
      c * (h⁻¹) ^ j * iteratedDeriv j doseBump ((a - t0) / h) := by
  have hinner :
      iteratedDeriv j (fun a : ℝ => doseBump ((a - t0) / h)) a =
        (h⁻¹) ^ j * iteratedDeriv j doseBump ((a - t0) / h) := by
    have hsub := congrFun
      (iteratedDeriv_comp_sub_const (n := j) (f := fun u : ℝ => doseBump (u / h)) (s := t0)) a
    rw [hsub]
    have hfun : (fun u : ℝ => doseBump (u / h)) = fun u : ℝ => doseBump (h⁻¹ * u) := by
      funext u
      rw [div_eq_mul_inv, mul_comm]
    rw [hfun, iteratedDeriv_comp_const_mul (doseBump_contDiff_nat j) h⁻¹]
    simp [div_eq_mul_inv, mul_comm]
  calc
    iteratedDeriv j (fun a : ℝ => c * doseBump ((a - t0) / h)) a
        = c * iteratedDeriv j (fun a : ℝ => doseBump ((a - t0) / h)) a := by
          rw [iteratedDeriv_const_mul_field]
    _ = c * ((h⁻¹) ^ j * iteratedDeriv j doseBump ((a - t0) / h)) := by
          rw [hinner]
    _ = c * (h⁻¹) ^ j * iteratedDeriv j doseBump ((a - t0) / h) := by
          ring

private lemma doseBump_ceilPred_iteratedDeriv_holder (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u v : ℝ,
        |iteratedDeriv (⌈alpha⌉₊ - 1) doseBump u - iteratedDeriv (⌈alpha⌉₊ - 1) doseBump v|
          ≤ C * |u - v| ^ (alpha - ((⌈alpha⌉₊ - 1 : ℕ) : ℝ)) := by
  classical
  let k : ℕ := ⌈alpha⌉₊ - 1
  let gamma : ℝ := alpha - (k : ℝ)
  have hceil_pos : 0 < ⌈alpha⌉₊ := Nat.ceil_pos.mpr halpha
  have hk_lt : (k : ℝ) < alpha := by
    rw [← Nat.lt_ceil]
    simpa [k] using Nat.pred_lt hceil_pos.ne'
  have halpha_le : alpha ≤ (k : ℝ) + 1 := by
    have hsucc : k + 1 = ⌈alpha⌉₊ := by
      simpa [k, Nat.add_comm] using Nat.succ_pred_eq_of_pos hceil_pos
    calc
      alpha ≤ (⌈alpha⌉₊ : ℝ) := Nat.le_ceil alpha
      _ = (k : ℝ) + 1 := by norm_num [← hsucc]
  have hgamma_nonneg : 0 ≤ gamma := by
    dsimp [gamma]
    exact sub_nonneg.mpr hk_lt.le
  have hgamma_le_one : gamma ≤ 1 := by
    dsimp [gamma]
    linarith [halpha_le]
  rcases doseBump_iteratedDeriv_bound k with ⟨B0, hB0_nonneg, hB0⟩
  rcases doseBump_iteratedDeriv_bound (k + 1) with ⟨B1, hB1_nonneg, hB1⟩
  let C : ℝ := max B1 (2 * B0)
  have hC_nonneg : 0 ≤ C := hB1_nonneg.trans (le_max_left _ _)
  have hB1C : B1 ≤ C := le_max_left _ _
  have h2B0C : 2 * B0 ≤ C := le_max_right _ _
  have hdiff : Differentiable ℝ (iteratedDeriv k doseBump) :=
    (doseBump_contDiff_nat (k + 1)).differentiable_iteratedDeriv' k
  have hlip : ∀ u v : ℝ,
      |iteratedDeriv k doseBump u - iteratedDeriv k doseBump v| ≤ B1 * |u - v| := by
    intro u v
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
      (𝕜 := ℝ) (s := Set.univ) (f := iteratedDeriv k doseBump) (C := B1)
      (fun x _hx => hdiff x)
      (fun x _hx => by
        have hderiv :
            deriv (iteratedDeriv k doseBump) x = iteratedDeriv (k + 1) doseBump x := by
          exact (congrFun (iteratedDeriv_succ (n := k) (f := doseBump)) x).symm
        simpa [Real.norm_eq_abs, hderiv] using hB1 x)
      convex_univ (x := v) (y := u) (Set.mem_univ _) (Set.mem_univ _)
    simpa [Real.norm_eq_abs] using hmvt
  refine ⟨C, hC_nonneg, ?_⟩
  intro u v
  have ht_nonneg : 0 ≤ |u - v| := abs_nonneg _
  by_cases ht0 : |u - v| = 0
  · have huv : u = v := by
      exact sub_eq_zero.mp (abs_eq_zero.mp ht0)
    subst v
    have hrpow_nonneg : 0 ≤ |u - u| ^ gamma :=
      Real.rpow_nonneg (abs_nonneg _) gamma
    have hmul_nonneg : 0 ≤ C * |u - u| ^ gamma :=
      mul_nonneg hC_nonneg hrpow_nonneg
    simpa [gamma] using hmul_nonneg
  · have htpos : 0 < |u - v| := lt_of_le_of_ne ht_nonneg (Ne.symm ht0)
    by_cases htle : |u - v| ≤ 1
    · have ht_le_pow : |u - v| ≤ |u - v| ^ gamma :=
        Real.self_le_rpow_of_le_one ht_nonneg htle hgamma_le_one
      calc
        |iteratedDeriv k doseBump u - iteratedDeriv k doseBump v|
            ≤ B1 * |u - v| := hlip u v
        _ ≤ B1 * |u - v| ^ gamma :=
            mul_le_mul_of_nonneg_left ht_le_pow hB1_nonneg
        _ ≤ C * |u - v| ^ gamma :=
            mul_le_mul_of_nonneg_right hB1C (Real.rpow_nonneg ht_nonneg gamma)
    · have htge : 1 ≤ |u - v| := le_of_not_ge htle
      have hpow_ge : 1 ≤ |u - v| ^ gamma :=
        Real.one_le_rpow htge hgamma_nonneg
      have hC_le_Cpow : C ≤ C * |u - v| ^ gamma := by
        simpa using mul_le_mul_of_nonneg_left hpow_ge hC_nonneg
      have hlarge :
          |iteratedDeriv k doseBump u - iteratedDeriv k doseBump v| ≤ 2 * B0 := by
        calc
          |iteratedDeriv k doseBump u - iteratedDeriv k doseBump v|
              = |iteratedDeriv k doseBump u + -iteratedDeriv k doseBump v| := by ring_nf
          _ ≤ |iteratedDeriv k doseBump u| + |-iteratedDeriv k doseBump v| :=
              abs_add_le _ _
          _ = |iteratedDeriv k doseBump u| + |iteratedDeriv k doseBump v| := by simp
          _ ≤ B0 + B0 := add_le_add (hB0 u) (hB0 v)
          _ = 2 * B0 := by ring_nf
      exact hlarge.trans (h2B0C.trans hC_le_Cpow)

private lemma rpow_mul_inv_pow_le_one {h alpha : ℝ} {j : ℕ}
    (hh_pos : 0 < h) (hh_le : h ≤ 1) (hj : (j : ℝ) ≤ alpha) :
    h ^ alpha * (h⁻¹) ^ j ≤ 1 := by
  have hinvpow_nonneg : 0 ≤ (h⁻¹) ^ j := pow_nonneg (inv_nonneg.mpr hh_pos.le) _
  have hpow_le : h ^ alpha ≤ h ^ j := by
    calc
      h ^ alpha ≤ h ^ (j : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' hh_pos.le hh_le (Nat.cast_nonneg j) hj
      _ = h ^ j := Real.rpow_natCast h j
  calc
    h ^ alpha * (h⁻¹) ^ j ≤ h ^ j * (h⁻¹) ^ j :=
      mul_le_mul_of_nonneg_right hpow_le hinvpow_nonneg
    _ = (h * h⁻¹) ^ j := by rw [mul_pow]
    _ = 1 := by
      rw [mul_inv_cancel₀ hh_pos.ne', one_pow]

private lemma rpow_scaled_holder_cancel {h alpha t0 x y : ℝ} (hh_pos : 0 < h) :
    let k : ℕ := ⌈alpha⌉₊ - 1
    let gamma : ℝ := alpha - (k : ℝ)
    h ^ alpha * (h⁻¹) ^ k * |(x - t0) / h - (y - t0) / h| ^ gamma =
      |x - y| ^ gamma := by
  intro k gamma
  have hh_ne : h ≠ 0 := hh_pos.ne'
  have hpowk_ne : h ^ k ≠ 0 := pow_ne_zero k hh_ne
  have hgamma_pos : 0 < h ^ gamma := Real.rpow_pos_of_pos hh_pos gamma
  have hscale : h ^ alpha * (h⁻¹) ^ k = h ^ gamma := by
    dsimp [gamma]
    rw [Real.rpow_sub_natCast hh_ne alpha k]
    rw [inv_pow]
    field_simp [hpowk_ne]
  have hdist : |(x - t0) / h - (y - t0) / h| = |x - y| / h := by
    rw [← sub_div]
    have hnum : (x - t0) - (y - t0) = x - y := by ring
    rw [hnum, abs_div, abs_of_pos hh_pos]
  calc
    h ^ alpha * (h⁻¹) ^ k * |(x - t0) / h - (y - t0) / h| ^ gamma
        = h ^ gamma * ((|x - y| / h) ^ gamma) := by rw [hscale, hdist]
    _ = h ^ gamma * (|x - y| ^ gamma / h ^ gamma) := by
          rw [Real.div_rpow (abs_nonneg _) hh_pos.le gamma]
    _ = |x - y| ^ gamma := by
          field_simp [hgamma_pos.ne']

-- @node: bump-holder-substrate-gate
/-- SUBSTRATE GATE (the only one of the genuine construction). For a positive Hölder
order `α` and radius `M`, there is a fixed amplitude `λ ∈ (0, M/4]` such that for every
sign `ζ ∈ {−1, +1}` and every bandwidth `h ∈ (0,1]`, the scaled smooth bump slice
`a ↦ ζ·λ·h^α·doseBump((a−t_0)/h)` lies in the univariate order-`α` radius-`M` Hölder
ball on the evaluation window `[t_0−ε_0, t_0+ε_0]`. This is the classical
`h^α`-normalized Hölder estimate for `ContDiffBump`; everything else in the
construction is proved. The amplitude bound `λ ≤ M/4` is the constraint consumed by
the two-point KL band (`|μ_ζ| ≤ λ ≤ B/2` with `B = M/2`). -/
lemma doseBump_holder_gate (alpha M t0 eps0 : ℝ)
    (halpha : 0 < alpha) (hM : 0 < M) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ M / 4 ∧
      ∀ {ζ h : ℝ}, (ζ = -1 ∨ ζ = 1) → 0 < h → h ≤ 1 →
        HolderBall1D
          (fun a => ζ * lam * h ^ alpha * doseBump ((a - t0) / h))
          alpha M (doseWindow t0 eps0) := by
  classical
  let k : ℕ := ⌈alpha⌉₊ - 1
  have hceil_pos : 0 < ⌈alpha⌉₊ := Nat.ceil_pos.mpr halpha
  have hk_le : (k : ℝ) ≤ alpha := by
    apply le_of_lt
    rw [← Nat.lt_ceil]
    simpa [k] using Nat.pred_lt hceil_pos.ne'
  let Cderiv : ℕ → ℝ := fun j => Classical.choose (doseBump_iteratedDeriv_bound j)
  have hCderiv_nonneg : ∀ j : ℕ, 0 ≤ Cderiv j := by
    intro j
    exact (Classical.choose_spec (doseBump_iteratedDeriv_bound j)).1
  have hCderiv_bound : ∀ j : ℕ, ∀ z : ℝ,
      |iteratedDeriv j doseBump z| ≤ Cderiv j := by
    intro j
    exact (Classical.choose_spec (doseBump_iteratedDeriv_bound j)).2
  rcases doseBump_ceilPred_iteratedDeriv_holder alpha halpha with ⟨CH, hCH_nonneg, hCH⟩
  let S : ℝ := ∑ j ∈ Finset.range (k + 1), Cderiv j
  let B : ℝ := max CH (max S 1)
  have hB_ge_one : 1 ≤ B := by
    exact (le_max_right S 1).trans (le_max_right CH (max S 1))
  have hB_nonneg : 0 ≤ B := (zero_le_one.trans hB_ge_one)
  have hB_pos_add : 0 < B + 1 := by linarith
  have hCH_le_B : CH ≤ B := le_max_left _ _
  have hlamB_aux :
      min (M / 4) (M / (B + 1)) * B ≤ M := by
    have hmin_le : min (M / 4) (M / (B + 1)) ≤ M / (B + 1) := min_le_right _ _
    have hMdiv_nonneg : 0 ≤ M / (B + 1) := (div_pos hM hB_pos_add).le
    have hB_le_add : B ≤ B + 1 := by linarith
    calc
      min (M / 4) (M / (B + 1)) * B ≤ (M / (B + 1)) * B :=
        mul_le_mul_of_nonneg_right hmin_le hB_nonneg
      _ ≤ (M / (B + 1)) * (B + 1) :=
        mul_le_mul_of_nonneg_left hB_le_add hMdiv_nonneg
      _ = M := by
        field_simp [hB_pos_add.ne']
  let lam : ℝ := min (M / 4) (M / (B + 1))
  have hlam_pos : 0 < lam := by
    have hM4 : 0 < M / 4 := by positivity
    have hMdiv : 0 < M / (B + 1) := div_pos hM hB_pos_add
    exact lt_min hM4 hMdiv
  have hlam_nonneg : 0 ≤ lam := hlam_pos.le
  have hlam_le_M4 : lam ≤ M / 4 := min_le_left _ _
  have hlamB : lam * B ≤ M := by
    simpa [lam] using hlamB_aux
  refine ⟨lam, hlam_pos, hlam_le_M4, ?_⟩
  intro ζ h hζ hh_pos hh_le
  have hζ_abs : |ζ| = 1 := by
    rcases hζ with rfl | rfl <;> norm_num
  have hinner : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun a : ℝ => (a - t0) / h) :=
    (contDiff_id.sub contDiff_const).div_const h
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun a : ℝ => ζ * lam * h ^ alpha * doseBump ((a - t0) / h)) :=
    contDiff_const.mul (doseBump_contDiff_top.comp hinner)
  refine ⟨hsmooth.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top), ?_, ?_⟩
  · intro j hj x _hx
    have hjk : j ≤ k := by simpa [k] using hj
    have hj_alpha : (j : ℝ) ≤ alpha := (Nat.cast_le.mpr hjk).trans hk_le
    have hj_mem : j ∈ Finset.range (k + 1) := by
      simpa [Finset.mem_range] using Nat.lt_succ_of_le hjk
    have hCj_le_S : Cderiv j ≤ S := by
      exact Finset.single_le_sum (fun i _hi => hCderiv_nonneg i) hj_mem
    have hCj_le_B : Cderiv j ≤ B := by
      exact hCj_le_S.trans ((le_max_left S 1).trans (le_max_right CH (max S 1)))
    have hlamCj : lam * Cderiv j ≤ M := by
      exact (mul_le_mul_of_nonneg_left hCj_le_B hlam_nonneg).trans hlamB
    have hscale_le : h ^ alpha * (h⁻¹) ^ j ≤ 1 :=
      rpow_mul_inv_pow_le_one hh_pos hh_le hj_alpha
    have hscale_nonneg : 0 ≤ h ^ alpha * (h⁻¹) ^ j :=
      mul_nonneg (Real.rpow_nonneg hh_pos.le alpha)
        (pow_nonneg (inv_nonneg.mpr hh_pos.le) j)
    have hscale_lam_le : lam * (h ^ alpha * (h⁻¹) ^ j) ≤ lam := by
      simpa using mul_le_mul_of_nonneg_left hscale_le hlam_nonneg
    have hD := hCderiv_bound j ((x - t0) / h)
    rw [iteratedDeriv_scaledBump (c := ζ * lam * h ^ alpha) (h := h)
      (t0 := t0) (_hh := hh_pos.ne') (j := j) (a := x)]
    change |(ζ * lam * h ^ alpha) * (h⁻¹) ^ j *
        iteratedDeriv j doseBump ((x - t0) / h)| ≤ M
    have habs :
        |(ζ * lam * h ^ alpha) * (h⁻¹) ^ j *
            iteratedDeriv j doseBump ((x - t0) / h)|
          = lam * (h ^ alpha * (h⁻¹) ^ j) *
            |iteratedDeriv j doseBump ((x - t0) / h)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, hζ_abs,
        abs_of_nonneg hlam_nonneg,
        abs_of_nonneg (Real.rpow_nonneg hh_pos.le alpha),
        abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hh_pos.le) j)]
      ring
    calc
      |(ζ * lam * h ^ alpha) * (h⁻¹) ^ j *
          iteratedDeriv j doseBump ((x - t0) / h)|
          = lam * (h ^ alpha * (h⁻¹) ^ j) *
              |iteratedDeriv j doseBump ((x - t0) / h)| := habs
      _ ≤ lam * Cderiv j :=
          mul_le_mul hscale_lam_le hD (abs_nonneg _)
            hlam_nonneg
      _ ≤ M := hlamCj
  · intro x _hx y _hy
    have hCH_lam : lam * CH ≤ M := by
      exact (mul_le_mul_of_nonneg_left hCH_le_B hlam_nonneg).trans hlamB
    let gamma : ℝ := alpha - (k : ℝ)
    let ux : ℝ := (x - t0) / h
    let uy : ℝ := (y - t0) / h
    have hscale_nonneg : 0 ≤ h ^ alpha * (h⁻¹) ^ k :=
      mul_nonneg (Real.rpow_nonneg hh_pos.le alpha)
        (pow_nonneg (inv_nonneg.mpr hh_pos.le) k)
    have hpref_nonneg : 0 ≤ lam * (h ^ alpha * (h⁻¹) ^ k) :=
      mul_nonneg hlam_nonneg hscale_nonneg
    have htop := hCH ux uy
    rw [iteratedDeriv_scaledBump (c := ζ * lam * h ^ alpha) (h := h)
        (t0 := t0) (_hh := hh_pos.ne') (j := k) (a := x),
      iteratedDeriv_scaledBump (c := ζ * lam * h ^ alpha) (h := h)
        (t0 := t0) (_hh := hh_pos.ne') (j := k) (a := y)]
    change
      |(ζ * lam * h ^ alpha) * (h⁻¹) ^ k * iteratedDeriv k doseBump ux -
        (ζ * lam * h ^ alpha) * (h⁻¹) ^ k * iteratedDeriv k doseBump uy|
        ≤ M * |x - y| ^ (alpha - ((⌈alpha⌉₊ - 1 : ℕ) : ℝ))
    have hfactor :
        (ζ * lam * h ^ alpha) * (h⁻¹) ^ k * iteratedDeriv k doseBump ux -
          (ζ * lam * h ^ alpha) * (h⁻¹) ^ k * iteratedDeriv k doseBump uy =
        (ζ * lam * h ^ alpha) * (h⁻¹) ^ k *
          (iteratedDeriv k doseBump ux - iteratedDeriv k doseBump uy) := by
      ring
    rw [hfactor]
    have habs :
        |(ζ * lam * h ^ alpha) * (h⁻¹) ^ k *
            (iteratedDeriv k doseBump ux - iteratedDeriv k doseBump uy)|
          = lam * (h ^ alpha * (h⁻¹) ^ k) *
            |iteratedDeriv k doseBump ux - iteratedDeriv k doseBump uy| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, hζ_abs,
        abs_of_nonneg hlam_nonneg,
        abs_of_nonneg (Real.rpow_nonneg hh_pos.le alpha),
        abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hh_pos.le) k)]
      ring
    have hcancel :
        h ^ alpha * (h⁻¹) ^ k * |ux - uy| ^ gamma = |x - y| ^ gamma := by
      simpa [ux, uy, gamma, k] using
        (rpow_scaled_holder_cancel (h := h) (alpha := alpha) (t0 := t0)
          (x := x) (y := y) hh_pos)
    calc
      |(ζ * lam * h ^ alpha) * (h⁻¹) ^ k *
          (iteratedDeriv k doseBump ux - iteratedDeriv k doseBump uy)|
          = lam * (h ^ alpha * (h⁻¹) ^ k) *
              |iteratedDeriv k doseBump ux - iteratedDeriv k doseBump uy| := habs
      _ ≤ lam * (h ^ alpha * (h⁻¹) ^ k) * (CH * |ux - uy| ^ gamma) :=
          mul_le_mul_of_nonneg_left htop hpref_nonneg
      _ = lam * CH * (h ^ alpha * (h⁻¹) ^ k * |ux - uy| ^ gamma) := by ring
      _ = lam * CH * |x - y| ^ gamma := by rw [hcancel]
      _ ≤ M * |x - y| ^ gamma :=
          mul_le_mul_of_nonneg_right hCH_lam (Real.rpow_nonneg (abs_nonneg _) gamma)
      _ = M * |x - y| ^ (alpha - ((⌈alpha⌉₊ - 1 : ℕ) : ℝ)) := by
          simp [gamma, k]

end CausalSmith.Stat.DoseResponseMinimax
