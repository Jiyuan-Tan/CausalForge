/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.SimplexTruncationDefs
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Weighted-simplex truncation: the 1-D boundary slice

On the truncation face `H_d` the objective restricts to the 1-D convex function
`g_d(σ) = α_x(M−d) + α_y σ + α_z(d−σ) + κ √(A + σ² + (d−σ)²)`, with `A = β_x(M−d)²`.
This file computes that restriction (`wsObj_truncSeg_eq`), shows the selector `s⋆`
lands in `[0,d]` (`truncSelector_mem`), and proves `g_d` is minimized at `s⋆`
(`truncSeg_selector_le`) via the tangent-line inequality of the convex slice. -/

namespace Causalean.Mathlib.Optimization

open scoped BigOperators

private lemma truncSeg_radicand_nonneg {A d s : ℝ} (hA : 0 ≤ A) :
    0 ≤ A + s ^ 2 + (d - s) ^ 2 := by
  nlinarith [sq_nonneg s, sq_nonneg (d - s)]

private lemma truncSeg_radicand_pos {A d s : ℝ} (hA : 0 ≤ A) (hd : 0 < d) :
    0 < A + s ^ 2 + (d - s) ^ 2 := by
  nlinarith [hA, sq_nonneg (s - (d - s)), sq_pos_of_pos hd]

private lemma truncSeg_cs_sqrt {A d s σ : ℝ} (hA : 0 ≤ A) :
    A + s * σ + (d - s) * (d - σ)
      ≤ Real.sqrt (A + s ^ 2 + (d - s) ^ 2)
          * Real.sqrt (A + σ ^ 2 + (d - σ) ^ 2) := by
  set a := Real.sqrt A
  have ha2 : a ^ 2 = A := by
    simp [a, Real.sq_sqrt hA]
  have hsq :
      (A + s * σ + (d - s) * (d - σ)) ^ 2
        ≤ (A + s ^ 2 + (d - s) ^ 2) *
            (A + σ ^ 2 + (d - σ) ^ 2) := by
    have hid :
        (A + s ^ 2 + (d - s) ^ 2) * (A + σ ^ 2 + (d - σ) ^ 2)
            - (A + s * σ + (d - s) * (d - σ)) ^ 2
          = (a * σ - s * a) ^ 2
              + (a * (d - σ) - (d - s) * a) ^ 2
              + (s * (d - σ) - (d - s) * σ) ^ 2 := by
      rw [← ha2]
      ring
    nlinarith [hid, sq_nonneg (a * σ - s * a),
      sq_nonneg (a * (d - σ) - (d - s) * a),
      sq_nonneg (s * (d - σ) - (d - s) * σ)]
  have hX : 0 ≤ A + s ^ 2 + (d - s) ^ 2 :=
    truncSeg_radicand_nonneg hA
  have hY : 0 ≤ A + σ ^ 2 + (d - σ) ^ 2 :=
    truncSeg_radicand_nonneg hA
  calc
    A + s * σ + (d - s) * (d - σ)
        ≤ |A + s * σ + (d - s) * (d - σ)| := le_abs_self _
    _ ≤ Real.sqrt ((A + s ^ 2 + (d - s) ^ 2) *
          (A + σ ^ 2 + (d - σ) ^ 2)) := by
        exact Real.le_sqrt_of_sq_le (by simpa [sq_abs] using hsq)
    _ = Real.sqrt (A + s ^ 2 + (d - s) ^ 2)
          * Real.sqrt (A + σ ^ 2 + (d - σ) ^ 2) := by
        rw [Real.sqrt_mul hX]

private lemma truncSelector_interior_sq_bound {A d kappa δ : ℝ}
    (hd : 0 < d) (hA : 0 ≤ A) (hk : 0 ≤ kappa)
    (hlo : ¬ kappa * d / Real.sqrt (A + d ^ 2) ≤ δ)
    (hhi : ¬ δ ≤ -(kappa * d / Real.sqrt (A + d ^ 2))) :
    δ ^ 2 * (A + d ^ 2) < kappa ^ 2 * d ^ 2 := by
  have hrad_pos : 0 < A + d ^ 2 := by
    nlinarith [hA, sq_pos_of_pos hd]
  have hBpos : 0 < Real.sqrt (A + d ^ 2) := Real.sqrt_pos.2 hrad_pos
  have hBsq :
      Real.sqrt (A + d ^ 2) ^ 2 = A + d ^ 2 :=
    Real.sq_sqrt (le_of_lt hrad_pos)
  have hlt : δ < kappa * d / Real.sqrt (A + d ^ 2) := lt_of_not_ge hlo
  have hgt : -(kappa * d / Real.sqrt (A + d ^ 2)) < δ := lt_of_not_ge hhi
  have h_abs : |δ| < kappa * d / Real.sqrt (A + d ^ 2) := by
    rw [abs_lt]
    exact ⟨hgt, hlt⟩
  have hright_nonneg : 0 ≤ kappa * d / Real.sqrt (A + d ^ 2) := by
    positivity
  have h_abs_abs :
      |δ| < |kappa * d / Real.sqrt (A + d ^ 2)| := by
    rwa [abs_of_nonneg hright_nonneg]
  have hsquare := sq_lt_sq.mpr h_abs_abs
  field_simp [ne_of_gt hBpos] at hsquare
  nlinarith [hBsq, hsquare]

private lemma truncSelector_interior_den_pos {A d kappa δ : ℝ}
    (hd : 0 < d) (hA : 0 ≤ A) (hk : 0 ≤ kappa)
    (hlo : ¬ kappa * d / Real.sqrt (A + d ^ 2) ≤ δ)
    (hhi : ¬ δ ≤ -(kappa * d / Real.sqrt (A + d ^ 2))) :
    0 < kappa ^ 2 - δ ^ 2 / 2 := by
  have hsq_lt :
      δ ^ 2 * (A + d ^ 2) < kappa ^ 2 * d ^ 2 :=
    truncSelector_interior_sq_bound hd hA hk hlo hhi
  have hd2pos : 0 < d ^ 2 := sq_pos_of_pos hd
  have hratio_le : d ^ 2 ≤ A + d ^ 2 := by
    nlinarith [hA]
  have hden_half : δ ^ 2 / 2 < kappa ^ 2 := by
    nlinarith [hsq_lt, hratio_le, hd2pos]
  nlinarith

private lemma truncSelector_interior_mem {A d kappa δ : ℝ}
    (hd : 0 < d) (hA : 0 ≤ A) (hk : 0 ≤ kappa)
    (hlo : ¬ kappa * d / Real.sqrt (A + d ^ 2) ≤ δ)
    (hhi : ¬ δ ≤ -(kappa * d / Real.sqrt (A + d ^ 2))) :
    0 ≤ (d - δ *
          Real.sqrt ((A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2))) / 2 ∧
      (d - δ *
          Real.sqrt ((A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2))) / 2 ≤ d := by
  let W := Real.sqrt ((A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2))
  have hden : 0 < kappa ^ 2 - δ ^ 2 / 2 :=
    truncSelector_interior_den_pos hd hA hk hlo hhi
  have hsq_lt :
      δ ^ 2 * (A + d ^ 2) < kappa ^ 2 * d ^ 2 :=
    truncSelector_interior_sq_bound hd hA hk hlo hhi
  have hQ : 0 ≤ (A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2) := by
    positivity
  have hWsq : W ^ 2 =
      (A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2) := by
    simp [W, Real.sq_sqrt hQ]
  have hδWsq : (δ * W) ^ 2 ≤ d ^ 2 := by
    have hcore :
        δ ^ 2 * (A + d ^ 2 / 2) ≤
          d ^ 2 * (kappa ^ 2 - δ ^ 2 / 2) := by
      nlinarith [le_of_lt hsq_lt]
    have hcalc : δ ^ 2 * W ^ 2 ≤ d ^ 2 := by
      calc
        δ ^ 2 * W ^ 2
            = (δ ^ 2 * (A + d ^ 2 / 2)) /
                (kappa ^ 2 - δ ^ 2 / 2) := by
              rw [hWsq]
              ring
        _ ≤ d ^ 2 := by
              rw [div_le_iff₀ hden]
              exact hcore
    nlinarith
  have hbounds : -d ≤ δ * W ∧ δ * W ≤ d :=
    abs_le_of_sq_le_sq' hδWsq (le_of_lt hd)
  constructor <;> nlinarith [hbounds.1, hbounds.2]

private lemma truncSelector_interior_stationary {A d kappa δ : ℝ}
    (hd : 0 < d) (hA : 0 ≤ A) (hk : 0 ≤ kappa)
    (hlo : ¬ kappa * d / Real.sqrt (A + d ^ 2) ≤ δ)
    (hhi : ¬ δ ≤ -(kappa * d / Real.sqrt (A + d ^ 2))) :
    Real.sqrt
          (A + ((d - δ *
              Real.sqrt ((A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2))) / 2) ^ 2
            + (d - (d - δ *
              Real.sqrt ((A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2))) / 2) ^ 2)
        * δ
      + kappa *
          (2 * ((d - δ *
              Real.sqrt ((A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2))) / 2) - d)
        = 0 := by
  let W := Real.sqrt ((A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2))
  let s := (d - δ * W) / 2
  let rs := Real.sqrt (A + s ^ 2 + (d - s) ^ 2)
  have hden : 0 < kappa ^ 2 - δ ^ 2 / 2 :=
    truncSelector_interior_den_pos hd hA hk hlo hhi
  have hQ : 0 ≤ (A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2) := by
    positivity
  have hWsq : W ^ 2 =
      (A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2) := by
    simp [W, Real.sq_sqrt hQ]
  have hRnonneg : 0 ≤ A + s ^ 2 + (d - s) ^ 2 := by
    nlinarith [hA, sq_nonneg s, sq_nonneg (d - s)]
  have hrs_sq : rs ^ 2 = A + s ^ 2 + (d - s) ^ 2 := by
    simp [rs, Real.sq_sqrt hRnonneg]
  have htwos : 2 * s - d = -δ * W := by
    simp [s]
    ring
  have hRs_expr :
      A + s ^ 2 + (d - s) ^ 2 =
        A + d ^ 2 / 2 + δ ^ 2 * W ^ 2 / 2 := by
    simp [s]
    ring
  have hmid :
      A + d ^ 2 / 2 + δ ^ 2 * W ^ 2 / 2 = kappa ^ 2 * W ^ 2 := by
    rw [hWsq]
    field_simp [ne_of_gt hden,
      show 2 * kappa ^ 2 - δ ^ 2 ≠ 0 by nlinarith [hden]]
    ring
  have hrs_kW_sq : rs ^ 2 = (kappa * W) ^ 2 := by
    rw [hrs_sq, hRs_expr, hmid]
    ring
  by_cases hδ : δ = 0
  · subst δ
    have hterm : rs * 0 + kappa * (2 * s - d) = 0 := by
      rw [htwos]
      ring
    simpa [W, s, rs] using hterm
  · have hrs_nonneg : 0 ≤ rs := by
      simp [rs]
    have hkW_nonneg : 0 ≤ kappa * W := by
      positivity
    have hrs_eq : rs = kappa * W := by
      nlinarith [hrs_kW_sq, hrs_nonneg, hkW_nonneg]
    have hterm : rs * δ + kappa * (2 * s - d) = 0 := by
      rw [htwos, hrs_eq]
      ring
    simpa [W, s, rs] using hterm

private lemma truncSelector_sign_core {A d kappa δ σ : ℝ}
    (hd : 0 < d) (hA : 0 ≤ A) (hk : 0 ≤ kappa)
    (hσ0 : 0 ≤ σ) (hσd : σ ≤ d) :
    let s :=
      if kappa * d / Real.sqrt (A + d ^ 2) ≤ δ then 0
      else if δ ≤ -(kappa * d / Real.sqrt (A + d ^ 2)) then d
      else (d - δ *
        Real.sqrt ((A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2))) / 2
    0 ≤ (σ - s) *
      (Real.sqrt (A + s ^ 2 + (d - s) ^ 2) * δ + kappa * (2 * s - d)) := by
  have hrad_pos : 0 < A + d ^ 2 := by
    nlinarith [hA, sq_pos_of_pos hd]
  have hBpos : 0 < Real.sqrt (A + d ^ 2) := Real.sqrt_pos.2 hrad_pos
  have hBsq : Real.sqrt (A + d ^ 2) ^ 2 = A + d ^ 2 :=
    Real.sq_sqrt (le_of_lt hrad_pos)
  dsimp only
  split_ifs with hlo hhi
  · have hmul :
        kappa * d ≤ δ * Real.sqrt (A + d ^ 2) := by
      have hmul' := mul_le_mul_of_nonneg_right hlo (le_of_lt hBpos)
      field_simp [ne_of_gt hBpos] at hmul'
      nlinarith
    have hterm :
        0 ≤ Real.sqrt (A + 0 ^ 2 + (d - 0) ^ 2) * δ
            + kappa * (2 * 0 - d) := by
      rw [show A + 0 ^ 2 + (d - 0) ^ 2 = A + d ^ 2 by ring]
      nlinarith
    have hσ_minus : 0 ≤ σ - 0 := by
      linarith
    exact mul_nonneg hσ_minus hterm
  · have hmul :
        δ * Real.sqrt (A + d ^ 2) ≤ -kappa * d := by
      have hmul' := mul_le_mul_of_nonneg_right hhi (le_of_lt hBpos)
      field_simp [ne_of_gt hBpos] at hmul'
      nlinarith
    have hterm :
        Real.sqrt (A + d ^ 2 + (d - d) ^ 2) * δ
            + kappa * (2 * d - d) ≤ 0 := by
      rw [show A + d ^ 2 + (d - d) ^ 2 = A + d ^ 2 by ring]
      nlinarith
    have hσ_nonpos : σ - d ≤ 0 := by
      linarith
    exact mul_nonneg_of_nonpos_of_nonpos hσ_nonpos hterm
  · have hterm :=
      truncSelector_interior_stationary hd hA hk hlo hhi
    rw [hterm]
    simp

/-- **Objective on the truncation face.** Evaluating `wsObj` at the face point
`truncSegPoint M d σ = (M−d, σ, d−σ)` (with `β_y = β_z = 1`) gives the explicit 1-D
form `α_x(M−d) + α_y σ + α_z(d−σ) + κ √(β_x(M−d)² + σ² + (d−σ)²)`. -/
lemma wsObj_truncSeg_eq (M d : ℝ) (α β : Fin 3 → ℝ) (kappa σ : ℝ)
    (hβy : β 1 = 1) (hβz : β 2 = 1) :
    wsObj α β kappa (truncSegPoint M d σ)
      = α 0 * (M - d) + α 1 * σ + α 2 * (d - σ)
        + kappa * Real.sqrt (β 0 * (M - d) ^ 2 + σ ^ 2 + (d - σ) ^ 2) := by
  unfold wsObj truncSegPoint
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, hβy, hβz]

/-- **The selector lands in `[0,d]`.** The endpoint/interior selector `truncSelector`
satisfies `0 ≤ s⋆ ≤ d`: the two endpoint branches give `0` and `d` directly, and in
the interior branch the guard failures `|δ| < κ d / √(A + d²)` force
`δ²(A + d²) < κ² d²`, whence `|s⋆ − d/2| < d/2`. -/
lemma truncSelector_mem (M d : ℝ) (α β : Fin 3 → ℝ) (kappa : ℝ)
    (hd : 0 < d) (hβ0 : 0 ≤ β 0) (hk : 0 ≤ kappa) :
    0 ≤ truncSelector M d α β kappa ∧ truncSelector M d α β kappa ≤ d := by
  unfold truncSelector
  let δ := α 1 - α 2
  let A := β 0 * (M - d) ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg hβ0 (sq_nonneg _)
  dsimp only
  split_ifs with hlo hhi
  · exact ⟨le_rfl, le_of_lt hd⟩
  · exact ⟨le_of_lt hd, le_rfl⟩
  · exact truncSelector_interior_mem hd hA hk hlo hhi

/-- **The selector minimizes the boundary slice.** For every `σ ∈ [0,d]` the face
objective at the selector is at most the face objective at `σ`. The slice
`g_d(σ) = δσ + κ‖(√A, σ, d−σ)‖ + const` (with `δ = α_y − α_z`) is convex (a linear
term plus a nonnegative multiple of the norm of an affine map), and `s⋆` is chosen so
the tangent-slope sign condition `g_d'(s⋆)·(σ − s⋆) ≥ 0` holds on `[0,d]`; convexity's
tangent-line inequality then gives `g_d(s⋆) ≤ g_d(σ)`. -/
lemma truncSeg_selector_le (M d : ℝ) (α β : Fin 3 → ℝ) (kappa : ℝ)
    (hd : 0 < d) (hβ0 : 0 ≤ β 0) (hβy : β 1 = 1) (hβz : β 2 = 1) (hk : 0 ≤ kappa)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσd : σ ≤ d) :
    wsObj α β kappa (truncSegPoint M d (truncSelector M d α β kappa))
      ≤ wsObj α β kappa (truncSegPoint M d σ) := by
  set s := truncSelector M d α β kappa with hs
  rw [wsObj_truncSeg_eq M d α β kappa s hβy hβz,
    wsObj_truncSeg_eq M d α β kappa σ hβy hβz]
  set A := β 0 * (M - d) ^ 2 with hAdef
  set δ := α 1 - α 2 with hδdef
  let Rs := A + s ^ 2 + (d - s) ^ 2
  let Rσ := A + σ ^ 2 + (d - σ) ^ 2
  let rs := Real.sqrt Rs
  let rσ := Real.sqrt Rσ
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg hβ0 (sq_nonneg _)
  have hRs_pos : 0 < Rs := by
    dsimp [Rs]
    exact truncSeg_radicand_pos hA hd
  have hRσ_pos : 0 < Rσ := by
    dsimp [Rσ]
    exact truncSeg_radicand_pos hA hd
  have hrs_pos : 0 < rs := by
    exact Real.sqrt_pos.2 hRs_pos
  have hrs_sq : rs ^ 2 = Rs := by
    simp [rs, Real.sq_sqrt (le_of_lt hRs_pos)]
  have hCS :
      A + s * σ + (d - s) * (d - σ) ≤ rs * rσ := by
    simpa [rs, rσ, Rs, Rσ] using
      truncSeg_cs_sqrt (A := A) (d := d) (s := s) (σ := σ) hA
  have hcross_id :
      A + s * σ + (d - s) * (d - σ) - Rs =
        (σ - s) * (2 * s - d) := by
    dsimp [Rs]
    ring
  have hdiff :
      (σ - s) * (2 * s - d) ≤ rs * rσ - rs * rs := by
    nlinarith [hCS, hcross_id, hrs_sq]
  have hkdiff :
      kappa * ((σ - s) * (2 * s - d)) ≤
        kappa * (rs * rσ - rs * rs) :=
    mul_le_mul_of_nonneg_left hdiff hk
  have hs_core :
      s =
        if kappa * d / Real.sqrt (A + d ^ 2) ≤ δ then 0
        else if δ ≤ -(kappa * d / Real.sqrt (A + d ^ 2)) then d
        else (d - δ *
          Real.sqrt ((A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2))) / 2 := by
    rw [hs]
    simp [truncSelector, A, δ]
  have hsign :
      0 ≤ (σ - s) * (rs * δ + kappa * (2 * s - d)) := by
    have hsign_core :=
      truncSelector_sign_core (A := A) (d := d) (kappa := kappa)
        (δ := δ) (σ := σ) hd hA hk hσ0 hσd
    dsimp only at hsign_core
    rw [← hs_core] at hsign_core
    simpa [rs, Rs] using hsign_core
  have hmul_nonneg :
      0 ≤ rs * (δ * (σ - s) + kappa * (rσ - rs)) := by
    nlinarith [hsign, hkdiff]
  have hnonneg : 0 ≤ δ * (σ - s) + kappa * (rσ - rs) := by
    have hmul' :
        0 ≤ (δ * (σ - s) + kappa * (rσ - rs)) * rs := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_nonneg
    exact nonneg_of_mul_nonneg_left hmul' hrs_pos
  have hslice_delta : δ * s + kappa * rs ≤ δ * σ + kappa * rσ := by
    nlinarith
  have hslice :
      α 1 * s + α 2 * (d - s) + kappa * rs ≤
        α 1 * σ + α 2 * (d - σ) + kappa * rσ := by
    nlinarith [hslice_delta]
  dsimp [rs, rσ, Rs, Rσ, A]
  nlinarith [hslice]

end Causalean.Mathlib.Optimization
