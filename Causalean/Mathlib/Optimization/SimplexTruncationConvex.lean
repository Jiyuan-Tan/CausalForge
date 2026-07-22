/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.SimplexTruncationDefs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Weighted-simplex truncation: convexity and boundary reduction

Two-point convexity of the SOCP objective `wsObj` (linear term plus a nonnegative
multiple of the weighted ℓ² norm), and the geometric consequence that on the
truncated simplex `K_d` any feasible point is dominated in objective value by a
point of the truncation face `H_d`, once the relaxed global minimizer is known to
be *infeasible* (`t_rel_y + t_rel_z < d`). -/

namespace Causalean.Mathlib.Optimization

open scoped BigOperators

private noncomputable def weightedVec (β t : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => Real.sqrt (β i) * t i)

private lemma weightedVec_norm (β t : Fin 3 → ℝ) (hβ : ∀ i, 0 ≤ β i) :
    ‖weightedVec β t‖ = Real.sqrt (∑ i, β i * t i ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp [weightedVec, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [Real.sq_sqrt (hβ 0), Real.sq_sqrt (hβ 1), Real.sq_sqrt (hβ 2),
    sq_abs (t 0), sq_abs (t 1), sq_abs (t 2)]

private lemma weighted_sqrt_segment_le (β : Fin 3 → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (u v : Fin 3 → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.sqrt (∑ i, β i * ((1 - θ) * u i + θ * v i) ^ 2)
      ≤ (1 - θ) * Real.sqrt (∑ i, β i * u i ^ 2) +
          θ * Real.sqrt (∑ i, β i * v i ^ 2) := by
  have hθc : 0 ≤ 1 - θ := by linarith
  have hvec :
      weightedVec β (fun i => (1 - θ) * u i + θ * v i)
        = (1 - θ) • weightedVec β u + θ • weightedVec β v := by
    ext i
    simp [weightedVec]
    ring
  calc
    Real.sqrt (∑ i, β i * ((1 - θ) * u i + θ * v i) ^ 2)
        = ‖weightedVec β (fun i => (1 - θ) * u i + θ * v i)‖ := by
            rw [weightedVec_norm β (fun i => (1 - θ) * u i + θ * v i) hβ]
    _ = ‖(1 - θ) • weightedVec β u + θ • weightedVec β v‖ := by rw [hvec]
    _ ≤ ‖(1 - θ) • weightedVec β u‖ + ‖θ • weightedVec β v‖ :=
        norm_add_le _ _
    _ = (1 - θ) * Real.sqrt (∑ i, β i * u i ^ 2) +
          θ * Real.sqrt (∑ i, β i * v i ^ 2) := by
        rw [norm_smul, norm_smul, weightedVec_norm β u hβ, weightedVec_norm β v hβ]
        simp [Real.norm_eq_abs, abs_of_nonneg hθc, abs_of_nonneg hθ0]

private lemma eq_truncSegPoint_of_simplex_face (M d : ℝ) (x : Fin 3 → ℝ)
    (hx : InSimplex M x) (hxd : x 1 + x 2 = d) :
    x = truncSegPoint M d (x 1) := by
  funext i
  fin_cases i
  · have hsum := hx.2
    rw [Fin.sum_univ_three] at hsum
    simp [truncSegPoint]
    linarith
  · simp [truncSegPoint]
  · simp [truncSegPoint]
    linarith

/-- **Two-point convexity of the weighted-simplex objective.** For nonnegative
weights `β` and `κ ≥ 0`, the objective `wsObj` evaluated at a convex combination
`(1−θ)·u + θ·v` (for `θ ∈ [0,1]`) is at most the same convex combination of the two
objective values. (The linear part is exactly linear; the `κ·√(Σ βᵢ tᵢ²)` part is a
nonnegative multiple of the weighted ℓ² norm, hence convex by the triangle
inequality.) -/
lemma wsObj_segment_le (α β : Fin 3 → ℝ) (kappa : ℝ) (hβ : ∀ i, 0 ≤ β i)
    (hk : 0 ≤ kappa) (u v : Fin 3 → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    wsObj α β kappa (fun i => (1 - θ) * u i + θ * v i)
      ≤ (1 - θ) * wsObj α β kappa u + θ * wsObj α β kappa v := by
  unfold wsObj
  have hlin :
      (∑ i, α i * ((1 - θ) * u i + θ * v i))
        = (1 - θ) * (∑ i, α i * u i) + θ * (∑ i, α i * v i) := by
    repeat rw [Fin.sum_univ_three]
    ring
  have hsqrt :=
    weighted_sqrt_segment_le β hβ u v θ hθ0 hθ1
  calc
    (∑ i, α i * ((1 - θ) * u i + θ * v i)) +
        kappa * Real.sqrt (∑ i, β i * ((1 - θ) * u i + θ * v i) ^ 2)
        ≤ (1 - θ) * (∑ i, α i * u i) + θ * (∑ i, α i * v i) +
            kappa * ((1 - θ) * Real.sqrt (∑ i, β i * u i ^ 2) +
              θ * Real.sqrt (∑ i, β i * v i ^ 2)) := by
          rw [hlin]
          exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsqrt hk)
    _ = (1 - θ) * ((∑ i, α i * u i) +
            kappa * Real.sqrt (∑ i, β i * u i ^ 2)) +
          θ * ((∑ i, α i * v i) +
            kappa * Real.sqrt (∑ i, β i * v i ^ 2)) := by
        ring

/-- **Boundary reduction onto the truncation face.** Suppose `t_rel` is a point of
the full simplex `Δ_M` that globally minimizes `wsObj` there, and is *infeasible*
for the parity cut (`t_rel_y + t_rel_z < d`). Then every feasible point `t ∈ K_d`
is dominated by some face point `truncSegPoint M d σ` with `σ ∈ [0,d]`:
`wsObj (truncSegPoint M d σ) ≤ wsObj t`. (If `t` already lies on the boundary
`t_y+t_z=d`, take `σ = t_y`; otherwise the segment `[t, t_rel]` crosses the boundary
at a point whose objective is `≤ wsObj t` by convexity, since `wsObj t_rel ≤
wsObj t`.) -/
lemma truncSeg_reduction (M d kappa : ℝ) (α β : Fin 3 → ℝ)
    (hd0 : 0 ≤ d) (hdM : d ≤ M) (hβ : ∀ i, 0 ≤ β i) (hk : 0 ≤ kappa)
    (t_rel : Fin 3 → ℝ) (hrel : InSimplex M t_rel)
    (hmin : ∀ s, InSimplex M s → wsObj α β kappa t_rel ≤ wsObj α β kappa s)
    (hinf : t_rel 1 + t_rel 2 < d)
    (t : Fin 3 → ℝ) (ht : InTruncSimplex M d t) :
    ∃ σ, 0 ≤ σ ∧ σ ≤ d ∧
      wsObj α β kappa (truncSegPoint M d σ) ≤ wsObj α β kappa t := by
  set S : ℝ := t 1 + t 2
  set P : ℝ := t_rel 1 + t_rel 2
  have hS_ge : d ≤ S := by
    have _ : 0 ≤ M := by linarith [hd0, hdM]
    simpa [S] using ht.2
  have hP_lt_d : P < d := by simpa [P] using hinf
  rcases eq_or_lt_of_le hS_ge with hS_eq | hd_lt_S
  · refine ⟨t 1, ht.1.1 1, ?_, ?_⟩
    · have ht2 := ht.1.1 2
      have hface : t 1 + t 2 = d := by simpa [S] using hS_eq.symm
      linarith
    · have hface : t 1 + t 2 = d := by simpa [S] using hS_eq.symm
      have ht_eq := eq_truncSegPoint_of_simplex_face M d t ht.1 hface
      rw [← ht_eq]
  · set θ : ℝ := (S - d) / (S - P) with hθ_def
    set t_b : Fin 3 → ℝ := fun i => (1 - θ) * t i + θ * t_rel i
    have hden_pos : 0 < S - P := by linarith
    have hden_ne : S - P ≠ 0 := by linarith
    have hθ0 : 0 ≤ θ := by
      have hnum : 0 ≤ S - d := by linarith
      exact div_nonneg hnum hden_pos.le
    have hθmul : θ * (S - P) = S - d := by
      rw [hθ_def]
      field_simp [hden_ne]
    have hθ1 : θ ≤ 1 := by
      have hnum_le : S - d ≤ S - P := by linarith
      nlinarith
    have hθc : 0 ≤ 1 - θ := by linarith
    have ht_b12 : t_b 1 + t_b 2 = d := by
      simp [t_b]
      nlinarith
    have ht_b_simplex : InSimplex M t_b := by
      refine ⟨?_, ?_⟩
      · intro i
        have hti := ht.1.1 i
        have hri := hrel.1 i
        nlinarith [mul_nonneg hθc hti, mul_nonneg hθ0 hri]
      · have hsumt := ht.1.2
        have hsumr := hrel.2
        rw [Fin.sum_univ_three] at hsumt hsumr
        rw [Fin.sum_univ_three]
        simp [t_b]
        nlinarith
    refine ⟨t_b 1, ht_b_simplex.1 1, ?_, ?_⟩
    · have ht_b2 := ht_b_simplex.1 2
      linarith
    · have ht_b_eq := eq_truncSegPoint_of_simplex_face M d t_b ht_b_simplex ht_b12
      have hconv :
          wsObj α β kappa t_b
            ≤ (1 - θ) * wsObj α β kappa t + θ * wsObj α β kappa t_rel := by
        simpa [t_b] using wsObj_segment_le α β kappa hβ hk t t_rel θ hθ0 hθ1
      have hrel_le_t : wsObj α β kappa t_rel ≤ wsObj α β kappa t := hmin t ht.1
      have hcomb_le :
          (1 - θ) * wsObj α β kappa t + θ * wsObj α β kappa t_rel
            ≤ wsObj α β kappa t := by
        nlinarith [mul_le_mul_of_nonneg_left hrel_le_t hθ0]
      calc
        wsObj α β kappa (truncSegPoint M d (t_b 1)) = wsObj α β kappa t_b := by
            rw [← ht_b_eq]
        _ ≤ (1 - θ) * wsObj α β kappa t + θ * wsObj α β kappa t_rel := hconv
        _ ≤ wsObj α β kappa t := hcomb_le

end Causalean.Mathlib.Optimization
