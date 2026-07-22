/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.ParitySliceVertices
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.ParitySliceParity

/-! # ±1 reduced-slice characterization: the backward (sufficiency) direction

Every point of the parity-truncated reduced triangle is the second moment of a
block-exchangeable `±1` design.  For even `m` the point is the barycentric mixture
`(y/2m)·cut + (z/2m)·all + (x·(m−1)/m)·spread` of the three triangle vertices; for
odd `m` the origin is unavailable and the region is a quadrilateral cut off at
`y+z = 2/m`, handled by `pm_slice_backward_odd`. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Causalean.Experimentation.DesignBased

/-- Backward direction, even `m`: the barycentric 3-vertex mixture. -/
lemma pm_slice_backward_even (m : ℕ) (hm : 2 ≤ m) (hEven : Even m) (u v : ℝ)
    (htri : InReducedTriangle m (1 - u) (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v)) :
    blockSymMatrix m u v ∈ implementableCovarianceClass m := by
  obtain ⟨hx, hy, hz, htrace⟩ := htri
  set x : ℝ := 1 - u with hxdef
  set y : ℝ := 1 + ((m : ℝ) - 1) * u - (m : ℝ) * v with hydef
  set z : ℝ := 1 + ((m : ℝ) - 1) * u + (m : ℝ) * v with hzdef
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  -- weights, components, and vertex coordinates
  let w : Fin 3 → ℝ := ![y / (2 * m), z / (2 * m), x * ((m : ℝ) - 1) / m]
  let Ds : Fin 3 → FiniteDesign (Fin (2 * m) → Bool) :=
    ![cutVDesign m, allVDesign m, spreadVDesign m hEven]
  let uu : Fin 3 → ℝ := ![1, 1, -1 / ((m : ℝ) - 1)]
  let vv : Fin 3 → ℝ := ![-1, 1, 0]
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i <;> simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    · exact div_nonneg hy (by positivity)
    · exact div_nonneg hz (by positivity)
    · apply div_nonneg _ (le_of_lt hm0); exact mul_nonneg hx (le_of_lt hm1)
  have hw1 : ∑ i, w i = 1 := by
    simp only [w, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    have hqp : qParam m = 2 * ((m : ℝ) - 1) := rfl
    rw [hqp] at htrace
    field_simp
    nlinarith [htrace]
  refine ⟨mixtureDesign m w Ds hw0 hw1, mixtureDesign_mem m w Ds hw0 hw1 ?_, ?_⟩
  · intro i
    fin_cases i <;> simp only [Ds, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    · exact cutVDesign_mem m
    · exact allVDesign_mem m
    · exact spreadVDesign_mem m hEven
  · have hSM := mixtureDesign_secondMoment m w Ds hw0 hw1 uu vv ?_
    · rw [hSM]
      congr 1
      · -- ∑ w_i uu_i = u
        simp only [w, uu, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
        have hqp : qParam m = 2 * ((m : ℝ) - 1) := rfl
        rw [hqp] at htrace
        field_simp
        nlinarith [htrace]
      · -- ∑ w_i vv_i = v
        simp only [w, vv, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
        field_simp
        ring
    · intro i
      fin_cases i <;> simp only [Ds, uu, vv, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      · exact cutVDesign_secondMoment m
      · exact allVDesign_secondMoment m
      · exact spreadVDesign_secondMoment m hm hEven

/-- **Backward (sufficiency) direction.** Any parity-truncated reduced-triangle
point is realized by a block-exchangeable `±1` design. -/
lemma pm_slice_backward (m : ℕ) (hm : 2 ≤ m) (u v : ℝ)
    (htri : InReducedTriangle m (1 - u) (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v))
    (hpar : parityThreshold m ≤ (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        + (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v)) :
    blockSymMatrix m u v ∈ implementableCovarianceClass m := by
  by_cases hEven : Even m
  · exact pm_slice_backward_even m hm hEven u v htri
  · exact pm_slice_backward_odd m hm (Nat.not_even_iff_odd.mp hEven) u v htri hpar

end CausalSmith.Experimentation.DesignPm1
