/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Frobenius-center certificate on the reduced triangle -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

-- @node: frobeniusCenterTangentXY_deriv
/-- Along the tangent `(x,y,z) = (1+t, 1-q t, 1)`, the Frobenius term has zero
first derivative at the center, so the objective derivative is `c_x - q c_y`. -/
lemma frobeniusCenterTangentXY_deriv (q cx cy cz kappa : ℝ) (hq : 0 < q) :
    HasDerivAt
      (fun t : ℝ => reducedObjective q cx cy cz kappa (1 + t) (1 - q * t) 1)
      (cx - q * cy) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (1 : ℝ) + t) 1 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id (0 : ℝ))
  have hqt : HasDerivAt (fun t : ℝ => q * t) q 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) q).mul (hasDerivAt_id (0 : ℝ))
  have hy : HasDerivAt (fun t : ℝ => (1 : ℝ) - q * t) (-q) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hqt
  have hz : HasDerivAt (fun _t : ℝ => (1 : ℝ)) 0 0 :=
    hasDerivAt_const (0 : ℝ) (1 : ℝ)
  have hcx : HasDerivAt (fun _t : ℝ => cx) 0 0 := hasDerivAt_const (0 : ℝ) cx
  have hcy : HasDerivAt (fun _t : ℝ => cy) 0 0 := hasDerivAt_const (0 : ℝ) cy
  have hcz : HasDerivAt (fun _t : ℝ => cz) 0 0 := hasDerivAt_const (0 : ℝ) cz
  have hk : HasDerivAt (fun _t : ℝ => kappa) 0 0 := hasDerivAt_const (0 : ℝ) kappa
  have hqconst : HasDerivAt (fun _t : ℝ => q) 0 0 := hasDerivAt_const (0 : ℝ) q
  have hpoly : HasDerivAt
      (fun t : ℝ => q * (1 + t) ^ 2 + (1 - q * t) ^ 2 + 1 ^ 2) 0 0 := by
    have hraw : HasDerivAt
        (fun t : ℝ => q * (1 + t) ^ 2 + (1 - q * t) ^ 2 + 1 ^ 2)
        (0 * ((1 + (0 : ℝ)) ^ 2) + q * (2 * (1 + (0 : ℝ)) ^ (2 - 1) * 1) +
          (2 * (1 - q * (0 : ℝ)) ^ (2 - 1) * (-q)) + 0) 0 := by
      simpa using ((hqconst.mul (h1.pow 2)).add (hy.pow 2)).add_const (1 ^ 2 : ℝ)
    convert hraw using 1
    ring
  have hval_ne : q * (1 + (0 : ℝ)) ^ 2 + (1 - q * (0 : ℝ)) ^ 2 + 1 ^ 2 ≠ 0 := by
    positivity
  have hnorm : HasDerivAt
      (fun t : ℝ => Real.sqrt (q * (1 + t) ^ 2 + (1 - q * t) ^ 2 + 1 ^ 2)) 0 0 := by
    convert hpoly.sqrt hval_ne using 1
    ring
  have hraw :=
    ((((hcx.mul h1).add (hcy.mul hy)).add (hcz.mul hz)).add (hk.mul hnorm))
  have hraw_fun : HasDerivAt
      (fun t : ℝ => cx * (1 + t) + cy * (1 - q * t) + cz * 1 +
        kappa * Real.sqrt (q * (1 + t) ^ 2 + (1 - q * t) ^ 2 + 1 ^ 2))
      (0 * (1 + (0 : ℝ)) + cx * 1 + (0 * (1 - q * (0 : ℝ)) + cy * (-q)) +
        (0 * (1 : ℝ) + cz * 0) +
        (0 * Real.sqrt (q * (1 + (0 : ℝ)) ^ 2 + (1 - q * (0 : ℝ)) ^ 2 + 1 ^ 2) +
          kappa * 0)) 0 := by
    refine hraw.congr_of_eventuallyEq ?_
    filter_upwards [] with t
    simp only [Pi.add_apply, Pi.mul_apply]
  have hraw' : HasDerivAt
      (fun t : ℝ => cx * (1 + t) + cy * (1 - q * t) + cz * 1 +
        kappa * Real.sqrt (q * (1 + t) ^ 2 + (1 - q * t) ^ 2 + 1 ^ 2))
      (cx - q * cy) 0 := by
    convert hraw_fun using 1
    ring
  simpa [reducedObjective] using hraw'

-- @node: frobeniusCenterTangentYZ_deriv
/-- Along the tangent `(x,y,z) = (1, 1+t, 1-t)`, the Frobenius term has zero
first derivative at the center, so the objective derivative is `c_y - c_z`. -/
lemma frobeniusCenterTangentYZ_deriv (q cx cy cz kappa : ℝ) (hq : 0 < q) :
    HasDerivAt
      (fun t : ℝ => reducedObjective q cx cy cz kappa 1 (1 + t) (1 - t))
      (cy - cz) 0 := by
  have hx : HasDerivAt (fun _t : ℝ => (1 : ℝ)) 0 0 :=
    hasDerivAt_const (0 : ℝ) (1 : ℝ)
  have hy : HasDerivAt (fun t : ℝ => (1 : ℝ) + t) 1 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id (0 : ℝ))
  have hz : HasDerivAt (fun t : ℝ => (1 : ℝ) - t) (-1) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))
  have hcx : HasDerivAt (fun _t : ℝ => cx) 0 0 := hasDerivAt_const (0 : ℝ) cx
  have hcy : HasDerivAt (fun _t : ℝ => cy) 0 0 := hasDerivAt_const (0 : ℝ) cy
  have hcz : HasDerivAt (fun _t : ℝ => cz) 0 0 := hasDerivAt_const (0 : ℝ) cz
  have hk : HasDerivAt (fun _t : ℝ => kappa) 0 0 := hasDerivAt_const (0 : ℝ) kappa
  have hq1 : HasDerivAt (fun _t : ℝ => q * 1 ^ 2) 0 0 :=
    hasDerivAt_const (0 : ℝ) (q * 1 ^ 2)
  have hpoly : HasDerivAt
      (fun t : ℝ => q * 1 ^ 2 + (1 + t) ^ 2 + (1 - t) ^ 2) 0 0 := by
    have hraw : HasDerivAt
        (fun t : ℝ => q * 1 ^ 2 + (1 + t) ^ 2 + (1 - t) ^ 2)
        (0 + (2 * (1 + (0 : ℝ)) ^ (2 - 1) * 1) +
          (2 * (1 - (0 : ℝ)) ^ (2 - 1) * (-1))) 0 := by
      simpa using (hq1.add (hy.pow 2)).add (hz.pow 2)
    convert hraw using 1
    ring
  have hval_ne : q * 1 ^ 2 + (1 + (0 : ℝ)) ^ 2 + (1 - (0 : ℝ)) ^ 2 ≠ 0 := by
    positivity
  have hnorm : HasDerivAt
      (fun t : ℝ => Real.sqrt (q * 1 ^ 2 + (1 + t) ^ 2 + (1 - t) ^ 2)) 0 0 := by
    convert hpoly.sqrt hval_ne using 1
    ring
  have hraw :=
    ((((hcx.mul hx).add (hcy.mul hy)).add (hcz.mul hz)).add (hk.mul hnorm))
  have hraw_fun : HasDerivAt
      (fun t : ℝ => cx * 1 + cy * (1 + t) + cz * (1 - t) +
        kappa * Real.sqrt (q * 1 ^ 2 + (1 + t) ^ 2 + (1 - t) ^ 2))
      (0 * (1 : ℝ) + cx * 0 + (0 * (1 + (0 : ℝ)) + cy * 1) +
        (0 * (1 - (0 : ℝ)) + cz * (-1)) +
        (0 * Real.sqrt (q * 1 ^ 2 + (1 + (0 : ℝ)) ^ 2 + (1 - (0 : ℝ)) ^ 2) +
          kappa * 0)) 0 := by
    refine hraw.congr_of_eventuallyEq ?_
    filter_upwards [] with t
    simp only [Pi.add_apply, Pi.mul_apply]
  have hraw' : HasDerivAt
      (fun t : ℝ => cx * 1 + cy * (1 + t) + cz * (1 - t) +
        kappa * Real.sqrt (q * 1 ^ 2 + (1 + t) ^ 2 + (1 - t) ^ 2))
      (cy - cz) 0 := by
    convert hraw_fun using 1
    ring
  simpa [reducedObjective] using hraw'

-- @node: lem:frobenius-center-certificate
/-- Frobenius-center certificate: `(1,1,1)` uniquely minimizes the weighted
Frobenius term on `T_m`; it minimizes the full objective for finite `κ` only if
`c_x/q = c_y = c_z`, and under that equality with `κ > 0` it is the unique
minimizer. -/
lemma frobenius_center_certificate (m : ℕ) (cx cy cz kappa : ℝ) (hq : 0 < qParam m) :
    (InReducedTriangle m 1 1 1 ∧
      ∀ x y z, InReducedTriangle m x y z → (x, y, z) ≠ (1, 1, 1) →
        Real.sqrt (qParam m * 1 ^ 2 + 1 ^ 2 + 1 ^ 2)
          < Real.sqrt (qParam m * x ^ 2 + y ^ 2 + z ^ 2)) ∧
    ((∀ x y z, InReducedTriangle m x y z →
        reducedObjective (qParam m) cx cy cz kappa 1 1 1
          ≤ reducedObjective (qParam m) cx cy cz kappa x y z) →
      cx / qParam m = cy ∧ cy = cz) ∧
    (0 < kappa → cx / qParam m = cy → cy = cz →
      ∀ x y z, InReducedTriangle m x y z → (x, y, z) ≠ (1, 1, 1) →
        reducedObjective (qParam m) cx cy cz kappa 1 1 1
          < reducedObjective (qParam m) cx cy cz kappa x y z) := by
  let q := qParam m
  have hq' : 0 < q := by simpa [q] using hq
  have hqM : q + 2 = 2 * (m : ℝ) := by
    simp [q, qParam]
    ring
  have hnorm :
      InReducedTriangle m 1 1 1 ∧
        ∀ x y z, InReducedTriangle m x y z → (x, y, z) ≠ (1, 1, 1) →
          Real.sqrt (qParam m * 1 ^ 2 + 1 ^ 2 + 1 ^ 2)
            < Real.sqrt (qParam m * x ^ 2 + y ^ 2 + z ^ 2) := by
    constructor
    · unfold InReducedTriangle
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · dsimp [q]
        nlinarith [hqM]
    · intro x y z hT hneq
      rcases hT with ⟨hx, hy, hz, hsum⟩
      have hsumq : q * x + y + z = 2 * (m : ℝ) := by simpa [q] using hsum
      have hdecomp :
          q * x ^ 2 + y ^ 2 + z ^ 2 =
            (q * 1 ^ 2 + 1 ^ 2 + 1 ^ 2) +
              (q * (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2) := by
        nlinarith [hsumq, hqM]
      have hsquares_nonneg :
          0 ≤ q * (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 := by
        positivity
      have hsquares_pos :
          0 < q * (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 := by
        by_contra hnot
        have hzero : q * (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 = 0 :=
          le_antisymm (le_of_not_gt hnot) hsquares_nonneg
        have hqx_nonneg : 0 ≤ q * (x - 1) ^ 2 :=
          mul_nonneg (le_of_lt hq') (sq_nonneg _)
        have hy_nonneg : 0 ≤ (y - 1) ^ 2 := sq_nonneg _
        have hz_nonneg : 0 ≤ (z - 1) ^ 2 := sq_nonneg _
        have hqx_zero : q * (x - 1) ^ 2 = 0 := by nlinarith
        have hy_zero : (y - 1) ^ 2 = 0 := by nlinarith
        have hz_zero : (z - 1) ^ 2 = 0 := by nlinarith
        have hx1 : x = 1 := by
          have hx_sq_zero : (x - 1) ^ 2 = 0 :=
            (mul_eq_zero.mp hqx_zero).resolve_left (ne_of_gt hq')
          exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx_sq_zero)
        have hy1 : y = 1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hy_zero)
        have hz1 : z = 1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hz_zero)
        apply hneq
        ext <;> simp [hx1, hy1, hz1]
      have hsq_lt : q * 1 ^ 2 + 1 ^ 2 + 1 ^ 2 < q * x ^ 2 + y ^ 2 + z ^ 2 := by
        rw [hdecomp]
        nlinarith
      exact Real.sqrt_lt_sqrt (by positivity) (by simpa [q] using hsq_lt)
  refine ⟨hnorm, ?_, ?_⟩
  · intro hmin
    constructor
    · let g : ℝ → ℝ :=
        fun t => reducedObjective q cx cy cz kappa (1 + t) (1 - q * t) 1
      have hloc : IsLocalMin g 0 := by
        unfold IsLocalMin IsMinFilter
        have hδ : 0 < min 1 (1 / q) := by positivity
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
        have habs : |t| < min 1 (1 / q) := by simpa [Real.dist_eq] using ht
        have ht_lt_one : t < 1 :=
          lt_of_le_of_lt (le_abs_self t) (lt_of_lt_of_le habs (min_le_left _ _))
        have hneg_lt_one : -t < 1 :=
          lt_of_le_of_lt (neg_le_abs t) (lt_of_lt_of_le habs (min_le_left _ _))
        have ht_gt_neg_one : -1 < t := by linarith
        have htq_lt_one : q * t < 1 := by
          have ht_lt_inv : t < 1 / q :=
            lt_of_le_of_lt (le_abs_self t) (lt_of_lt_of_le habs (min_le_right _ _))
          have hmul := mul_lt_mul_of_pos_left ht_lt_inv hq'
          have hqinv : q * (1 / q) = 1 := by field_simp [ne_of_gt hq']
          nlinarith
        have hT : InReducedTriangle m (1 + t) (1 - q * t) 1 := by
          unfold InReducedTriangle
          constructor
          · linarith
          constructor
          · linarith
          constructor
          · norm_num
          · dsimp [q]
            nlinarith [hqM]
        have := hmin (1 + t) (1 - q * t) 1 hT
        simpa [g, q] using this
      have hderiv : HasDerivAt g (cx - q * cy) 0 := by
        simpa [g, q] using frobeniusCenterTangentXY_deriv q cx cy cz kappa hq'
      have hzero : cx - q * cy = 0 := hloc.hasDerivAt_eq_zero hderiv
      have hcx : cx = q * cy := by linarith
      rw [hcx]
      exact mul_div_cancel_left₀ cy (ne_of_gt hq')
    · let g : ℝ → ℝ :=
        fun t => reducedObjective q cx cy cz kappa 1 (1 + t) (1 - t)
      have hloc : IsLocalMin g 0 := by
        unfold IsLocalMin IsMinFilter
        have hδ : 0 < (1 : ℝ) := by norm_num
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
        have habs : |t| < (1 : ℝ) := by simpa [Real.dist_eq] using ht
        have ht_lt_one : t < 1 := lt_of_le_of_lt (le_abs_self t) habs
        have hneg_lt_one : -t < 1 := lt_of_le_of_lt (neg_le_abs t) habs
        have ht_gt_neg_one : -1 < t := by linarith
        have hT : InReducedTriangle m 1 (1 + t) (1 - t) := by
          unfold InReducedTriangle
          constructor
          · norm_num
          constructor
          · linarith
          constructor
          · linarith
          · dsimp [q]
            nlinarith [hqM]
        have := hmin 1 (1 + t) (1 - t) hT
        simpa [g, q] using this
      have hderiv : HasDerivAt g (cy - cz) 0 := by
        simpa [g, q] using frobeniusCenterTangentYZ_deriv q cx cy cz kappa hq'
      have hzero : cy - cz = 0 := hloc.hasDerivAt_eq_zero hderiv
      linarith
  · intro hk hcxq hcyz x y z hT hneq
    have hnorm_lt := hnorm.2 x y z hT hneq
    rcases hT with ⟨hx, hy, hz, hsum⟩
    have hsumq : q * x + y + z = 2 * (m : ℝ) := by simpa [q] using hsum
    have hcx_eq0 : cx = qParam m * cy := by
      rw [← hcxq]
      field_simp [ne_of_gt hq]
    have hcx_eq : cx = q * cy := by simpa [q] using hcx_eq0
    have hsum_center : q + 1 + 1 = q * x + y + z := by nlinarith [hsumq, hqM]
    have hlinear : cx * 1 + cy * 1 + cz * 1 = cx * x + cy * y + cz * z := by
      rw [hcx_eq, ← hcyz]
      calc
        q * cy * 1 + cy * 1 + cy * 1 = cy * (q + 1 + 1) := by ring
        _ = cy * (q * x + y + z) := by rw [hsum_center]
        _ = q * cy * x + cy * y + cy * z := by ring
    have hpen :
        kappa * Real.sqrt (q * 1 ^ 2 + 1 ^ 2 + 1 ^ 2) <
          kappa * Real.sqrt (q * x ^ 2 + y ^ 2 + z ^ 2) := by
      exact mul_lt_mul_of_pos_left (by simpa [q] using hnorm_lt) hk
    unfold reducedObjective
    nlinarith [hlinear, hpen]

end CausalSmith.Experimentation.DesignPm1
