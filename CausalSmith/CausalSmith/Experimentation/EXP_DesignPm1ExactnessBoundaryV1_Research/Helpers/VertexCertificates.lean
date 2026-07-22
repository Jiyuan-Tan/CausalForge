/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic

/-! # Vertex certificates on the reduced triangle

Three elementary linear-plus-weighted-Frobenius optimality certificates over
`T_m`: the cut vertex `(0,2m,0)`, the spread vertex `(2m/q,0,0)`, and the
Frobenius center `(1,1,1)`. The `0 < qParam m` side-condition is the
non-degeneracy `m ≥ 2` regularity premise. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

-- @node: lem:cut-vertex-certificate
/-- Cut-vertex certificate: on `T_m`, if `κ ≥ 0`, `c_x/q > c_y + κ` and `c_z > c_y + κ`
then `(0, 2m, 0)` is the unique minimizer of `φ`. -/
lemma cut_vertex_certificate (m : ℕ) (cx cy cz kappa : ℝ)
    (hq : 0 < qParam m) (hk : 0 ≤ kappa)
    (h1 : cx / qParam m > cy + kappa) (h2 : cz > cy + kappa) :
    InReducedTriangle m 0 (2 * (m : ℝ)) 0 ∧
    ∀ x y z, InReducedTriangle m x y z → (x, y, z) ≠ (0, 2 * (m : ℝ), 0) →
      reducedObjective (qParam m) cx cy cz kappa 0 (2 * (m : ℝ)) 0
        < reducedObjective (qParam m) cx cy cz kappa x y z := by
  let q := qParam m
  let M : ℝ := 2 * (m : ℝ)
  constructor
  · unfold InReducedTriangle
    constructor
    · norm_num
    constructor
    · positivity
    constructor
    · norm_num
    · ring
  · intro x y z hT hneq
    rcases hT with ⟨hx, _hy, hz, hsum⟩
    have hsumq : q * x + y + z = M := by simpa [q, M] using hsum
    have hq0 : 0 ≤ q := le_of_lt hq
    have hnorm_sq : y ^ 2 ≤ q * x ^ 2 + y ^ 2 + z ^ 2 := by
      have hx2 : 0 ≤ q * x ^ 2 := mul_nonneg hq0 (sq_nonneg x)
      have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
      nlinarith
    have hnorm : y ≤ Real.sqrt (q * x ^ 2 + y ^ 2 + z ^ 2) :=
      Real.le_sqrt_of_sq_le hnorm_sq
    have hknorm : kappa * y ≤ kappa * Real.sqrt (q * x ^ 2 + y ^ 2 + z ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm hk
    have hcxmul : (cx / q) * q = cx := by
      exact div_mul_cancel₀ cx (ne_of_gt hq)
    have hcoefx : 0 < cx - q * cy - q * kappa := by
      have hmul := mul_lt_mul_of_pos_right h1 hq
      nlinarith [hcxmul]
    have hcoefz : 0 < cz - cy - kappa := by
      nlinarith [h2]
    have hxz : x ≠ 0 ∨ z ≠ 0 := by
      by_contra hnot
      push_neg at hnot
      have hyM : y = M := by nlinarith [hsumq, hnot.1, hnot.2]
      apply hneq
      ext <;> simp [hnot.1, hnot.2, hyM, M]
    have hposcombo : 0 < (cx - q * cy - q * kappa) * x + (cz - cy - kappa) * z := by
      rcases hxz with hxne | hzne
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxne)
        have hleft : 0 < (cx - q * cy - q * kappa) * x := mul_pos hcoefx hxpos
        have hright : 0 ≤ (cz - cy - kappa) * z := mul_nonneg (le_of_lt hcoefz) hz
        nlinarith
      · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hzne)
        have hleft : 0 ≤ (cx - q * cy - q * kappa) * x := mul_nonneg (le_of_lt hcoefx) hx
        have hright : 0 < (cz - cy - kappa) * z := mul_pos hcoefz hzpos
        nlinarith
    have hdiff_eq :
        (cx * x + cy * y + cz * z + kappa * y) - (cy * M + kappa * M) =
          (cx - q * cy - q * kappa) * x + (cz - cy - kappa) * z := by
      have hMexpr : M = q * x + y + z := by linarith [hsumq]
      rw [hMexpr]
      ring
    have hlinear : cy * M + kappa * M < cx * x + cy * y + cz * z + kappa * y := by
      nlinarith [hposcombo, hdiff_eq]
    have hobjLower : cx * x + cy * y + cz * z + kappa * y ≤
        reducedObjective q cx cy cz kappa x y z := by
      unfold reducedObjective
      nlinarith [hknorm]
    calc
      reducedObjective (qParam m) cx cy cz kappa 0 (2 * (m : ℝ)) 0
          = cy * M + kappa * M := by
            simp [reducedObjective, M]
      _ < cx * x + cy * y + cz * z + kappa * y := hlinear
      _ ≤ reducedObjective q cx cy cz kappa x y z := hobjLower
      _ = reducedObjective (qParam m) cx cy cz kappa x y z := by rfl

-- @node: spreadObjectiveDiff_mul_sqrt
/-- Algebraic difference identity used by the spread-vertex certificate after
multiplying through by `sqrt q`. -/
lemma spreadObjectiveDiff_mul_sqrt (cx cy cz kappa x y z M q s : ℝ)
    (hs : s ≠ 0) (hsq : s * s = q) (hM : M = q * x + y + z) :
    ((cx * x + cy * y + cz * z + kappa * (s * x)) -
          (cx * (M / q) + kappa * (s * (M / q)))) * s =
        ((cy - cx / q) * s - kappa) * y + ((cz - cx / q) * s - kappa) * z := by
  rw [hM]
  rw [← hsq]
  field_simp [hs]
  ring

-- @node: lem:spread-vertex-certificate
/-- Spread-vertex certificate: on `T_m`, if `κ ≥ 0`, `c_y > c_x/q + κ/√q` and
`c_z > c_x/q + κ/√q` then `(2m/q, 0, 0)` is the unique minimizer of `φ`. -/
lemma spread_vertex_certificate (m : ℕ) (cx cy cz kappa : ℝ)
    (hq : 0 < qParam m) (hk : 0 ≤ kappa)
    (h1 : cy > cx / qParam m + kappa / Real.sqrt (qParam m))
    (h2 : cz > cx / qParam m + kappa / Real.sqrt (qParam m)) :
    InReducedTriangle m (2 * (m : ℝ) / qParam m) 0 0 ∧
    ∀ x y z, InReducedTriangle m x y z → (x, y, z) ≠ (2 * (m : ℝ) / qParam m, 0, 0) →
      reducedObjective (qParam m) cx cy cz kappa (2 * (m : ℝ) / qParam m) 0 0
        < reducedObjective (qParam m) cx cy cz kappa x y z := by
  let q := qParam m
  let M : ℝ := 2 * (m : ℝ)
  let s := Real.sqrt q
  have hM0 : 0 ≤ M := by positivity
  have hq0 : 0 ≤ q := le_of_lt hq
  have hspos : 0 < s := by simpa [s] using Real.sqrt_pos.2 hq
  have hs0 : 0 ≤ s := le_of_lt hspos
  have hsq : s ^ 2 = q := by simpa [s] using Real.sq_sqrt hq0
  have hsq_mul : s * s = q := by nlinarith [hsq]
  constructor
  · unfold InReducedTriangle
    constructor
    · exact div_nonneg hM0 hq0
    constructor
    · norm_num
    constructor
    · norm_num
    · field_simp [q, M, ne_of_gt hq]
      ring_nf
  · intro x y z hT hneq
    rcases hT with ⟨hx, hy, hz, hsum⟩
    have hsumq : q * x + y + z = M := by simpa [q, M] using hsum
    have hsx_sq_le : (s * x) ^ 2 ≤ q * x ^ 2 + y ^ 2 + z ^ 2 := by
      have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
      have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
      nlinarith [hsq]
    have hnorm : s * x ≤ Real.sqrt (q * x ^ 2 + y ^ 2 + z ^ 2) :=
      Real.le_sqrt_of_sq_le hsx_sq_le
    have hknorm : kappa * (s * x) ≤ kappa * Real.sqrt (q * x ^ 2 + y ^ 2 + z ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm hk
    have hspreadNorm : Real.sqrt (q * (M / q) ^ 2 + 0 ^ 2 + 0 ^ 2) = s * (M / q) := by
      have hMq0 : 0 ≤ M / q := div_nonneg hM0 hq0
      calc
        Real.sqrt (q * (M / q) ^ 2 + 0 ^ 2 + 0 ^ 2)
            = Real.sqrt ((s * (M / q)) ^ 2) := by
              rw [← hsq_mul]
              ring_nf
        _ = s * (M / q) := Real.sqrt_sq (mul_nonneg hs0 hMq0)
    have hcoefyS : 0 < (cy - cx / q) * s - kappa := by
      have h1' : cx / q + kappa / s < cy := by simpa [q, s] using h1
      have hmul := mul_lt_mul_of_pos_right h1' hspos
      have hkdiv : (kappa / s) * s = kappa := div_mul_cancel₀ kappa (ne_of_gt hspos)
      nlinarith [hmul, hkdiv]
    have hcoefzS : 0 < (cz - cx / q) * s - kappa := by
      have h2' : cx / q + kappa / s < cz := by simpa [q, s] using h2
      have hmul := mul_lt_mul_of_pos_right h2' hspos
      have hkdiv : (kappa / s) * s = kappa := div_mul_cancel₀ kappa (ne_of_gt hspos)
      nlinarith [hmul, hkdiv]
    have hyz : y ≠ 0 ∨ z ≠ 0 := by
      by_contra hnot
      push_neg at hnot
      have hxM : x = M / q := by
        have hqx : x * q = M := by nlinarith [hsumq, hnot.1, hnot.2]
        exact eq_div_of_mul_eq (ne_of_gt hq) hqx
      apply hneq
      ext <;> simp [hxM, hnot.1, hnot.2, q, M]
    have hposcomboS :
        0 < ((cy - cx / q) * s - kappa) * y + ((cz - cx / q) * s - kappa) * z := by
      rcases hyz with hyne | hzne
      · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hyne)
        have hleft : 0 < ((cy - cx / q) * s - kappa) * y := mul_pos hcoefyS hypos
        have hright : 0 ≤ ((cz - cx / q) * s - kappa) * z :=
          mul_nonneg (le_of_lt hcoefzS) hz
        nlinarith
      · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hzne)
        have hleft : 0 ≤ ((cy - cx / q) * s - kappa) * y :=
          mul_nonneg (le_of_lt hcoefyS) hy
        have hright : 0 < ((cz - cx / q) * s - kappa) * z := mul_pos hcoefzS hzpos
        nlinarith
    have hdiff_eq :
        ((cx * x + cy * y + cz * z + kappa * (s * x)) -
          (cx * (M / q) + kappa * (s * (M / q)))) * s =
          ((cy - cx / q) * s - kappa) * y + ((cz - cx / q) * s - kappa) * z :=
      spreadObjectiveDiff_mul_sqrt cx cy cz kappa x y z M q s (ne_of_gt hspos) hsq_mul
        (by linarith [hsumq])
    have hlinear : cx * (M / q) + kappa * (s * (M / q)) <
        cx * x + cy * y + cz * z + kappa * (s * x) := by
      have hdiffpos : 0 <
          ((cx * x + cy * y + cz * z + kappa * (s * x)) -
            (cx * (M / q) + kappa * (s * (M / q)))) * s := by
        simpa [hdiff_eq] using hposcomboS
      have hdiff_pos : 0 <
          (cx * x + cy * y + cz * z + kappa * (s * x)) -
            (cx * (M / q) + kappa * (s * (M / q))) :=
        (mul_pos_iff_of_pos_right hspos).mp hdiffpos
      linarith
    have hobjLower : cx * x + cy * y + cz * z + kappa * (s * x) ≤
        reducedObjective q cx cy cz kappa x y z := by
      unfold reducedObjective
      linarith [hknorm]
    have hobjSpread :
        reducedObjective (qParam m) cx cy cz kappa (2 * (m : ℝ) / qParam m) 0 0 =
          cx * (M / q) + kappa * (s * (M / q)) := by
      change cx * (M / q) + cy * 0 + cz * 0 +
          kappa * Real.sqrt (q * (M / q) ^ 2 + 0 ^ 2 + 0 ^ 2) =
        cx * (M / q) + kappa * (s * (M / q))
      rw [hspreadNorm]
      ring
    calc
      reducedObjective (qParam m) cx cy cz kappa (2 * (m : ℝ) / qParam m) 0 0
          = cx * (M / q) + kappa * (s * (M / q)) := hobjSpread
      _ < cx * x + cy * y + cz * z + kappa * (s * x) := hlinear
      _ ≤ reducedObjective q cx cy cz kappa x y z := hobjLower
      _ = reducedObjective (qParam m) cx cy cz kappa x y z := by rfl

end CausalSmith.Experimentation.DesignPm1
