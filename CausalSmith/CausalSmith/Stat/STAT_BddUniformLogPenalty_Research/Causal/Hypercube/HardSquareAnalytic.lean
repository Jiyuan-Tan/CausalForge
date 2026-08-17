import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.Family

/-!
# Analytic reductions for the fixed hard square

This module starts the remaining local-mass, slice, and Gram block by
reducing the uniform kernel to its closed-ball support.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The quadratic form of a scaled rank-one matrix is the scaled square of
the corresponding dot product.  This is the algebraic step that rewrites the
population Gram form as an integral of a squared local polynomial. -/
-- @node: matrixQuadratic_rankOne
lemma matrixQuadratic_rankOne {d : ℕ} (a : ℝ) (f v : Fin d → ℝ) :
    matrixQuadratic (fun i j => a * f i * f j) v =
      a * (∑ i, v i * f i) ^ 2 := by
  classical
  unfold matrixQuadratic
  calc
    ∑ i, ∑ j, v i * (a * f i * f j) * v j =
        ∑ i, (a * (v i * f i)) * (∑ j, v j * f j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = a * (∑ i, v i * f i) * (∑ j, v j * f j) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]
    _ = a * (∑ i, v i * f i) ^ 2 := by ring

/-- Specializing the rank-one identity to the local-polynomial basis gives
the squared polynomial integrand appearing in the population Gram floor. -/
-- @node: matrixQuadratic_polyBasis_rankOne
lemma matrixQuadratic_polyBasis_rankOne (p : ℕ) (a u : ℝ)
    (v : Fin (p + 1) → ℝ) :
    matrixQuadratic
        (fun i j => a * polyBasis p u i * polyBasis p u j) v =
      a * (∑ i, v i * u ^ (i : ℕ)) ^ 2 := by
  rw [matrixQuadratic_rankOne]
  rfl

/-- A nonnegative local weight makes every rank-one polynomial Gram
contribution positive semidefinite. -/
-- @node: matrixQuadratic_polyBasis_rankOne_nonneg
lemma matrixQuadratic_polyBasis_rankOne_nonneg (p : ℕ) {a u : ℝ}
    (ha : 0 ≤ a) (v : Fin (p + 1) → ℝ) :
    0 ≤ matrixQuadratic
      (fun i j => a * polyBasis p u i * polyBasis p u j) v := by
  rw [matrixQuadratic_polyBasis_rankOne]
  positivity

/-- A closed axis-aligned box in the two-dimensional score space. -/
-- @node: causalHardScoreBox
def causalHardScoreBox (a0 b0 a1 b1 : ℝ) : Set Score :=
  {z | a0 ≤ z 0 ∧ z 0 ≤ b0 ∧ a1 ≤ z 1 ∧ z 1 ≤ b1}

/-- The volume of a nonempty score box is the product of its side lengths. -/
-- @node: causalHardScoreBox_volume
lemma causalHardScoreBox_volume {a0 b0 a1 b1 : ℝ}
    (h0 : a0 ≤ b0) (_h1 : a1 ≤ b1) :
    volume (causalHardScoreBox a0 b0 a1 b1) =
      ENNReal.ofReal ((b0 - a0) * (b1 - a1)) := by
  let a : Fin 2 → ℝ := ![a0, a1]
  let b : Fin 2 → ℝ := ![b0, b1]
  have hset : causalHardScoreBox a0 b0 a1 b1 =
      ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) ⁻¹' Icc a b := by
    ext z
    simp only [causalHardScoreBox, mem_setOf_eq, mem_preimage, mem_Icc, Pi.le_def]
    constructor
    · intro hz
      constructor <;> intro i <;> fin_cases i
      · exact hz.1
      · exact hz.2.2.1
      · exact hz.2.1
      · exact hz.2.2.2
    · rintro ⟨hlo, hhi⟩
      exact ⟨hlo 0, hhi 0, hlo 1, hhi 1⟩
  rw [hset, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin 2)).measure_preimage]
  · rw [Real.volume_Icc_pi]
    simp only [Fin.prod_univ_two, a, b, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [ENNReal.ofReal_mul (sub_nonneg.mpr h0)]
  · exact (measurableSet_Icc : MeasurableSet (Icc a b)).nullMeasurableSet

/-- Coordinatewise displacement by at most half the radius stays inside the
Euclidean closed ball in dimension two. -/
-- @node: mem_closedBall_of_coordinate_diff_le_half
lemma mem_closedBall_of_coordinate_diff_le_half {x z : Score} {h : ℝ}
    (hh : 0 ≤ h) (h0 : |z 0 - x 0| ≤ h / 2)
    (h1 : |z 1 - x 1| ≤ h / 2) :
    z ∈ Metric.closedBall x h := by
  rw [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  rw [Real.sqrt_le_iff]
  constructor
  · exact hh
  · change |z 0 - x 0| ^ 2 + |z 1 - x 1| ^ 2 ≤ h ^ 2
    have hh2 : 0 ≤ h / 2 := by positivity
    have hs0 := (sq_le_sq₀ (abs_nonneg (z 0 - x 0)) hh2).2 h0
    have hs1 := (sq_le_sq₀ (abs_nonneg (z 1 - x 1)) hh2).2 h1
    nlinarith

/-- Coordinate characterization of the fixed assignment rectangle's
frontier. -/
-- @node: mem_frontier_causalHardArmOne_iff
lemma mem_frontier_causalHardArmOne_iff (x : Score) :
    x ∈ frontier causalHardArmOne ↔
      -1 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 2 ∧
        (x 0 = -1 ∨ x 0 = 1 ∨ x 1 = 0 ∨ x 1 = 2) := by
  rw [← causalHardRectangleAffineHomeomorph_image,
    ← causalHardRectangleAffineHomeomorph.image_frontier]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases (mem_frontier_scoreCube_half_iff y).mp hy with ⟨hy0, hy1, hedge⟩
    rw [abs_le] at hy0 hy1
    simp only [causalHardRectangleAffineHomeomorph, Homeomorph.trans_apply,
      Homeomorph.smulOfNeZero_apply, Homeomorph.coe_addLeft,
      PiLp.add_apply, PiLp.smul_apply, scorePoint_apply_zero,
      scorePoint_apply_one, smul_eq_mul, zero_add]
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    rcases hedge with hedge | hedge
    · rcases (abs_eq (by norm_num : 0 ≤ (1 / 2 : ℝ))).mp hedge with h | h
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inl (by linarith)
    · rcases (abs_eq (by norm_num : 0 ≤ (1 / 2 : ℝ))).mp hedge with h | h
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · rintro ⟨hx0l, hx0u, hx1l, hx1u, hedge⟩
    let y : Score := scorePoint (x 0 / 2) ((x 1 - 1) / 2)
    refine ⟨y, ?_, ?_⟩
    · rw [mem_frontier_scoreCube_half_iff]
      have hy0 : |y 0| ≤ 1 / 2 := by
        rw [show y 0 = x 0 / 2 by simp [y, scorePoint_apply_zero], abs_le]
        constructor <;> linarith
      have hy1 : |y 1| ≤ 1 / 2 := by
        rw [show y 1 = (x 1 - 1) / 2 by simp [y, scorePoint_apply_one], abs_le]
        constructor <;> linarith
      refine ⟨hy0, hy1, ?_⟩
      rcases hedge with h | h | h | h
      · left; rw [show y 0 = x 0 / 2 by simp [y, scorePoint_apply_zero], h]; norm_num
      · left; rw [show y 0 = x 0 / 2 by simp [y, scorePoint_apply_zero], h]; norm_num
      · right; rw [show y 1 = (x 1 - 1) / 2 by simp [y, scorePoint_apply_one], h]; norm_num
      · right; rw [show y 1 = (x 1 - 1) / 2 by simp [y, scorePoint_apply_one], h]; norm_num
    · ext i
      fin_cases i
      · simp [causalHardRectangleAffineHomeomorph, y, scorePoint_apply_zero]
        ring
      · simp [causalHardRectangleAffineHomeomorph, y, scorePoint_apply_one]
        ring

/-- Every positive radius at most one cuts at least a quarter-box from the
fixed treatment rectangle at each frontier point. -/
-- @node: causalHardArmOne_inter_closedBall_volume_lower
lemma causalHardArmOne_inter_closedBall_volume_lower
    {x : Score} {h : ℝ} (hx : x ∈ frontier causalHardArmOne)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    ENNReal.ofReal (h ^ 2 / 4) ≤
      volume (causalHardArmOne ∩ Metric.closedBall x h) := by
  have hx' := (mem_frontier_causalHardArmOne_iff x).mp hx
  by_cases hx0 : x 0 ≤ 0
  · by_cases hx1 : x 1 ≤ 1
    · let R := causalHardScoreBox (x 0) (x 0 + h / 2) (x 1) (x 1 + h / 2)
      have hRvol : volume R = ENNReal.ofReal (h ^ 2 / 4) := by
        rw [causalHardScoreBox_volume (by linarith) (by linarith)]
        congr 1
        ring
      rw [← hRvol]
      apply measure_mono
      intro z hz
      refine ⟨⟨by linarith [hz.1], by linarith [hz.2.1],
        by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩, ?_⟩
      apply mem_closedBall_of_coordinate_diff_le_half hh.le
      · rw [abs_of_nonneg (by linarith [hz.1])]; linarith [hz.2.1]
      · rw [abs_of_nonneg (by linarith [hz.2.2.1])]; linarith [hz.2.2.2]
    · let R := causalHardScoreBox (x 0) (x 0 + h / 2) (x 1 - h / 2) (x 1)
      have hRvol : volume R = ENNReal.ofReal (h ^ 2 / 4) := by
        rw [causalHardScoreBox_volume (by linarith) (by linarith)]
        congr 1
        ring
      rw [← hRvol]
      apply measure_mono
      intro z hz
      refine ⟨⟨by linarith [hz.1], by linarith [hz.2.1],
        by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩, ?_⟩
      apply mem_closedBall_of_coordinate_diff_le_half hh.le
      · rw [abs_of_nonneg (by linarith [hz.1])]; linarith [hz.2.1]
      · rw [abs_of_nonpos (by linarith [hz.2.2.2])]; linarith [hz.2.2.1]
  · have hx0' : 0 ≤ x 0 := le_of_not_ge hx0
    by_cases hx1 : x 1 ≤ 1
    · let R := causalHardScoreBox (x 0 - h / 2) (x 0) (x 1) (x 1 + h / 2)
      have hRvol : volume R = ENNReal.ofReal (h ^ 2 / 4) := by
        rw [causalHardScoreBox_volume (by linarith) (by linarith)]
        congr 1
        ring
      rw [← hRvol]
      apply measure_mono
      intro z hz
      refine ⟨⟨by linarith [hz.1], by linarith [hz.2.1],
        by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩, ?_⟩
      apply mem_closedBall_of_coordinate_diff_le_half hh.le
      · rw [abs_of_nonpos (by linarith [hz.2.1])]; linarith [hz.1]
      · rw [abs_of_nonneg (by linarith [hz.2.2.1])]; linarith [hz.2.2.2]
    · let R := causalHardScoreBox (x 0 - h / 2) (x 0) (x 1 - h / 2) (x 1)
      have hRvol : volume R = ENNReal.ofReal (h ^ 2 / 4) := by
        rw [causalHardScoreBox_volume (by linarith) (by linarith)]
        congr 1
        ring
      rw [← hRvol]
      apply measure_mono
      intro z hz
      refine ⟨⟨by linarith [hz.1], by linarith [hz.2.1],
        by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩, ?_⟩
      apply mem_closedBall_of_coordinate_diff_le_half hh.le
      · rw [abs_of_nonpos (by linarith [hz.2.1])]; linarith [hz.1]
      · rw [abs_of_nonpos (by linarith [hz.2.2.2])]; linarith [hz.2.2.1]

/-- Every positive radius at most one cuts a fixed positive-area box from
the support-side complement of the treatment rectangle. -/
-- @node: causalHardArmZero_inter_closedBall_volume_lower
lemma causalHardArmZero_inter_closedBall_volume_lower
    {x : Score} {h : ℝ} (hx : x ∈ frontier causalHardArmOne)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    ENNReal.ofReal (h ^ 2 / 8) ≤
      volume ((causalHardSquare \ causalHardArmOne) ∩ Metric.closedBall x h) := by
  have hx' := (mem_frontier_causalHardArmOne_iff x).mp hx
  rcases hx'.2.2.2.2 with hedge | hedge | hedge | hedge
  · let R := causalHardScoreBox (x 0 - h / 2) (x 0 - h / 4)
        (x 1 - h / 4) (x 1 + h / 4)
    have hRvol : volume R = ENNReal.ofReal (h ^ 2 / 8) := by
      rw [causalHardScoreBox_volume (by linarith) (by linarith)]
      congr 1
      ring
    rw [← hRvol]
    apply measure_mono
    intro z hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      fin_cases i
      · change -3 ≤ z 0 ∧ z 0 ≤ 3
        exact ⟨by linarith [hz.1, hx'.1], by linarith [hz.2.1, hx'.2.1]⟩
      · change -3 ≤ z 1 ∧ z 1 ≤ 3
        exact ⟨by linarith [hz.2.2.1, hx'.2.2.1],
          by linarith [hz.2.2.2, hx'.2.2.2.1]⟩
    · intro hA; linarith [hA.1, hz.2.1]
    · apply mem_closedBall_of_coordinate_diff_le_half hh.le
      · rw [abs_of_nonpos (by linarith [hz.2.1])]; linarith [hz.1]
      · rw [abs_le]; exact ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
  · let R := causalHardScoreBox (x 0 + h / 4) (x 0 + h / 2)
        (x 1 - h / 4) (x 1 + h / 4)
    have hRvol : volume R = ENNReal.ofReal (h ^ 2 / 8) := by
      rw [causalHardScoreBox_volume (by linarith) (by linarith)]
      congr 1
      ring
    rw [← hRvol]
    apply measure_mono
    intro z hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      fin_cases i
      · change -3 ≤ z 0 ∧ z 0 ≤ 3
        exact ⟨by linarith [hz.1, hx'.1], by linarith [hz.2.1, hx'.2.1]⟩
      · change -3 ≤ z 1 ∧ z 1 ≤ 3
        exact ⟨by linarith [hz.2.2.1, hx'.2.2.1],
          by linarith [hz.2.2.2, hx'.2.2.2.1]⟩
    · intro hA; linarith [hA.2.1, hz.1]
    · apply mem_closedBall_of_coordinate_diff_le_half hh.le
      · rw [abs_of_nonneg (by linarith [hz.1])]; linarith [hz.2.1]
      · rw [abs_le]; exact ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
  · let R := causalHardScoreBox (x 0 - h / 4) (x 0 + h / 4)
        (x 1 - h / 2) (x 1 - h / 4)
    have hRvol : volume R = ENNReal.ofReal (h ^ 2 / 8) := by
      rw [causalHardScoreBox_volume (by linarith) (by linarith)]
      congr 1
      ring
    rw [← hRvol]
    apply measure_mono
    intro z hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      fin_cases i
      · change -3 ≤ z 0 ∧ z 0 ≤ 3
        exact ⟨by linarith [hz.1, hx'.1], by linarith [hz.2.1, hx'.2.1]⟩
      · change -3 ≤ z 1 ∧ z 1 ≤ 3
        exact ⟨by linarith [hz.2.2.1, hx'.2.2.1],
          by linarith [hz.2.2.2, hx'.2.2.2.1]⟩
    · intro hA; linarith [hA.2.2.1, hz.2.2.2]
    · apply mem_closedBall_of_coordinate_diff_le_half hh.le
      · rw [abs_le]; exact ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
      · rw [abs_of_nonpos (by linarith [hz.2.2.2])]; linarith [hz.2.2.1]
  · let R := causalHardScoreBox (x 0 - h / 4) (x 0 + h / 4)
        (x 1 + h / 4) (x 1 + h / 2)
    have hRvol : volume R = ENNReal.ofReal (h ^ 2 / 8) := by
      rw [causalHardScoreBox_volume (by linarith) (by linarith)]
      congr 1
      ring
    rw [← hRvol]
    apply measure_mono
    intro z hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      fin_cases i
      · change -3 ≤ z 0 ∧ z 0 ≤ 3
        exact ⟨by linarith [hz.1, hx'.1], by linarith [hz.2.1, hx'.2.1]⟩
      · change -3 ≤ z 1 ∧ z 1 ≤ 3
        exact ⟨by linarith [hz.2.2.1, hx'.2.2.1],
          by linarith [hz.2.2.2, hx'.2.2.2.1]⟩
    · intro hA; linarith [hA.2.2.2, hz.2.2.1]
    · apply mem_closedBall_of_coordinate_diff_le_half hh.le
      · rw [abs_le]; exact ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
      · rw [abs_of_nonneg (by linarith [hz.2.2.1])]; linarith [hz.2.2.2]

/-- The two fixed assignment arms have a common quadratic intersection-area
lower bound at every interface point. -/
-- @node: causalHardArm_inter_closedBall_volume_lower
lemma causalHardArm_inter_closedBall_volume_lower (t : Bool)
    {x : Score} {h : ℝ} (hx : x ∈ frontier causalHardArmOne)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    ENNReal.ofReal (h ^ 2 / 8) ≤
      volume ((if t then causalHardArmOne else
        causalHardSquare \ causalHardArmOne) ∩ Metric.closedBall x h) := by
  cases t with
  | false => exact causalHardArmZero_inter_closedBall_volume_lower hx hh hh1
  | true =>
      exact (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg h])).trans
        (causalHardArmOne_inter_closedBall_volume_lower hx hh hh1)

/-- The uniform kernel is one exactly on its defining unit interval. -/
-- @node: uniformKernel_eq_one_iff_abs_le
lemma uniformKernel_eq_one_iff_abs_le (u : ℝ) :
    uniformKernel u = 1 ↔ |u| ≤ 1 := by
  by_cases hu : u ∈ Set.Icc (-1 : ℝ) 1
  · rw [uniformKernel, Set.indicator_of_mem hu]
    simp [abs_le.mpr hu]
  · rw [uniformKernel, Set.indicator_of_notMem hu]
    simp only [zero_ne_one, false_iff]
    exact fun ha ↦ hu (abs_le.mp ha)

/-- At positive bandwidth, either signed radial argument has uniform-kernel
weight one exactly on the closed metric ball of that bandwidth. -/
-- @node: uniformKernel_signedDist_eq_one_iff
lemma uniformKernel_signedDist_eq_one_iff (t : Bool) (x z : Score)
    {h : ℝ} (hh : 0 < h) :
    uniformKernel (((if t then 1 else -1 : ℝ) * dist z x) / h) = 1 ↔
      z ∈ Metric.closedBall x h := by
  rw [uniformKernel_eq_one_iff_abs_le, Metric.mem_closedBall]
  have hsign : |(if t then 1 else -1 : ℝ)| = 1 := by
    cases t <;> norm_num
  rw [abs_div, abs_mul, hsign, one_mul, abs_of_pos hh]
  rw [abs_of_nonneg dist_nonneg, div_le_one hh, dist_comm]

/-- The nonnegative integrand defining arm local mass is the constant
`h⁻²` on the arm's closed bandwidth ball and zero elsewhere. -/
-- @node: armLocalMass_integrand_eq_indicator_closedBall
lemma armLocalMass_integrand_eq_indicator_closedBall
    (t : Bool) (x z : Score) {h : ℝ} (hh : 0 < h) :
    ENNReal.ofReal (h⁻¹ ^ 2 *
        uniformKernel (((if t then 1 else -1 : ℝ) * dist z x) / h)) =
      (Metric.closedBall x h).indicator
        (fun _ : Score ↦ ENNReal.ofReal (h⁻¹ ^ 2)) z := by
  by_cases hz : z ∈ Metric.closedBall x h
  · rw [Set.indicator_of_mem hz,
      (uniformKernel_signedDist_eq_one_iff t x z hh).2 hz, mul_one]
  · rw [Set.indicator_of_notMem hz]
    have hk : uniformKernel (((if t then 1 else -1 : ℝ) * dist z x) / h) = 0 := by
      unfold uniformKernel
      rw [Set.indicator_of_notMem]
      intro hu
      exact hz ((uniformKernel_signedDist_eq_one_iff t x z hh).1
        (by rw [uniformKernel, Set.indicator_of_mem hu]))
    rw [hk, mul_zero, ENNReal.ofReal_zero]

/-- Arm local mass is the normalized Lebesgue area of the intersection of
the chosen assignment arm with the closed bandwidth ball. -/
-- @node: armLocalMass_eq_normalized_inter_closedBall
lemma armLocalMass_eq_normalized_inter_closedBall
    (P : A1A2Law) (t : Bool) (x : Score) {h : ℝ} (hh : 0 < h) :
    armLocalMass P t x h =
      ENNReal.ofReal (h⁻¹ ^ 2) *
        volume ((if t then P.A1 else P.A0) ∩ Metric.closedBall x h) := by
  unfold armLocalMass
  simp_rw [armLocalMass_integrand_eq_indicator_closedBall t x _ hh]
  rw [setLIntegral_indicator Metric.isClosed_closedBall.measurableSet]
  rw [setLIntegral_const]
  rw [inter_comm]

/-- The fixed hard-square arms have normalized uniform-kernel local mass at
least `1/8` at every interface point and every bandwidth at most one. -/
-- @node: causalHardArmLocalMass_lower
lemma causalHardArmLocalMass_lower (P : A1A2Law) (t : Bool)
    {x : Score} {h : ℝ}
    (hA1 : P.A1 = causalHardArmOne)
    (hA0 : P.A0 = causalHardSquare \ causalHardArmOne)
    (hx : x ∈ frontier causalHardArmOne) (hh : 0 < h) (hh1 : h ≤ 1) :
    ENNReal.ofReal (1 / 8 : ℝ) ≤ armLocalMass P t x h := by
  rw [armLocalMass_eq_normalized_inter_closedBall P t x hh, hA1, hA0]
  have harea := causalHardArm_inter_closedBall_volume_lower t hx hh hh1
  calc
    ENNReal.ofReal (1 / 8 : ℝ) =
        ENNReal.ofReal (h⁻¹ ^ 2) * ENNReal.ofReal (h ^ 2 / 8) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ h⁻¹ ^ 2)]
      congr 1
      field_simp
    _ ≤ _ := mul_le_mul_right harea _

/-- Every explicit angular hard law satisfies the class's uniform local-mass
clause once the envelope is at least `48`. -/
-- @node: causalHardA1A2Law_localMass_certificate
lemma causalHardA1A2Law_localMass_certificate {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare)
    {L : ℝ} (hL : 48 ≤ L) :
    let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
      hdelta hw hsep hcell
    ∀ t x h, x ∈ P.boundary → 0 < h → h ≤ L⁻¹ →
      ENNReal.ofReal L⁻¹ ≤ armLocalMass P t x h := by
  dsimp only
  intro t x h hx hh hhL
  let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
    hdelta hw hsep hcell
  have hgeom := causalHardA1A2Law_geometry b cA delta w centers omega hb
    hscale hcA hdelta hw hsep hcell
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hh1 : h ≤ 1 := hhL.trans ((inv_le_one₀ hLpos).2 (by linarith))
  have hconst : ENNReal.ofReal L⁻¹ ≤ ENNReal.ofReal (1 / 8 : ℝ) := by
    apply ENNReal.ofReal_le_ofReal
    simpa only [one_div] using
      (inv_le_inv₀ hLpos (by norm_num : (0 : ℝ) < 8)).mpr (by linarith)
  exact hconst.trans (causalHardArmLocalMass_lower P t hgeom.2.1
    hgeom.2.2.1 (hgeom.2.2.2 ▸ hx) hh hh1)

end CausalSmith.Stat.BddUniformLogPenalty
