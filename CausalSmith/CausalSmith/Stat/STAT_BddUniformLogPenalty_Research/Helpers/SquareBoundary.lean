import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularGrid

/-!
# Rectifiable boundary of the packing square

This file gives an explicit piecewise-linear traversal of the boundary of the
unit square and proves the Lipschitz and image properties needed by the CTY
law class.
-/

open Set
open scoped NNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The horizontal coordinate of the counterclockwise square-boundary path. -/
-- @node: squareFrontierX
noncomputable def squareFrontierX (t : ℝ) : ℝ :=
  min (1 / 2) (max (-1 / 2) (min (-1 / 2 + 4 * t) (5 / 2 - 4 * t)))

/-- The vertical coordinate of the counterclockwise square-boundary path. -/
-- @node: squareFrontierY
noncomputable def squareFrontierY (t : ℝ) : ℝ :=
  min (1 / 2) (max (-1 / 2) (min (-3 / 2 + 4 * t) (7 / 2 - 4 * t)))

/-- An explicit traversal of the four edges of the unit square. -/
-- @node: squareFrontierParam
noncomputable def squareFrontierParam (t : ℝ) : Score :=
  scorePoint (squareFrontierX t) (squareFrontierY t)

/-- Both scalar coordinates of the square-boundary path are globally
`4`-Lipschitz. -/
-- @node: squareFrontier_coordinates_lipschitz
lemma squareFrontier_coordinates_lipschitz :
    LipschitzWith 4 squareFrontierX ∧ LipschitzWith 4 squareFrontierY := by
  have hfour : LipschitzWith 4 (fun t : ℝ => 4 * t) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.dist_eq, Real.dist_eq]
    rw [show 4 * s - 4 * t = 4 * (s - t) by ring, abs_mul]
    norm_num
  have hnegfour : LipschitzWith 4 (fun t : ℝ => -4 * t) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.dist_eq, Real.dist_eq]
    rw [show -4 * s - -4 * t = -4 * (s - t) by ring, abs_mul]
    norm_num
  constructor
  · have hrise : LipschitzWith 4 (fun t : ℝ => -1 / 2 + 4 * t) := by
      apply LipschitzWith.of_dist_le_mul
      intro s t
      simpa [Real.dist_eq, abs_mul, mul_comm] using hfour.dist_le_mul s t
    have hfall : LipschitzWith 4 (fun t : ℝ => 5 / 2 - 4 * t) := by
      apply LipschitzWith.of_dist_le_mul
      intro s t
      convert hnegfour.dist_le_mul s t using 1 <;> simp [Real.dist_eq]
      rw [show 5 / 2 - 4 * s + 4 * t - 5 / 2 = -(4 * s - 4 * t) by ring,
        abs_neg]
    unfold squareFrontierX
    convert ((hrise.min hfall).const_max (-1 / 2)).min_const (1 / 2) using 1 <;>
      norm_num [min_comm]
  · have hrise : LipschitzWith 4 (fun t : ℝ => -3 / 2 + 4 * t) := by
      apply LipschitzWith.of_dist_le_mul
      intro s t
      simpa [Real.dist_eq, abs_mul, mul_comm] using hfour.dist_le_mul s t
    have hfall : LipschitzWith 4 (fun t : ℝ => 7 / 2 - 4 * t) := by
      apply LipschitzWith.of_dist_le_mul
      intro s t
      convert hnegfour.dist_le_mul s t using 1 <;> simp [Real.dist_eq]
      rw [show 7 / 2 - 4 * s + 4 * t - 7 / 2 = -(4 * s - 4 * t) by ring,
        abs_neg]
    unfold squareFrontierY
    convert ((hrise.min hfall).const_max (-1 / 2)).min_const (1 / 2) using 1 <;>
      norm_num [min_comm]

/-- The explicit square-boundary traversal is globally Lipschitz. -/
-- @node: squareFrontierParam_lipschitz
lemma squareFrontierParam_lipschitz : LipschitzWith 8 squareFrontierParam := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hx := squareFrontier_coordinates_lipschitz.1.dist_le_mul s t
  have hy := squareFrontier_coordinates_lipschitz.2.dist_le_mul s t
  have htri := dist_triangle
    (scorePoint (squareFrontierX s) (squareFrontierY s))
    (scorePoint (squareFrontierX t) (squareFrontierY s))
    (scorePoint (squareFrontierX t) (squareFrontierY t))
  rw [dist_scorePoint_same_second, dist_scorePoint_same_first] at htri
  rw [squareFrontierParam, squareFrontierParam]
  calc
    _ ≤ |squareFrontierX s - squareFrontierX t| +
        |squareFrontierY s - squareFrontierY t| := htri
    _ ≤ (4 : ℝ) * dist s t + 4 * dist s t := add_le_add hx hy
    _ = (8 : ℝ) * dist s t := by ring

/-- A point is on the frontier of the unit square exactly when both
coordinates are bounded by `1/2` and at least one coordinate is extremal. -/
-- @node: mem_frontier_scoreCube_half_iff
lemma mem_frontier_scoreCube_half_iff (x : Score) :
    x ∈ frontier (scoreCube (1 / 2 : ℝ)) ↔
      |x 0| ≤ 1 / 2 ∧ |x 1| ≤ 1 / 2 ∧
        (|x 0| = 1 / 2 ∨ |x 1| = 1 / 2) := by
  have hclosed : IsClosed (scoreCube (1 / 2 : ℝ)) := by
    unfold scoreCube
    rw [show {z : Score | ∀ i, |z i| ≤ (1 / 2 : ℝ)} =
        ⋂ i : Fin 2, {z : Score | |z i| ≤ (1 / 2 : ℝ)} by ext z; simp]
    exact isClosed_iInter (fun i => isClosed_le
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) i).abs)
      continuous_const)
  constructor
  · intro hx
    have hmem : x ∈ scoreCube (1 / 2 : ℝ) := by
      have := frontier_subset_closure hx
      rw [hclosed.closure_eq] at this
      exact this
    have h0 := hmem (0 : Fin 2)
    have h1 := hmem (1 : Fin 2)
    refine ⟨h0, h1, ?_⟩
    by_contra heq
    push_neg at heq
    have h0lt : |x 0| < 1 / 2 := lt_of_le_of_ne h0 heq.1
    have h1lt : |x 1| < 1 / 2 := lt_of_le_of_ne h1 heq.2
    let ε := min (1 / 2 - |x 0|) (1 / 2 - |x 1|)
    have hε : 0 < ε := by
      dsimp [ε]
      exact lt_min (by linarith) (by linarith)
    have hball : Metric.ball x ε ⊆ scoreCube (1 / 2 : ℝ) := by
      intro y hy i
      have hcoord : |y i - x i| ≤ dist y x := by
        simpa [dist_eq_norm, Real.norm_eq_abs] using
          (PiLp.norm_apply_le (y - x) i)
      have hdist : dist y x < ε := by
        simpa [Metric.mem_ball, dist_comm] using hy
      have hmargin : ε ≤ 1 / 2 - |x i| := by
        fin_cases i <;> simp [ε]
      exact (calc
        |y i| = |x i + (y i - x i)| := by congr 1 <;> ring
        _ ≤ |x i| + |y i - x i| := abs_add_le _ _
        _ ≤ |x i| + dist y x := by
          simpa [add_comm] using add_le_add_left hcoord |x i|
        _ < |x i| + ε := by simpa using add_lt_add_left hdist |x i|
        _ ≤ 1 / 2 := by linarith).le
    have hinterior : x ∈ interior (scoreCube (1 / 2 : ℝ)) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (Metric.ball_mem_nhds x hε) hball
    exact (mem_frontier_iff_notMem_interior hmem).mp hx hinterior
  · rintro ⟨h0, h1, hedge⟩
    have hmem : x ∈ scoreCube (1 / 2 : ℝ) := by
      intro i
      fin_cases i
      · exact h0
      · exact h1
    rw [mem_frontier_iff_notMem_interior hmem]
    intro hinterior
    rw [mem_interior_iff_mem_nhds] at hinterior
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hinterior
    rcases hedge with hedge | hedge
    · rcases (abs_eq (by norm_num : 0 ≤ (1 / 2 : ℝ))).mp hedge with hx0 | hx0
      · let y := scorePoint (x 0 + ε / 2) (x 1)
        have hxrepr : x = scorePoint (x 0) (x 1) := by
          ext i
          fin_cases i <;> simp [scorePoint]
        have hydist : dist y x = ε / 2 := by
          calc
            dist y x = dist y (scorePoint (x 0) (x 1)) := congrArg (dist y) hxrepr
            _ = ε / 2 := by
              simp only [y]
              rw [dist_scorePoint_same_second]
              rw [show x 0 + ε / 2 - x 0 = ε / 2 by ring,
                abs_of_pos (half_pos hε)]
        have hyS := hball (show y ∈ Metric.ball x ε by
          rw [Metric.mem_ball, hydist]
          exact half_lt_self hε)
        have := hyS (0 : Fin 2)
        simp [y, scorePoint, hx0] at this
        rw [abs_of_pos (by linarith : 0 < (2⁻¹ : ℝ) + ε / 2)] at this
        linarith
      · let y := scorePoint (x 0 - ε / 2) (x 1)
        have hxrepr : x = scorePoint (x 0) (x 1) := by
          ext i
          fin_cases i <;> simp [scorePoint]
        have hydist : dist y x = ε / 2 := by
          calc
            dist y x = dist y (scorePoint (x 0) (x 1)) := congrArg (dist y) hxrepr
            _ = ε / 2 := by
              simp only [y]
              rw [dist_scorePoint_same_second]
              rw [show x 0 - ε / 2 - x 0 = -(ε / 2) by ring, abs_neg,
                abs_of_pos (half_pos hε)]
        have hyS := hball (show y ∈ Metric.ball x ε by
          rw [Metric.mem_ball, hydist]
          exact half_lt_self hε)
        have := hyS (0 : Fin 2)
        simp [y, scorePoint, hx0] at this
        rw [abs_of_neg (by linarith : (-2⁻¹ : ℝ) - ε / 2 < 0)] at this
        linarith
    · rcases (abs_eq (by norm_num : 0 ≤ (1 / 2 : ℝ))).mp hedge with hx1 | hx1
      · let y := scorePoint (x 0) (x 1 + ε / 2)
        have hxrepr : x = scorePoint (x 0) (x 1) := by
          ext i
          fin_cases i <;> simp [scorePoint]
        have hydist : dist y x = ε / 2 := by
          calc
            dist y x = dist y (scorePoint (x 0) (x 1)) := congrArg (dist y) hxrepr
            _ = ε / 2 := by
              simp only [y]
              rw [dist_scorePoint_same_first]
              rw [show x 1 + ε / 2 - x 1 = ε / 2 by ring,
                abs_of_pos (half_pos hε)]
        have hyS := hball (show y ∈ Metric.ball x ε by
          rw [Metric.mem_ball, hydist]
          exact half_lt_self hε)
        have := hyS (1 : Fin 2)
        simp [y, scorePoint, hx1] at this
        rw [abs_of_pos (by linarith : 0 < (2⁻¹ : ℝ) + ε / 2)] at this
        linarith
      · let y := scorePoint (x 0) (x 1 - ε / 2)
        have hxrepr : x = scorePoint (x 0) (x 1) := by
          ext i
          fin_cases i <;> simp [scorePoint]
        have hydist : dist y x = ε / 2 := by
          calc
            dist y x = dist y (scorePoint (x 0) (x 1)) := congrArg (dist y) hxrepr
            _ = ε / 2 := by
              simp only [y]
              rw [dist_scorePoint_same_first]
              rw [show x 1 - ε / 2 - x 1 = -(ε / 2) by ring, abs_neg,
                abs_of_pos (half_pos hε)]
        have hyS := hball (show y ∈ Metric.ball x ε by
          rw [Metric.mem_ball, hydist]
          exact half_lt_self hε)
        have := hyS (1 : Fin 2)
        simp [y, scorePoint, hx1] at this
        rw [abs_of_neg (by linarith : (-2⁻¹ : ℝ) - ε / 2 < 0)] at this
        linarith

/-- The second quarter of the path parametrizes the right edge. -/
-- @node: squareFrontierParam_right_edge
lemma squareFrontierParam_right_edge {y : ℝ} (hy0 : -(1 / 2) ≤ y)
    (hy1 : y ≤ 1 / 2) :
    squareFrontierParam ((y + 3 / 2) / 4) = scorePoint (1 / 2) y := by
  have hy0' : (-1 / 2 : ℝ) ≤ y := by norm_num at hy0 ⊢; exact hy0
  rw [squareFrontierParam]
  apply congrArg₂ scorePoint
  · unfold squareFrontierX
    rw [show -1 / 2 + 4 * ((y + 3 / 2) / 4) = y + 1 by ring,
      show 5 / 2 - 4 * ((y + 3 / 2) / 4) = 1 - y by ring]
    exact min_eq_left ((le_min (by linarith) (by linarith)).trans (le_max_right _ _))
  · unfold squareFrontierY
    rw [show -3 / 2 + 4 * ((y + 3 / 2) / 4) = y by ring,
      show 7 / 2 - 4 * ((y + 3 / 2) / 4) = 2 - y by ring]
    have hinner : min y (2 - y) = y := min_eq_left (by linarith)
    rw [hinner, max_eq_right hy0', min_eq_right hy1]

/-- The fourth quarter of the path parametrizes the left edge. -/
-- @node: squareFrontierParam_left_edge
lemma squareFrontierParam_left_edge {y : ℝ} (hy0 : -(1 / 2) ≤ y)
    (hy1 : y ≤ 1 / 2) :
    squareFrontierParam ((7 / 2 - y) / 4) = scorePoint (-(1 / 2)) y := by
  have hy0' : (-1 / 2 : ℝ) ≤ y := by norm_num at hy0 ⊢; exact hy0
  rw [squareFrontierParam]
  apply congrArg₂ scorePoint
  · unfold squareFrontierX
    rw [show -1 / 2 + 4 * ((7 / 2 - y) / 4) = 3 - y by ring,
      show 5 / 2 - 4 * ((7 / 2 - y) / 4) = y - 1 by ring]
    have hinner : min (3 - y) (y - 1) = y - 1 := min_eq_right (by linarith)
    rw [hinner, max_eq_left (by linarith), min_eq_right (by norm_num)]
    norm_num
  · unfold squareFrontierY
    rw [show -3 / 2 + 4 * ((7 / 2 - y) / 4) = 2 - y by ring,
      show 7 / 2 - 4 * ((7 / 2 - y) / 4) = y by ring]
    have hinner : min (2 - y) y = y := min_eq_right (by linarith)
    rw [hinner, max_eq_right hy0', min_eq_right hy1]

/-- The third quarter of the path parametrizes the top edge. -/
-- @node: squareFrontierParam_top_edge
lemma squareFrontierParam_top_edge {x : ℝ} (hx0 : -(1 / 2) ≤ x)
    (hx1 : x ≤ 1 / 2) :
    squareFrontierParam ((5 / 2 - x) / 4) = scorePoint x (1 / 2) := by
  have hx0' : (-1 / 2 : ℝ) ≤ x := by norm_num at hx0 ⊢; exact hx0
  rw [squareFrontierParam]
  apply congrArg₂ scorePoint
  · unfold squareFrontierX
    rw [show -1 / 2 + 4 * ((5 / 2 - x) / 4) = 2 - x by ring,
      show 5 / 2 - 4 * ((5 / 2 - x) / 4) = x by ring]
    have hinner : min (2 - x) x = x := min_eq_right (by linarith)
    rw [hinner, max_eq_right hx0', min_eq_right hx1]
  · unfold squareFrontierY
    rw [show -3 / 2 + 4 * ((5 / 2 - x) / 4) = 1 - x by ring,
      show 7 / 2 - 4 * ((5 / 2 - x) / 4) = 1 + x by ring]
    exact min_eq_left ((le_min (by linarith) (by linarith)).trans (le_max_right _ _))

/-- The first quarter of the path parametrizes the bottom edge. -/
-- @node: squareFrontierParam_bottom_edge
lemma squareFrontierParam_bottom_edge {x : ℝ} (hx0 : -(1 / 2) ≤ x)
    (hx1 : x ≤ 1 / 2) :
    squareFrontierParam ((x + 1 / 2) / 4) = scorePoint x (-(1 / 2)) := by
  have hx0' : (-1 / 2 : ℝ) ≤ x := by norm_num at hx0 ⊢; exact hx0
  rw [squareFrontierParam]
  apply congrArg₂ scorePoint
  · unfold squareFrontierX
    rw [show -1 / 2 + 4 * ((x + 1 / 2) / 4) = x by ring,
      show 5 / 2 - 4 * ((x + 1 / 2) / 4) = 2 - x by ring]
    have hinner : min x (2 - x) = x := min_eq_left (by linarith)
    rw [hinner, max_eq_right hx0', min_eq_right hx1]
  · unfold squareFrontierY
    rw [show -3 / 2 + 4 * ((x + 1 / 2) / 4) = x - 1 by ring,
      show 7 / 2 - 4 * ((x + 1 / 2) / 4) = 3 - x by ring]
    have hinner : min (x - 1) (3 - x) = x - 1 := min_eq_left (by linarith)
    rw [hinner, max_eq_left (by linarith), min_eq_right (by norm_num)]
    norm_num

/-- The explicit path has exactly the frontier of the unit square as its
image on the unit interval. -/
-- @node: squareFrontierParam_image
lemma squareFrontierParam_image :
    squareFrontierParam '' Icc (0 : ℝ) 1 = frontier (scoreCube (1 / 2 : ℝ)) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [mem_frontier_scoreCube_half_iff]
    simp only [squareFrontierParam, scorePoint_apply_zero, scorePoint_apply_one]
    have hxrange : |squareFrontierX t| ≤ (1 / 2 : ℝ) := by
      rw [abs_le]
      constructor
      · have hbase : -(1 / 2 : ℝ) ≤ (-1 / 2 : ℝ) := by norm_num
        unfold squareFrontierX
        exact le_min (by norm_num) (hbase.trans (le_max_left _ _))
      · exact min_le_left _ _
    have hyrange : |squareFrontierY t| ≤ (1 / 2 : ℝ) := by
      rw [abs_le]
      constructor
      · have hbase : -(1 / 2 : ℝ) ≤ (-1 / 2 : ℝ) := by norm_num
        unfold squareFrontierY
        exact le_min (by norm_num) (hbase.trans (le_max_left _ _))
      · exact min_le_left _ _
    refine ⟨hxrange, hyrange, ?_⟩
    rcases le_total t (1 / 4 : ℝ) with ht1 | ht1
    · have hy : squareFrontierY t = (-1 / 2 : ℝ) := by
        have hylo : -3 / 2 + 4 * t ≤ -1 / 2 := by linarith
        have hyhi : -3 / 2 + 4 * t ≤ 7 / 2 - 4 * t := by linarith [ht.2]
        rw [squareFrontierY, min_eq_left hyhi, max_eq_left hylo]
        norm_num
      exact Or.inr (by rw [hy]; norm_num)
    · rcases le_total t (1 / 2 : ℝ) with ht2 | ht2
      · have hx : squareFrontierX t = (1 / 2 : ℝ) := by
          have hxrise : 1 / 2 ≤ -1 / 2 + 4 * t := by linarith
          have hxfall : 1 / 2 ≤ 5 / 2 - 4 * t := by linarith
          rw [squareFrontierX, min_eq_left]
          exact (le_min hxrise hxfall).trans (le_max_right _ _)
        exact Or.inl (by rw [hx]; norm_num)
      · rcases le_total t (3 / 4 : ℝ) with ht3 | ht3
        · have hy : squareFrontierY t = (1 / 2 : ℝ) := by
            have hyrise : 1 / 2 ≤ -3 / 2 + 4 * t := by linarith
            have hyfall : 1 / 2 ≤ 7 / 2 - 4 * t := by linarith
            rw [squareFrontierY, min_eq_left]
            exact (le_min hyrise hyfall).trans (le_max_right _ _)
          exact Or.inr (by rw [hy]; norm_num)
        · have hx : squareFrontierX t = (-1 / 2 : ℝ) := by
            have hxlo : 5 / 2 - 4 * t ≤ -1 / 2 := by linarith
            have hxord : 5 / 2 - 4 * t ≤ -1 / 2 + 4 * t := by linarith
            rw [squareFrontierX, min_eq_right hxord, max_eq_left hxlo]
            norm_num
          exact Or.inl (by rw [hx]; norm_num)
  · intro hx
    rcases (mem_frontier_scoreCube_half_iff x).mp hx with ⟨h0, h1, hedge⟩
    rw [abs_le] at h0 h1
    rcases hedge with hedge | hedge
    · rcases (abs_eq (by norm_num : 0 ≤ (1 / 2 : ℝ))).mp hedge with hx0 | hx0
      · refine ⟨(x 1 + 3 / 2) / 4, ⟨by linarith, by linarith⟩, ?_⟩
        rw [squareFrontierParam_right_edge h1.1 h1.2]
        ext i
        fin_cases i <;> simp [scorePoint, hx0]
      · refine ⟨(7 / 2 - x 1) / 4, ⟨by linarith, by linarith⟩, ?_⟩
        rw [squareFrontierParam_left_edge h1.1 h1.2]
        ext i
        fin_cases i <;> simp [scorePoint, hx0]
    · rcases (abs_eq (by norm_num : 0 ≤ (1 / 2 : ℝ))).mp hedge with hx1 | hx1
      · refine ⟨(5 / 2 - x 0) / 4, ⟨by linarith, by linarith⟩, ?_⟩
        rw [squareFrontierParam_top_edge h0.1 h0.2]
        ext i
        fin_cases i <;> simp [scorePoint, hx1]
      · refine ⟨(x 0 + 1 / 2) / 4, ⟨by linarith, by linarith⟩, ?_⟩
        rw [squareFrontierParam_bottom_edge h0.1 h0.2]
        ext i
        fin_cases i <;> simp [scorePoint, hx1]

/-- The boundary of the packing square is rectifiable, witnessed by the
explicit eight-Lipschitz traversal above. -/
-- @node: packingSquare_rectifiableBoundary
lemma packingSquare_rectifiableBoundary :
    RectifiableBoundary (scoreCube (1 / 2 : ℝ)) := by
  refine ⟨8, squareFrontierParam, squareFrontierParam_lipschitz.lipschitzOnWith, ?_⟩
  exact squareFrontierParam_image

end CausalSmith.Stat.BddUniformLogPenalty
