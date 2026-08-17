import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Basic

/-!
# Lower-edge angular packing grid

This file constructs an explicit equispaced family of centers on the middle
half of the lower edge of the unit square. It proves boundary membership,
exact pairwise distances, quantitative separation, and disjointness of the
associated closed half-disc cells.
-/

open Set Filter

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- A point of the Euclidean score plane specified by its two coordinates. -/
-- @node: scorePoint
noncomputable def scorePoint (x y : ℝ) : Score :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

/-- The first coordinate of an explicitly specified score point. -/
-- @node: scorePoint_apply_zero
lemma scorePoint_apply_zero (x y : ℝ) : scorePoint x y 0 = x := by
  simp [scorePoint]

/-- The second coordinate of an explicitly specified score point. -/
-- @node: scorePoint_apply_one
lemma scorePoint_apply_one (x y : ℝ) : scorePoint x y 1 = y := by
  simp [scorePoint]

/-- Euclidean distance between two points on a horizontal line is their
one-dimensional horizontal distance. -/
-- @node: dist_scorePoint_same_second
lemma dist_scorePoint_same_second (x x' y : ℝ) :
    dist (scorePoint x y) (scorePoint x' y) = |x - x'| := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp [scorePoint, Fin.sum_univ_two, Real.norm_eq_abs]
  exact Real.sqrt_sq_eq_abs _

/-- Euclidean distance between two points on a vertical line is their
one-dimensional vertical distance. -/
-- @node: dist_scorePoint_same_first
lemma dist_scorePoint_same_first (x y y' : ℝ) :
    dist (scorePoint x y) (scorePoint x y') = |y - y'| := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp [scorePoint, Fin.sum_univ_two, Real.norm_eq_abs]
  exact Real.sqrt_sq_eq_abs _

/-- Every non-corner point on the lower edge belongs to the frontier of the
unit square. -/
-- @node: lowerEdgePoint_mem_frontier
lemma lowerEdgePoint_mem_frontier (x : ℝ) (hx : |x| < (1 / 2 : ℝ)) :
    scorePoint x (-1 / 2) ∈ frontier (scoreCube (1 / 2)) := by
  rw [frontier_eq_closure_inter_closure]
  constructor
  · have hclosed : IsClosed (scoreCube (1 / 2 : ℝ)) := by
      unfold scoreCube
      rw [show {z : Score | ∀ i, |z i| ≤ (1 / 2 : ℝ)} =
          ⋂ i : Fin 2, {z : Score | |z i| ≤ (1 / 2 : ℝ)} by ext z; simp]
      exact isClosed_iInter (fun i => isClosed_le
        ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) i).abs)
        continuous_const)
    rw [hclosed.closure_eq]
    intro i
    fin_cases i
    · simpa [scoreCube, scorePoint] using hx.le
    · norm_num [scoreCube, scorePoint]
  · rw [mem_closure_iff]
    intro U hU hxU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ hxU
    let z := scorePoint x (-1 / 2 - ε / 2)
    have hzdist : dist z (scorePoint x (-1 / 2)) = ε / 2 := by
      unfold z
      rw [dist_scorePoint_same_first]
      rw [show -1 / 2 - ε / 2 - -1 / 2 = -(ε / 2) by ring,
        abs_neg, abs_of_pos (half_pos hε)]
    have hzU : z ∈ U := hball (by simpa [hzdist] using half_lt_self hε)
    refine ⟨z, hzU, ?_⟩
    intro hzS
    have hzbound := hzS (1 : Fin 2)
    simp [z, scorePoint] at hzbound
    have hlow := neg_le_of_abs_le hzbound
    norm_num at hlow
    linarith

/-- The explicit equispaced `Fin M` grid on the middle half of the square's
lower edge. -/
-- @node: angularGridCenter
noncomputable def angularGridCenter (M : ℕ) (j : Fin M) : Score :=
  scorePoint (-1 / 4 + ((j : ℕ) + 1 : ℝ) / (2 * (M + 1 : ℕ))) (-1 / 2)

/-- Formula for the horizontal coordinate of a grid center. -/
-- @node: angularGridCenter_apply_zero
lemma angularGridCenter_apply_zero (M : ℕ) (j : Fin M) :
    angularGridCenter M j 0 =
      -1 / 4 + ((j : ℕ) + 1 : ℝ) / (2 * (M + 1 : ℕ)) := by
  simp [angularGridCenter, scorePoint_apply_zero]

/-- Every grid center lies on the lower edge. -/
-- @node: angularGridCenter_apply_one
lemma angularGridCenter_apply_one (M : ℕ) (j : Fin M) :
    angularGridCenter M j 1 = -1 / 2 := by
  simp [angularGridCenter, scorePoint_apply_one]

/-- Grid centers remain strictly inside the middle horizontal span, hence
avoid both lower corners. -/
-- @node: angularGridCenter_first_abs_lt
lemma angularGridCenter_first_abs_lt (M : ℕ) (j : Fin M) :
    |angularGridCenter M j 0| < (1 / 2 : ℝ) := by
  have hj : (j : ℕ) + 1 ≤ M := j.isLt
  have hnum : (((j : ℕ) + 1 : ℕ) : ℝ) < ((M + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_of_le hj
  have hden : 0 < (2 * (M + 1 : ℕ) : ℝ) := by positivity
  have hfrac0 : 0 < (((j : ℕ) + 1 : ℝ) / (2 * (M + 1 : ℕ))) := by positivity
  have hfrac : (((j : ℕ) + 1 : ℝ) / (2 * (M + 1 : ℕ))) < 1 / 2 := by
    apply (div_lt_iff₀ hden).2
    push_cast at hnum ⊢
    nlinarith
  rw [angularGridCenter_apply_zero, abs_lt]
  constructor <;> linarith

/-- Grid centers lie strictly in the middle half of the lower edge, so in
particular none of them is a corner of the square. -/
-- @node: angularGridCenter_first_abs_lt_quarter
lemma angularGridCenter_first_abs_lt_quarter (M : ℕ) (j : Fin M) :
    |angularGridCenter M j 0| < (1 / 4 : ℝ) := by
  have hj : (j : ℕ) + 1 ≤ M := j.isLt
  have hnum : (((j : ℕ) + 1 : ℕ) : ℝ) < ((M + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_of_le hj
  have hden : 0 < (2 * (M + 1 : ℕ) : ℝ) := by positivity
  have hfrac0 : 0 < (((j : ℕ) + 1 : ℝ) / (2 * (M + 1 : ℕ))) := by
    positivity
  have hfrac : (((j : ℕ) + 1 : ℝ) / (2 * (M + 1 : ℕ))) < 1 / 2 := by
    apply (div_lt_iff₀ hden).2
    push_cast at hnum ⊢
    nlinarith
  rw [angularGridCenter_apply_zero, abs_lt]
  constructor <;> linarith

/-- Every grid center lies on the frontier of the unit square. -/
-- @node: angularGridCenter_mem_frontier
lemma angularGridCenter_mem_frontier (M : ℕ) (j : Fin M) :
    angularGridCenter M j ∈ frontier (scoreCube (1 / 2)) := by
  rw [angularGridCenter]
  exact lowerEdgePoint_mem_frontier _ (angularGridCenter_first_abs_lt M j)

/-- Exact pairwise distance formula for the equispaced lower-edge grid. -/
-- @node: angularGridCenter_dist
lemma angularGridCenter_dist (M : ℕ) (i j : Fin M) :
    dist (angularGridCenter M i) (angularGridCenter M j) =
      |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| / (2 * (M + 1 : ℕ)) := by
  rw [angularGridCenter, angularGridCenter, dist_scorePoint_same_second]
  have hden : 0 ≤ (2 * (M + 1 : ℕ) : ℝ) := by positivity
  have hinner :
      -1 / 4 + (((i : ℕ) : ℝ) + 1) / (2 * (M + 1 : ℕ)) -
          (-1 / 4 + (((j : ℕ) : ℝ) + 1) / (2 * (M + 1 : ℕ))) =
        (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) / (2 * (M + 1 : ℕ)) := by ring
  rw [hinner, abs_div, abs_of_nonneg hden]

/-- Distinct grid centers are separated by at least one grid spacing. -/
-- @node: angularGridCenter_separated
lemma angularGridCenter_separated (M : ℕ) (i j : Fin M) (hij : i ≠ j) :
    1 / (2 * (M + 1 : ℕ) : ℝ) ≤
      dist (angularGridCenter M i) (angularGridCenter M j) := by
  rw [angularGridCenter_dist]
  have hcast : ((i : ℕ) : ℝ) ≠ ((j : ℕ) : ℝ) := by
    exact_mod_cast (Fin.val_ne_of_ne hij)
  have habs : 1 ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
    rcases lt_or_gt_of_ne hcast with hlt | hgt
    · rw [abs_of_nonpos (sub_nonpos.mpr hlt.le)]
      have hnat : (i : ℕ) + 1 ≤ (j : ℕ) := Nat.succ_le_iff.mpr (by exact_mod_cast hlt)
      have hnatR : (((i : ℕ) : ℝ) + 1) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hnat
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hgt.le)]
      have hnat : (j : ℕ) + 1 ≤ (i : ℕ) := Nat.succ_le_iff.mpr (by exact_mod_cast hgt)
      have hnatR : (((j : ℕ) : ℝ) + 1) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hnat
      linarith
  exact div_le_div_of_nonneg_right habs (by positivity)

/-- If twice the radius is smaller than one grid spacing, the square-truncated
closed balls around distinct centers are disjoint. -/
-- @node: angularGridCells_disjoint
lemma angularGridCells_disjoint (M : ℕ) (w : ℝ)
    (hw : 2 * w < 1 / (2 * (M + 1 : ℕ) : ℝ))
    (i j : Fin M) (hij : i ≠ j) :
    Disjoint
      (Metric.closedBall (angularGridCenter M i) w ∩ scoreCube (1 / 2))
      (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) := by
  apply (Metric.closedBall_disjoint_closedBall ?_).mono inter_subset_left inter_subset_left
  simpa [two_mul] using hw.trans_le (angularGridCenter_separated M i j hij)

/-- A radius at most one third of the grid spacing gives the paper's `3w`
center separation. -/
-- @node: angularGridCenter_three_radius_separated
lemma angularGridCenter_three_radius_separated (M : ℕ) (w : ℝ)
    (hw : 3 * w ≤ 1 / (2 * (M + 1 : ℕ) : ℝ))
    (i j : Fin M) (hij : i ≠ j) :
    3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M j) := by
  exact hw.trans (angularGridCenter_separated M i j hij)

/-- Positive cells whose radius is at most one third of the grid spacing are
pairwise disjoint after truncation to the square. -/
-- @node: angularGridPacking_three_radius
lemma angularGridPacking_three_radius (M : ℕ) (w : ℝ) (hw0 : 0 < w)
    (hw : 3 * w ≤ 1 / (2 * (M + 1 : ℕ) : ℝ))
    (i j : Fin M) (hij : i ≠ j) :
    Disjoint
      (Metric.closedBall (angularGridCenter M i) w ∩ scoreCube (1 / 2))
      (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) := by
  exact angularGridCells_disjoint M w (by linarith) i j hij

/-- Number of lower-edge grid points used at cell radius `w`. The factor
`12` leaves enough slack for the paper's `3w` separation. -/
-- @node: angularGridSize
noncomputable def angularGridSize (w : ℝ) : ℕ :=
  ⌊(1 / (12 * w) : ℝ)⌋₊

/-- The paper-scale radius: the `q`th power scale of the frontier rate. -/
-- @node: angularGridRadius
noncomputable def angularGridRadius (n q : ℕ) : ℝ :=
  Real.rpow (frontierRate n) ((1 : ℝ) / q)

/-- At every positive smoothness order, the paper-scale radius is eventually
positive and small enough for the explicit grid geometry. -/
-- @node: angularGridRadius_eventually_small
lemma angularGridRadius_eventually_small (q : ℕ) (hq : 1 ≤ q) :
    ∀ᶠ n in atTop,
      0 < angularGridRadius n q ∧ angularGridRadius n q ≤ 1 / 24 := by
  have hqR : (0 : ℝ) < q := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hp : 0 < (1 : ℝ) / q := by positivity
  have ht : Tendsto (fun n => angularGridRadius n q) atTop (nhds 0) := by
    unfold angularGridRadius
    convert frontierRate_tendsto_zero.rpow_const (Or.inr hp.le) using 1
    case e'_3 => rfl
    case e'_5 => rw [Real.zero_rpow hp.ne']
  have hsmall : ∀ᶠ n in atTop, angularGridRadius n q < 1 / 24 :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 24))
  filter_upwards [eventually_ge_atTop (2 : ℕ), hsmall] with n hn hs
  exact ⟨Real.rpow_pos_of_pos (frontierRate_pos hn) _, hs.le⟩

/-- For small positive radii, the explicit grid has at least a constant
multiple of `w⁻¹` points. -/
-- @node: angularGridSize_lower
lemma angularGridSize_lower (w : ℝ) (hw0 : 0 < w) (hw : w ≤ 1 / 24) :
    1 / (24 * w) ≤ (angularGridSize w : ℝ) := by
  have hfloor : (1 / (12 * w) : ℝ) < angularGridSize w + 1 := by
    simpa [angularGridSize] using Nat.lt_floor_add_one (1 / (12 * w) : ℝ)
  have hlarge : 2 ≤ (1 / (12 * w) : ℝ) := by
    apply (le_div_iff₀ (by positivity : 0 < 12 * w)).2
    nlinarith
  have hhalf : 1 / (24 * w) = (1 / (12 * w)) / 2 := by
    field_simp
    ring
  rw [hhalf]
  linarith

/-- At the frontier-rate radius, the explicit grid meets the theorem's
`a_n⁻¹ᐟᵠ` cardinality lower bound with constant `1/24`. -/
-- @node: angularGridSize_frontier_lower
lemma angularGridSize_frontier_lower (n q : ℕ) (hn : 2 ≤ n)
    (hsmall : angularGridRadius n q ≤ 1 / 24) :
    (1 / 24 : ℝ) * Real.rpow (frontierRate n) (-(1 : ℝ) / q) ≤
      (angularGridSize (angularGridRadius n q) : ℝ) := by
  have hr0 : 0 < frontierRate n := frontierRate_pos hn
  have hw0 : 0 < angularGridRadius n q := Real.rpow_pos_of_pos hr0 _
  have hid :
      (1 / 24 : ℝ) * Real.rpow (frontierRate n) (-(1 : ℝ) / q) =
        1 / (24 * angularGridRadius n q) := by
    have hneg :
        Real.rpow (frontierRate n) (-((1 : ℝ) / q)) =
          (Real.rpow (frontierRate n) ((1 : ℝ) / q))⁻¹ :=
      Real.rpow_neg hr0.le _
    rw [show -(1 : ℝ) / q = -((1 : ℝ) / q) by ring, hneg]
    unfold angularGridRadius
    field_simp
  rw [hid]
  exact angularGridSize_lower _ hw0 hsmall

/-- The spacing of the grid selected by `angularGridSize` is at least three
times its cell radius. -/
-- @node: angularGridSize_spacing
lemma angularGridSize_spacing (w : ℝ) (hw0 : 0 < w) (hw : w ≤ 1 / 24) :
    3 * w ≤ 1 / (2 * (angularGridSize w + 1 : ℕ) : ℝ) := by
  have hfloor : (angularGridSize w : ℝ) ≤ 1 / (12 * w) := by
    exact_mod_cast Nat.floor_le (by positivity : 0 ≤ (1 / (12 * w) : ℝ))
  have hsum : (angularGridSize w + 1 : ℕ) ≤ 1 / (6 * w) := by
    push_cast
    have hone : (1 : ℝ) ≤ 1 / (12 * w) := by
      apply (le_div_iff₀ (by positivity : 0 < 12 * w)).2
      nlinarith
    have hdouble : 1 / (6 * w) = 2 * (1 / (12 * w)) := by
      field_simp
      ring
    rw [hdouble]
    linarith
  apply (le_div_iff₀
    (by positivity : 0 < (2 * (angularGridSize w + 1 : ℕ) : ℝ))).2
  have hcast : ((angularGridSize w + 1 : ℕ) : ℝ) ≤ 1 / (6 * w) := by
    exact_mod_cast hsum
  have hmul := mul_le_mul_of_nonneg_left hcast (show 0 ≤ 6 * w by positivity)
  field_simp at hmul ⊢
  nlinarith

/-- The radius-dependent explicit grid simultaneously has the required
cardinality, frontier membership, corner avoidance, `3w` separation, and
pairwise-disjoint square-truncated cells. -/
-- @node: angularGridSize_geometry
lemma angularGridSize_geometry (w : ℝ) (hw0 : 0 < w) (hw : w ≤ 1 / 24) :
    1 / (24 * w) ≤ (angularGridSize w : ℝ) ∧
    (∀ j : Fin (angularGridSize w),
      angularGridCenter (angularGridSize w) j ∈ frontier (scoreCube (1 / 2)) ∧
      |angularGridCenter (angularGridSize w) j 0| < (1 / 4 : ℝ)) ∧
    (∀ i j : Fin (angularGridSize w), i ≠ j →
      3 * w ≤ dist (angularGridCenter (angularGridSize w) i)
        (angularGridCenter (angularGridSize w) j) ∧
      Disjoint
        (Metric.closedBall (angularGridCenter (angularGridSize w) i) w ∩
          scoreCube (1 / 2))
        (Metric.closedBall (angularGridCenter (angularGridSize w) j) w ∩
          scoreCube (1 / 2))) := by
  refine ⟨angularGridSize_lower w hw0 hw, ?_, ?_⟩
  · intro j
    exact ⟨angularGridCenter_mem_frontier _ j,
      angularGridCenter_first_abs_lt_quarter _ j⟩
  · intro i j hij
    have hspacing := angularGridSize_spacing w hw0 hw
    exact ⟨angularGridCenter_three_radius_separated _ w hspacing i j hij,
      angularGridPacking_three_radius _ w hw0 hspacing i j hij⟩

/-- Eventually, the frontier-rate grid simultaneously realizes every geometric
part of the angular packing: the sharp radius scale, inverse-radius
cardinality, non-corner frontier centers, three-radius separation, and
pairwise-disjoint square-truncated cells. -/
-- @node: angularGrid_frontierRate_geometry
lemma angularGrid_frontierRate_geometry (q : ℕ) (hq : 1 ≤ q) :
    ∀ᶠ n in atTop,
      let w := angularGridRadius n q
      let M := angularGridSize w
      0 < w ∧
      w = Real.rpow (frontierRate n) ((1 : ℝ) / q) ∧
      (1 / 24 : ℝ) * Real.rpow (frontierRate n) (-(1 : ℝ) / q) ≤ M ∧
      (∀ j : Fin M,
        angularGridCenter M j ∈ frontier (scoreCube (1 / 2)) ∧
        |angularGridCenter M j 0| < (1 / 4 : ℝ)) ∧
      (∀ i j : Fin M, i ≠ j →
        3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M j) ∧
        Disjoint
          (Metric.closedBall (angularGridCenter M i) w ∩ scoreCube (1 / 2))
          (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2))) := by
  filter_upwards [angularGridRadius_eventually_small q hq,
    eventually_ge_atTop (2 : ℕ)] with n hnSmall hn
  let w := angularGridRadius n q
  let M := angularGridSize w
  have hgeometry := angularGridSize_geometry w hnSmall.1 hnSmall.2
  refine ⟨hnSmall.1, rfl, angularGridSize_frontier_lower n q hn hnSmall.2,
    hgeometry.2.1, ?_⟩
  exact hgeometry.2.2

/-- Once the frontier rate is at most one, it is no larger than its
`q`th-root bandwidth for every positive integer smoothness order. -/
-- @node: frontierRate_le_angularGridRadius
lemma frontierRate_le_angularGridRadius (n q : ℕ) (hq : 1 ≤ q) (hn : 2 ≤ n)
    (hrate : frontierRate n ≤ 1) :
    frontierRate n ≤ angularGridRadius n q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hexp : (1 : ℝ) / q ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hqR
  have h := Real.rpow_le_rpow_of_exponent_ge
    (frontierRate_pos hn) hrate hexp
  simpa [angularGridRadius] using h

/-- The frontier rate is eventually at most one. -/
-- @node: frontierRate_eventually_le_one
lemma frontierRate_eventually_le_one :
    ∀ᶠ n in atTop, frontierRate n ≤ 1 := by
  have h := frontierRate_tendsto_zero.eventually
    (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  simpa only [mem_Iic] using h

/-- The deliberately small regression-bump amplitude used by the angular
construction.  The factor `1024` leaves room for the clipped angular tilt. -/
-- @node: angularPackingDelta
noncomputable def angularPackingDelta (n : ℕ) : ℝ :=
  frontierRate n / 1024

/-- Eventually the packing amplitude is positive, lies below the regression
envelope, and its full angular-cutoff radius fits inside the packing bandwidth. -/
-- @node: angularPackingDelta_eventually_admissible
lemma angularPackingDelta_eventually_admissible (q : ℕ) (hq : 1 ≤ q) :
    ∀ᶠ n in atTop,
      0 < angularPackingDelta n ∧
      angularPackingDelta n ≤ 1 / 8 ∧
      2 * (8 * angularPackingDelta n) ≤
        (1 / 4 : ℝ) * angularGridRadius n q := by
  filter_upwards [eventually_ge_atTop (2 : ℕ), frontierRate_eventually_le_one]
    with n hn hrate
  have hpos := frontierRate_pos hn
  have hdom := frontierRate_le_angularGridRadius n q hq hn hrate
  unfold angularPackingDelta
  constructor
  · positivity
  constructor <;> nlinarith

/-- Eventually the explicit grid geometry and all elementary amplitude/cutoff
side conditions needed by the angular hard family hold at the same sample
size.  This is the common threshold consumed by the family constructor. -/
-- @node: angularPacking_eventually_geometry_admissible
lemma angularPacking_eventually_geometry_admissible (q : ℕ) (hq : 1 ≤ q) :
    ∀ᶠ n in atTop,
      let w := angularGridRadius n q
      let M := angularGridSize w
      let delta := angularPackingDelta n
      0 < w ∧
      w = Real.rpow (frontierRate n) ((1 : ℝ) / q) ∧
      (1 / 24 : ℝ) * Real.rpow (frontierRate n) (-(1 : ℝ) / q) ≤ M ∧
      (∀ j : Fin M,
        angularGridCenter M j ∈ frontier (scoreCube (1 / 2)) ∧
        |angularGridCenter M j 0| < (1 / 4 : ℝ)) ∧
      (∀ i j : Fin M, i ≠ j →
        3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M j) ∧
        Disjoint
          (Metric.closedBall (angularGridCenter M i) w ∩ scoreCube (1 / 2))
          (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2))) ∧
      0 < delta ∧ delta ≤ 1 / 8 ∧
      2 * (8 * delta) ≤ (1 / 4 : ℝ) * w := by
  filter_upwards [angularGrid_frontierRate_geometry q hq,
    angularPackingDelta_eventually_admissible q hq] with n hgeom hadm
  exact ⟨hgeom.1, hgeom.2.1, hgeom.2.2.1, hgeom.2.2.2.1,
    hgeom.2.2.2.2, hadm.1, hadm.2.1, hadm.2.2⟩

/-- The fourth power of the frontier rate exactly cancels the sample size,
leaving the logarithmic budget used in the adjacent KL calculation. -/
-- @node: frontierRate_fourth_power
lemma frontierRate_fourth_power (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * frontierRate n ^ 4 = Real.log n := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hbase : 0 ≤ Real.log (n : ℝ) / n := (div_pos hlog hn0).le
  unfold frontierRate
  have hr := Real.rpow_inv_natCast_pow hbase (by norm_num : (4 : ℕ) ≠ 0)
  rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
  calc
    (n : ℝ) * (Real.log n / n).rpow (((4 : ℕ) : ℝ)⁻¹) ^ 4 =
        (n : ℝ) * (Real.log n / n) := by
      exact congrArg (fun z : ℝ => (n : ℝ) * z) hr
    _ = Real.log n := by field_simp

/-- The selected packing amplitude spends exactly a `1024⁻⁴` fraction of
the logarithmic KL budget before construction-specific constants. -/
-- @node: angularPackingDelta_fourth_power
lemma angularPackingDelta_fourth_power (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * angularPackingDelta n ^ 4 =
      Real.log n / 1024 ^ 4 := by
  unfold angularPackingDelta
  rw [div_pow]
  calc
    (n : ℝ) * (frontierRate n ^ 4 / 1024 ^ 4) =
        ((n : ℝ) * frontierRate n ^ 4) / 1024 ^ 4 := by ring
    _ = _ := by rw [frontierRate_fourth_power n hn]

end CausalSmith.Stat.BddUniformLogPenalty
