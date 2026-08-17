import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.PotentialOutcomeLaw
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularDesign
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Geometry of the fixed causal hard square

This file records the elementary square, rectangle, and disk facts used by
the causal angular hypercube construction.
-/

open MeasureTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The common square support `[-3,3]²`. -/
def causalHardSquare : Set Score :=
  {x | ∀ i, (-3 : ℝ) ≤ x i ∧ x i ≤ 3}

/-- The common arm-one rectangle `[-1,1] × [0,2]`. -/
def causalHardArmOne : Set Score :=
  {x | -1 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 2}

/-- The middle of the bottom edge on which the packing points lie. -/
def causalHardBottomEdge : Set Score :=
  {x | -1 / 2 ≤ x 0 ∧ x 0 ≤ 1 / 2 ∧ x 1 = 0}

/-- The equispaced hard-family centers on the middle of the assignment
rectangle's bottom edge. -/
-- @node: causalHardGridCenter
noncomputable def causalHardGridCenter (M : ℕ) (j : Fin M) : Score :=
  scorePoint (-1 / 4 + ((j : ℕ) + 1 : ℝ) / (2 * (M + 1 : ℕ))) 0

/-- Every hard-family grid center lies on the prescribed middle bottom edge. -/
-- @node: causalHardGridCenter_mem_bottomEdge
lemma causalHardGridCenter_mem_bottomEdge (M : ℕ) (j : Fin M) :
    causalHardGridCenter M j ∈ causalHardBottomEdge := by
  have hj := angularGridCenter_first_abs_lt_quarter M j
  have habs : |causalHardGridCenter M j 0| < (1 / 4 : ℝ) := by
    simpa [causalHardGridCenter, angularGridCenter, scorePoint] using hj
  rw [causalHardBottomEdge]
  constructor
  · have h := (abs_lt.mp habs).1
    linarith
  constructor
  · have h := (abs_lt.mp habs).2
    linarith
  · simp [causalHardGridCenter, scorePoint_apply_one]

/-- The translated hard-family grid has the same exact spacing as the
lower-edge grid used by the support-boundary construction. -/
-- @node: causalHardGridCenter_dist
lemma causalHardGridCenter_dist (M : ℕ) (i j : Fin M) :
    dist (causalHardGridCenter M i) (causalHardGridCenter M j) =
      |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| / (2 * (M + 1 : ℕ)) := by
  rw [causalHardGridCenter, causalHardGridCenter,
    dist_scorePoint_same_second]
  have hden : 0 ≤ (2 * (M + 1 : ℕ) : ℝ) := by positivity
  have hinner :
      -1 / 4 + (((i : ℕ) : ℝ) + 1) / (2 * (M + 1 : ℕ)) -
          (-1 / 4 + (((j : ℕ) : ℝ) + 1) / (2 * (M + 1 : ℕ))) =
        (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) / (2 * (M + 1 : ℕ)) := by
    ring
  rw [hinner, abs_div, abs_of_nonneg hden]

/-- Distinct translated grid centers are separated by at least one grid
spacing. -/
-- @node: causalHardGridCenter_separated
lemma causalHardGridCenter_separated (M : ℕ) (i j : Fin M) (hij : i ≠ j) :
    1 / (2 * (M + 1 : ℕ) : ℝ) ≤
      dist (causalHardGridCenter M i) (causalHardGridCenter M j) := by
  rw [causalHardGridCenter_dist]
  have hcast : ((i : ℕ) : ℝ) ≠ ((j : ℕ) : ℝ) := by
    exact_mod_cast (Fin.val_ne_of_ne hij)
  have habs : 1 ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
    rcases lt_or_gt_of_ne hcast with hlt | hgt
    · rw [abs_of_nonpos (sub_nonpos.mpr hlt.le)]
      have hnat : (i : ℕ) + 1 ≤ (j : ℕ) :=
        Nat.succ_le_iff.mpr (by exact_mod_cast hlt)
      have hnatR : (((i : ℕ) : ℝ) + 1) ≤ ((j : ℕ) : ℝ) := by
        exact_mod_cast hnat
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hgt.le)]
      have hnat : (j : ℕ) + 1 ≤ (i : ℕ) :=
        Nat.succ_le_iff.mpr (by exact_mod_cast hgt)
      have hnatR : (((j : ℕ) : ℝ) + 1) ≤ ((i : ℕ) : ℝ) := by
        exact_mod_cast hnat
      linarith
  exact div_le_div_of_nonneg_right habs (by positivity)

/-- The local disk associated with a packing point. -/
def causalHardCell (x : Score) (w : ℝ) : Set Score :=
  Metric.closedBall x w

/-- The coordinate description of the hard square agrees with the standard
score-cube representation used by the angular helpers. -/
-- @node: causalHardSquare_eq_scoreCube
lemma causalHardSquare_eq_scoreCube : causalHardSquare = scoreCube 3 := by
  ext x
  simp only [causalHardSquare, scoreCube, mem_setOf_eq]
  constructor
  · intro hx i
    exact abs_le.mpr (hx i)
  · intro hx i
    exact abs_le.mp (hx i)

/-- The fixed hard square is Borel measurable. -/
-- @node: causalHardSquare_measurableSet
lemma causalHardSquare_measurableSet : MeasurableSet causalHardSquare := by
  rw [causalHardSquare_eq_scoreCube]
  exact scoreCube_measurableSet 3

/-- The fixed hard square is compact. -/
-- @node: causalHardSquare_isCompact
lemma causalHardSquare_isCompact : IsCompact causalHardSquare := by
  rw [causalHardSquare_eq_scoreCube, Metric.isCompact_iff_isClosed_bounded]
  constructor
  · unfold scoreCube
    rw [show {x : Score | ∀ i, |x i| ≤ (3 : ℝ)} =
        ⋂ i : Fin 2, {x : Score | |x i| ≤ (3 : ℝ)} by ext; simp]
    exact isClosed_iInter fun i => isClosed_le
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) i).abs)
      continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨6, ?_⟩
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    have h0 := hx (0 : Fin 2)
    have h1 := hx (1 : Fin 2)
    simp only [Fin.sum_univ_two, Real.norm_eq_abs]
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · have h0sq : |x 0| ^ 2 ≤ (3 : ℝ) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 h0
      have h1sq : |x 1| ^ 2 ≤ (3 : ℝ) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 h1
      nlinarith

/-- The closure of the interior of the fixed hard square is the square itself. -/
-- @node: closure_interior_causalHardSquare
lemma closure_interior_causalHardSquare :
    closure (interior causalHardSquare) = causalHardSquare := by
  rw [causalHardSquare_eq_scoreCube]
  have hconvex : Convex ℝ (scoreCube 3) := by
    intro x hx y hy a b ha hb hab i
    unfold scoreCube at hx hy
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [abs_le]
    constructor
    · have := add_le_add
        (mul_le_mul_of_nonneg_left (abs_le.mp (hx i)).1 ha)
        (mul_le_mul_of_nonneg_left (abs_le.mp (hy i)).1 hb)
      nlinarith
    · have := add_le_add
        (mul_le_mul_of_nonneg_left (abs_le.mp (hx i)).2 ha)
        (mul_le_mul_of_nonneg_left (abs_le.mp (hy i)).2 hb)
      nlinarith
  have hzero : (0 : Score) ∈ interior (scoreCube 3) := by
    rw [mem_interior_iff_mem_nhds]
    apply Filter.mem_of_superset
      (Metric.ball_mem_nhds (0 : Score) (show (0 : ℝ) < 3 by norm_num))
    intro x hx
    unfold scoreCube
    intro i
    rw [Metric.mem_ball, dist_zero_right] at hx
    exact (PiLp.norm_apply_le x i).trans hx.le
  have hclosed : IsClosed (scoreCube 3) := by
    rw [← causalHardSquare_eq_scoreCube]
    exact causalHardSquare_isCompact.isClosed
  rw [hconvex.closure_interior_eq_closure_of_nonempty_interior ⟨0, hzero⟩,
    hclosed.closure_eq]

/-- Restricting planar Lebesgue measure to the fixed hard square has exactly
that square as its topological support. -/
-- @node: volume_restrict_causalHardSquare_support
lemma volume_restrict_causalHardSquare_support :
    (volume.restrict causalHardSquare).support = causalHardSquare := by
  apply Set.Subset.antisymm
  · intro x hx
    have hmem := (Measure.support_restrict_subset hx).1
    rwa [causalHardSquare_isCompact.isClosed.closure_eq] at hmem
  · have hi : interior causalHardSquare ⊆
        (volume.restrict causalHardSquare).support := by
      intro x hx
      exact Measure.interior_inter_support
        ⟨hx, by simp [Measure.support_eq_univ]⟩
    have hc := closure_mono hi
    rw [closure_interior_causalHardSquare,
      Measure.isClosed_support.closure_eq] at hc
    exact hc

/-- The fixed hard square has planar Lebesgue mass `36`. -/
-- @node: causalHardSquare_volume
lemma causalHardSquare_volume : volume causalHardSquare = 36 := by
  have hset : causalHardSquare =
      ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) ⁻¹'
        Icc (fun _ => (-3 : ℝ)) (fun _ => 3) := by
    ext x
    simp only [causalHardSquare, mem_setOf_eq, mem_preimage, mem_Icc, Pi.le_def]
    constructor
    · intro hx
      exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩
    · rintro ⟨hlo, hhi⟩ i
      exact ⟨hlo i, hhi i⟩
  rw [hset, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin 2)).measure_preimage]
  · rw [Real.volume_Icc_pi]
    simp only [Fin.prod_const]
    have hsix : (3 : ℝ) - -3 = ((6 : ℕ) : ℝ) := by norm_num
    rw [hsix, ENNReal.ofReal_natCast]
    norm_num
  · exact (measurableSet_Icc : MeasurableSet
      (Icc (fun _ : Fin 2 => (-3 : ℝ)) (fun _ => 3))).nullMeasurableSet

/-- The arm-one rectangle is a Borel subset of the hard square. -/
-- @node: causalHardArmOne_measurableSet
lemma causalHardArmOne_measurableSet : MeasurableSet causalHardArmOne := by
  apply IsClosed.measurableSet
  unfold causalHardArmOne
  let c0 := PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0
  let c1 := PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1
  exact (isClosed_le continuous_const c0).inter
    ((isClosed_le c0 continuous_const).inter
      ((isClosed_le continuous_const c1).inter
        (isClosed_le c1 continuous_const)))

/-- The fixed arm-one rectangle is closed. -/
-- @node: causalHardArmOne_isClosed
lemma causalHardArmOne_isClosed : IsClosed causalHardArmOne := by
  unfold causalHardArmOne
  let c0 := PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 0
  let c1 := PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) 1
  exact (isClosed_le continuous_const c0).inter
    ((isClosed_le c0 continuous_const).inter
      ((isClosed_le continuous_const c1).inter
        (isClosed_le c1 continuous_const)))

/-- The fixed arm-one rectangle is compact. -/
-- @node: causalHardArmOne_isCompact
lemma causalHardArmOne_isCompact : IsCompact causalHardArmOne := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨causalHardArmOne_isClosed, ?_⟩
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨3, ?_⟩
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  have h0sq : |x 0| ^ 2 ≤ (1 : ℝ) := by
    have h0 : |x 0| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2.1⟩
    nlinarith [abs_nonneg (x 0)]
  have h1sq : |x 1| ^ 2 ≤ (4 : ℝ) := by
    have h1 : |x 1| ≤ 2 := abs_le.mpr ⟨by linarith [hx.2.2.1], hx.2.2.2⟩
    nlinarith [abs_nonneg (x 1)]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith

/-- The assignment rectangle, including its frontier, lies strictly inside
the common score support. -/
-- @node: causalHardArmOne_subset_interior_square
lemma causalHardArmOne_subset_interior_square :
    causalHardArmOne ⊆ interior causalHardSquare := by
  intro x hx
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset
    (Metric.ball_mem_nhds x (show (0 : ℝ) < 1 / 2 by norm_num))
  intro z hz i
  have hcoord : |z i - x i| < 1 / 2 := by
    have hle : |z i - x i| ≤ dist z x := by
      simpa [dist_eq_norm, Real.norm_eq_abs] using PiLp.norm_apply_le (z - x) i
    exact hle.trans_lt (by simpa [Metric.mem_ball] using hz)
  change -1 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 2 at hx
  fin_cases i
  · change |z 0 - x 0| < 1 / 2 at hcoord
    change -3 ≤ z 0 ∧ z 0 ≤ 3
    have hc := abs_lt.mp hcoord
    constructor <;> linarith [hx.1, hx.2.1]
  · change |z 1 - x 1| < 1 / 2 at hcoord
    change -3 ≤ z 1 ∧ z 1 ≤ 3
    have hc := abs_lt.mp hcoord
    constructor <;> linarith [hx.2.2.1, hx.2.2.2]

/-- The common assignment frontier is compact and lies in the interior of
the fixed hard square. -/
-- @node: causalHardFrontier_compact_and_interior
lemma causalHardFrontier_compact_and_interior :
    IsCompact (frontier causalHardArmOne) ∧
      frontier causalHardArmOne ⊆ interior causalHardSquare := by
  have hsub : frontier causalHardArmOne ⊆ causalHardArmOne :=
    causalHardArmOne_isClosed.frontier_subset
  exact ⟨causalHardArmOne_isCompact.of_isClosed_subset isClosed_frontier hsub,
    hsub.trans causalHardArmOne_subset_interior_square⟩

/-- The frontier shared by the two assignment arms is exactly the frontier
of the arm-one rectangle. -/
-- @node: causalHardAssignment_frontier
lemma causalHardAssignment_frontier :
    frontier (causalHardSquare \ causalHardArmOne) ∩
        frontier causalHardArmOne = frontier causalHardArmOne := by
  apply Set.Subset.antisymm inter_subset_right
  intro x hx
  have hxInt : x ∈ interior causalHardSquare :=
    causalHardFrontier_compact_and_interior.2 hx
  have hxFront := hx
  rw [frontier_eq_closure_inter_closure] at hx
  refine ⟨?_, hxFront⟩
  rw [frontier_eq_closure_inter_closure]
  change x ∈ closure (causalHardSquare \ causalHardArmOne) ∧
    x ∈ closure (causalHardSquare \ causalHardArmOne)ᶜ
  constructor
  · rw [mem_closure_iff]
    intro o ho hxo
    have hmeet := (mem_closure_iff.mp hx.2) (o ∩ interior causalHardSquare)
      (ho.inter isOpen_interior) ⟨hxo, hxInt⟩
    rcases hmeet with ⟨y, ⟨hyo, hyS⟩, hyA⟩
    exact ⟨y, hyo, ⟨interior_subset hyS, hyA⟩⟩
  · exact closure_mono (fun y (hy : y ∈ causalHardArmOne) =>
      show y ∈ (causalHardSquare \ causalHardArmOne)ᶜ from by
        intro hdiff
        exact hdiff.2 hy) hx.1

/-- The fixed arm-zero region is Borel measurable. -/
-- @node: causalHardArmZero_measurableSet
lemma causalHardArmZero_measurableSet :
    MeasurableSet (causalHardSquare \ causalHardArmOne) :=
  causalHardSquare_measurableSet.diff causalHardArmOne_measurableSet

/-- Every point of the fixed assignment rectangle lies in the support square. -/
-- @node: causalHardArmOne_subset_square
lemma causalHardArmOne_subset_square : causalHardArmOne ⊆ causalHardSquare := by
  intro x hx i
  fin_cases i
  · change -3 ≤ x 0 ∧ x 0 ≤ 3
    exact ⟨by linarith [hx.1], by linarith [hx.2.1]⟩
  · change -3 ≤ x 1 ∧ x 1 ≤ 3
    exact ⟨by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩

/-- The square complement of arm one and arm one form the required disjoint
partition of the fixed support. -/
-- @node: causalHardAssignment_partition
lemma causalHardAssignment_partition :
    (causalHardSquare \ causalHardArmOne) ∪ causalHardArmOne = causalHardSquare ∧
      Disjoint (causalHardSquare \ causalHardArmOne) causalHardArmOne := by
  constructor
  · exact diff_union_of_subset causalHardArmOne_subset_square
  · exact disjoint_sdiff_left

/-- A radius-at-most-one disk centered on the selected middle bottom edge is
strictly contained in the hard support square. -/
-- @node: causalHardCell_subset_square
lemma causalHardCell_subset_square {x : Score} {w : ℝ}
    (hx : x ∈ causalHardBottomEdge) (hw : w ≤ 1) :
    causalHardCell x w ⊆ causalHardSquare := by
  intro z hz i
  have hcoord : |z i - x i| ≤ dist z x := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using PiLp.norm_apply_le (z - x) i
  have hdist : dist z x ≤ w := by
    simpa [causalHardCell, Metric.mem_closedBall, dist_comm] using hz
  have hxi : |x i| ≤ 1 / 2 := by
    fin_cases i <;> norm_num [causalHardBottomEdge] at hx ⊢
    · exact abs_le.mpr ⟨hx.1, hx.2.1⟩
    · simp [hx.2.2]
  have hzi : |z i| ≤ |x i| + |z i - x i| := by
    calc
      |z i| = |x i + (z i - x i)| := by congr 1 <;> ring
      _ ≤ _ := abs_add_le _ _
  constructor
  · have : |z i| ≤ 3 := by linarith
    exact (abs_le.mp this).1
  · have : |z i| ≤ 3 := by linarith
    exact (abs_le.mp this).2

/-- A planar hard cell has the usual disk area. -/
-- @node: causalHardCell_volume
lemma causalHardCell_volume (x : Score) (w : ℝ) (hw : 0 ≤ w) :
    volume (causalHardCell x w) = ENNReal.ofReal (Real.pi * w ^ 2) := by
  rw [causalHardCell, EuclideanSpace.volume_closedBall_fin_two]
  rw [← ENNReal.ofReal_pow hw]
  rw [← ENNReal.ofReal_mul (sq_nonneg w)]
  congr 1
  ring

/-- For every sufficiently small positive radius, the translated explicit
grid supplies the cardinality, containment, three-radius separation, and
full-disc disjointness required by the causal hard family. -/
-- @node: causalHardGrid_geometry
lemma causalHardGrid_geometry (w : ℝ) (hw0 : 0 < w) (hw : w ≤ 1 / 24) :
    let M := angularGridSize w
    1 / (24 * w) ≤ (M : ℝ) ∧
    (∀ j : Fin M, causalHardGridCenter M j ∈ causalHardBottomEdge) ∧
    (∀ j : Fin M,
      causalHardCell (causalHardGridCenter M j) w ⊆ causalHardSquare) ∧
    (∀ i j : Fin M, i ≠ j →
      3 * w ≤ dist (causalHardGridCenter M i) (causalHardGridCenter M j)) ∧
    (∀ i j : Fin M, i ≠ j →
      Disjoint (causalHardCell (causalHardGridCenter M i) w)
        (causalHardCell (causalHardGridCenter M j) w)) := by
  let M := angularGridSize w
  have hspacing : 3 * w ≤ 1 / (2 * (M + 1 : ℕ) : ℝ) := by
    simpa [M] using angularGridSize_spacing w hw0 hw
  have hsep : ∀ i j : Fin M, i ≠ j →
      3 * w ≤ dist (causalHardGridCenter M i) (causalHardGridCenter M j) := by
    intro i j hij
    exact hspacing.trans (causalHardGridCenter_separated M i j hij)
  refine ⟨angularGridSize_lower w hw0 hw, ?_, ?_, hsep, ?_⟩
  · exact fun j => causalHardGridCenter_mem_bottomEdge M j
  · intro j
    exact causalHardCell_subset_square (causalHardGridCenter_mem_bottomEdge M j)
      (hw.trans (by norm_num))
  · intro i j hij
    change Disjoint
      (Metric.closedBall (causalHardGridCenter M i) w)
      (Metric.closedBall (causalHardGridCenter M j) w)
    apply Metric.closedBall_disjoint_closedBall
    have hs := hsep i j hij
    linarith

/-- At the paper bandwidth `w = A Δ^(1/(p+1))`, the explicit grid realizes
the exact inverse-bandwidth cardinality rate and every geometric cell clause
of `A1A2HypercubeAt`. -/
-- @node: causalHardGrid_scaled_geometry
lemma causalHardGrid_scaled_geometry (p : ℕ) {A Δ : ℝ}
    (hA : 0 < A) (hΔ : 0 < Δ)
    (hsmall : A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ)) ≤ 1 / 24) :
    let w := A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))
    let M := angularGridSize w
    (M : ℝ) ≥ (1 / (24 * A)) *
        Real.rpow Δ (-(1 : ℝ) / (p + 1 : ℝ)) ∧
    w = A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ)) ∧
    (∀ j : Fin M, causalHardGridCenter M j ∈ causalHardBottomEdge) ∧
    (∀ j : Fin M,
      causalHardCell (causalHardGridCenter M j) w ⊆ causalHardSquare) ∧
    (∀ i j : Fin M, i ≠ j →
      dist (causalHardGridCenter M i) (causalHardGridCenter M j) ≥ 2 * w) ∧
    (∀ i j : Fin M, i ≠ j →
      Disjoint (causalHardCell (causalHardGridCenter M i) w)
        (causalHardCell (causalHardGridCenter M j) w)) := by
  let w := A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))
  let M := angularGridSize w
  have hrpow : 0 < Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ)) :=
    Real.rpow_pos_of_pos hΔ _
  have hw0 : 0 < w := mul_pos hA hrpow
  have hgeom := causalHardGrid_geometry w hw0 hsmall
  have hrate :
      (1 / (24 * A)) * Real.rpow Δ (-(1 : ℝ) / (p + 1 : ℝ)) =
        1 / (24 * w) := by
    have hneg : Real.rpow Δ (-(1 : ℝ) / (p + 1 : ℝ)) =
        (Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ)))⁻¹ := by
      rw [show -(1 : ℝ) / (p + 1 : ℝ) =
        -((1 : ℝ) / (p + 1 : ℝ)) by ring]
      exact Real.rpow_neg hΔ.le _
    rw [hneg]
    dsimp [w]
    field_simp
  refine ⟨?_, rfl, hgeom.2.1, hgeom.2.2.1, ?_, hgeom.2.2.2.2⟩
  · rw [hrate]
    exact hgeom.1
  · intro i j hij
    have hs := hgeom.2.2.2.1 i j hij
    linarith [hw0]

/-- The scaled grid certificates in the constructor-ready form used by the
hard-law family, retaining the stronger three-radius separation proved by the
underlying explicit grid. -/
-- @node: causalHardGrid_scaled_family_geometry
lemma causalHardGrid_scaled_family_geometry (p : ℕ) {A Δ : ℝ}
    (hA : 0 < A) (hΔ : 0 < Δ)
    (hsmall : A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ)) ≤ 1 / 24) :
    let w := A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))
    let M := angularGridSize w
    0 < w ∧
    (M : ℝ) ≥ (1 / (24 * A)) *
        Real.rpow Δ (-(1 : ℝ) / (p + 1 : ℝ)) ∧
    w = A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ)) ∧
    (∀ j : Fin M, causalHardGridCenter M j ∈ causalHardBottomEdge) ∧
    (∀ j : Fin M,
      causalHardCell (causalHardGridCenter M j) w ⊆ causalHardSquare) ∧
    (∀ i j : Fin M, i ≠ j →
      3 * w ≤ dist (causalHardGridCenter M i) (causalHardGridCenter M j)) ∧
    (∀ i j : Fin M, i ≠ j →
      Disjoint (causalHardCell (causalHardGridCenter M i) w)
        (causalHardCell (causalHardGridCenter M j) w)) := by
  let w := A * Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ))
  let M := angularGridSize w
  have hrpow : 0 < Real.rpow Δ ((1 : ℝ) / (p + 1 : ℝ)) :=
    Real.rpow_pos_of_pos hΔ _
  have hw0 : 0 < w := mul_pos hA hrpow
  have hscaled := causalHardGrid_scaled_geometry p hA hΔ hsmall
  have hgrid := causalHardGrid_geometry w hw0 hsmall
  exact ⟨hw0, hscaled.1, hscaled.2.1, hscaled.2.2.1,
    hscaled.2.2.2.1, hgrid.2.2.2.1, hscaled.2.2.2.2.2⟩

end CausalSmith.Stat.BddUniformLogPenalty
