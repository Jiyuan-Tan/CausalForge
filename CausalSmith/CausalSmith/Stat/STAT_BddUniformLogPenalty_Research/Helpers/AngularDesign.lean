import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularMeasure

/-!
# Angular packing design measure

This file packages the paper's angular density as a Lebesgue density supported
on the fixed square.  It records the measurable-density, continuity, envelope,
positivity, and absolute-continuity facts needed by the eventual `CtyLaw`
constructor.
-/

open MeasureTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Coordinate cubes are Borel measurable. -/
-- @node: scoreCube_measurableSet
lemma scoreCube_measurableSet (r : ℝ) : MeasurableSet (scoreCube r) := by
  apply IsClosed.measurableSet
  unfold scoreCube
  rw [show {x : Score | ∀ i, |x i| ≤ r} =
      ⋂ i : Fin 2, {x : Score | |x i| ≤ r} by
    ext x
    simp]
  apply isClosed_iInter
  intro i
  exact isClosed_le
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) i).abs)
    continuous_const

/-- The fixed square supporting the angular packing has unit Lebesgue mass. -/
-- @node: packingSquare_volume
lemma packingSquare_volume : volume (scoreCube (1 / 2 : ℝ)) = 1 := by
  have hset : scoreCube (1 / 2 : ℝ) =
      ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) ⁻¹'
        Icc (fun _ => -(1 / 2 : ℝ)) (fun _ => 1 / 2) := by
    ext x
    simp only [scoreCube, mem_setOf_eq, mem_preimage, mem_Icc, Pi.le_def]
    constructor
    · intro hx
      constructor
      · intro i
        exact (abs_le.mp (hx i)).1
      · intro i
        exact (abs_le.mp (hx i)).2
    · rintro ⟨hlo, hhi⟩ i
      exact abs_le.mpr ⟨hlo i, hhi i⟩
  rw [hset, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin 2)).measure_preimage]
  · rw [Real.volume_Icc_pi]
    simp only [Fin.prod_const]
    rw [show (1 / 2 : ℝ) - -(1 / 2) = 1 by norm_num, ENNReal.ofReal_one]
    norm_num
  · exact (measurableSet_Icc : MeasurableSet
      (Icc (fun _ : Fin 2 => -(1 / 2 : ℝ)) (fun _ => 1 / 2))).nullMeasurableSet

/-- The square supporting the angular construction is convex. -/
-- @node: packingScoreCube_convex
lemma packingScoreCube_convex : Convex ℝ (scoreCube (1 / 2 : ℝ)) := by
  intro x hx y hy a b ha hb hab i
  unfold scoreCube at hx hy
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [abs_le]
  constructor
  · have := add_le_add (mul_le_mul_of_nonneg_left (abs_le.mp (hx i)).1 ha)
        (mul_le_mul_of_nonneg_left (abs_le.mp (hy i)).1 hb)
    nlinarith
  · have := add_le_add (mul_le_mul_of_nonneg_left (abs_le.mp (hx i)).2 ha)
        (mul_le_mul_of_nonneg_left (abs_le.mp (hy i)).2 hb)
    nlinarith

/-- The square supporting the angular packing is compact. -/
-- @node: packingScoreCube_isCompact
lemma packingScoreCube_isCompact : IsCompact (scoreCube (1 / 2 : ℝ)) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · unfold scoreCube
    rw [show {x : Score | ∀ i, |x i| ≤ (1 / 2 : ℝ)} =
        ⋂ i : Fin 2, {x : Score | |x i| ≤ (1 / 2 : ℝ)} by ext; simp]
    exact isClosed_iInter fun i => isClosed_le
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) i).abs)
      continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, ?_⟩
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    have h0 := hx (0 : Fin 2)
    have h1 := hx (1 : Fin 2)
    have h0sq : |x 0| ^ 2 ≤ ((1 / 2 : ℝ) ^ 2) := by
      nlinarith [abs_nonneg (x 0)]
    have h1sq : |x 1| ^ 2 ≤ ((1 / 2 : ℝ) ^ 2) := by
      nlinarith [abs_nonneg (x 1)]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs]
    rw [Real.sqrt_le_one]
    nlinarith
/-- The origin is an interior point of the square supporting the angular
construction. -/
-- @node: zero_mem_interior_packingScoreCube
lemma zero_mem_interior_packingScoreCube :
    (0 : Score) ∈ interior (scoreCube (1 / 2 : ℝ)) := by
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset
    (Metric.ball_mem_nhds (0 : Score) (show (0 : ℝ) < 1 / 2 by norm_num))
  intro x hx
  unfold scoreCube
  intro i
  rw [Metric.mem_ball, dist_zero_right] at hx
  exact (PiLp.norm_apply_le x i).trans hx.le

/-- The closure of the interior of the supporting square is the whole
square. -/
-- @node: closure_interior_packingScoreCube
lemma closure_interior_packingScoreCube :
    closure (interior (scoreCube (1 / 2 : ℝ))) = scoreCube (1 / 2 : ℝ) := by
  have hclosed : IsClosed (scoreCube (1 / 2 : ℝ)) := by
    unfold scoreCube
    rw [show {x : Score | ∀ i, |x i| ≤ (1 / 2 : ℝ)} =
        ⋂ i : Fin 2, {x : Score | |x i| ≤ (1 / 2 : ℝ)} by ext; simp]
    exact isClosed_iInter fun i => isClosed_le
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) i).abs)
      continuous_const
  rw [packingScoreCube_convex.closure_interior_eq_closure_of_nonempty_interior
      ⟨0, zero_mem_interior_packingScoreCube⟩,
    hclosed.closure_eq]

/-- Restricting planar Lebesgue measure to the closed supporting square has
exactly that square as its topological support. -/
-- @node: volume_restrict_packingScoreCube_support
lemma volume_restrict_packingScoreCube_support :
    (volume.restrict (scoreCube (1 / 2 : ℝ))).support =
      scoreCube (1 / 2 : ℝ) := by
  have hclosed : IsClosed (scoreCube (1 / 2 : ℝ)) := by
    unfold scoreCube
    rw [show {x : Score | ∀ i, |x i| ≤ (1 / 2 : ℝ)} =
        ⋂ i : Fin 2, {x : Score | |x i| ≤ (1 / 2 : ℝ)} by ext; simp]
    exact isClosed_iInter fun i => isClosed_le
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) i).abs)
      continuous_const
  apply Set.Subset.antisymm
  · intro x hx
    have hmem := (Measure.support_restrict_subset hx).1
    rwa [hclosed.closure_eq] at hmem
  · have hi : interior (scoreCube (1 / 2 : ℝ)) ⊆
        (volume.restrict (scoreCube (1 / 2 : ℝ))).support := by
      intro x hx
      exact Measure.interior_inter_support ⟨hx, by simp [Measure.support_eq_univ]⟩
    have hc := closure_mono hi
    rw [closure_interior_packingScoreCube,
      Measure.isClosed_support.closure_eq] at hc
    exact hc

/-- The real-valued angular design density, extended by zero away from the
fixed square. -/
-- @node: angularDesignDensity
noncomputable def angularDesignDensity {M : ℕ} (b cA delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) : Score → ℝ :=
  (scoreCube (1 / 2 : ℝ)).indicator
    (packingAngularDensity b cA delta w centers omega)

/-- On the square, the extended design density is the angular density. -/
-- @node: angularDesignDensity_eq_on_square
lemma angularDesignDensity_eq_on_square {M : ℕ} {b cA delta w : ℝ}
    {centers : Fin M → Score} {omega : Fin M → Bool} {x : Score}
    (hx : x ∈ scoreCube (1 / 2 : ℝ)) :
    angularDesignDensity b cA delta w centers omega x =
      packingAngularDensity b cA delta w centers omega x := by
  rw [angularDesignDensity, Set.indicator_of_mem hx]

/-- Away from the square, the extended design density vanishes. -/
-- @node: angularDesignDensity_eq_zero_off_square
lemma angularDesignDensity_eq_zero_off_square {M : ℕ} {b cA delta w : ℝ}
    {centers : Fin M → Score} {omega : Fin M → Bool} {x : Score}
    (hx : x ∉ scoreCube (1 / 2 : ℝ)) :
    angularDesignDensity b cA delta w centers omega x = 0 := by
  rw [angularDesignDensity, Set.indicator_of_notMem hx]

/-- Within one square-truncated packing cell, the extended design density
depends on a vertex only through that cell's Boolean coordinate. -/
-- @node: angularDesignDensity_eq_on_cell
lemma angularDesignDensity_eq_on_cell {M : ℕ} {b cA delta w : ℝ}
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    {omega omega' : Fin M → Bool} {j : Fin M} (hbit : omega j = omega' j)
    {x : Score}
    (hx : x ∈ Metric.closedBall (centers j) w ∩ scoreCube (1 / 2 : ℝ)) :
    angularDesignDensity b cA delta w centers omega x =
      angularDesignDensity b cA delta w centers omega' x := by
  rw [angularDesignDensity_eq_on_square hx.2,
    angularDesignDensity_eq_on_square hx.2]
  exact packingAngularDensity_eq_on_cell hw hsep hbit hx.1

/-- Outside all packing cells, the extended design density is independent of
the packing vertex (and equals one on the supporting square). -/
-- @node: angularDesignDensity_eq_one_off_cells
lemma angularDesignDensity_eq_one_off_cells {M : ℕ} {b cA delta w : ℝ}
    (hw : 0 < w) {centers : Fin M → Score} (omega : Fin M → Bool)
    {x : Score} (hxSquare : x ∈ scoreCube (1 / 2 : ℝ))
    (hxCells : ∀ j, x ∉ Metric.closedBall (centers j) w) :
    angularDesignDensity b cA delta w centers omega x = 1 := by
  rw [angularDesignDensity_eq_on_square hxSquare]
  exact packingAngularDensity_eq_one_off_cells hw omega hxCells

/-- The square-supported angular density is Borel measurable. -/
-- @node: angularDesignDensity_measurable
lemma angularDesignDensity_measurable {M : ℕ} {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (centers : Fin M → Score)
    (omega : Fin M → Bool) :
    Measurable (angularDesignDensity b cA delta w centers omega) := by
  exact (packingAngularDensity_measurable hb hscale centers omega).indicator
    (scoreCube_measurableSet (1 / 2 : ℝ))

/-- Restricted to the square, the angular design density is continuous. -/
-- @node: angularDesignDensity_continuousOn
lemma angularDesignDensity_continuousOn {M : ℕ} {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (centers : Fin M → Score)
    (omega : Fin M → Bool) :
    ContinuousOn (angularDesignDensity b cA delta w centers omega)
      (scoreCube (1 / 2 : ℝ)) := by
  refine (packingAngularDensity_continuous (w := w) hb hscale centers omega).continuousOn.congr ?_
  intro x hx
  exact angularDesignDensity_eq_on_square (b := b) (cA := cA) (delta := delta)
    (w := w) (centers := centers) (omega := omega) hx

/-- The extended density inherits the paper's uniform envelope on its square
support. -/
-- @node: angularDesignDensity_mem_Icc
lemma angularDesignDensity_mem_Icc {M : ℕ} {b cA delta w : ℝ}
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) {x : Score} (hx : x ∈ scoreCube (1 / 2 : ℝ)) :
    angularDesignDensity b cA delta w centers omega x ∈
      Icc (3 / 4 : ℝ) (5 / 4 : ℝ) := by
  rw [angularDesignDensity_eq_on_square hx]
  exact packingAngularDensity_mem_Icc hcA hdelta hw hsep omega x

/-- In particular, the angular design density is strictly positive at every
point of the square. -/
-- @node: angularDesignDensity_pos
lemma angularDesignDensity_pos {M : ℕ} {b cA delta w : ℝ}
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) {x : Score} (hx : x ∈ scoreCube (1 / 2 : ℝ)) :
    0 < angularDesignDensity b cA delta w centers omega x := by
  exact (by norm_num : (0 : ℝ) < 3 / 4).trans_le
    (angularDesignDensity_mem_Icc hcA hdelta hw hsep omega hx).1

/-- The covariate design measure associated with an angular packing vertex. -/
-- @node: angularDesignMeasure
noncomputable def angularDesignMeasure {M : ℕ} (b cA delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) : Measure Score :=
  volume.withDensity fun x =>
    ENNReal.ofReal (angularDesignDensity b cA delta w centers omega x)

/-- Restricting the score design to one packing cell erases every Boolean
coordinate except the coordinate indexing that cell. -/
-- @node: angularDesignMeasure_restrict_cell_eq
lemma angularDesignMeasure_restrict_cell_eq {M : ℕ} {b cA delta w : ℝ}
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    {omega omega' : Fin M → Bool} {j : Fin M} (hbit : omega j = omega' j) :
    (angularDesignMeasure b cA delta w centers omega).restrict
        (Metric.closedBall (centers j) w ∩ scoreCube (1 / 2 : ℝ)) =
      (angularDesignMeasure b cA delta w centers omega').restrict
        (Metric.closedBall (centers j) w ∩ scoreCube (1 / 2 : ℝ)) := by
  let C := Metric.closedBall (centers j) w ∩ scoreCube (1 / 2 : ℝ)
  have hC : MeasurableSet C :=
    Metric.isClosed_closedBall.measurableSet.inter (scoreCube_measurableSet _)
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  unfold angularDesignMeasure
  rw [withDensity_apply _ (hs.inter hC), withDensity_apply _ (hs.inter hC)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (hs.inter hC)] with x hx
  apply congrArg ENNReal.ofReal
  exact angularDesignDensity_eq_on_cell hw hsep hbit hx.2

/-- Outside the union of the square-truncated packing cells, every angular
design restricts to the same unit-density square measure. -/
-- @node: angularDesignMeasure_restrict_off_cells_eq
lemma angularDesignMeasure_restrict_off_cells_eq {M : ℕ}
    {b cA delta w : ℝ} (hw : 0 < w) {centers : Fin M → Score}
    (omega omega' : Fin M → Bool) :
    (angularDesignMeasure b cA delta w centers omega).restrict
        (scoreCube (1 / 2 : ℝ) \ ⋃ j,
          Metric.closedBall (centers j) w ∩ scoreCube (1 / 2 : ℝ)) =
      (angularDesignMeasure b cA delta w centers omega').restrict
        (scoreCube (1 / 2 : ℝ) \ ⋃ j,
          Metric.closedBall (centers j) w ∩ scoreCube (1 / 2 : ℝ)) := by
  let C := scoreCube (1 / 2 : ℝ) \ ⋃ j,
    Metric.closedBall (centers j) w ∩ scoreCube (1 / 2 : ℝ)
  have hC : MeasurableSet C :=
    (scoreCube_measurableSet _).diff (MeasurableSet.iUnion fun _ =>
      Metric.isClosed_closedBall.measurableSet.inter (scoreCube_measurableSet _))
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  unfold angularDesignMeasure
  rw [withDensity_apply _ (hs.inter hC), withDensity_apply _ (hs.inter hC)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (hs.inter hC)] with x hx
  have hxBalls : ∀ j, x ∉ Metric.closedBall (centers j) w := by
    intro j hxj
    exact hx.2.2 (Set.mem_iUnion.2 ⟨j, hxj, hx.2.1⟩)
  rw [angularDesignDensity_eq_one_off_cells hw omega hx.2.1 hxBalls,
    angularDesignDensity_eq_one_off_cells hw omega' hx.2.1 hxBalls]

/-- An angular design is the restriction of Lebesgue measure to the square,
tilted there by the untruncated angular density. -/
-- @node: angularDesignMeasure_eq_restrict_withDensity
lemma angularDesignMeasure_eq_restrict_withDensity {M : ℕ}
    {b cA delta w : ℝ} (centers : Fin M → Score) (omega : Fin M → Bool) :
    angularDesignMeasure b cA delta w centers omega =
      (volume.restrict (scoreCube (1 / 2 : ℝ))).withDensity
        (fun x => ENNReal.ofReal
          (packingAngularDensity b cA delta w centers omega x)) := by
  rw [angularDesignMeasure]
  have hfun : (fun x => ENNReal.ofReal
      (angularDesignDensity b cA delta w centers omega x)) =
      (scoreCube (1 / 2 : ℝ)).indicator (fun x => ENNReal.ofReal
        (packingAngularDensity b cA delta w centers omega x)) := by
    funext x
    by_cases hx : x ∈ scoreCube (1 / 2 : ℝ)
    · rw [angularDesignDensity, indicator_of_mem hx, indicator_of_mem hx]
    · rw [angularDesignDensity, indicator_of_notMem hx, indicator_of_notMem hx]
      simp
  rw [hfun, withDensity_indicator (scoreCube_measurableSet (1 / 2 : ℝ))]

/-- Every admissibly separated angular design has the fixed square as its
exact topological support. -/
-- @node: angularDesignMeasure_support
lemma angularDesignMeasure_support {M : ℕ} {b cA delta w : ℝ} (hb : 0 < b)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA) (hdelta : 0 < delta)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) :
    (angularDesignMeasure b cA delta w centers omega).support =
      scoreCube (1 / 2 : ℝ) := by
  let f : Score → ENNReal := fun x => ENNReal.ofReal
    (packingAngularDensity b cA delta w centers omega x)
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp
      (packingAngularDensity_measurable hb hscale centers omega)
  have hf0 : ∀ x, f x ≠ 0 := by
    intro x
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      ((by norm_num : (0 : ℝ) < 3 / 4).trans_le
        (packingAngularDensity_mem_Icc hcA hdelta hw hsep omega x).1))
  have heq : angularDesignMeasure b cA delta w centers omega =
      (volume.restrict (scoreCube (1 / 2 : ℝ))).withDensity f := by
    simpa [f] using angularDesignMeasure_eq_restrict_withDensity centers omega
  apply Set.Subset.antisymm
  · calc
      _ ⊆ (volume.restrict (scoreCube (1 / 2 : ℝ))).support := by
        rw [heq]
        exact (withDensity_absolutelyContinuous _ _).support_mono
      _ = _ := volume_restrict_packingScoreCube_support
  · calc
      _ = (volume.restrict (scoreCube (1 / 2 : ℝ))).support :=
        volume_restrict_packingScoreCube_support.symm
      _ ⊆ _ := by
        rw [heq]
        exact (withDensity_absolutelyContinuous' hf.aemeasurable
          (Filter.Eventually.of_forall hf0)).support_mono

/-- The all-false angular design is exactly Lebesgue measure restricted to
the supporting square. -/
-- @node: angularDesignMeasure_allFalse_eq_restrict
lemma angularDesignMeasure_allFalse_eq_restrict {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) :
    angularDesignMeasure b cA delta w centers (fun _ => false) =
      volume.restrict (scoreCube (1 / 2 : ℝ)) := by
  ext s hs
  rw [angularDesignMeasure, withDensity_apply _ hs, Measure.restrict_apply hs]
  have hfun : (fun x => ENNReal.ofReal
      (angularDesignDensity b cA delta w centers (fun _ => false) x)) =
      (scoreCube (1 / 2 : ℝ)).indicator (fun _ => (1 : ENNReal)) := by
    funext x
    by_cases hx : x ∈ scoreCube (1 / 2 : ℝ)
    · rw [angularDesignDensity, Set.indicator_of_mem hx,
          Set.indicator_of_mem hx]
      simp [packingAngularDensity]
    · rw [angularDesignDensity, Set.indicator_of_notMem hx,
          Set.indicator_of_notMem hx]
      simp
  rw [hfun, lintegral_indicator (scoreCube_measurableSet (1 / 2 : ℝ))]
  rw [lintegral_one]
  simp only [Measure.restrict_apply, scoreCube_measurableSet,
    MeasurableSet.univ, univ_inter]
  rw [inter_comm]

/-- The all-false angular design has the supporting square as its exact
topological support. -/
-- @node: angularDesignMeasure_allFalse_support
lemma angularDesignMeasure_allFalse_support {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) :
    (angularDesignMeasure b cA delta w centers (fun _ => false)).support =
      scoreCube (1 / 2 : ℝ) := by
  rw [angularDesignMeasure_allFalse_eq_restrict,
    volume_restrict_packingScoreCube_support]

/-- Every angular design measure is absolutely continuous with respect to
Lebesgue measure. -/
-- @node: angularDesignMeasure_absolutelyContinuous
lemma angularDesignMeasure_absolutelyContinuous {M : ℕ} (b cA delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) :
    angularDesignMeasure b cA delta w centers omega ≪ volume := by
  exact withDensity_absolutelyContinuous volume _

/-- A grid-centered angular correction has zero integral over the whole
supporting square, because it vanishes away from its own half-disc cell. -/
-- @node: packingAngularTerm_integral_square
lemma packingAngularTerm_integral_square {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hw0 : 0 < w) (hw : w ≤ 1 / 4) :
    (∫ x : Score in scoreCube (1 / 2),
      packingAngularTerm b cA delta w (angularGridCenter M j) x) = 0 := by
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero
    (scoreCube_measurableSet (1 / 2 : ℝ)) inter_subset_right]
  · exact packingAngularTerm_integral_gridCell j hw
  · rintro x ⟨hxSquare, hxCell⟩
    have hxBall : x ∉ Metric.closedBall (angularGridCenter M j) w := by
      intro hx
      exact hxCell ⟨hx, hxSquare⟩
    apply packingAngularTerm_eq_zero_of_bandwidth_le_dist hw0
    exact (not_le.mp (by simpa [Metric.mem_closedBall] using hxBall)).le

/-- Every separated angular grid density integrates to one over the square. -/
-- @node: packingAngularDensity_integral_square
lemma packingAngularDensity_integral_square {M : ℕ} {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (hw0 : 0 < w) (hw : w ≤ 1 / 4)
    (omega : Fin M → Bool) :
    (∫ x : Score in scoreCube (1 / 2),
      packingAngularDensity b cA delta w (angularGridCenter M) omega x) = 1 := by
  have hconst : IntegrableOn (fun _ : Score => (1 : ℝ)) (scoreCube (1 / 2)) :=
    continuous_const.continuousOn.integrableOn_compact packingScoreCube_isCompact
  have hterms : ∀ j : Fin M, IntegrableOn
      (fun x : Score => if omega j then
        packingAngularTerm b cA delta w (angularGridCenter M j) x else 0)
      (scoreCube (1 / 2)) := by
    intro j
    by_cases hj : omega j = true
    · simpa [hj] using
        (packingAngularTerm_continuous hb hscale
          (angularGridCenter M j)).continuousOn.integrableOn_compact
            packingScoreCube_isCompact
    · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
      simpa [hjf] using
        continuous_const.continuousOn.integrableOn_compact
          (K := scoreCube (1 / 2 : ℝ)) packingScoreCube_isCompact
  unfold packingAngularDensity
  rw [integral_add hconst (integrable_finset_sum _ fun j _ => hterms j)]
  rw [integral_const]
  change ((volume.restrict (scoreCube (1 / 2 : ℝ))) univ).toReal * 1 + _ = 1
  rw [Measure.restrict_apply MeasurableSet.univ,
    univ_inter, packingSquare_volume, ENNReal.toReal_one]
  simp only [one_mul]
  have hz : (∫ x : Score in scoreCube (1 / 2),
      ∑ j, if omega j then
        packingAngularTerm b cA delta w (angularGridCenter M j) x else 0) = 0 := by
    rw [integral_finset_sum _ fun j _ => hterms j]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : omega j = true
    · simp only [hj, if_true]
      exact packingAngularTerm_integral_square (b := b) (cA := cA)
        (delta := delta) j hw0 hw
    · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
      simp [hjf]
  rw [hz]
  norm_num

/-- Every admissibly separated angular design on the explicit grid is a
probability measure. -/
-- @node: angularDesignMeasure_isProbabilityMeasure
lemma angularDesignMeasure_isProbabilityMeasure {M : ℕ}
    {b cA delta w : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw0 : 0 < w) (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) :
    IsProbabilityMeasure
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega) := by
  rw [isProbabilityMeasure_iff, angularDesignMeasure,
    withDensity_apply _ MeasurableSet.univ]
  have hint : Integrable
      (angularDesignDensity b cA delta w (angularGridCenter M) omega) volume := by
    have hzero : angularDesignDensity b cA delta w (angularGridCenter M) omega =
        (scoreCube (1 / 2 : ℝ)).indicator
          (packingAngularDensity b cA delta w (angularGridCenter M) omega) := rfl
    rw [hzero]
    have hOn : IntegrableOn
        (packingAngularDensity b cA delta w (angularGridCenter M) omega)
        (scoreCube (1 / 2 : ℝ)) volume :=
      (packingAngularDensity_continuous hb hscale
        (angularGridCenter M) omega).continuousOn.integrableOn_compact
          packingScoreCube_isCompact
    exact hOn.integrable_indicator (scoreCube_measurableSet (1 / 2 : ℝ))
  have hnonneg : 0 ≤ᵐ[volume]
      angularDesignDensity b cA delta w (angularGridCenter M) omega := by
    filter_upwards with x
    by_cases hx : x ∈ scoreCube (1 / 2 : ℝ)
    · have hlo := (angularDesignDensity_mem_Icc (b := b)
        hcA hdelta hw0 hsep omega hx).1
      norm_num at hlo ⊢
      linarith
    · rw [angularDesignDensity_eq_zero_off_square hx]
      simp
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [show (∫ x, angularDesignDensity b cA delta w (angularGridCenter M) omega x) =
      ∫ x in scoreCube (1 / 2),
        packingAngularDensity b cA delta w (angularGridCenter M) omega x by
    rw [angularDesignDensity]
    exact integral_indicator (scoreCube_measurableSet (1 / 2 : ℝ))]
  rw [packingAngularDensity_integral_square hb hscale hw0 hw omega]
  simp

/-- With every angular bit off, the square-supported design is a probability
measure.  Later normalization reduces the general vertex to this baseline by
showing that each active cosine tilt has zero integral. -/
-- @node: angularDesignMeasure_allFalse_isProbabilityMeasure
lemma angularDesignMeasure_allFalse_isProbabilityMeasure {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) :
    IsProbabilityMeasure
      (angularDesignMeasure b cA delta w centers (fun _ => false)) := by
  constructor
  rw [angularDesignMeasure, withDensity_apply _ MeasurableSet.univ]
  have hfun : (fun x => ENNReal.ofReal
      (angularDesignDensity b cA delta w centers (fun _ => false) x)) =
      (scoreCube (1 / 2 : ℝ)).indicator (fun _ => (1 : ENNReal)) := by
    funext x
    by_cases hx : x ∈ scoreCube (1 / 2 : ℝ)
    · rw [angularDesignDensity, Set.indicator_of_mem hx,
        Set.indicator_of_mem hx]
      simp [packingAngularDensity]
    · rw [angularDesignDensity, Set.indicator_of_notMem hx,
        Set.indicator_of_notMem hx]
      simp
  rw [hfun, lintegral_indicator (scoreCube_measurableSet (1 / 2 : ℝ))]
  simp only [Measure.restrict_apply_univ, lintegral_one]
  simpa using packingSquare_volume

end CausalSmith.Stat.BddUniformLogPenalty
