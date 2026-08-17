import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularDesign

/-!
# Radial cancellation for angular packing cells

This module strengthens the polar cancellation identities to measurable radial
subsets and transports them to the square-truncated cells used by the angular
packing.  These setwise identities are the leaf input for equality of adjacent
radius pushforwards.
-/

open MeasureTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Cartesian direction-cosine cancellation continues to hold after
restricting an open upper half-disc to any measurable set of radii. -/
-- @node: halfDisc_radialSet_weighted_first_div_radius_cancellation
lemma halfDisc_radialSet_weighted_first_div_radius_cancellation
    (g : ℝ → ℝ) (r : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ z : ℝ × ℝ in
      {z | 0 < z.2 ∧ planarRadius z ≤ r} ∩ planarRadius ⁻¹' A,
      g (planarRadius z) * (z.1 / planarRadius z)) = 0 := by
  have hD : MeasurableSet
      ({z : ℝ × ℝ | 0 < z.2 ∧ planarRadius z ≤ r} ∩ planarRadius ⁻¹' A) := by
    exact ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le planarRadius_measurable measurable_const)).inter
        (hA.preimage planarRadius_measurable)
  calc
    _ = ∫ z : ℝ × ℝ in
        {z | 0 < z.2 ∧ planarRadius z ≤ r} ∩ planarRadius ⁻¹' A,
        g (planarRadius z) * Real.cos (planarAngle z) := by
      apply integral_congr_ae
      exact ae_restrict_of_forall_mem hD fun z hz => by
        change g (planarRadius z) * (z.1 / planarRadius z) =
          g (planarRadius z) * Real.cos (planarAngle z)
        rw [planarFirst_div_radius_eq_cos z hz.1.1]
    _ = 0 := halfDisc_radialSet_weighted_cos_cancellation g r hA

/-- Closing the diameter of the half-disc does not alter setwise radial
Cartesian direction-cosine cancellation. -/
-- @node: closedHalfDisc_radialSet_weighted_first_div_radius_cancellation
lemma closedHalfDisc_radialSet_weighted_first_div_radius_cancellation
    (g : ℝ → ℝ) (r : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ z : ℝ × ℝ in
      {z | 0 ≤ z.2 ∧ planarRadius z ≤ r} ∩ planarRadius ⁻¹' A,
      g (planarRadius z) * (z.1 / planarRadius z)) = 0 := by
  let Dc : Set (ℝ × ℝ) :=
    {z | 0 ≤ z.2 ∧ planarRadius z ≤ r} ∩ planarRadius ⁻¹' A
  let Do : Set (ℝ × ℝ) :=
    {z | 0 < z.2 ∧ planarRadius z ≤ r} ∩ planarRadius ⁻¹' A
  change (∫ z : ℝ × ℝ in Dc,
    g (planarRadius z) * (z.1 / planarRadius z)) = 0
  rw [setIntegral_congr_set (show Dc =ᵐ[volume] Do by
    simp only [Filter.EventuallyEq]
    rw [ae_iff]
    apply measure_mono_null (t := {z : ℝ × ℝ | z.2 = 0})
    · intro z hz
      simp only [mem_setOf_eq]
      by_contra hy
      apply hz
      apply propext
      constructor
      · rintro ⟨⟨hy0, hr⟩, hrad⟩
        exact ⟨⟨lt_of_le_of_ne hy0 (Ne.symm hy), hr⟩, hrad⟩
      · rintro ⟨⟨hy0, hr⟩, hrad⟩
        exact ⟨⟨hy0.le, hr⟩, hrad⟩
    · rw [Measure.volume_eq_prod]
      rw [show {z : ℝ × ℝ | z.2 = 0} = Set.univ ×ˢ ({0} : Set ℝ) by
        ext z
        simp]
      rw [Measure.prod_prod]
      simp)]
  simpa [Do] using
    halfDisc_radialSet_weighted_first_div_radius_cancellation g r hA

/-- Translation preserves closed-half-disc cancellation on every measurable
radial subset. -/
-- @node: translatedClosedHalfDisc_radialSet_weighted_first_div_radius_cancellation
lemma translatedClosedHalfDisc_radialSet_weighted_first_div_radius_cancellation
    (g : ℝ → ℝ) (r : ℝ) (c : ℝ × ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ z : ℝ × ℝ in
      {z | 0 ≤ (z - c).2 ∧ planarRadius (z - c) ≤ r} ∩
        {z | planarRadius (z - c) ∈ A},
      g (planarRadius (z - c)) * ((z - c).1 / planarRadius (z - c))) = 0 := by
  let D : Set (ℝ × ℝ) :=
    ({u | 0 ≤ u.2 ∧ planarRadius u ≤ r} ∩ planarRadius ⁻¹' A)
  let T : (ℝ × ℝ) → (ℝ × ℝ) := fun u => c + u
  have hT : MeasurableEmbedding T :=
    (Homeomorph.addLeft c).measurableEmbedding
  have hmp : MeasurePreserving T (volume : Measure (ℝ × ℝ)) volume :=
    measurePreserving_add_left volume c
  have hset :
      ({z : ℝ × ℝ | 0 ≤ (z - c).2 ∧ planarRadius (z - c) ≤ r} ∩
        {z | planarRadius (z - c) ∈ A}) = T '' D := by
    ext z
    constructor
    · rintro ⟨hz, hA'⟩
      refine ⟨z - c, ?_, by simp [T]⟩
      exact ⟨hz, hA'⟩
    · rintro ⟨u, ⟨hu, hAu⟩, rfl⟩
      simpa [T] using And.intro hu hAu
  rw [hset, hmp.setIntegral_image_emb hT]
  have hfun : (fun u : ℝ × ℝ =>
      g (planarRadius (T u - c)) * ((T u - c).1 / planarRadius (T u - c))) =
      fun u => g (planarRadius u) * (u.1 / planarRadius u) := by
    funext u
    simp [T]
  rw [hfun]
  exact closedHalfDisc_radialSet_weighted_first_div_radius_cancellation g r hA

/-- At a lower-edge angular grid center, every radial weight times the
horizontal direction cosine integrates to zero on each measurable radial
slice of the square-truncated cell. -/
-- @node: angularGridCenter_closedRadialSet_weighted_direction_cancellation
lemma angularGridCenter_closedRadialSet_weighted_direction_cancellation
    {M : ℕ} (j : Fin M) (g : ℝ → ℝ) (w : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    let c := angularGridCenter M j
    let D : Set Score :=
      {x | 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A}
    (∫ x in D, g (dist x c) *
      ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) = 0 := by
  dsimp only
  let c : Score := angularGridCenter M j
  let cp : ℝ × ℝ := scoreCoordinates c
  let D : Set Score :=
    {x | 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ A}
  let E : Set (ℝ × ℝ) :=
    {z | 0 ≤ (z - cp).2 ∧ planarRadius (z - cp) ≤ w} ∩
      {z | planarRadius (z - cp) ∈ A}
  have himage : scoreCoordinates '' D = E := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [D, E, cp, c, planarRadius_scoreCoordinates_sub] using hx
    · intro hz
      let x : Score := scorePoint z.1 z.2
      have hcoord : scoreCoordinates x = z := by
        ext <;> simp [x, scoreCoordinates, scorePoint_apply_zero,
          scorePoint_apply_one]
      have hdist : dist x c = planarRadius (z - scoreCoordinates c) := by
        rw [← planarRadius_scoreCoordinates_sub, hcoord]
      refine ⟨x, ?_, hcoord⟩
      simpa [D, E, cp, c, hcoord, hdist] using hz
  change (∫ x in D, g (dist x c) *
    ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) = 0
  have hfun : (fun x : Score => g (dist x c) *
      ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) =
      fun x => g (planarRadius (scoreCoordinates x - scoreCoordinates c)) *
        ((scoreCoordinates x - scoreCoordinates c).1 /
          planarRadius (scoreCoordinates x - scoreCoordinates c)) := by
    funext x
    rw [planarRadius_scoreCoordinates_sub]
  rw [hfun]
  rw [← scoreCoordinates_measurePreserving.setIntegral_image_emb
      scoreCoordinates_measurableEmbedding
      (fun z : ℝ × ℝ => g (planarRadius (z - scoreCoordinates c)) *
        ((z - scoreCoordinates c).1 /
          planarRadius (z - scoreCoordinates c))) D]
  rw [himage]
  simpa [E, cp, c] using
    translatedClosedHalfDisc_radialSet_weighted_first_div_radius_cancellation
      g w (scoreCoordinates (angularGridCenter M j)) hA

/-- An angular correction integrates to zero on every measurable radial
slice of its square-truncated packing cell. -/
-- @node: packingAngularTerm_integral_gridCell_radialSet
lemma packingAngularTerm_integral_gridCell_radialSet {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hw : w ≤ 1 / 4) {A : Set ℝ}
    (hA : MeasurableSet A) :
    (∫ x : Score in
      (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) ∩
        {x | dist x (angularGridCenter M j) ∈ A},
      packingAngularTerm b cA delta w (angularGridCenter M j) x) = 0 := by
  let c := scoreCoordinates (angularGridCenter M j)
  let D : Set (ℝ × ℝ) :=
    ({z | 0 ≤ (z - c).2 ∧ planarRadius (z - c) ≤ w} ∩
      {z | planarRadius (z - c) ∈ A})
  have himage : scoreCoordinates ''
      ((Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) ∩
        {x | dist x (angularGridCenter M j) ∈ A}) = D := by
    ext z
    constructor
    · rintro ⟨x, ⟨hx, hr⟩, rfl⟩
      refine ⟨(mem_angularGrid_packingCell_iff_closedUpperHalfDisc j hw x).mp hx, ?_⟩
      simpa [c, planarRadius_scoreCoordinates_sub] using hr
    · rintro ⟨hz, hr⟩
      let x : Score := scorePoint z.1 z.2
      have hcoord : scoreCoordinates x = z := by
        ext <;> simp [x, scoreCoordinates, scorePoint_apply_zero,
          scorePoint_apply_one]
      refine ⟨x, ⟨?_, ?_⟩, hcoord⟩
      · apply (mem_angularGrid_packingCell_iff_closedUpperHalfDisc j hw x).mpr
        simpa [D, c, hcoord] using hz
      · change dist x (angularGridCenter M j) ∈ A
        rw [← planarRadius_scoreCoordinates_sub]
        simpa [c, hcoord] using hr
  have hterm : packingAngularTerm b cA delta w (angularGridCenter M j) =
      fun x => angularTilt b cA delta w
          (planarRadius (scoreCoordinates x - scoreCoordinates (angularGridCenter M j))) *
        ((scoreCoordinates x - scoreCoordinates (angularGridCenter M j)).1 /
          planarRadius (scoreCoordinates x - scoreCoordinates (angularGridCenter M j))) := by
    funext x
    rw [packingAngularTerm,
      packingDirectionCos_eq_planarFirst_div_radius,
      planarRadius_scoreCoordinates_sub]
  rw [hterm]
  rw [← scoreCoordinates_measurePreserving.setIntegral_image_emb
    scoreCoordinates_measurableEmbedding
    (fun z : ℝ × ℝ =>
      angularTilt b cA delta w
          (planarRadius (z - scoreCoordinates (angularGridCenter M j))) *
        ((z - scoreCoordinates (angularGridCenter M j)).1 /
          planarRadius (z - scoreCoordinates (angularGridCenter M j))))
    ((Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) ∩
      {x | dist x (angularGridCenter M j) ∈ A})]
  rw [himage]
  change (∫ z : ℝ × ℝ in D,
    angularTilt b cA delta w (planarRadius (z - c)) *
      ((z - c).1 / planarRadius (z - c))) = 0
  exact translatedClosedHalfDisc_radialSet_weighted_first_div_radius_cancellation
    (angularTilt b cA delta w) w c hA

/-- Every measurable radial slice of a grid cell has its unperturbed
Lebesgue mass under the angular density, independently of the active bit. -/
-- @node: packingAngularDensity_integral_gridCell_radialSet
lemma packingAngularDensity_integral_gridCell_radialSet {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hw0 : 0 < w) (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ x : Score in
      (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) ∩
        {x | dist x (angularGridCenter M j) ∈ A},
      packingAngularDensity b cA delta w (angularGridCenter M) omega x) =
      (volume ((Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) ∩
        {x | dist x (angularGridCenter M j) ∈ A})).toReal := by
  let C := Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)
  let R : Set Score := {x | dist x (angularGridCenter M j) ∈ A}
  let omega' : Fin M → Bool := fun k => if k = j then omega j else false
  have hR : MeasurableSet R := hA.preimage (by fun_prop)
  have hCR : MeasurableSet (C ∩ R) :=
    (Metric.isClosed_closedBall.measurableSet.inter
      (scoreCube_measurableSet _)).inter hR
  have hpoint : ∀ x ∈ C ∩ R,
      packingAngularDensity b cA delta w (angularGridCenter M) omega x =
        1 + if omega j then
          packingAngularTerm b cA delta w (angularGridCenter M j) x else 0 := by
    intro x hx
    rw [packingAngularDensity_eq_on_cell hw0 hsep
      (omega' := omega') (j := j) (by simp [omega']) hx.1.1]
    simp only [packingAngularDensity, omega']
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj]
    · simp
  rw [setIntegral_congr_fun hCR hpoint]
  have hcompact : IsCompact C :=
    (isCompact_closedBall (angularGridCenter M j) w).inter_right
      packingScoreCube_isCompact.isClosed
  have hconst : IntegrableOn (fun _ : Score => (1 : ℝ)) (C ∩ R) :=
    (continuous_const.continuousOn.integrableOn_compact hcompact).mono_set inter_subset_left
  have hterm : IntegrableOn
      (fun x : Score => if omega j then
        packingAngularTerm b cA delta w (angularGridCenter M j) x else 0) (C ∩ R) := by
    by_cases hj : omega j = true
    · simpa [hj] using
        (((packingAngularTerm_continuous hb hscale
          (angularGridCenter M j)).continuousOn.integrableOn_compact hcompact).mono_set
            inter_subset_left : IntegrableOn
              (packingAngularTerm b cA delta w (angularGridCenter M j)) (C ∩ R))
    · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
      simpa [hjf] using hconst.const_mul 0
  rw [integral_add hconst hterm, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ]
  have hz : (∫ x : Score in C ∩ R,
      if omega j then
        packingAngularTerm b cA delta w (angularGridCenter M j) x else 0) = 0 := by
    by_cases hj : omega j = true
    · simpa [C, R, hj] using
        (packingAngularTerm_integral_gridCell_radialSet (b := b) (cA := cA)
          (delta := delta) j hw hA)
    · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
      simp [hjf]
  rw [hz]
  simp [C, R]

/-- The score design assigns every measurable radial slice of a grid cell
exactly its Lebesgue volume, uniformly over packing vertices. -/
-- @node: angularDesignMeasure_gridCell_radialSet_eq_volume
lemma angularDesignMeasure_gridCell_radialSet_eq_volume {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw0 : 0 < w)
    (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) {A : Set ℝ} (hA : MeasurableSet A) :
    angularDesignMeasure b cA delta w (angularGridCenter M) omega
        ((Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) ∩
          {x | dist x (angularGridCenter M j) ∈ A}) =
      volume ((Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) ∩
        {x | dist x (angularGridCenter M j) ∈ A}) := by
  let C := (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) ∩
    {x | dist x (angularGridCenter M j) ∈ A}
  have hC : MeasurableSet C :=
    (Metric.isClosed_closedBall.measurableSet.inter
      (scoreCube_measurableSet _)).inter (hA.preimage (by fun_prop))
  rw [angularDesignMeasure, withDensity_apply _ hC]
  have hcompact : IsCompact
      (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) :=
    (isCompact_closedBall (angularGridCenter M j) w).inter_right
      packingScoreCube_isCompact.isClosed
  have hint : IntegrableOn
      (packingAngularDensity b cA delta w (angularGridCenter M) omega) C volume :=
    ((packingAngularDensity_continuous hb hscale
      (angularGridCenter M) omega).continuousOn.integrableOn_compact hcompact).mono_set
        (by intro x hx; exact hx.1)
  have hnonneg : 0 ≤ᵐ[volume.restrict C]
      packingAngularDensity b cA delta w (angularGridCenter M) omega := by
    filter_upwards with x
    exact (packingAngularDensity_mem_Icc hcA hdelta hw0 hsep omega x).1.trans'
      (by norm_num)
  have heq : (fun x => ENNReal.ofReal
      (angularDesignDensity b cA delta w (angularGridCenter M) omega x)) =ᵐ[volume.restrict C]
      fun x => ENNReal.ofReal
        (packingAngularDensity b cA delta w (angularGridCenter M) omega x) := by
    filter_upwards [ae_restrict_mem hC] with x hx
    rw [angularDesignDensity_eq_on_square hx.1.2]
  rw [lintegral_congr_ae heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [show (∫ x : Score in C,
      packingAngularDensity b cA delta w (angularGridCenter M) omega x) =
        (volume C).toReal by
    exact packingAngularDensity_integral_gridCell_radialSet j hb hscale hw0 hw
      hsep omega hA]
  apply ENNReal.ofReal_toReal
  exact ne_of_lt ((measure_mono (by
    intro x hx
    exact hx.1)).trans_lt hcompact.measure_lt_top)

/-- Outside one grid cell, two angular design densities agree whenever all
Boolean coordinates other than that cell's coordinate agree. -/
-- @node: angularDesignDensity_eq_off_gridCell
lemma angularDesignDensity_eq_off_gridCell {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hw0 : 0 < w)
    (omega omega' : Fin M → Bool)
    (hother : ∀ k, k ≠ j → omega k = omega' k)
    {x : Score}
    (hx : x ∉ Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) :
    angularDesignDensity b cA delta w (angularGridCenter M) omega x =
      angularDesignDensity b cA delta w (angularGridCenter M) omega' x := by
  by_cases hxSquare : x ∈ scoreCube (1 / 2 : ℝ)
  · rw [angularDesignDensity_eq_on_square hxSquare,
      angularDesignDensity_eq_on_square hxSquare]
    unfold packingAngularDensity
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : k = j
    · subst k
      have hxBall : x ∉ Metric.closedBall (angularGridCenter M j) w :=
        fun h => hx ⟨h, hxSquare⟩
      have hfar : w ≤ dist x (angularGridCenter M j) := by
        exact le_of_lt (by simpa [Metric.mem_closedBall, not_le] using
          (show w < dist x (angularGridCenter M j) by
            simpa [Metric.mem_closedBall, not_le] using hxBall))
      rw [packingAngularTerm_eq_zero_of_bandwidth_le_dist hw0 hfar]
      simp
    · rw [hother k hkj]
  · rw [angularDesignDensity_eq_zero_off_square hxSquare,
      angularDesignDensity_eq_zero_off_square hxSquare]

/-- The restrictions of two adjacent angular score designs to the complement
of the changed grid cell are identical. -/
-- @node: angularDesignMeasure_restrict_compl_gridCell_eq
lemma angularDesignMeasure_restrict_compl_gridCell_eq {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hw0 : 0 < w)
    (omega omega' : Fin M → Bool)
    (hother : ∀ k, k ≠ j → omega k = omega' k) :
    (angularDesignMeasure b cA delta w (angularGridCenter M) omega).restrict
        (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2))ᶜ =
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega').restrict
        (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2))ᶜ := by
  let C := Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)
  have hC : MeasurableSet C :=
    Metric.isClosed_closedBall.measurableSet.inter (scoreCube_measurableSet _)
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  unfold angularDesignMeasure
  rw [withDensity_apply _ (hs.inter hC.compl),
    withDensity_apply _ (hs.inter hC.compl)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (hs.inter hC.compl)] with x hx
  apply congrArg ENNReal.ofReal
  exact angularDesignDensity_eq_off_gridCell j hw0 omega omega' hother hx.2

/-- The radius pushforwards of two angular score designs agree whenever the
vertices differ, if at all, only at the queried grid cell. -/
-- @node: angularDesignMeasure_map_distance_eq
lemma angularDesignMeasure_map_distance_eq {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw0 : 0 < w)
    (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega omega' : Fin M → Bool)
    (hother : ∀ k, k ≠ j → omega k = omega' k) :
    Measure.map (fun x : Score => dist x (angularGridCenter M j))
        (angularDesignMeasure b cA delta w (angularGridCenter M) omega) =
      Measure.map (fun x : Score => dist x (angularGridCenter M j))
        (angularDesignMeasure b cA delta w (angularGridCenter M) omega') := by
  let C := Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)
  let radial : Score → ℝ := fun x => dist x (angularGridCenter M j)
  have hC : MeasurableSet C :=
    Metric.isClosed_closedBall.measurableSet.inter (scoreCube_measurableSet _)
  have hradial : Measurable radial := by fun_prop
  have hcell : Measure.map radial
        ((angularDesignMeasure b cA delta w (angularGridCenter M) omega).restrict C) =
      Measure.map radial
        ((angularDesignMeasure b cA delta w (angularGridCenter M) omega').restrict C) := by
    ext A hA
    rw [Measure.map_apply hradial hA, Measure.map_apply hradial hA,
      Measure.restrict_apply (hA.preimage hradial),
      Measure.restrict_apply (hA.preimage hradial)]
    have hset : radial ⁻¹' A ∩ C = C ∩ {x | dist x (angularGridCenter M j) ∈ A} := by
      ext x
      simp [radial, and_comm]
    rw [hset,
      angularDesignMeasure_gridCell_radialSet_eq_volume j hb hscale hcA hdelta
        hw0 hw hsep omega hA,
      angularDesignMeasure_gridCell_radialSet_eq_volume j hb hscale hcA hdelta
        hw0 hw hsep omega' hA]
  have hcompl :
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega).restrict Cᶜ =
        (angularDesignMeasure b cA delta w (angularGridCenter M) omega').restrict Cᶜ := by
    exact angularDesignMeasure_restrict_compl_gridCell_eq j hw0 omega omega' hother
  calc
    Measure.map radial
        (angularDesignMeasure b cA delta w (angularGridCenter M) omega) =
        Measure.map radial
          ((angularDesignMeasure b cA delta w (angularGridCenter M) omega).restrict C +
            (angularDesignMeasure b cA delta w
              (angularGridCenter M) omega).restrict Cᶜ) := by
          rw [Measure.restrict_add_restrict_compl hC]
    _ = Measure.map radial
          ((angularDesignMeasure b cA delta w (angularGridCenter M) omega).restrict C) +
        Measure.map radial
          ((angularDesignMeasure b cA delta w (angularGridCenter M) omega).restrict Cᶜ) :=
      Measure.map_add _ _ hradial
    _ = Measure.map radial
          ((angularDesignMeasure b cA delta w (angularGridCenter M) omega').restrict C) +
        Measure.map radial
          ((angularDesignMeasure b cA delta w (angularGridCenter M) omega').restrict Cᶜ) := by
      rw [hcell, hcompl]
    _ = Measure.map radial
        (angularDesignMeasure b cA delta w (angularGridCenter M) omega') := by
      rw [← Measure.map_add _ _ hradial, Measure.restrict_add_restrict_compl hC]

/-- On every measurable set of radii where the angular cutoff is fully active,
the radial bump contribution is exactly cancelled by the affine-times-angular
contribution after integration over the upper half-disc. -/
-- @node: halfDisc_radialSet_angular_outcome_cancellation
lemma halfDisc_radialSet_angular_outcome_cancellation
    {b cA delta w R : ℝ} (hscale : 0 < cA * delta)
    {A : Set ℝ} (hA : MeasurableSet A)
    (hactive : ∀ r ∈ A, 2 * (cA * delta) ≤ b * r) :
    (∫ z : ℝ × ℝ in
      {z | 0 < z.2 ∧ planarRadius z ≤ R} ∩ planarRadius ⁻¹' A,
      delta * angularRadialProfile w (planarRadius z)) +
    (∫ z : ℝ × ℝ in
      {z | 0 < z.2 ∧ planarRadius z ≤ R} ∩ planarRadius ⁻¹' A,
      b * z.1 * angularTilt b cA delta w (planarRadius z) *
        (z.1 / planarRadius z)) = 0 := by
  let D : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ planarRadius z ≤ R}
  let E : Set (ℝ × ℝ) := planarRadius ⁻¹' A
  have hD : MeasurableSet D :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le planarRadius_measurable measurable_const)
  have hE : MeasurableSet E := hA.preimage planarRadius_measurable
  have hfirst := halfDisc_radial_integral
    (fun r => A.indicator (fun s => delta * angularRadialProfile w s) r) R
  have hsecond := halfDisc_weighted_cos_sq
    (fun r => A.indicator (fun s => b * r * angularTilt b cA delta w r) r) R
  change (∫ z : ℝ × ℝ in D ∩ E,
      delta * angularRadialProfile w (planarRadius z)) +
    (∫ z : ℝ × ℝ in D ∩ E,
      b * z.1 * angularTilt b cA delta w (planarRadius z) *
        (z.1 / planarRadius z)) = 0
  have hfirst' :
      (∫ z : ℝ × ℝ in D ∩ E,
        delta * angularRadialProfile w (planarRadius z)) =
        ∫ r : ℝ in Ioc 0 R,
          Real.pi * r * A.indicator
            (fun s => delta * angularRadialProfile w s) r := by
    rw [inter_comm, ← Measure.restrict_restrict hE, ← integral_indicator hE]
    calc
      (∫ z : ℝ × ℝ in D,
          E.indicator (fun z => delta * angularRadialProfile w (planarRadius z)) z) =
          ∫ z : ℝ × ℝ in D,
            A.indicator (fun s => delta * angularRadialProfile w s)
              (planarRadius z) := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : planarRadius z ∈ A <;> simp [E, hz]
      _ = _ := by simpa [D] using hfirst
  have hsecond' :
      (∫ z : ℝ × ℝ in D ∩ E,
        b * z.1 * angularTilt b cA delta w (planarRadius z) *
          (z.1 / planarRadius z)) =
        (∫ r : ℝ in Ioc 0 R,
          r * A.indicator
            (fun s => b * s * angularTilt b cA delta w s) r) *
          (Real.pi / 2) := by
    rw [inter_comm, ← Measure.restrict_restrict hE, ← integral_indicator hE]
    calc
      (∫ z : ℝ × ℝ in D,
          E.indicator (fun z => b * z.1 * angularTilt b cA delta w
            (planarRadius z) * (z.1 / planarRadius z)) z) =
          ∫ z : ℝ × ℝ in D,
            A.indicator (fun s => b * planarRadius z *
              angularTilt b cA delta w (planarRadius z)) (planarRadius z) *
                Real.cos (planarAngle z) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hD] with z hzD
        by_cases hz : planarRadius z ∈ A
        · rw [Set.indicator_of_mem (show z ∈ E by exact hz),
            Set.indicator_of_mem hz]
          have hr := planarFirst_div_radius_eq_cos z hzD.1
          have hr0 : planarRadius z ≠ 0 := by
            intro hzero
            have hs : z.1 ^ 2 + z.2 ^ 2 ≤ 0 := by
              exact Real.sqrt_eq_zero'.mp (by simpa [planarRadius] using hzero)
            nlinarith [hzD.1, sq_nonneg z.1, sq_nonneg z.2]
          field_simp [hr0] at hr
          field_simp [hr0]
          rw [hr]
          ring
        · rw [Set.indicator_of_notMem (show z ∉ E by exact hz),
            Set.indicator_of_notMem hz]
          simp
      _ = _ := hsecond
  rw [hfirst', hsecond']
  have hfint : IntegrableOn
      (fun r : ℝ => Real.pi * r * A.indicator
        (fun s => delta * angularRadialProfile w s) r) (Ioc 0 R) := by
    have hbase : IntegrableOn
        (fun r : ℝ => Real.pi * r * (delta * angularRadialProfile w r))
        (Ioc 0 R) := by
      have hcont : Continuous (fun r : ℝ =>
          Real.pi * r * (delta * angularRadialProfile w r)) :=
        (continuous_const.mul continuous_id).mul
          (continuous_const.mul (angularRadialProfile_continuous w))
      exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Ioc_subset_Icc_self
    exact (hbase.indicator hA).congr
      (Filter.Eventually.of_forall fun r => by
        by_cases hr : r ∈ A <;> simp [Set.indicator, hr])
  have hgint : IntegrableOn
      (fun r : ℝ => r * A.indicator
        (fun s => b * s * angularTilt b cA delta w s) r) (Ioc 0 R) := by
    have hbase : IntegrableOn
        (fun r : ℝ => r * (b * r * angularTilt b cA delta w r))
        (Ioc 0 R) := by
      exact ((continuous_id.mul
          ((continuous_const.mul continuous_id).mul
            (angularTilt_continuous hscale))).continuousOn.integrableOn_compact
              isCompact_Icc).mono_set Ioc_subset_Icc_self
    exact (hbase.indicator hA).congr
      (Filter.Eventually.of_forall fun r => by
        by_cases hr : r ∈ A <;> simp [Set.indicator, hr])
  rw [← integral_mul_const,
    ← integral_add hfint (hgint.mul_const (Real.pi / 2))]
  apply integral_eq_zero_of_ae
  filter_upwards with r
  by_cases hrA : r ∈ A
  · simp only [Set.indicator_of_mem hrA]
    have hc := angularOutcomeCancellation_identity (w := w) hscale (hactive r hrA)
    calc
      Real.pi * r * (delta * angularRadialProfile w r) +
          r * (b * r * angularTilt b cA delta w r) * (Real.pi / 2) =
          r * (Real.pi * delta * angularRadialProfile w r +
            (Real.pi / 2) * (b * r) * angularTilt b cA delta w r) := by ring
      _ = 0 := by rw [hc, mul_zero]
  · simp [Set.indicator_of_notMem hrA]

/-- Translation of the fully-active radial outcome cancellation to a packing
center.  This is the form used when the lower-edge half-disc is written in
the ambient score coordinates. -/
-- @node: translatedHalfDisc_radialSet_angular_outcome_cancellation
lemma translatedHalfDisc_radialSet_angular_outcome_cancellation
    {b cA delta w R : ℝ} (hscale : 0 < cA * delta)
    (c : ℝ × ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    (hactive : ∀ r ∈ A, 2 * (cA * delta) ≤ b * r) :
    (∫ z : ℝ × ℝ in
      {z | 0 < (z - c).2 ∧ planarRadius (z - c) ≤ R} ∩
          {z | planarRadius (z - c) ∈ A},
      delta * angularRadialProfile w (planarRadius (z - c))) +
    (∫ z : ℝ × ℝ in
      {z | 0 < (z - c).2 ∧ planarRadius (z - c) ≤ R} ∩
          {z | planarRadius (z - c) ∈ A},
      b * (z - c).1 * angularTilt b cA delta w (planarRadius (z - c)) *
        ((z - c).1 / planarRadius (z - c))) = 0 := by
  let D : Set (ℝ × ℝ) :=
    {u | 0 < u.2 ∧ planarRadius u ≤ R} ∩ {u | planarRadius u ∈ A}
  let T : (ℝ × ℝ) → (ℝ × ℝ) := fun u => c + u
  have hT : MeasurableEmbedding T :=
    (Homeomorph.addLeft c).measurableEmbedding
  have hmp : MeasurePreserving T (volume : Measure (ℝ × ℝ)) volume :=
    measurePreserving_add_left volume c
  have hset :
      ({z : ℝ × ℝ | 0 < (z - c).2 ∧ planarRadius (z - c) ≤ R} ∩
          {z | planarRadius (z - c) ∈ A}) = T '' D := by
    ext z
    constructor
    · rintro ⟨hz, hAz⟩
      refine ⟨z - c, ⟨?_, ?_⟩, by simp [T]⟩
      · exact hz
      · exact hAz
    · rintro ⟨u, ⟨hu, hAu⟩, rfl⟩
      simpa [T] using And.intro hu hAu
  rw [hset, hmp.setIntegral_image_emb hT,
    hmp.setIntegral_image_emb hT]
  have hfirst : (fun u : ℝ × ℝ =>
      delta * angularRadialProfile w (planarRadius (T u - c))) =
      fun u => delta * angularRadialProfile w (planarRadius u) := by
    funext u
    simp [T]
  have hsecond : (fun u : ℝ × ℝ =>
      b * (T u - c).1 * angularTilt b cA delta w (planarRadius (T u - c)) *
        ((T u - c).1 / planarRadius (T u - c))) =
      fun u => b * u.1 * angularTilt b cA delta w (planarRadius u) *
        (u.1 / planarRadius u) := by
    funext u
    simp [T]
  rw [hfirst, hsecond]
  exact halfDisc_radialSet_angular_outcome_cancellation
    (w := w) (R := R) hscale hA hactive

end CausalSmith.Stat.BddUniformLogPenalty
