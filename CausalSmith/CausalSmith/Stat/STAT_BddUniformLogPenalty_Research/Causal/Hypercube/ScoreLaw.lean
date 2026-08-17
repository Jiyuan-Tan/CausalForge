import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareGeometry
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularFullDisc

/-!
# Angular score law on the causal hard square

This module puts the existing smooth angular tilt over the fixed square
`[-3,3]²` with baseline density `1/36`.  Complete-disk cancellation gives
normalization and exact bit-independent cell mass.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The causal hard-family score density: uniform background `1/36` plus the
disjoint smooth angular tilts. -/
-- @node: causalHardScoreDensity
noncomputable def causalHardScoreDensity {M : ℕ} (b cA delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) (x : Score) : ℝ :=
  (1 / 36 : ℝ) * packingAngularDensity b cA delta w centers omega x

/-- The causal score measure supported on the fixed hard square. -/
-- @node: causalHardScoreMeasure
noncomputable def causalHardScoreMeasure {M : ℕ} (b cA delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) : Measure Score :=
  volume.withDensity fun x =>
    ENNReal.ofReal (causalHardSquare.indicator
      (causalHardScoreDensity b cA delta w centers omega) x)

/-- The causal hard score density is continuous on the whole score plane. -/
-- @node: causalHardScoreDensity_continuous
lemma causalHardScoreDensity_continuous {M : ℕ} {b cA delta w : ℝ}
    (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) :
    Continuous (causalHardScoreDensity b cA delta w centers omega) := by
  unfold causalHardScoreDensity
  exact continuous_const.mul
    (packingAngularDensity_continuous hb hscale centers omega)

/-- Under three-bandwidth separation the causal density lies in the exact
paper envelope `[1/48,5/144]`. -/
-- @node: causalHardScoreDensity_mem_Icc
lemma causalHardScoreDensity_mem_Icc {M : ℕ} {b cA delta w : ℝ}
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (x : Score) :
    causalHardScoreDensity b cA delta w centers omega x ∈
      Icc (1 / 48 : ℝ) (5 / 144 : ℝ) := by
  have h := packingAngularDensity_mem_Icc (b := b)
    hcA hdelta hw hsep omega x
  unfold causalHardScoreDensity
  constructor <;> norm_num at h ⊢ <;> linarith

/-- Every admissible causal hard score law has the whole hard square as its
exact topological support. -/
-- @node: causalHardScoreMeasure_support
lemma causalHardScoreMeasure_support {M : ℕ} {b cA delta w : ℝ}
    (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k)) :
    (causalHardScoreMeasure b cA delta w centers omega).support =
      causalHardSquare := by
  let f : Score → ENNReal := fun x => ENNReal.ofReal
    (causalHardScoreDensity b cA delta w centers omega x)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    (causalHardScoreDensity_continuous centers omega hb hscale).measurable
  have hf0 : ∀ x, f x ≠ 0 := by
    intro x
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      ((by norm_num : (0 : ℝ) < 1 / 48).trans_le
        (causalHardScoreDensity_mem_Icc hcA hdelta hw hsep omega x).1))
  have hfun : (fun x => ENNReal.ofReal (causalHardSquare.indicator
      (causalHardScoreDensity b cA delta w centers omega) x)) =
      causalHardSquare.indicator f := by
    funext x
    by_cases hx : x ∈ causalHardSquare
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
      simp
  have heq : causalHardScoreMeasure b cA delta w centers omega =
      (volume.restrict causalHardSquare).withDensity f := by
    unfold causalHardScoreMeasure
    rw [hfun]
    rw [withDensity_indicator causalHardSquare_measurableSet]
  apply Set.Subset.antisymm
  · calc
      _ ⊆ (volume.restrict causalHardSquare).support := by
        rw [heq]
        exact (withDensity_absolutelyContinuous _ _).support_mono
      _ = _ := volume_restrict_causalHardSquare_support
  · calc
      _ = (volume.restrict causalHardSquare).support :=
        volume_restrict_causalHardSquare_support.symm
      _ ⊆ _ := by
        rw [heq]
        exact (withDensity_absolutelyContinuous' hf.aemeasurable
          (Filter.Eventually.of_forall hf0)).support_mono

/-- Restricting the causal score design to one packing cell erases every bit
except the bit indexing that cell. -/
-- @node: causalHardScoreMeasure_restrict_cell_eq
lemma causalHardScoreMeasure_restrict_cell_eq {M : ℕ} {b cA delta w : ℝ}
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    {omega omega' : Fin M → Bool} {j : Fin M} (hbit : omega j = omega' j) :
    (causalHardScoreMeasure b cA delta w centers omega).restrict
        (causalHardCell (centers j) w) =
      (causalHardScoreMeasure b cA delta w centers omega').restrict
        (causalHardCell (centers j) w) := by
  have hC : MeasurableSet (causalHardCell (centers j) w) :=
    Metric.isClosed_closedBall.measurableSet
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  unfold causalHardScoreMeasure
  rw [withDensity_apply _ (hs.inter hC), withDensity_apply _ (hs.inter hC)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (hs.inter hC)] with x hx
  apply congrArg ENNReal.ofReal
  by_cases hxS : x ∈ causalHardSquare
  · rw [indicator_of_mem hxS, indicator_of_mem hxS]
    unfold causalHardScoreDensity
    rw [packingAngularDensity_eq_on_cell hw hsep hbit hx.2]
  · rw [indicator_of_notMem hxS, indicator_of_notMem hxS]

/-- Away from all packing cells, every causal hard score law has the same
restriction. -/
-- @node: causalHardScoreMeasure_restrict_off_cells_eq
lemma causalHardScoreMeasure_restrict_off_cells_eq {M : ℕ}
    {b cA delta w : ℝ} (hw : 0 < w) {centers : Fin M → Score}
    (omega omega' : Fin M → Bool) :
    (causalHardScoreMeasure b cA delta w centers omega).restrict
        (causalHardSquare \ ⋃ j, causalHardCell (centers j) w) =
      (causalHardScoreMeasure b cA delta w centers omega').restrict
        (causalHardSquare \ ⋃ j, causalHardCell (centers j) w) := by
  let C := causalHardSquare \ ⋃ j, causalHardCell (centers j) w
  have hC : MeasurableSet C := causalHardSquare_measurableSet.diff
    (MeasurableSet.iUnion fun _ => Metric.isClosed_closedBall.measurableSet)
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  unfold causalHardScoreMeasure
  rw [withDensity_apply _ (hs.inter hC), withDensity_apply _ (hs.inter hC)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (hs.inter hC)] with x hx
  have hxBalls : ∀ j, x ∉ Metric.closedBall (centers j) w := by
    intro j hxj
    exact hx.2.2 (Set.mem_iUnion.2 ⟨j, hxj⟩)
  rw [indicator_of_mem hx.2.1, indicator_of_mem hx.2.1]
  unfold causalHardScoreDensity
  rw [packingAngularDensity_eq_one_off_cells hw omega hxBalls,
    packingAngularDensity_eq_one_off_cells hw omega' hxBalls]

/-- Restricting to the complement of all hard cells is bit-independent.  This
version includes the zero-mass region outside the hard square and therefore
matches the full-law hypercube locality clause directly. -/
-- @node: causalHardScoreMeasure_restrict_compl_cells_eq
lemma causalHardScoreMeasure_restrict_compl_cells_eq {M : ℕ}
    {b cA delta w : ℝ} (hw : 0 < w) {centers : Fin M → Score}
    (omega omega' : Fin M → Bool) :
    (causalHardScoreMeasure b cA delta w centers omega).restrict
        ((⋃ j, causalHardCell (centers j) w)ᶜ) =
      (causalHardScoreMeasure b cA delta w centers omega').restrict
        ((⋃ j, causalHardCell (centers j) w)ᶜ) := by
  let C := (⋃ j, causalHardCell (centers j) w)ᶜ
  have hC : MeasurableSet C :=
    (MeasurableSet.iUnion fun _ ↦ Metric.isClosed_closedBall.measurableSet).compl
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  unfold causalHardScoreMeasure
  rw [withDensity_apply _ (hs.inter hC), withDensity_apply _ (hs.inter hC)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (hs.inter hC)] with x hx
  by_cases hxS : x ∈ causalHardSquare
  · rw [indicator_of_mem hxS, indicator_of_mem hxS]
    unfold causalHardScoreDensity
    have hxBalls : ∀ j, x ∉ causalHardCell (centers j) w := by
      intro j hxj
      exact hx.2 (Set.mem_iUnion.2 ⟨j, hxj⟩)
    rw [packingAngularDensity_eq_one_off_cells hw omega hxBalls,
      packingAngularDensity_eq_one_off_cells hw omega' hxBalls]
  · rw [indicator_of_notMem hxS, indicator_of_notMem hxS]

/-- The unscaled angular density integrates to the hard square's area. -/
-- @node: causalHardPackingDensity_integral_square
lemma causalHardPackingDensity_integral_square {M : ℕ}
    {b cA delta w : ℝ} (centers : Fin M → Score)
    (omega : Fin M → Bool) (hb : 0 < b) (hscale : 0 < cA * delta)
    (hw : 0 < w)
    (hcell : ∀ j, Metric.closedBall (centers j) w ⊆ causalHardSquare) :
    (∫ x : Score in causalHardSquare,
      packingAngularDensity b cA delta w centers omega x) = 36 := by
  have hconst : IntegrableOn (fun _ : Score ↦ (1 : ℝ)) causalHardSquare :=
    continuous_const.continuousOn.integrableOn_compact causalHardSquare_isCompact
  have hterms : ∀ j : Fin M, IntegrableOn
      (fun x : Score ↦ if omega j then
        packingAngularTerm b cA delta w (centers j) x else 0)
      causalHardSquare := by
    intro j
    by_cases hj : omega j = true
    · simpa [hj] using
        (packingAngularTerm_continuous hb hscale
          (centers j)).continuousOn.integrableOn_compact causalHardSquare_isCompact
    · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
      simpa [hjf] using
        continuous_const.continuousOn.integrableOn_compact
          (K := causalHardSquare) causalHardSquare_isCompact
  unfold packingAngularDensity
  rw [integral_add hconst (integrable_finset_sum _ fun j _ ↦ hterms j)]
  rw [integral_const]
  change ((volume.restrict causalHardSquare) Set.univ).toReal * 1 + _ = 36
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    causalHardSquare_volume]
  norm_num
  have hz : (∫ x : Score in causalHardSquare,
      ∑ j, if omega j then
        packingAngularTerm b cA delta w (centers j) x else 0) = 0 := by
    rw [integral_finset_sum _ fun j _ ↦ hterms j]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : omega j = true
    · simp only [hj, if_true]
      rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero
        causalHardSquare_measurableSet (hcell j)]
      · exact packingAngularTerm_integral_closedBall (b := b) (cA := cA)
          (delta := delta) (w := w) (centers j)
      · rintro x ⟨_, hxBall⟩
        apply packingAngularTerm_eq_zero_of_bandwidth_le_dist hw
        exact (not_le.mp (by simpa [Metric.mem_closedBall] using hxBall)).le
    · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
      simp [hjf]
  rw [hz]

/-- The angular score measure is normalized to total mass one. -/
-- @node: causalHardScoreMeasure_isProbabilityMeasure
lemma causalHardScoreMeasure_isProbabilityMeasure {M : ℕ}
    {b cA delta w : ℝ} (centers : Fin M → Score)
    (omega : Fin M → Bool) (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, Metric.closedBall (centers j) w ⊆ causalHardSquare) :
    IsProbabilityMeasure (causalHardScoreMeasure b cA delta w centers omega) := by
  rw [isProbabilityMeasure_iff, causalHardScoreMeasure,
    withDensity_apply _ MeasurableSet.univ]
  have hcont := causalHardScoreDensity_continuous (w := w)
    centers omega hb hscale
  have hint : Integrable
      (causalHardSquare.indicator
        (causalHardScoreDensity b cA delta w centers omega)) volume :=
    (hcont.continuousOn.integrableOn_compact
      causalHardSquare_isCompact).integrable_indicator causalHardSquare_measurableSet
  have hnonneg : 0 ≤ᵐ[volume]
      causalHardSquare.indicator
        (causalHardScoreDensity b cA delta w centers omega) := by
    filter_upwards with x
    by_cases hx : x ∈ causalHardSquare
    · rw [Set.indicator_of_mem hx]
      exact (by norm_num : (0 : ℝ) ≤ 1 / 48).trans
        (causalHardScoreDensity_mem_Icc hcA hdelta hw hsep omega x).1
    · rw [Set.indicator_of_notMem hx]
      exact le_rfl
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [integral_indicator causalHardSquare_measurableSet]
  unfold causalHardScoreDensity
  rw [integral_const_mul,
    causalHardPackingDensity_integral_square centers omega hb hscale hw hcell]
  norm_num

/-- Every complete packing cell has the exact bit-independent probability
`pi * w² / 36`. -/
-- @node: causalHardScoreMeasure_cell_mass
lemma causalHardScoreMeasure_cell_mass {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : Metric.closedBall (centers j) w ⊆ causalHardSquare) :
    causalHardScoreMeasure b cA delta w centers omega
        (Metric.closedBall (centers j) w) =
      ENNReal.ofReal (Real.pi * w ^ 2 / 36) := by
  rw [causalHardScoreMeasure, withDensity_apply _
    Metric.isClosed_closedBall.measurableSet]
  have hcont := causalHardScoreDensity_continuous (w := w)
    centers omega hb hscale
  have hint : IntegrableOn
      (causalHardScoreDensity b cA delta w centers omega)
      (Metric.closedBall (centers j) w) :=
    hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Metric.closedBall (centers j) w)]
      causalHardScoreDensity b cA delta w centers omega := by
    filter_upwards with x
    exact (by norm_num : (0 : ℝ) ≤ 1 / 48).trans
      (causalHardScoreDensity_mem_Icc hcA hdelta hw hsep omega x).1
  have hind : (∀ᵐ x ∂volume.restrict (Metric.closedBall (centers j) w),
      causalHardSquare.indicator
          (causalHardScoreDensity b cA delta w centers omega) x =
        causalHardScoreDensity b cA delta w centers omega x) := by
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet]
      with x hx
    rw [Set.indicator_of_mem (hcell hx)]
  have hind' : (∀ᵐ x ∂volume.restrict (Metric.closedBall (centers j) w),
      ENNReal.ofReal (causalHardSquare.indicator
          (causalHardScoreDensity b cA delta w centers omega) x) =
        ENNReal.ofReal (causalHardScoreDensity b cA delta w centers omega x)) := by
    filter_upwards [hind] with x hx
    rw [hx]
  rw [lintegral_congr_ae hind']
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  unfold causalHardScoreDensity
  rw [integral_const_mul,
    packingAngularDensity_integral_closedBall j centers omega hb hscale hw hsep]
  rw [show volume (Metric.closedBall (centers j) w) =
      ENNReal.ofReal (Real.pi * w ^ 2) by
    exact causalHardCell_volume (centers j) w hw.le]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * w ^ 2)]
  congr 1
  ring

end CausalSmith.Stat.BddUniformLogPenalty
